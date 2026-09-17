/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Polynomial
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# Gauss's lemma for heights

At a nonarchimedean absolute value the local factor of the height of a polynomial — the supremum
of the absolute values of its coefficients — is exactly multiplicative:
`⨆ n, v ((p * q).coeff n) = (⨆ n, v (p.coeff n)) * ⨆ n, v (q.coeff n)`. This is Gauss's lemma,
and it is the only place in the theory where the ultrametric inequality is used sharply. Its
consequence for the height itself is that the discrepancy between `mulHeight (p * q)` and
`mulHeight p * mulHeight q` is *purely archimedean*: a bound on the local factors at the
archimedean places alone already bounds the height of the product, with the exponent
`Height.totalWeight K`. Supplying that archimedean bound is Gelfond's inequality, Layer 2.3;
this file supplies everything else.

## Main results

* `Polynomial.iSup_coeff_mul` and `MvPolynomial.iSup_coeff_mul`: **Gauss's lemma**, the
  multiplicativity of the local factor at a nonarchimedean absolute value.
* `Finsupp.mulHeight_le_of_forall_iSup_le` and
  `Finsupp.mulHeight_mul_mulHeight_le_of_forall_le_iSup`: the transport, in both directions. A
  comparison of local factors that is an *equality* at the nonarchimedean places and holds up to
  a factor `C` at the archimedean ones compares the heights up to `C ^ totalWeight K`.
* `Polynomial.mulHeight_mul_le_of_forall_iSup_le` and
  `Polynomial.mulHeight_mul_mulHeight_le_of_forall_le_iSup`, with their `MvPolynomial` forms: the
  same statement for polynomials, with Gauss's lemma already discharging the nonarchimedean half.
  This is the shape Layer 2.3 instantiates at `C = 2 ^ (natDegree p + natDegree q)`.
* `Polynomial.mulHeight_mul` and `MvPolynomial.mulHeight_mul`: the height of a product is the
  product of the heights when there are no archimedean places at all.
* `Polynomial.iSup_coeff_eq_gaussNorm`: the local factor is Mathlib's Gauss norm at `c = 1`, and
  `Polynomial.iSup_coeff_eq_iSup_fin`: it is the supremum over `Fin (natDegree p + 1)`, the local
  form of `Polynomial.mulHeight_eq_mulHeight_coeff`.
* `Finsupp.exists_min_eq_iSup_apply`: the supremum of `v ∘ x` is attained, and attained at an
  index minimal for any given linear order. This is what the multivariate Gauss lemma needs.

Every multiplicative statement is accompanied by its logarithmic form.

## Implementation notes

The univariate half is Mathlib's: `Polynomial.gaussNorm_mul` is Gauss's lemma, and all that is
missing is the identification of the local factor `⨆ n : ℕ, v (p.coeff n)` with
`Polynomial.gaussNorm v 1 p`, which is `Polynomial.iSup_coeff_eq_gaussNorm`.

The multivariate half is not. Mathlib has `MvPowerSeries.gaussNorm_mul_eq_mul`, but it takes as a
hypothesis exactly the hard part — the existence of a pair of exponents `i`, `j` dominating the
antidiagonal of `i + j` — and nothing supplies it. Producing it needs a linear order on
`σ →₀ ℕ` compatible with addition, so that "the least exponent among those where `v (coeff ·)` is
largest" makes sense. Mathlib's `MonomialOrder` is *not* usable: its only construction is
`MonomialOrder.lex`, which requires `[WellFoundedGT σ]` — false already for `σ = ℕ` — and the
structure demands a well-founded order, which the argument does not need. What it needs is only
`Lex (σ →₀ ℕ)`, a `LinearOrder` and an `IsOrderedCancelAddMonoid` for every `[LinearOrder σ]`; and
any `σ` carries a linear order classically. The minimum is taken over a *finite* set — the set of
exponents realising the supremum, a subset of the support — so no well-foundedness is involved.

The transport from local factors to heights goes through
`Height.mulHeight_fun_mul_eq`, the Segre relation, applied to the multiplication table
`fun a ↦ x a.1 * y a.2` on `x.support × y.support`. That lemma already contains the splitting of
the nonarchimedean `finprod` over a product, which is otherwise unavailable here: Mathlib's
`Height.hasFiniteMulSupport_iSup_nonarchAbsVal` is `private` and assumes a finite index type,
while the index type of a polynomial's coefficients is `ℕ`.

The junk value `mulHeight 0 = 1` makes the two directions asymmetric. The upper bound holds with
no hypotheses; the lower bound is false at `p = 0` — over `ℚ`, `mulHeight 0 * mulHeight (X - 100)`
is `100` while `mulHeight (0 * (X - 100))` is `1` — so `p ≠ 0` and `q ≠ 0` are not removable
there. Both are among the examples at the end of the file.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 1.6.3. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
(2000), §B.7.

This is Layer 2.2 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Finsupp

open Height AdmissibleAbsValues

variable {K : Type*} [Field K] {α β γ : Type*}

/-!
### The supremum of an absolute value on a finitely supported function

The supremum is attained, and can be taken at an index minimal for any prescribed linear order.
This is the ingredient the multivariate Gauss lemma needs: the "leading" exponent of a polynomial
for Gauss's lemma is not the one of largest degree, but the least one among those of largest
coefficient.
-/

/-- The supremum of `v ∘ x` over the index type is attained, and is attained at an index that is
minimal for a prescribed order: all indices strictly below it give a strictly smaller value. -/
lemma exists_min_eq_iSup_apply {δ : Type*} [LinearOrder δ] (f : α → δ) {x : α →₀ K} (hx : x ≠ 0)
    (v : AbsoluteValue K ℝ) :
    ∃ i, v (x i) = (⨆ m : α, v (x m)) ∧ ∀ a, f a < f i → v (x a) < ⨆ m : α, v (x m) := by
  classical
  obtain ⟨i₁, hi₁⟩ := Finsupp.support_nonempty_iff.mpr hx
  have hpos : 0 < ⨆ m : α, v (x m) :=
    lt_of_lt_of_le (v.pos (Finsupp.mem_support_iff.mp hi₁))
      (le_ciSup (bddAbove_range_apply x v) i₁)
  have hne : Nonempty x.support := ⟨⟨i₁, hi₁⟩⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i : x.support, v (x i.val) = ⨆ i : x.support, v (x i.val) :=
    exists_eq_ciSup_of_finite
  have hSne : (x.support.filter fun m ↦ v (x m) = ⨆ m : α, v (x m)).Nonempty :=
    ⟨i₀.val, by simp [i₀.prop, hi₀, iSup_apply_eq_iSup_support x]⟩
  obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image _ f hSne
  refine ⟨i, (Finset.mem_filter.mp hiS).2, fun a ha ↦ ?_⟩
  rcases eq_or_lt_of_le (le_ciSup (bddAbove_range_apply x v) a) with h | h
  · refine absurd (hmin a (Finset.mem_filter.mpr ⟨?_, h⟩)) ha.not_ge
    refine Finsupp.mem_support_iff.mpr fun hc ↦ ?_
    rw [hc, map_zero] at h
    exact hpos.ne h
  · exact h

/-!
### Transport from local factors to heights

A comparison of local factors that is an equality at every nonarchimedean absolute value and
holds up to a constant `C` at every archimedean one compares the heights up to
`C ^ Height.totalWeight K`. Nothing here is special to polynomials.
-/

variable [AdmissibleAbsValues K]

private lemma prod_le_prod_of_forall {F G : AbsoluteValue K ℝ → ℝ} {C : ℝ}
    (hF : ∀ v, 0 ≤ F v) (hG : ∀ v, 0 ≤ G v)
    (harch : ∀ v ∈ archAbsVal (K := K), G v ≤ C * F v)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), G v = F v) :
    (archAbsVal.map G).prod * ∏ᶠ v : nonarchAbsVal (K := K), G v.val
      ≤ C ^ totalWeight K * ((archAbsVal.map F).prod * ∏ᶠ v : nonarchAbsVal (K := K), F v.val) := by
  have hfin : ∏ᶠ v : nonarchAbsVal (K := K), G v.val = ∏ᶠ v : nonarchAbsVal (K := K), F v.val :=
    finprod_congr fun v ↦ hnon v.val v.prop
  have harch' : (archAbsVal.map G).prod ≤ C ^ totalWeight K * (archAbsVal.map F).prod := by
    calc (archAbsVal.map G).prod
        ≤ (archAbsVal.map fun v ↦ C * F v).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hG v) harch
      _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod * (archAbsVal.map F).prod :=
          Multiset.prod_map_mul
      _ = C ^ totalWeight K * (archAbsVal.map F).prod := by
          rw [Multiset.map_const', Multiset.prod_replicate]
          rfl
  rw [hfin, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right harch' (finprod_nonneg fun v ↦ hF v.val)

omit [AdmissibleAbsValues K] in
private lemma iSup_fun_mul_eq (x : α →₀ K) (y : β →₀ K) (v : AbsoluteValue K ℝ) :
    (⨆ a : x.support × y.support, v (x a.1.val * y a.2.val))
      = (⨆ i : α, v (x i)) * ⨆ i : β, v (y i) := by
  rw [Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v (fun i : x.support ↦ x i.val)
    (fun i : y.support ↦ y i.val), ← iSup_apply_eq_iSup_support x v,
    ← iSup_apply_eq_iSup_support y v]

omit [AdmissibleAbsValues K] in
private lemma ne_zero_restrict {x : α →₀ K} (hx : x ≠ 0) : (fun i : x.support ↦ x i.val) ≠ 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
  exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩

omit [AdmissibleAbsValues K] in
private lemma ne_zero_table {x : α →₀ K} {y : β →₀ K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (fun a : x.support × y.support ↦ x a.1.val * y a.2.val) ≠ 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hy
  exact Function.ne_iff.mpr ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩,
    mul_ne_zero (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)⟩

/-- **The loss is purely archimedean, upper half.** If the local factor of `z` is at most `C`
times the product of those of `x` and `y` at every archimedean absolute value, and is *equal* to
it at every nonarchimedean one, then the height of `z` is at most `C ^ totalWeight K` times the
product of the heights. -/
theorem mulHeight_le_of_forall_iSup_le {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K} {C : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ i : γ, v (z i)) ≤ C * ((⨆ i : α, v (x i)) * ⨆ i : β, v (y i)))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K),
      (⨆ i : γ, v (z i)) = (⨆ i : α, v (x i)) * ⨆ i : β, v (y i)) :
    z.mulHeight ≤ C ^ totalWeight K * (x.mulHeight * y.mulHeight) := by
  have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
  rw [← Finsupp.mulHeight_coe_eq z, Height.mulHeight_eq hzc, Finsupp.mulHeight, Finsupp.mulHeight,
    ← Height.mulHeight_fun_mul_eq (ne_zero_restrict hx) (ne_zero_restrict hy),
    Height.mulHeight_eq (ne_zero_table hx hy)]
  simp only [iSup_fun_mul_eq x y]
  exact prod_le_prod_of_forall
    (fun v ↦ mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    (fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) harch hnon

/-- **The loss is purely archimedean, lower half.** The companion of
`Finsupp.mulHeight_le_of_forall_iSup_le`, bounding the product of the heights by the height of
the object whose local factors they multiply to. -/
theorem mulHeight_mul_mulHeight_le_of_forall_le_iSup {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K}
    {C : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ i : α, v (x i)) * ⨆ i : β, v (y i)) ≤ C * ⨆ i : γ, v (z i))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K),
      (⨆ i : γ, v (z i)) = (⨆ i : α, v (x i)) * ⨆ i : β, v (y i)) :
    x.mulHeight * y.mulHeight ≤ C ^ totalWeight K * z.mulHeight := by
  have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
  rw [← Finsupp.mulHeight_coe_eq z, Height.mulHeight_eq hzc, Finsupp.mulHeight, Finsupp.mulHeight,
    ← Height.mulHeight_fun_mul_eq (ne_zero_restrict hx) (ne_zero_restrict hy),
    Height.mulHeight_eq (ne_zero_table hx hy)]
  simp only [iSup_fun_mul_eq x y]
  exact prod_le_prod_of_forall (fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _)
    (fun v ↦ mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _)) harch fun v hv ↦ (hnon v hv).symm

end Finsupp

namespace Polynomial

open Height AdmissibleAbsValues

section LocalFactor

variable {K : Type*} [Field K]

/-!
### Gauss's lemma, univariate

The local factor of the height at an absolute value `v` is Mathlib's Gauss norm at `c = 1`, and
Gauss's lemma is `Polynomial.gaussNorm_mul`.
-/

/-- The local factor of the height at `v` is Mathlib's Gauss norm at `c = 1`. -/
theorem iSup_coeff_eq_gaussNorm (v : AbsoluteValue K ℝ) (p : K[X]) :
    (⨆ n : ℕ, v (p.coeff n)) = p.gaussNorm v 1 := by
  rw [← Polynomial.gaussNorm_coe_powerSeries v p zero_le_one, PowerSeries.gaussNorm_eq]
  simp

/-- The local factor only sees the coefficients up to the degree: it is the supremum over
`Fin (natDegree p + 1)`, the local form of `Polynomial.mulHeight_eq_mulHeight_coeff`. -/
theorem iSup_coeff_eq_iSup_fin (v : AbsoluteValue K ℝ) (p : K[X]) :
    (⨆ n : ℕ, v (p.coeff n)) = ⨆ i : Fin (p.natDegree + 1), v (p.coeff i.val) := by
  refine le_antisymm (Real.iSup_le (fun n ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    (Real.iSup_le (fun i ↦ le_ciSup (Finsupp.bddAbove_range_apply p.coeff v) i.val)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  rcases le_or_gt n p.natDegree with h | h
  · exact Finite.le_ciSup_of_le (⟨n, Nat.lt_succ_of_le h⟩ : Fin (p.natDegree + 1)) le_rfl
  · rw [p.coeff_eq_zero_of_natDegree_lt h, map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _

/-- The local factor of a nonzero polynomial is positive. -/
theorem iSup_coeff_pos {v : AbsoluteValue K ℝ} {p : K[X]} (hp : p ≠ 0) :
    0 < ⨆ n : ℕ, v (p.coeff n) := by
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hp
  exact lt_of_lt_of_le (v.pos (Polynomial.mem_support_iff.mp hn))
    (le_ciSup (Finsupp.bddAbove_range_apply p.coeff v) n)

/-- **Gauss's lemma for heights** (Bombieri–Gubler, Lemma 1.6.3; Hindry–Silverman, §B.7). At a
nonarchimedean absolute value the local factor of the height is exactly multiplicative. This is
the only place in the theory where the ultrametric inequality is used sharply, and it is what
makes the loss in Gelfond's inequality purely archimedean. -/
theorem iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (p q : K[X]) :
    (⨆ n : ℕ, v ((p * q).coeff n)) = (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) := by
  simp only [iSup_coeff_eq_gaussNorm]
  exact Polynomial.gaussNorm_mul hv one_pos p q

/-- The logarithmic form of Gauss's lemma: the local log-factors add. -/
theorem log_iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) {p q : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    Real.log (⨆ n : ℕ, v ((p * q).coeff n))
      = Real.log (⨆ n : ℕ, v (p.coeff n)) + Real.log (⨆ n : ℕ, v (q.coeff n)) := by
  rw [iSup_coeff_mul hv, Real.log_mul (iSup_coeff_pos hp).ne' (iSup_coeff_pos hq).ne']

end LocalFactor

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-!
### From Gauss's lemma to the height of a product

Gauss's lemma discharges the nonarchimedean half of the transport lemmas of the first section.
What remains is a hypothesis at the archimedean places only; Layer 2.3 supplies it with
`C = 2 ^ (natDegree p + natDegree q)`.
-/

omit [AdmissibleAbsValues K] in
private lemma coeff_ne_zero {p : K[X]} (hp : p ≠ 0) : p.coeff ≠ 0 :=
  Finsupp.support_nonempty_iff.mp (Polynomial.support_nonempty.mpr hp)

/-- **The height of a product, upper half.** A bound on the local factors at the *archimedean*
absolute values alone bounds the height of `p * q`: Gauss's lemma makes the nonarchimedean
contribution exact. No nonvanishing hypothesis is needed — at `p = 0` both sides are governed by
the junk value. -/
theorem mulHeight_mul_le_of_forall_iSup_le {p q : K[X]} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ n : ℕ, v ((p * q).coeff n)) ≤ C * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n))) :
    (p * q).mulHeight ≤ C ^ totalWeight K * (p.mulHeight * q.mulHeight) := by
  have hCw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_mul, Polynomial.mulHeight_zero, one_mul]
    exact one_le_mul_of_one_le_of_one_le hCw q.one_le_mulHeight
  rcases eq_or_ne q 0 with rfl | hq
  · rw [mul_zero, Polynomial.mulHeight_zero, mul_one]
    exact one_le_mul_of_one_le_of_one_le hCw p.one_le_mulHeight
  exact Finsupp.mulHeight_le_of_forall_iSup_le (coeff_ne_zero hp) (coeff_ne_zero hq)
    (coeff_ne_zero (mul_ne_zero hp hq)) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

/-- The logarithmic form of `Polynomial.mulHeight_mul_le_of_forall_iSup_le`. -/
theorem logHeight_mul_le_of_forall_iSup_le {p q : K[X]} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ n : ℕ, v ((p * q).coeff n)) ≤ C * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n))) :
    (p * q).logHeight ≤ totalWeight K * Real.log C + (p.logHeight + q.logHeight) := by
  have hC₀ : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    ← Real.log_pow, ← Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q),
    ← Real.log_mul (pow_ne_zero _ hC₀.ne')
      (mul_ne_zero (mulHeight_ne_zero p) (mulHeight_ne_zero q))]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_mul_le_of_forall_iSup_le hC harch)

/-- **The height of a product, lower half.** The junk value makes the nonvanishing hypotheses
necessary here: over `ℚ`, `mulHeight 0 * mulHeight (X - C 100) = 100` while
`mulHeight (0 * (X - C 100)) = 1`. -/
theorem mulHeight_mul_mulHeight_le_of_forall_le_iSup {p q : K[X]} {C : ℝ} (hp : p ≠ 0)
    (hq : q ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) ≤ C * ⨆ n : ℕ, v ((p * q).coeff n)) :
    p.mulHeight * q.mulHeight ≤ C ^ totalWeight K * (p * q).mulHeight :=
  Finsupp.mulHeight_mul_mulHeight_le_of_forall_le_iSup (coeff_ne_zero hp) (coeff_ne_zero hq)
    (coeff_ne_zero (mul_ne_zero hp hq)) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

/-- The logarithmic form of `Polynomial.mulHeight_mul_mulHeight_le_of_forall_le_iSup`. -/
theorem logHeight_add_logHeight_le_of_forall_le_iSup {p q : K[X]} {C : ℝ} (hC : 0 < C)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) ≤ C * ⨆ n : ℕ, v ((p * q).coeff n)) :
    p.logHeight + q.logHeight ≤ totalWeight K * Real.log C + (p * q).logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    ← Real.log_pow, ← Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q),
    ← Real.log_mul (pow_ne_zero _ hC.ne') (mulHeight_ne_zero (p * q))]
  exact Real.log_le_log (mul_pos (mulHeight_pos p) (mulHeight_pos q))
    (mulHeight_mul_mulHeight_le_of_forall_le_iSup hp hq harch)

/-- **The height of a product is the product of the heights when there are no archimedean
places.** Gauss's lemma is then the whole story, and there is no loss at all. Over a number field
`totalWeight K = [K : ℚ] ≠ 0`, so this is a statement about function fields. -/
theorem mulHeight_mul (h : totalWeight K = 0) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).mulHeight = p.mulHeight * q.mulHeight := by
  have harch : archAbsVal (K := K) = 0 := Multiset.card_eq_zero.mp h
  refine le_antisymm ?_ ?_
  · simpa [h] using mulHeight_mul_le_of_forall_iSup_le (C := 1) le_rfl (by simp [harch])
  · simpa [h] using
      mulHeight_mul_mulHeight_le_of_forall_le_iSup (C := 1) hp hq (by simp [harch])

/-- The logarithmic form of `Polynomial.mulHeight_mul`. -/
theorem logHeight_mul (h : totalWeight K = 0) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).logHeight = p.logHeight + q.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_mul h hp hq, Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q)]

end Heights

end Polynomial

namespace MvPolynomial

open Height AdmissibleAbsValues

section LocalFactor

variable {K : Type*} [Field K] {σ : Type*}

/-!
### Gauss's lemma, multivariate

Mathlib has no multivariate Gauss's lemma: `MvPowerSeries.gaussNorm_mul_eq_mul` assumes the
existence of a dominant pair of exponents, which is the whole content. It is produced here from
the lexicographic order on `σ →₀ ℕ`, which needs only a linear order on `σ` — available
classically for any `σ` — and none of the well-foundedness that `MonomialOrder` demands.
-/

omit [Field K] in
private lemma coeff_ne_zero [CommSemiring K] {p : MvPolynomial σ K} (hp : p ≠ 0) :
    p.coeff ≠ 0 :=
  Finsupp.support_nonempty_iff.mp (MvPolynomial.support_nonempty.mpr hp)

/-- The local factor of a nonzero polynomial is positive. -/
theorem iSup_coeff_pos {v : AbsoluteValue K ℝ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    0 < ⨆ m : σ →₀ ℕ, v (p.coeff m) := by
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr (coeff_ne_zero hp)
  exact lt_of_lt_of_le (v.pos (Finsupp.mem_support_iff.mp hm))
    (le_ciSup (Finsupp.bddAbove_range_apply p.coeff v) m)

private lemma iSup_coeff_mul_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) := by
  classical
  have hbp := Finsupp.bddAbove_range_apply p.coeff v
  have hbq := Finsupp.bddAbove_range_apply q.coeff v
  have hnp : (0 : ℝ) ≤ ⨆ m : σ →₀ ℕ, v (p.coeff m) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hnq : (0 : ℝ) ≤ ⨆ m : σ →₀ ℕ, v (q.coeff m) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rw [MvPolynomial.coeff_mul]
  refine hv.apply_sum_le.trans (Real.iSup_le ?_ (by positivity))
  rintro ⟨⟨a, b⟩, hab⟩
  rw [map_mul]
  exact mul_le_mul (le_ciSup hbp a) (le_ciSup hbq b) (v.nonneg _) hnp

private lemma le_iSup_coeff_mul [LinearOrder σ] {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (⨆ m : σ →₀ ℕ, v (p.coeff m)) * (⨆ m : σ →₀ ℕ, v (q.coeff m))
      ≤ ⨆ m : σ →₀ ℕ, v ((p * q).coeff m) := by
  classical
  have hbp := Finsupp.bddAbove_range_apply p.coeff v
  have hbq := Finsupp.bddAbove_range_apply q.coeff v
  have hbpq := Finsupp.bddAbove_range_apply (p * q).coeff v
  obtain ⟨i, hi, hilt⟩ :=
    Finsupp.exists_min_eq_iSup_apply (toLex : (σ →₀ ℕ) → Lex (σ →₀ ℕ)) (coeff_ne_zero hp) v
  obtain ⟨j, hj, hjlt⟩ :=
    Finsupp.exists_min_eq_iSup_apply (toLex : (σ →₀ ℕ) → Lex (σ →₀ ℕ)) (coeff_ne_zero hq) v
  have key : v ((p * q).coeff (i + j)) = v (p.coeff i * q.coeff j) := by
    rw [MvPolynomial.coeff_mul]
    refine hv.apply_sum_eq_of_lt (fun x : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ p.coeff x.1 * q.coeff x.2)
      v.map_neg (k := (i, j)) (Finset.mem_antidiagonal.mpr rfl) ?_
    rintro ⟨a, b⟩ hab hne
    have hsum : a + b = i + j := Finset.mem_antidiagonal.mp hab
    have hane : a ≠ i := by
      rintro rfl
      exact hne (by simp [add_left_cancel hsum])
    rw [map_mul, map_mul, hi, hj]
    rcases lt_or_gt_of_ne (fun h ↦ hane (toLex.injective h)) with h | h
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_ciSup hbq b) (v.nonneg _))
        (mul_lt_mul_of_pos_right (hilt a h) (iSup_coeff_pos hq))
    · have hb : toLex b < toLex j := by
        have heq : toLex a + toLex b = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hsum]
        by_contra hcon
        exact absurd heq (ne_of_gt (add_lt_add_of_lt_of_le h (not_lt.mp hcon)))
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_ciSup hbp a) (v.nonneg _))
        (mul_lt_mul_of_pos_left (hjlt b hb) (iSup_coeff_pos hp))
  calc (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)
      = v ((p * q).coeff (i + j)) := by rw [key, map_mul, hi, hj]
    _ ≤ ⨆ m : σ →₀ ℕ, v ((p * q).coeff m) := le_ciSup hbpq _

/-- **Gauss's lemma for heights, multivariate.** At a nonarchimedean absolute value the local
factor of the height is exactly multiplicative. The dominant exponent is the one *least* in a
monomial order among those realising the supremum, which is why a linear order on `σ →₀ ℕ`
compatible with addition — and no more — is what the proof needs. -/
theorem iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      = (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  classical
  let _ : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact le_antisymm (iSup_coeff_mul_le hv p q) (le_iSup_coeff_mul hv hp hq)

/-- The logarithmic form of the multivariate Gauss lemma. -/
theorem log_iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    Real.log (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      = Real.log (⨆ m : σ →₀ ℕ, v (p.coeff m)) + Real.log (⨆ m : σ →₀ ℕ, v (q.coeff m)) := by
  rw [iSup_coeff_mul hv, Real.log_mul (iSup_coeff_pos hp).ne' (iSup_coeff_pos hq).ne']

end LocalFactor

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-- **The height of a product, upper half, multivariate.** -/
theorem mulHeight_mul_le_of_forall_iSup_le {p q : MvPolynomial σ K} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ C * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))) :
    (p * q).mulHeight ≤ C ^ totalWeight K * (p.mulHeight * q.mulHeight) := by
  have hCw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_mul, MvPolynomial.mulHeight_zero, one_mul]
    exact one_le_mul_of_one_le_of_one_le hCw q.one_le_mulHeight
  rcases eq_or_ne q 0 with rfl | hq
  · rw [mul_zero, MvPolynomial.mulHeight_zero, mul_one]
    exact one_le_mul_of_one_le_of_one_le hCw p.one_le_mulHeight
  exact Finsupp.mulHeight_le_of_forall_iSup_le (coeff_ne_zero hp) (coeff_ne_zero hq)
    (coeff_ne_zero (mul_ne_zero hp hq)) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

/-- The logarithmic form of `MvPolynomial.mulHeight_mul_le_of_forall_iSup_le`. -/
theorem logHeight_mul_le_of_forall_iSup_le {p q : MvPolynomial σ K} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ C * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))) :
    (p * q).logHeight ≤ totalWeight K * Real.log C + (p.logHeight + q.logHeight) := by
  have hC₀ : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    ← Real.log_pow, ← Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q),
    ← Real.log_mul (pow_ne_zero _ hC₀.ne')
      (mul_ne_zero (mulHeight_ne_zero p) (mulHeight_ne_zero q))]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_mul_le_of_forall_iSup_le hC harch)

/-- **The height of a product, lower half, multivariate.** -/
theorem mulHeight_mul_mulHeight_le_of_forall_le_iSup {p q : MvPolynomial σ K} {C : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))
        ≤ C * ⨆ m : σ →₀ ℕ, v ((p * q).coeff m)) :
    p.mulHeight * q.mulHeight ≤ C ^ totalWeight K * (p * q).mulHeight :=
  Finsupp.mulHeight_mul_mulHeight_le_of_forall_le_iSup (coeff_ne_zero hp) (coeff_ne_zero hq)
    (coeff_ne_zero (mul_ne_zero hp hq)) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

/-- The logarithmic form of `MvPolynomial.mulHeight_mul_mulHeight_le_of_forall_le_iSup`. -/
theorem logHeight_add_logHeight_le_of_forall_le_iSup {p q : MvPolynomial σ K} {C : ℝ} (hC : 0 < C)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))
        ≤ C * ⨆ m : σ →₀ ℕ, v ((p * q).coeff m)) :
    p.logHeight + q.logHeight ≤ totalWeight K * Real.log C + (p * q).logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    ← Real.log_pow, ← Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q),
    ← Real.log_mul (pow_ne_zero _ hC.ne') (mulHeight_ne_zero (p * q))]
  exact Real.log_le_log (mul_pos (mulHeight_pos p) (mulHeight_pos q))
    (mulHeight_mul_mulHeight_le_of_forall_le_iSup hp hq harch)

/-- **The multivariate height is multiplicative when there are no archimedean places.** -/
theorem mulHeight_mul (h : totalWeight K = 0) {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).mulHeight = p.mulHeight * q.mulHeight := by
  have harch : archAbsVal (K := K) = 0 := Multiset.card_eq_zero.mp h
  refine le_antisymm ?_ ?_
  · simpa [h] using mulHeight_mul_le_of_forall_iSup_le (C := 1) le_rfl (by simp [harch])
  · simpa [h] using
      mulHeight_mul_mulHeight_le_of_forall_le_iSup (C := 1) hp hq (by simp [harch])

/-- The logarithmic form of `MvPolynomial.mulHeight_mul`. -/
theorem logHeight_mul (h : totalWeight K = 0) {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).logHeight = p.logHeight + q.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_mul h hp hq, Real.log_mul (mulHeight_ne_zero p) (mulHeight_ne_zero q)]

end Heights

end MvPolynomial

/-!
### Examples

The tests that fix the shape of the statements above: that the ultrametric hypothesis in Gauss's
lemma is not decoration, that the junk value forces the nonvanishing hypotheses on the lower half,
and that the archimedean loss can be nil.
-/

section Examples

open Height Polynomial

/-- **Rejection test, first half.** The local factor of `X + 1` at the ordinary absolute value
on `ℝ` is `1`. -/
example : (⨆ n : ℕ, AbsoluteValue.abs (((X : ℝ[X]) + 1).coeff n)) = 1 := by
  refine le_antisymm (Real.iSup_le (fun n ↦ ?_) zero_le_one)
    (le_ciSup_of_le (Finsupp.bddAbove_range_apply _ _) 0 (by simp))
  match n with
  | 0 => simp
  | 1 => simp [coeff_one]
  | (k + 2) => simp [coeff_X, coeff_one]

/-- **Rejection test, second half.** The local factor of `(X + 1) ^ 2` at the same absolute value
is `2`, not `1`: the ordinary absolute value on `ℝ` is archimedean, and `Polynomial.iSup_coeff_mul`
is false without `IsNonarchimedean`. The gap is exactly what Gelfond's inequality has to pay for,
and it is why the constant there is a power of two. -/
example : (⨆ n : ℕ, AbsoluteValue.abs ((((X : ℝ[X]) + 1) ^ 2).coeff n)) = 2 := by
  have hexp : ((X : ℝ[X]) + 1) ^ 2 = X ^ 2 + C 2 * X + C 1 := by
    simp only [map_ofNat, map_one]; ring
  refine le_antisymm (Real.iSup_le (fun n ↦ ?_) zero_le_two)
    (le_ciSup_of_le (Finsupp.bddAbove_range_apply _ _) 1 (by simp [hexp, coeff_one]))
  match n with
  | 0 => simp [hexp, coeff_one]
  | 1 => simp [hexp, coeff_one]
  | 2 => simp [hexp, coeff_one]
  | (k + 3) => simp [hexp, coeff_one]

/-- **Rejection test.** `Polynomial.mulHeight_mul_mulHeight_le_of_forall_le_iSup` cannot drop the
hypothesis `p ≠ 0`: at `p = 0` the left side is the junk value `1` times the height of `q`, which
is unbounded, while the right side collapses to a constant times `1`. Over `ℚ` with
`q = X - C 100` the two sides are `100` and `1`. -/
example : (0 : ℚ[X]).mulHeight * ((X : ℚ[X]) - C 100).mulHeight = 100 ∧
    ((0 : ℚ[X]) * ((X : ℚ[X]) - C 100)).mulHeight = 1 := by
  refine ⟨?_, by rw [zero_mul, Polynomial.mulHeight_zero]⟩
  rw [Polynomial.mulHeight_zero, one_mul, mulHeight_X_sub_C]
  simpa using Rat.mulHeight₁_natCast 100

/-- **Acceptance test.** The archimedean loss really can be nil: over `ℚ`,
`(X - 2)(X - 3) = X ^ 2 - 5X + 6` has height `6`, which is exactly `2 * 3`. So the factor
`2 ^ (deg p + deg q)` of Layer 2.3 is far from attained, which is the point of recording the
sharp Mahler-measure statement alongside it. -/
example : (((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3)).mulHeight
    = ((X : ℚ[X]) - C 2).mulHeight * ((X : ℚ[X]) - C 3).mulHeight := by
  have hdeg : (((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3)).natDegree = 2 := by
    rw [natDegree_mul (X_sub_C_ne_zero 2) (X_sub_C_ne_zero 3), natDegree_X_sub_C,
      natDegree_X_sub_C]
  have hexp : ((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3) = X ^ 2 - C 5 * X + C 6 := by
    simp only [map_ofNat]; ring
  have hcoeff : (fun i : Fin 3 ↦ (((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3)).coeff i.val)
      = (Int.cast : ℤ → ℚ) ∘ (![6, -5, 1] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;> simp [hexp]
  have hcov : ∀ m ∈ (((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3)).coeff.support,
      m ∈ Set.range (Fin.val : Fin 3 → ℕ) := by
    intro m hm
    have hm2 : m ∈ (((X : ℚ[X]) - C 2) * ((X : ℚ[X]) - C 3)).support := hm
    have h1 := le_natDegree_of_mem_supp m hm2
    rw [hdeg] at h1
    exact ⟨⟨m, by omega⟩, rfl⟩
  have hsup : (⨆ i : Fin 3, |(![6, -5, 1] : Fin 3 → ℤ) i|) = 6 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le 0 (by decide))
    fin_cases i <;> decide
  rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_comp _ _ Fin.val_injective hcov,
    hcoeff, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hsup, mulHeight_X_sub_C,
    mulHeight_X_sub_C, show ((2 : ℚ)) = ((2 : ℕ) : ℚ) by norm_num,
    show ((3 : ℚ)) = ((3 : ℕ) : ℚ) by norm_num, Rat.mulHeight₁_natCast, Rat.mulHeight₁_natCast]
  norm_num

/-- **Conformance.** Multiplying by a nonzero constant is exactly multiplicative, since a constant
has height `1`: the general bound is an equality here, at every place at once. -/
example {K : Type*} [Field K] [AdmissibleAbsValues K] (p : K[X]) {c : K} (hc : c ≠ 0) :
    (C c * p).mulHeight = (C c).mulHeight * p.mulHeight := by
  rw [mulHeight_C_mul p hc, mulHeight_C, one_mul]

end Examples
