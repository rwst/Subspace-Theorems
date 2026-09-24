/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceNormal
public import DiophantineApproximation.LinearFormValue
public import DiophantineApproximation.ApproximationRank

/-!
# The height of the span of an approximation domain

Step III of Bombieri–Gubler's proof of the Subspace Theorem (7.5.20, Lemma 7.5.21) compares the
height of `V(Q)`, the span of the approximation domain of level `Q`, with `log Q`. This file
proves the two estimates that comparison rests on, for a basis `y` of `V(Q)` drawn from the
domain, in terms of the Plücker point `plucker n y` whose height is that of `V(Q)`
(`Submodule.mulHeight_span_range`).

*Above.* At a place of `S` the coordinates of a point of the domain are bounded by the values of
the forms at it, so each Plücker coordinate is at most `Q` to `n` times the largest exponent; off
`S` the point is integral and the Plücker coordinate is at most `1`. Hence
`H(V(Q)) ≤ C · Q ^ (n ∑_{v ∈ S} d_v c_max(v))`.

*Below.* The wedge of the forms at a place, evaluated at the Plücker point, is at once a
determinant of the small numbers `L v i (y j)` — so it is at most `Q` to the sum of the
exponents omitting one — and a linear form in the Plücker coordinates with coefficients fixed by
the forms — so, by Liouville's inequality for the value of a linear form
(`DiophantineApproximation/LinearFormValue.lean`), it is at least the local factor of the Plücker
point divided by its height. Multiplying over `S` and using that the local factors over `S`
multiply to at least the height gives

```text
κ ^ |S| · H(V(Q))  ≤  H(V(Q)) ^ |S| · ∏_{v ∈ S} |D_v|_v  ≤  H(V(Q)) ^ |S| · C · Q ^ (w - γ),
```

with `w` the weight of the exponents and `γ` the weight along the chosen indices.

## Main definitions

* `NumberField.cMax`: the largest exponent at a place.
* `NumberField.weightAt`: the weight of the exponents along a choice of one index at each place.

## Main results

* `NumberField.exists_one_le_forall_mulHeight_plucker_le`: the upper bound.
* `NumberField.exists_pos_forall_prod_le`: the lower bound, over all of `S`.
* `NumberField.prod_apply_plucker_pi_le`: the upper bound on the same product, from the domain.
* `LinearMap.exists_inverse_forms`: an independent system of `#ι` forms on `Kⁱ` is invertible.
* `Finset.exists_pos_forall_le` and `Finset.exists_one_le_forall_le`: a constant uniform over a
  finite family, the device that keeps every constant below independent of `Q`.

## Implementation notes

⚠ **Every constant is quantified before `Q` and before the basis, and that is the whole point of
Lemma 7.5.21.** The book writes `C₄`, `C₅`, `C₆` and says they depend only on `K`, `S`, the forms
and `c`; here each is produced by `Finset.exists_pos_forall_le` or
`Finset.exists_one_le_forall_le` from a family indexed by the places of `S` and by `ι`, both
finite. The `⨅`/`⨆` of such a family is a product of truncations, which avoids the nonemptiness
side conditions of `Finset.inf'`.

⚠ **The lower bound is stronger than the book's, by one power of the height.** Summing the
per-place inequality costs `|S|` powers of `H(V(Q))` on the right but returns one on the left,
because the local factors of the Plücker point at the places of `S` multiply to at least its
height (`NumberField.mulHeight_plucker_le_prod`, which is where the integrality off `S` is
spent). The book's chain gives `H ^ (-|S|)`; this one gives `H ^ (1 - |S|)`.

⚠ **The inverse of the system of forms is used only for the upper bound.** The lower bound never
inverts anything: the coefficients it needs are the maximal minors of the coefficient matrix of
the forms, which are the coefficients of the wedge forms, and those are nonzero exactly because
the forms are independent (`exteriorPower.wedgeCoeff_ne_zero`).

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.20 and Lemma 7.5.21.

This is Layer 5.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Module exteriorPower Matrix Real NumberField Height

namespace Finset

/-- A positive lower bound for a family, uniform over a `Finset`. -/
theorem exists_pos_forall_le {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 < f a) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a ∈ s, κ ≤ f a := by
  classical
  refine ⟨∏ a ∈ s, min 1 (f a), Finset.prod_pos fun a ha ↦ lt_min zero_lt_one (hf a ha),
    fun a ha ↦ ?_⟩
  have h1 : ∏ b ∈ s.erase a, min 1 (f b) ≤ 1 :=
    Finset.prod_le_one₀ (fun b hb ↦ le_min zero_le_one (hf b (Finset.mem_of_mem_erase hb)).le)
      fun b _ ↦ min_le_left _ _
  have h2 : (0 : ℝ) < min 1 (f a) := lt_min zero_lt_one (hf a ha)
  calc ∏ b ∈ s, min 1 (f b) = (∏ b ∈ s.erase a, min 1 (f b)) * min 1 (f a) :=
        (Finset.prod_erase_mul s _ ha).symm
    _ ≤ 1 * min 1 (f a) := mul_le_mul_of_nonneg_right h1 h2.le
    _ ≤ f a := by rw [one_mul]; exact min_le_right _ _

/-- An upper bound for a family, uniform over a `Finset` and at least `1`. -/
theorem exists_one_le_forall_le {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ s, f a ≤ C := by
  classical
  have hnn : (0 : ℝ) ≤ ∑ a ∈ s, |f a| := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  refine ⟨1 + ∑ a ∈ s, |f a|, by linarith, fun a ha ↦ ?_⟩
  have h1 : |f a| ≤ ∑ b ∈ s, |f b| :=
    Finset.single_le_sum (f := fun b ↦ |f b|) (fun b _ ↦ abs_nonneg _) ha
  have := le_abs_self (f a)
  linarith

end Finset

namespace LinearMap

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- **A linearly independent system of `#ι` forms on `Kⁱ` can be inverted**: there are forms
reading back the coordinates of a point from its values under the system. -/
theorem exists_inverse_forms {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) :
    ∃ e : ι → Dual K (ι → K), ∀ (x : ι → K) (i : ι), e i (fun k ↦ l k x) = x i := by
  obtain ⟨u, hu⟩ : IsUnit (LinearMap.pi l : Module.End K (ι → K)) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (LinearMap.det_pi_ne_zero hl))
  refine ⟨fun i ↦ (Pi.basisFun K ι).coord i ∘ₗ (↑u⁻¹ : Module.End K (ι → K)), fun x i ↦ ?_⟩
  have hx : (fun k ↦ l k x) = (u : Module.End K (ι → K)) x := by rw [hu]; rfl
  have h1 : (↑u⁻¹ : Module.End K (ι → K)) ((u : Module.End K (ι → K)) x) = x := by
    calc (↑u⁻¹ : Module.End K (ι → K)) ((u : Module.End K (ι → K)) x)
        = ((↑u⁻¹ * ↑u : Module.End K (ι → K))) x := rfl
      _ = x := by rw [u.inv_mul]; rfl
  simp [hx, h1]

end LinearMap

namespace AbsoluteValue

variable {K : Type*} [Field K] {ρ : Type*} [Fintype ρ] [Nonempty ρ]

omit [Nonempty ρ] in
/-- The value of a linear form is at most the number of terms times the product of the local
factors of the coefficients and of the point. -/
theorem apply_sum_mul_le (v : AbsoluteValue K ℝ) (a z : ρ → K) :
    v (∑ s, a s * z s) ≤ (Fintype.card ρ : ℝ) * ((⨆ s, v (a s)) * ⨆ s, v (z s)) := by
  have hb : ∀ s, v (a s) * v (z s) ≤ (⨆ t, v (a t)) * ⨆ t, v (z t) := fun s ↦
    mul_le_mul (Finite.le_ciSup_of_le s le_rfl) (Finite.le_ciSup_of_le s le_rfl) (v.nonneg _)
      (le_trans (v.nonneg (a s)) (Finite.le_ciSup_of_le s le_rfl))
  calc v (∑ s, a s * z s) ≤ ∑ s, v (a s * z s) := v.sum_le _ _
    _ = ∑ s, v (a s) * v (z s) := by simp [map_mul]
    _ ≤ ∑ _s : ρ, (⨆ t, v (a t)) * ⨆ t, v (z t) := Finset.sum_le_sum fun s _ ↦ hb s
    _ = (Fintype.card ρ : ℝ) * ((⨆ s, v (a s)) * ⨆ s, v (z s)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The nonarchimedean companion of `AbsoluteValue.apply_sum_mul_le`: no count of the terms. -/
theorem apply_sum_mul_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (a z : ρ → K) : v (∑ s, a s * z s) ≤ (⨆ s, v (a s)) * ⨆ s, v (z s) := by
  have hb : ∀ s, v (a s) * v (z s) ≤ (⨆ t, v (a t)) * ⨆ t, v (z t) := fun s ↦
    mul_le_mul (Finite.le_ciSup_of_le s le_rfl) (Finite.le_ciSup_of_le s le_rfl) (v.nonneg _)
      (le_trans (v.nonneg (a s)) (Finite.le_ciSup_of_le s le_rfl))
  refine Finset.sum_induction _ (fun t ↦ v t ≤ (⨆ s, v (a s)) * ⨆ s, v (z s))
    (fun p q hp hq ↦ (hv p q).trans (max_le hp hq)) ?_ fun s _ ↦ by
      rw [map_mul]; exact hb s
  have h0 : (0 : ℝ) ≤ (⨆ s, v (a s)) * ⨆ s, v (z s) :=
    le_trans (mul_nonneg (v.nonneg (a Classical.ofNonempty)) (v.nonneg (z Classical.ofNonempty)))
      (hb Classical.ofNonempty)
  simpa using h0

end AbsoluteValue

/-- A form is the linear form in the coordinates given by its values at the standard basis. -/
theorem Module.Dual.apply_eq_sum {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Dual K (ι → K)) (x : ι → K) : f x = ∑ k, x k * f (Pi.single k 1) := by
  conv_lhs => rw [← (Pi.basisFun K ι).sum_repr x]
  simp [map_sum]

/-- **At a place where the system of forms is invertible, the coordinates of a point are
bounded by the values of the forms**, up to a constant depending only on the forms. -/
theorem NumberField.exists_one_le_forall_apply_le {K : Type*} [Field K] {ι : Type*} [Finite ι]
    [Nonempty ι] (v : AbsoluteValue K ℝ) {l : ι → Dual K (ι → K)}
    (hl : LinearIndependent K l) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (x : ι → K) (b : ℝ), 0 ≤ b → (∀ k, v (l k x) ≤ b) →
      ∀ i, v (x i) ≤ B * b := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨e, he⟩ := LinearMap.exists_inverse_forms hl
  obtain ⟨B₀, hB₀, hB⟩ := Finset.exists_one_le_forall_le (univ : Finset (ι × ι))
    fun p ↦ v (e p.1 (Pi.single p.2 1))
  refine ⟨(Fintype.card ι : ℝ) * B₀, ?_, fun x b hb hx i ↦ ?_⟩
  · have : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
    nlinarith
  · have hxi : x i = ∑ k, (l k x) * e i (Pi.single k 1) := by
      rw [← Module.Dual.apply_eq_sum (e i) (fun k ↦ l k x), he x i]
    rw [hxi]
    refine (AbsoluteValue.apply_sum_mul_le v (fun k ↦ l k x) (fun k ↦ e i (Pi.single k 1))).trans ?_
    have h1 : (⨆ k, v (l k x)) ≤ b := Real.iSup_le hx hb
    have h2 : (⨆ k, v (e i (Pi.single k 1))) ≤ B₀ :=
      Real.iSup_le (fun k ↦ hB (i, k) (mem_univ _)) (le_trans zero_le_one hB₀)
    have h3 : (0 : ℝ) ≤ ⨆ k, v (l k x) :=
      le_trans (v.nonneg (l (Classical.ofNonempty) x)) (Finite.le_ciSup_of_le _ le_rfl)
    have h5 : (0 : ℝ) ≤ ⨆ k, v (e i (Pi.single k 1)) :=
      le_trans (v.nonneg (e i (Pi.single Classical.ofNonempty 1)))
        (Finite.le_ciSup_of_le _ le_rfl)
    have hkey : (⨆ s, v (l s x)) * (⨆ s, v (e i (Pi.single s 1))) ≤ b * B₀ :=
      mul_le_mul h1 h2 h5 hb
    have h4 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    calc (Fintype.card ι : ℝ) * ((⨆ s, v (l s x)) * ⨆ s, v (e i (Pi.single s 1)))
        ≤ (Fintype.card ι : ℝ) * (b * B₀) := by nlinarith
      _ = (Fintype.card ι : ℝ) * B₀ * b := by ring


namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
  [Nonempty ι] {n : ℕ} {S₀ : Finset (FinitePlace K)}
  {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}

omit [NumberField K] in
/-- **The local factor of the Plücker point of a family is bounded by the local bound on the
values of the forms**, to the power `n`. -/
theorem exists_one_le_forall_apply_plucker_le (v : AbsoluteValue K ℝ) {l : ι → Dual K (ι → K)}
    (hl : LinearIndependent K l) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (y : Fin n → ι → K) (b : ℝ), 0 ≤ b → (∀ j k, v (l k (y j)) ≤ b) →
      ∀ t : Set.powersetCard ι n, v (plucker n y t) ≤ A * b ^ n := by
  obtain ⟨B, hB1, hB⟩ := exists_one_le_forall_apply_le v hl
  have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  have h2 : (1 : ℝ) ≤ B ^ n := one_le_pow₀ hB1
  refine ⟨n.factorial * B ^ n, by nlinarith, fun y b hb hy t ↦ ?_⟩
  have hcoord : ∀ j i, v (y j i) ≤ B * b := fun j i ↦ hB (y j) b hb (fun k ↦ hy j k) i
  have key := apply_plucker_le v y (b := fun _ ↦ B * b) (fun i j ↦ hcoord j i) t
  rw [Finset.prod_const, Set.powersetCard.card_eq] at key
  calc v (plucker n y t) ≤ n.factorial * (B * b) ^ n := key
    _ = n.factorial * B ^ n * b ^ n := by rw [mul_pow]; ring

/-- The largest exponent at a place. -/
def cMax (c : AbsoluteValue K ℝ → ι → ℝ) (v : AbsoluteValue K ℝ) : ℝ := ⨆ i, c v i

/-- **The local factors of the Plücker point of a domain basis**, at the places of `S` and
outside. -/
theorem exists_one_le_forall_iSup_apply_plucker_le
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ y : Fin n → ι → K,
      (∀ j, y j ∈ approxDomain S₀ L c Q) →
        (∀ (w : InfinitePlace K) (t : Set.powersetCard ι n),
            w (plucker n y t) ≤ A * Q ^ ((n : ℝ) * cMax c w.1)) ∧
        (∀ w ∈ S₀, ∀ t : Set.powersetCard ι n,
            w (plucker n y t) ≤ A * Q ^ ((n : ℝ) * cMax c w.1)) ∧
        ∀ w : FinitePlace K, w ∉ S₀ → ∀ t : Set.powersetCard ι n, w (plucker n y t) ≤ 1 := by
  classical
  choose AI hAI1 hAI using fun w : InfinitePlace K ↦
    exists_one_le_forall_apply_plucker_le (n := n) w.1 (hLinf w)
  choose AF hAF1 hAF using fun w : {w : FinitePlace K // w ∈ S₀} ↦
    exists_one_le_forall_apply_plucker_le (n := n) w.1.1 (hLfin w.1 w.2)
  obtain ⟨A₁, hA₁, hA₁le⟩ := Finset.exists_one_le_forall_le (univ : Finset (InfinitePlace K)) AI
  obtain ⟨A₂, hA₂, hA₂le⟩ :=
    Finset.exists_one_le_forall_le (univ : Finset {w : FinitePlace K // w ∈ S₀}) AF
  have hA : (1 : ℝ) ≤ A₁ * A₂ := by
    simpa using mul_le_mul hA₁ hA₂ zero_le_one (by linarith : (0 : ℝ) ≤ A₁)
  refine ⟨A₁ * A₂, hA, fun Q hQ y hy ↦ ⟨?_, ?_, ?_⟩⟩
  · intro w t
    have hb : ∀ j k, w (L w.1 k (y j)) ≤ Q ^ cMax c w.1 := fun j k ↦
      le_trans ((hy j).1 w k)
        (Real.rpow_le_rpow_of_exponent_le hQ (Finite.le_ciSup_of_le k le_rfl))
    have := hAI w y (Q ^ cMax c w.1) (Real.rpow_nonneg (by linarith) _) hb t
    rw [← Real.rpow_natCast (Q ^ cMax c w.1) n, ← Real.rpow_mul (by linarith),
      mul_comm (cMax c w.1)] at this
    refine this.trans ?_
    have h0 : (0 : ℝ) ≤ Q ^ ((n : ℝ) * cMax c w.1) := Real.rpow_nonneg (by linarith) _
    have hle : AI w ≤ A₁ * A₂ :=
      le_trans (hA₁le w (mem_univ w)) (le_mul_of_one_le_right (by linarith) hA₂)
    exact mul_le_mul_of_nonneg_right hle h0
  · intro w hw t
    have hb : ∀ j k, w (L w.1 k (y j)) ≤ Q ^ cMax c w.1 := fun j k ↦
      le_trans ((hy j).2.1 w hw k)
        (Real.rpow_le_rpow_of_exponent_le hQ (Finite.le_ciSup_of_le k le_rfl))
    have := hAF ⟨w, hw⟩ y (Q ^ cMax c w.1) (Real.rpow_nonneg (by linarith) _) hb t
    rw [← Real.rpow_natCast (Q ^ cMax c w.1) n, ← Real.rpow_mul (by linarith),
      mul_comm (cMax c w.1)] at this
    refine this.trans ?_
    have h0 : (0 : ℝ) ≤ Q ^ ((n : ℝ) * cMax c w.1) := Real.rpow_nonneg (by linarith) _
    have hle : AF ⟨w, hw⟩ ≤ A₁ * A₂ :=
      le_trans (hA₂le ⟨w, hw⟩ (mem_univ _)) (le_mul_of_one_le_left (by linarith) hA₁)
    exact mul_le_mul_of_nonneg_right hle h0
  · intro w hw t
    exact apply_plucker_le_one (fun a b ↦ w.add_le a b) (fun b i ↦ (hy b).2.2 w hw i) t

/-- A product of powers of `A * Q ^ f a`, read off as a power of `A` times a power of `Q`. -/
theorem prod_mul_rpow_pow {A Q : ℝ} (hQ : 0 < Q) {α : Type*} (s : Finset α) (f : α → ℝ)
    (m : α → ℕ) :
    ∏ a ∈ s, (A * Q ^ f a) ^ m a = A ^ (∑ a ∈ s, m a) * Q ^ (∑ a ∈ s, f a * m a) := by
  rw [Real.rpow_sum_of_pos hQ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [mul_pow, ← Real.rpow_natCast (Q ^ f a) (m a), ← Real.rpow_mul hQ.le]

/-- **The upper bound of Bombieri–Gubler, Lemma 7.5.21**: the height of the span of a basis of
the domain is at most `Q` to `n` times the sum over `S` of the largest exponents. -/
theorem exists_one_le_forall_mulHeight_plucker_le
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ y : Fin n → ι → K, LinearIndependent K y →
      (∀ j, y j ∈ approxDomain S₀ L c Q) →
        Height.mulHeight (plucker n y)
          ≤ C * Q ^ ((n : ℝ) * (∑ w : InfinitePlace K, (w.mult : ℝ) * cMax c w.1
              + ∑ w ∈ S₀, cMax c w.1)) := by
  obtain ⟨A, hA1, hA⟩ := exists_one_le_forall_iSup_apply_plucker_le (c := c) hLinf hLfin
  have hA0 : (0 : ℝ) ≤ A := by linarith
  refine ⟨A ^ (Height.totalWeight K + #S₀), one_le_pow₀ hA1, fun Q hQ y hyli hy ↦ ?_⟩
  have hQ0 : (0 : ℝ) < Q := by linarith
  obtain ⟨hinf, hfin, hout⟩ := hA Q hQ y hy
  have hz : plucker n y ≠ 0 := plucker_ne_zero hyli
  have hnn : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ⨆ t, v (plucker n y t) :=
    fun v ↦ Real.iSup_nonneg fun t ↦ v.nonneg _
  have hIsup : ∀ w : InfinitePlace K,
      (⨆ t, w (plucker n y t)) ≤ A * Q ^ ((n : ℝ) * cMax c w.1) := fun w ↦
    Real.iSup_le (hinf w) (by positivity)
  have hFsup : ∀ w ∈ S₀, (⨆ t, w (plucker n y t)) ≤ A * Q ^ ((n : ℝ) * cMax c w.1) :=
    fun w hw ↦ Real.iSup_le (hfin w hw) (by positivity)
  have hOsup : ∀ w : FinitePlace K, w ∉ S₀ → (⨆ t, w (plucker n y t)) ≤ 1 :=
    fun w hw ↦ Real.iSup_le (hout w hw) zero_le_one
  rw [NumberField.mulHeight_eq hz]
  have h1 : (∏ w : InfinitePlace K, (⨆ t, w (plucker n y t)) ^ w.mult)
      ≤ ∏ w : InfinitePlace K, (A * Q ^ ((n : ℝ) * cMax c w.1)) ^ w.mult :=
    Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (hnn w.1) _)
      fun w _ ↦ pow_le_pow_left₀ (hnn w.1) (hIsup w) _
  have h2 : (∏ᶠ w : FinitePlace K, ⨆ t, w (plucker n y t))
      ≤ ∏ w ∈ S₀, A * Q ^ ((n : ℝ) * cMax c w.1) := by
    refine le_trans (finprod_le_prod_of_le_one_outside S₀ (fun w ↦ hnn w.1) hOsup
      (FinitePlace.hasFiniteMulSupport_iSup hz)) ?_
    exact Finset.prod_le_prod₀ (fun w _ ↦ hnn w.1) fun w hw ↦ hFsup w hw
  have h3 : (0 : ℝ) ≤ ∏ᶠ w : FinitePlace K, ⨆ t, w (plucker n y t) :=
    finprod_nonneg fun w ↦ hnn w.1
  have h4 : (0 : ℝ) ≤ ∏ w : InfinitePlace K, (A * Q ^ ((n : ℝ) * cMax c w.1)) ^ w.mult :=
    Finset.prod_nonneg fun w _ ↦ pow_nonneg (by positivity) _
  refine le_trans (mul_le_mul h1 h2 h3 h4) ?_
  rw [prod_mul_rpow_pow hQ0 univ (fun w : InfinitePlace K ↦ (n : ℝ) * cMax c w.1)
      (fun w ↦ w.mult),
    show (∏ w ∈ S₀, A * Q ^ ((n : ℝ) * cMax c w.1))
        = ∏ w ∈ S₀, (A * Q ^ ((n : ℝ) * cMax c w.1)) ^ (fun _ : FinitePlace K ↦ 1) w from
      by simp,
    prod_mul_rpow_pow hQ0 S₀ (fun w : FinitePlace K ↦ (n : ℝ) * cMax c w.1) (fun _ ↦ 1)]
  rw [mul_mul_mul_comm, ← pow_add, ← Real.rpow_add hQ0]
  refine le_of_eq (congrArg₂ _ (congrArg _ ?_) (congrArg _ ?_))
  · rw [← NumberField.totalWeight_eq_sum_mult K, Finset.sum_const, smul_eq_mul, mul_one]
  · rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ by ring)
      (Finset.sum_congr rfl fun w _ ↦ by push_cast; ring)

omit [NumberField K] in
/-- The local factor of a nonzero tuple is positive. -/
private theorem iSup_pos {ρ : Type*} [Finite ρ] {v : AbsoluteValue K ℝ} {a : ρ → K}
    (ha : a ≠ 0) : 0 < ⨆ t, v (a t) := by
  obtain ⟨t, ht⟩ := Function.ne_iff.mp ha
  exact lt_of_lt_of_le (v.pos ht) (Finite.le_ciSup_of_le t le_rfl)

/-- **The lower bound of Bombieri–Gubler, Lemma 7.5.21, at one place**: a nonvanishing
transformed Plücker coordinate is at least the local factor of the Plücker point divided by its
height, up to a constant depending only on the forms. -/
theorem exists_pos_forall_mul_iSup_le (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : Fin n → ι → K,
      (∀ (w : InfinitePlace K) (s : Set.powersetCard ι n),
          plucker n (fun j i ↦ L w.1 i (y j)) s ≠ 0 →
          κ * (⨆ t, w (plucker n y t)) ^ w.mult
            ≤ Height.mulHeight (plucker n y)
                * w (plucker n (fun j i ↦ L w.1 i (y j)) s) ^ w.mult) ∧
      ∀ w ∈ S₀, ∀ s : Set.powersetCard ι n,
          plucker n (fun j i ↦ L w.1 i (y j)) s ≠ 0 →
          κ * (⨆ t, w (plucker n y t))
            ≤ Height.mulHeight (plucker n y)
                * w (plucker n (fun j i ↦ L w.1 i (y j)) s) := by
  classical
  have hne : Nonempty (Set.powersetCard ι n) :=
    ⟨Set.powersetCard.omitOne hlk Classical.ofNonempty⟩
  set N : ℝ := (Fintype.card (Set.powersetCard ι n) : ℝ) ^ Height.totalWeight K with hNdef
  have hN0 : 0 < N := pow_pos (by exact_mod_cast Fintype.card_pos) _
  set κI : InfinitePlace K × Set.powersetCard ι n → ℝ := fun p ↦
    (⨆ t, p.1 (wedgeFormCoeff (L p.1.1) n p.2 t)) ^ p.1.mult
      / (N * Height.mulHeight (wedgeFormCoeff (L p.1.1) n p.2)) with hκIdef
  set κF : FinitePlace K × Set.powersetCard ι n → ℝ := fun p ↦
    (⨆ t, p.1 (wedgeFormCoeff (L p.1.1) n p.2 t))
      / (N * Height.mulHeight (wedgeFormCoeff (L p.1.1) n p.2)) with hκFdef
  have hposI : ∀ p : InfinitePlace K × Set.powersetCard ι n, 0 < κI p := fun p ↦
    div_pos (pow_pos (iSup_pos (wedgeCoeff_ne_zero (hLinf p.1) p.2)) _)
      (mul_pos hN0 (Height.mulHeight_pos _))
  have hposF : ∀ p ∈ S₀ ×ˢ (univ : Finset (Set.powersetCard ι n)), 0 < κF p := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact div_pos (iSup_pos (wedgeCoeff_ne_zero (hLfin p.1 hp.1) p.2))
      (mul_pos hN0 (Height.mulHeight_pos _))
  obtain ⟨κ₁, hκ₁, hκ₁le⟩ := Finset.exists_pos_forall_le univ κI fun p _ ↦ hposI p
  obtain ⟨κ₂, hκ₂, hκ₂le⟩ := Finset.exists_pos_forall_le (S₀ ×ˢ univ) κF hposF
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun y ↦ ⟨fun w s hD ↦ ?_, fun w hw s hD ↦ ?_⟩⟩
  · set a := wedgeFormCoeff (L w.1) n s with hadef
    have hDz : (∑ t, a t * plucker n y t) = plucker n (fun j i ↦ L w.1 i (y j)) s := by
      rw [plucker_pi_apply, wedgeForms_eq_sum]
    have key := InfinitePlace.iSup_mul_iSup_pow_mult_le w a (plucker n y) (by rw [hDz]; exact hD)
    rw [mul_pow, hDz] at key
    have hHa : 0 < Height.mulHeight a := Height.mulHeight_pos _
    have hzn : (0 : ℝ) ≤ (⨆ t, w (plucker n y t)) ^ w.mult :=
      pow_nonneg (Real.iSup_nonneg fun t ↦ w.1.nonneg _) _
    calc min κ₁ κ₂ * (⨆ t, w (plucker n y t)) ^ w.mult
        ≤ ((⨆ t, w (a t)) ^ w.mult / (N * Height.mulHeight a))
            * (⨆ t, w (plucker n y t)) ^ w.mult :=
          mul_le_mul_of_nonneg_right
            (le_trans (min_le_left _ _) (hκ₁le (w, s) (mem_univ _))) hzn
      _ ≤ Height.mulHeight (plucker n y)
            * w (plucker n (fun j i ↦ L w.1 i (y j)) s) ^ w.mult := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hN0 hHa)]
          exact le_trans key (le_of_eq (by ring))
  · set a := wedgeFormCoeff (L w.1) n s with hadef
    have hDz : (∑ t, a t * plucker n y t) = plucker n (fun j i ↦ L w.1 i (y j)) s := by
      rw [plucker_pi_apply, wedgeForms_eq_sum]
    have key := FinitePlace.iSup_mul_iSup_le w a (plucker n y) (by rw [hDz]; exact hD)
    rw [hDz] at key
    have hHa : 0 < Height.mulHeight a := Height.mulHeight_pos _
    have hzn : (0 : ℝ) ≤ ⨆ t, w (plucker n y t) := Real.iSup_nonneg fun t ↦ w.1.nonneg _
    calc min κ₁ κ₂ * (⨆ t, w (plucker n y t))
        ≤ ((⨆ t, w (a t)) / (N * Height.mulHeight a)) * (⨆ t, w (plucker n y t)) :=
          mul_le_mul_of_nonneg_right
            (le_trans (min_le_right _ _)
              (hκ₂le (w, s) (Finset.mem_product.mpr ⟨hw, mem_univ _⟩))) hzn
      _ ≤ Height.mulHeight (plucker n y)
            * w (plucker n (fun j i ↦ L w.1 i (y j)) s) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hN0 hHa)]
          exact le_trans key (le_of_eq (by ring))

/-- The weight of a system of exponents along a choice of one index at each place of `S`. -/
def weightAt (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) : ℝ :=
  ∑ v : InfinitePlace K, (v.mult : ℝ) * c v.1 (k v.1) + ∑ v ∈ S₀, c v.1 (k v.1)

omit [Nonempty ι] in
/-- **The upper bound of the generalized Roth machinery at the places of `S`** (Bombieri–Gubler
(7.30) and (7.32)): the product over `S` of the transformed Plücker coordinates omitting the
chosen index is at most `Q` to the weight of the exponents minus the weight along the choice. -/
theorem prod_apply_plucker_pi_le (hlk : 1 + n = Fintype.card ι) {Q : ℝ} (hQ : 1 ≤ Q)
    {y : Fin n → ι → K} (hy : ∀ j, y j ∈ approxDomain S₀ L c Q)
    (k : AbsoluteValue K ℝ → ι) :
    (∏ w : InfinitePlace K, w (plucker n (fun j i ↦ L w.1 i (y j))
          (Set.powersetCard.omitOne hlk (k w.1))) ^ w.mult)
        * ∏ w ∈ S₀, w (plucker n (fun j i ↦ L w.1 i (y j))
          (Set.powersetCard.omitOne hlk (k w.1)))
      ≤ ((n.factorial : ℝ) ^ Height.totalWeight K)
          * Q ^ (approxWeight S₀ c - weightAt S₀ c k) := by
  classical
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hsum : ∀ (v : AbsoluteValue K ℝ) (i₀ : ι),
      ∑ i ∈ ((Set.powersetCard.omitOne hlk i₀ : Set.powersetCard ι n) : Finset ι), c v i
        = (∑ i, c v i) - c v i₀ := by
    intro v i₀
    rw [Set.powersetCard.coe_omitOne]
    have := Finset.sum_compl_add_sum ({i₀} : Finset ι) (fun i ↦ c v i)
    simp only [Finset.sum_singleton] at this
    linarith
  have hI : ∀ w : InfinitePlace K,
      w (plucker n (fun j i ↦ L w.1 i (y j)) (Set.powersetCard.omitOne hlk (k w.1)))
        ≤ (n.factorial : ℝ) * Q ^ ((∑ i, c w.1 i) - c w.1 (k w.1)) := by
    intro w
    rw [← hsum w.1 (k w.1), Real.rpow_sum_of_pos hQ0]
    exact apply_plucker_pi_le w.1 (L w.1) y (fun i j ↦ (hy j).1 w i) _
  have hF : ∀ w ∈ S₀,
      w (plucker n (fun j i ↦ L w.1 i (y j)) (Set.powersetCard.omitOne hlk (k w.1)))
        ≤ (1 : ℝ) * Q ^ ((∑ i, c w.1 i) - c w.1 (k w.1)) := by
    intro w hw
    rw [← hsum w.1 (k w.1), Real.rpow_sum_of_pos hQ0, one_mul]
    exact apply_plucker_pi_le_of_isNonarchimedean (fun a b ↦ w.add_le a b) (L w.1) y
      (fun i ↦ Real.rpow_nonneg hQ0.le _) (fun i j ↦ (hy j).2.1 w hw i) _
  have h1 : (∏ w : InfinitePlace K, w (plucker n (fun j i ↦ L w.1 i (y j))
          (Set.powersetCard.omitOne hlk (k w.1))) ^ w.mult)
      ≤ ∏ w : InfinitePlace K,
          ((n.factorial : ℝ) * Q ^ ((∑ i, c w.1 i) - c w.1 (k w.1))) ^ w.mult :=
    Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (w.1.nonneg _) _)
      fun w _ ↦ pow_le_pow_left₀ (w.1.nonneg _) (hI w) _
  have h2 : (∏ w ∈ S₀, w (plucker n (fun j i ↦ L w.1 i (y j))
          (Set.powersetCard.omitOne hlk (k w.1))))
      ≤ ∏ w ∈ S₀,
          ((1 : ℝ) * Q ^ ((∑ i, c w.1 i) - c w.1 (k w.1))) ^ (fun _ ↦ 1 : FinitePlace K → ℕ) w := by
    simp only [pow_one]
    exact Finset.prod_le_prod₀ (fun w _ ↦ w.1.nonneg _) fun w hw ↦ hF w hw
  refine le_trans (mul_le_mul h1 h2 (Finset.prod_nonneg fun w _ ↦ w.1.nonneg _)
    (Finset.prod_nonneg fun w _ ↦ pow_nonneg (by positivity) _)) (le_of_eq ?_)
  rw [prod_mul_rpow_pow hQ0 univ (fun w : InfinitePlace K ↦ (∑ i, c w.1 i) - c w.1 (k w.1))
      (fun w ↦ w.mult),
    prod_mul_rpow_pow hQ0 S₀ (fun w : FinitePlace K ↦ (∑ i, c w.1 i) - c w.1 (k w.1))
      (fun _ ↦ 1),
    one_pow, one_mul, mul_assoc, ← Real.rpow_add hQ0]
  refine congrArg₂ _ (congrArg _ ?_) (congrArg _ ?_)
  · rw [← NumberField.totalWeight_eq_sum_mult K]
  · rw [approxWeight, weightAt]
    simp only [Nat.cast_one, mul_one]
    rw [show (∑ w : InfinitePlace K, ((∑ i, c w.1 i) - c w.1 (k w.1)) * (w.mult : ℝ))
          = (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, c w.1 i)
            - ∑ w : InfinitePlace K, (w.mult : ℝ) * c w.1 (k w.1) from by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ ↦ by ring,
      show (∑ w ∈ S₀, ((∑ i, c w.1 i) - c w.1 (k w.1)))
          = (∑ w ∈ S₀, ∑ i, c w.1 i) - ∑ w ∈ S₀, c w.1 (k w.1) from
        Finset.sum_sub_distrib (fun w : FinitePlace K ↦ ∑ i, c w.1 i)
          (fun w : FinitePlace K ↦ c w.1 (k w.1))]
    ring

omit [Nonempty ι] in
/-- **The height of an `S`-integral tuple is at most the product of its local factors over
`S`**: the factors outside `S` are at most `1`. -/
theorem mulHeight_plucker_le_prod {Q : ℝ} {y : Fin n → ι → K} (hyli : LinearIndependent K y)
    (hy : ∀ j, y j ∈ approxDomain S₀ L c Q) :
    Height.mulHeight (plucker n y)
      ≤ (∏ w : InfinitePlace K, (⨆ t, w (plucker n y t)) ^ w.mult)
          * ∏ w ∈ S₀, ⨆ t, w (plucker n y t) := by
  have hz : plucker n y ≠ 0 := plucker_ne_zero hyli
  have hnn : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ⨆ t, v (plucker n y t) :=
    fun v ↦ Real.iSup_nonneg fun t ↦ v.nonneg _
  rw [NumberField.mulHeight_eq hz]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun w _ ↦ pow_nonneg (hnn w.1) _)
  refine finprod_le_prod_of_le_one_outside S₀ (fun w ↦ hnn w.1) (fun w hw ↦ ?_)
    (FinitePlace.hasFiniteMulSupport_iSup hz)
  exact Real.iSup_le
    (fun t ↦ apply_plucker_le_one (fun a b ↦ w.add_le a b) (fun b i ↦ (hy b).2.2 w hw i) t)
    zero_le_one

/-- **The lower bound of Bombieri–Gubler, Lemma 7.5.21, over all of `S`**: the product of the
nonvanishing transformed Plücker coordinates is at least the height of the subspace to the power
`1 - |S|`, up to a constant. -/
theorem exists_pos_forall_prod_le (hlk : 1 + n = Fintype.card ι)
    (hLinf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLfin : ∀ w ∈ S₀, LinearIndependent K (L w.1)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {Q : ℝ} (y : Fin n → ι → K), LinearIndependent K y →
      (∀ j, y j ∈ approxDomain S₀ L c Q) →
      ∀ s : AbsoluteValue K ℝ → Set.powersetCard ι n,
        (∀ w : InfinitePlace K, plucker n (fun j i ↦ L w.1 i (y j)) (s w.1) ≠ 0) →
        (∀ w ∈ S₀, plucker n (fun j i ↦ L w.1 i (y j)) (s w.1) ≠ 0) →
        κ ^ (Fintype.card (InfinitePlace K) + #S₀) * Height.mulHeight (plucker n y)
          ≤ Height.mulHeight (plucker n y) ^ (Fintype.card (InfinitePlace K) + #S₀)
            * ((∏ w : InfinitePlace K,
                  w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1)) ^ w.mult)
                * ∏ w ∈ S₀, w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1))) := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_pos_forall_mul_iSup_le hlk hLinf hLfin
  refine ⟨κ, hκ0, fun {Q} y hyli hy s hsI hsF ↦ ?_⟩
  obtain ⟨hI, hF⟩ := hκ y
  set H := Height.mulHeight (plucker n y) with hHdef
  have hH0 : 0 < H := Height.mulHeight_pos _
  have hnn : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ⨆ t, v (plucker n y t) :=
    fun v ↦ Real.iSup_nonneg fun t ↦ v.nonneg _
  have h1 : (∏ w : InfinitePlace K, κ * (⨆ t, w (plucker n y t)) ^ w.mult)
      ≤ ∏ w : InfinitePlace K,
          H * w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1)) ^ w.mult :=
    Finset.prod_le_prod₀ (fun w _ ↦ mul_nonneg hκ0.le (pow_nonneg (hnn w.1) _))
      fun w _ ↦ hI w (s w.1) (hsI w)
  have h2 : (∏ w ∈ S₀, κ * ⨆ t, w (plucker n y t))
      ≤ ∏ w ∈ S₀, H * w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1)) :=
    Finset.prod_le_prod₀ (fun w _ ↦ mul_nonneg hκ0.le (hnn w.1))
      fun w hw ↦ hF w hw (s w.1) (hsF w hw)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_univ] at h1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const] at h2
  have hmul := mul_le_mul h1 h2
    (mul_nonneg (pow_nonneg hκ0.le _) (Finset.prod_nonneg fun w _ ↦ hnn w.1))
    (mul_nonneg (pow_nonneg hH0.le _)
      (Finset.prod_nonneg fun w _ ↦ pow_nonneg (w.1.nonneg _) _))
  have hHle := mulHeight_plucker_le_prod (c := c) hyli hy
  calc κ ^ (Fintype.card (InfinitePlace K) + #S₀) * H
      ≤ κ ^ (Fintype.card (InfinitePlace K) + #S₀)
          * ((∏ w : InfinitePlace K, (⨆ t, w (plucker n y t)) ^ w.mult)
              * ∏ w ∈ S₀, ⨆ t, w (plucker n y t)) :=
        mul_le_mul_of_nonneg_left hHle (pow_nonneg hκ0.le _)
    _ = (κ ^ Fintype.card (InfinitePlace K)
            * ∏ w : InfinitePlace K, (⨆ t, w (plucker n y t)) ^ w.mult)
          * (κ ^ #S₀ * ∏ w ∈ S₀, ⨆ t, w (plucker n y t)) := by rw [pow_add]; ring
    _ ≤ (H ^ Fintype.card (InfinitePlace K)
            * ∏ w : InfinitePlace K,
                w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1)) ^ w.mult)
          * (H ^ #S₀ * ∏ w ∈ S₀, w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1))) := hmul
    _ = H ^ (Fintype.card (InfinitePlace K) + #S₀)
          * ((∏ w : InfinitePlace K,
                w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1)) ^ w.mult)
              * ∏ w ∈ S₀, w (plucker n (fun j i ↦ L w.1 i (y j)) (s w.1))) := by
        rw [pow_add]; ring

end NumberField
