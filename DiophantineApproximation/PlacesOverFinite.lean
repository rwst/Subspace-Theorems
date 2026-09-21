/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.Nonarchimedean
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- Used only inside proofs.
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The absolute values of a number field lying over a finite place

Let `F / K` be an extension of number fields, `v` a finite place of `K` and `w` an absolute value
of `F` with `w.LiesOver v` — Mathlib's `AbsoluteValue.LiesOver`, that is, `w` restricted to `K`
is `v` on the nose. Then

```text
w = (NumberField.FinitePlace.mk 𝔓) ^ ((e 𝔓 * f 𝔓 : ℕ) : ℝ)⁻¹
```

for a unique prime `𝔓` of `𝓞 F` above the prime of `v`, `e` and `f` its ramification index and
inertia degree. ⚠ **`w` is in general not itself a finite place of `F`**: it is a *root* of one,
and it is a finite place exactly when `𝔓` is unramified of inertia degree one over `𝔭`.

The classification is the nonarchimedean half of Ostrowski's theorem over a number field, which
Mathlib's `NumberTheory/Ostrowski.lean` proves over `ℚ` and records extending to number fields as
a TODO.

## Main results

* `AbsoluteValue.exists_heightOneSpectrum_rpow_eq`: the theorem with no extension in sight — a
  nonarchimedean absolute value of a number field that is at most `1` on the ring of integers and
  somewhere less than `1` is a positive real power of a finite place. This is where the work is.
* `NumberField.exists_finitePlace_rpow_eq_of_liesOver`: the milestone, in the shape the roadmap
  pins, with the exponent bounded by `1`.
* `NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver`: the same with the exponent named,
  `(e f)⁻¹`, and the prime exhibited above `v`.
* `AbsoluteValue.integerLtIdeal`: the prime the classification produces, `{y ∈ 𝓞 F | w y < 1}`,
  and `AbsoluteValue.heightOneSpectrum_eq_of_rpow_eq`: it is the only one that works, so the `𝔓`
  above is unique. `AbsoluteValue.mem_iff_apply_lt_one_of_rpow_eq` is the step that reads the
  prime off `w`, and is what Layer 0.2 uses to identify the prime of a conjugate.
* `NumberField.exists_apply_algebraMap_eq_mk_rpow`: **nonemptiness**, in the form the further
  extensions of Layer 0.1 need — above `(FinitePlace.mk 𝔭) ^ t` there is an absolute value of `F`,
  for every `t > 0`. `NumberField.exists_liesOver_finitePlace` is the case `t = 1`.
* `NumberField.FinitePlace.mk_algebraMap`: **the local extension formula at a finite place**,
  Layer 0.2's finite half, restated for `FinitePlace.mk`.
* `NumberField.isNonarchimedean_of_liesOver_finitePlace` and
  `NumberField.apply_le_one_of_liesOver_finitePlace`: the two hypotheses of the classification,
  supplied from `w.LiesOver v`.
* `NumberField.FinitePlace.mk_le_one_iff`, `mk_lt_one_iff_mem`, `mk_eq_one_iff_notMem`,
  `apply_intCast_le_one` and `isNonarchimedean_mk`: small bridges Mathlib states for
  `FinitePlace.embedding` but not for `FinitePlace.mk`.

## Implementation notes

The proof is Mathlib's `AbsoluteValue.isEquiv_of_lt_one_imp` plus one decomposition. The only
inequality that has to be proved by hand is `∀ x : F, 𝔓-adic x < 1 → w x < 1`; writing `x = n / d`
with `d` outside `𝔓` (`HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`) turns it into two
membership statements in `𝔓`, because `w d = 1` for `d` outside `𝔓` and `w n < 1` for `n` inside.
No discrete valuation ring, no uniformizer and no unique factorization of ideals appears.

The bound on the exponent is *not* proved by hand either: Mathlib already has the local extension
formula for finite places, `NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`,
which is Layer 0.2's finite half, and it pins the exponent to `(e f)⁻¹` at once. ⚠ Without it the
bound `t ≤ 1` still needs `absNorm 𝔭 ≤ absNorm 𝔓`, so it is not free.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.3. K. Conrad, *Ostrowski for number fields*.

This is the nonarchimedean half of Layer 0.1 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField.FinitePlace

variable {F : Type*} [Field F] [NumberField F]

/-- A finite place is at most `1` at `x` exactly when the adic valuation is. -/
theorem mk_le_one_iff (P : HeightOneSpectrum (𝓞 F)) (x : F) :
    FinitePlace.mk P x ≤ 1 ↔ P.valuation F x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def,
    ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal P)

/-- A finite place is at most `1` on the rational integers. -/
theorem apply_intCast_le_one (v : FinitePlace F) (n : ℤ) : v (n : F) ≤ 1 := by
  rw [← v.norm_embedding_eq, FinitePlace.norm_embedding]
  exact HeightOneSpectrum.adicAbv_intCast_le_one F v.maximalIdeal n

/-- A finite place is less than `1` exactly on its own prime. -/
theorem mk_lt_one_iff_mem (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F) :
    FinitePlace.mk P (y : F) < 1 ↔ y ∈ P.asIdeal := by
  rw [FinitePlace.mk_apply]
  exact FinitePlace.norm_lt_one_iff_mem F P y

/-- A finite place is `1` exactly off its own prime. -/
theorem mk_eq_one_iff_notMem (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F) :
    FinitePlace.mk P (y : F) = 1 ↔ y ∉ P.asIdeal := by
  rw [FinitePlace.mk_apply]
  exact FinitePlace.norm_eq_one_iff_notMem F P y

/-- A finite place is nonarchimedean. -/
theorem isNonarchimedean_mk (P : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedean ((FinitePlace.mk P).1 : F → ℝ) :=
  fun x y => FinitePlace.add_le (FinitePlace.mk P) x y

/-- **The local extension formula at a finite place** (Layer 0.2, finite half), restated for
`FinitePlace.mk`: restricted to the base field, the place of `𝔓` is the `e f`-th power of the
place of the prime below it. This is Mathlib's
`NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` with the equivalence
unfolded. -/
theorem mk_algebraMap {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (v : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver v.asIdeal] (u : K) :
    FinitePlace.mk P (algebraMap K F u)
      = FinitePlace.mk v u ^ (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) := by
  have h := FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap v P u
  simpa [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply] using h

end NumberField.FinitePlace

namespace AbsoluteValue

section Ideal

variable {F : Type*} [Field F] {w : AbsoluteValue F ℝ}

/-- The algebraic integers of absolute value less than one, as an ideal of `𝓞 F`. It is the prime
that the classification below attaches to `w`. -/
def integerLtIdeal (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) : Ideal (𝓞 F) where
  carrier := {y : 𝓞 F | w (y : F) < 1}
  add_mem' {a b} ha hb := by
    have ha' : w (a : F) < 1 := ha
    have hb' : w (b : F) < 1 := hb
    change w ((a + b : 𝓞 F) : F) < 1
    refine lt_of_le_of_lt ?_ (max_lt ha' hb')
    push_cast
    exact hna (a : F) (b : F)
  zero_mem' := by change w ((0 : 𝓞 F) : F) < 1; simp
  smul_mem' c y hy := by
    have hy' : w (y : F) < 1 := hy
    change w ((c • y : 𝓞 F) : F) < 1
    rw [smul_eq_mul]
    push_cast
    rw [map_mul]
    calc w (c : F) * w (y : F) ≤ 1 * w (y : F) :=
          mul_le_mul_of_nonneg_right (hle c) (w.nonneg _)
      _ < 1 := by rw [one_mul]; exact hy'

@[simp] theorem mem_integerLtIdeal {hna : IsNonarchimedean (w : F → ℝ)}
    {hle : ∀ y : 𝓞 F, w (y : F) ≤ 1} {y : 𝓞 F} :
    y ∈ w.integerLtIdeal hna hle ↔ w (y : F) < 1 := Iff.rfl

theorem isPrime_integerLtIdeal (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) : (w.integerLtIdeal hna hle).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : 𝓞 F) ∈ w.integerLtIdeal hna hle := htop ▸ Submodule.mem_top
    rw [mem_integerLtIdeal] at h1
    simp at h1
  · intro a b hab
    rw [mem_integerLtIdeal] at hab
    push_cast at hab
    rw [map_mul] at hab
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    rw [mem_integerLtIdeal] at ha hb
    have ha1 : (1 : ℝ) ≤ w (a : F) := le_of_not_gt ha
    have hb1 : (1 : ℝ) ≤ w (b : F) := le_of_not_gt hb
    nlinarith [w.nonneg (a : F), w.nonneg (b : F)]

end Ideal

variable {F : Type*} [Field F] [NumberField F] {w : AbsoluteValue F ℝ}

/-- The prime of the classification is read off from `w` alone: it is `{y ∈ 𝓞 F | w y < 1}`,
whatever positive exponent is used. -/
theorem mem_iff_apply_lt_one_of_rpow_eq {P : HeightOneSpectrum (𝓞 F)} {t : ℝ} (ht : 0 < t)
    (h : ∀ y : F, w y = FinitePlace.mk P y ^ t) (y : 𝓞 F) :
    y ∈ P.asIdeal ↔ w (y : F) < 1 := by
  rw [← FinitePlace.mk_lt_one_iff_mem, h, Real.rpow_lt_one_iff' (apply_nonneg _ _) ht]

/-- The prime of the classification is determined by `w`. So the `𝔓` produced below is unique. -/
theorem heightOneSpectrum_eq_of_rpow_eq {P P' : HeightOneSpectrum (𝓞 F)} {t t' : ℝ} (ht : 0 < t)
    (ht' : 0 < t') (h : ∀ y : F, w y = FinitePlace.mk P y ^ t)
    (h' : ∀ y : F, w y = FinitePlace.mk P' y ^ t') : P = P' :=
  HeightOneSpectrum.ext (SetLike.ext fun y =>
    (mem_iff_apply_lt_one_of_rpow_eq ht h y).trans (mem_iff_apply_lt_one_of_rpow_eq ht' h' y).symm)

/-- **Ostrowski's theorem at a finite place**, for a number field: a nonarchimedean absolute value
that is at most `1` on the ring of integers and less than `1` somewhere on it is a positive real
power of the absolute value of a finite place. -/
theorem exists_heightOneSpectrum_rpow_eq (hna : IsNonarchimedean (w : F → ℝ))
    (hle : ∀ y : 𝓞 F, w (y : F) ≤ 1) (hnt : ∃ y : 𝓞 F, y ≠ 0 ∧ w (y : F) < 1) :
    ∃ (P : HeightOneSpectrum (𝓞 F)) (t : ℝ), 0 < t ∧
      ∀ y : F, w y = FinitePlace.mk P y ^ t := by
  obtain ⟨y₀, hy₀0, hy₀1⟩ := hnt
  have hIbot : w.integerLtIdeal hna hle ≠ ⊥ := by
    intro h
    have hmem : y₀ ∈ w.integerLtIdeal hna hle := hy₀1
    rw [h, Ideal.mem_bot] at hmem
    exact hy₀0 hmem
  set P : HeightOneSpectrum (𝓞 F) :=
    ⟨w.integerLtIdeal hna hle, isPrime_integerLtIdeal hna hle, hIbot⟩ with hPdef
  have hmemP : ∀ y : 𝓞 F, y ∈ P.asIdeal ↔ w (y : F) < 1 := fun _ => Iff.rfl
  have himp : ∀ x : F, (FinitePlace.mk P).1 x < 1 → w x < 1 := by
    intro x hx
    have hx' : FinitePlace.mk P x < 1 := hx
    obtain ⟨n, d, hnd⟩ :=
      P.exists_primeCompl_mul_eq_of_integer x ((FinitePlace.mk_le_one_iff P x).mp hx'.le)
    have hd_notin : (d : 𝓞 F) ∉ P.asIdeal := d.2
    have hwd1 : w ((d : 𝓞 F) : F) = 1 :=
      le_antisymm (hle d) (le_of_not_gt fun h => hd_notin ((hmemP _).mpr h))
    have hWd1 : FinitePlace.mk P ((d : 𝓞 F) : F) = 1 :=
      (FinitePlace.mk_eq_one_iff_notMem P _).mpr hd_notin
    have hWn : FinitePlace.mk P ((n : 𝓞 F) : F) < 1 := by
      have h1 : FinitePlace.mk P x * FinitePlace.mk P ((d : 𝓞 F) : F)
          = FinitePlace.mk P ((n : 𝓞 F) : F) := by
        rw [← map_mul]; exact congrArg (FinitePlace.mk P) hnd
      rw [hWd1, mul_one] at h1
      rw [← h1]
      exact hx'
    have hwn : w ((n : 𝓞 F) : F) < 1 :=
      (hmemP _).mp ((FinitePlace.mk_lt_one_iff_mem P n).mp hWn)
    have hxd : w x * w ((d : 𝓞 F) : F) = w ((n : 𝓞 F) : F) := by
      rw [← map_mul]; exact congrArg w hnd
    rw [hwd1, mul_one] at hxd
    rw [hxd]
    exact hwn
  have hWnt : (FinitePlace.mk P).1.IsNontrivial := by
    refine ⟨(y₀ : F), by simpa using hy₀0, ?_⟩
    exact ne_of_lt ((FinitePlace.mk_lt_one_iff_mem P y₀).mpr ((hmemP _).mpr hy₀1))
  obtain ⟨t, ht, hfun⟩ := isEquiv_iff_exists_rpow_eq.mp (isEquiv_of_lt_one_imp hWnt himp)
  exact ⟨P, t, ht, fun y => (congrFun hfun y).symm⟩

end AbsoluteValue

namespace AbsoluteValue

/-- An absolute value lying over `v` agrees with `v` on the base field, by definition of
`AbsoluteValue.under`. -/
theorem apply_algebraMap_of_liesOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    {v : AbsoluteValue K ℝ} (w : AbsoluteValue F ℝ) [w.LiesOver v] (y : K) :
    w (algebraMap K F y) = v y := by
  conv_rhs => rw [← AbsoluteValue.LiesOver.under_eq w v]
  rfl

end AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- An absolute value lying over a finite place is nonarchimedean: it is at most `1` on the
rational integers, which is all the criterion needs. -/
theorem isNonarchimedean_of_liesOver_finitePlace (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsNonarchimedean (w : F → ℝ) :=
  AbsoluteValue.isNonarchimedean_of_natCast_le_one fun n => by
    rw [show ((n : ℕ) : F) = algebraMap K F ((n : ℕ) : K) by push_cast; rfl,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1) w]
    exact_mod_cast v.apply_intCast_le_one (n : ℤ)

/-- An absolute value lying over a finite place is at most `1` on the ring of integers. -/
theorem apply_le_one_of_liesOver_finitePlace (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] (y : 𝓞 F) : w (y : F) ≤ 1 :=
  AbsoluteValue.le_one_of_isIntegral (isNonarchimedean_of_liesOver_finitePlace v w)
    (fun n => by
      rw [← map_intCast (algebraMap K F) n, AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1) w]
      exact v.apply_intCast_le_one n)
    (RingOfIntegers.isIntegral_coe y)

/-- **Layer 0.1, the nonarchimedean half, with the exponent named.** An absolute value of `F`
lying over a finite place `v` of `K` is the `(e f)⁻¹`-th power of the finite place of a prime
`𝔓` of `𝓞 F` above the prime of `v`, with `e` and `f` the ramification index and the inertia
degree of `𝔓`. -/
theorem exists_finitePlace_rpow_inv_eq_of_liesOver (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal.LiesOver v.maximalIdeal.asIdeal ∧
      ∀ y : F, w y = FinitePlace.mk P y ^
        (((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹ := by
  have hres : ∀ y : K, w (algebraMap K F y) = v y :=
    AbsoluteValue.apply_algebraMap_of_liesOver w
  have hint : ∀ n : ℤ, w ((n : ℤ) : F) ≤ 1 := by
    intro n
    rw [← map_intCast (algebraMap K F) n, hres]
    exact v.apply_intCast_le_one n
  have hna : IsNonarchimedean (w : F → ℝ) := isNonarchimedean_of_liesOver_finitePlace v w
  have hle : ∀ y : 𝓞 F, w (y : F) ≤ 1 := apply_le_one_of_liesOver_finitePlace v w
  have hcoe : ∀ u : 𝓞 K,
      ((algebraMap (𝓞 K) (𝓞 F) u : 𝓞 F) : F) = algebraMap K F ((u : 𝓞 K) : K) := by
    intro u
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 F) F, ← IsScalarTower.algebraMap_apply (𝓞 K) K F]
  have hvmem : ∀ u : 𝓞 K, u ∈ v.maximalIdeal.asIdeal ↔ v ((u : 𝓞 K) : K) < 1 := by
    intro u
    rw [← FinitePlace.mk_lt_one_iff_mem, FinitePlace.mk_maximalIdeal]
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
  have hzK0 : ((z : 𝓞 K) : K) ≠ 0 := fun h => hz0 (by exact_mod_cast h)
  have hvz : v ((z : 𝓞 K) : K) < 1 := (hvmem z).mp hzmem
  have hzF0 : algebraMap (𝓞 K) (𝓞 F) z ≠ 0 := fun h => hz0 <|
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))).mp h
  have hwzF : w ((algebraMap (𝓞 K) (𝓞 F) z : 𝓞 F) : F) < 1 := by
    rw [hcoe z, hres]; exact hvz
  obtain ⟨P, t, ht, hPt⟩ :=
    AbsoluteValue.exists_heightOneSpectrum_rpow_eq hna hle ⟨_, hzF0, hwzF⟩
  have hmem : ∀ y : 𝓞 F, y ∈ P.asIdeal ↔ w (y : F) < 1 := by
    intro y
    rw [← FinitePlace.mk_lt_one_iff_mem, hPt, Real.rpow_lt_one_iff' (by positivity) ht]
  have hover : P.asIdeal.LiesOver v.maximalIdeal.asIdeal := by
    refine ⟨?_⟩
    ext u
    rw [Ideal.under_def, Ideal.mem_comap, hmem, hcoe u, hres, ← hvmem u]
  refine ⟨P, hover, ?_⟩
  set e := P.asIdeal.ramificationIdx (𝓞 K) with he
  set f := P.asIdeal.inertiaDeg (𝓞 K) with hf
  have hef : 0 < e * f :=
    Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
  have hloc : ∀ u : K,
      FinitePlace.mk P (algebraMap K F u) = FinitePlace.mk v.maximalIdeal u ^ (e * f) := fun u =>
    FinitePlace.mk_algebraMap v.maximalIdeal P u
  have hb0 : 0 < FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) := FinitePlace.pos_iff.mpr hzK0
  have hb1 : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) < 1 := by
    rw [FinitePlace.mk_maximalIdeal]; exact hvz
  have hkey : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^ (((e * f : ℕ) : ℝ) * t)
      = FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^ (1 : ℝ) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast, Real.rpow_one, ← hloc ((z : 𝓞 K) : K), ← hPt,
      hres, FinitePlace.mk_maximalIdeal]
  have htef : ((e * f : ℕ) : ℝ) * t = 1 := (Real.rpow_right_inj hb0 hb1.ne).mp hkey
  have ht' : t = (((e * f : ℕ) : ℝ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact htef)
  intro y
  rw [hPt y, ht']

/-- **Layer 0.1, the nonarchimedean half, in the shape the roadmap pins.** An absolute value of
`F` lying over a finite place of `K` is a positive power, of exponent at most `1`, of the absolute
value of a finite place of `F`. ⚠ It is a finite place of `F` itself only when the exponent is
`1`, that is, only for an unramified prime of inertia degree one. -/
theorem exists_finitePlace_rpow_eq_of_liesOver (v : FinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃ (P : HeightOneSpectrum (𝓞 F)) (t : ℝ), 0 < t ∧ t ≤ 1 ∧
      ∀ y : F, w y = FinitePlace.mk P y ^ t := by
  obtain ⟨P, hover, hPt⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver (K := K) v w
  have hef : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
    Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
  have hefR : (1 : ℝ) ≤ ((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ) :=
    by exact_mod_cast hef
  exact ⟨P, _, by positivity, inv_le_one_of_one_le₀ hefR, hPt⟩

end NumberField

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Above a power of a finite place there is an absolute value.** Given a prime `𝔭` of `𝓞 K`
and an exponent `t > 0`, some absolute value of `F` restricts to `(FinitePlace.mk 𝔭) ^ t`: take a
prime `𝔓` of `𝓞 F` above `𝔭` and the exponent `t / (e f)`. The exponent has to be allowed to move,
which is why `AbsoluteValue.nonarchRpow` is stated for every positive exponent. -/
theorem exists_apply_algebraMap_eq_mk_rpow (P : HeightOneSpectrum (𝓞 K)) {t : ℝ} (ht : 0 < t) :
    ∃ w : AbsoluteValue F ℝ, ∀ u : K, w (algebraMap K F u) = FinitePlace.mk P u ^ t := by
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver P.asIdeal (𝓞 F)))
  have hQbot : Q ≠ ⊥ := fun h => P.ne_bot (by
    rw [hQover.over, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))])
  set R : HeightOneSpectrum (𝓞 F) := ⟨Q, hQprime, hQbot⟩ with hR
  have hover : R.asIdeal.LiesOver P.asIdeal := hQover
  set n := R.asIdeal.ramificationIdx (𝓞 K) * R.asIdeal.inertiaDeg (𝓞 K) with hn
  have hn0 : 0 < n :=
    Nat.mul_pos (R.asIdeal.ramificationIdx_pos (𝓞 K)) (R.asIdeal.inertiaDeg_pos (𝓞 K))
  have hnR : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn0
  refine ⟨AbsoluteValue.nonarchRpow (FinitePlace.isNonarchimedean_mk R) (div_pos ht hnR),
    fun u => ?_⟩
  have hb : (0 : ℝ) ≤ FinitePlace.mk P u := apply_nonneg _ u
  change FinitePlace.mk R (algebraMap K F u) ^ (t / (n : ℝ)) = FinitePlace.mk P u ^ t
  rw [FinitePlace.mk_algebraMap P R u, ← Real.rpow_natCast _ n, ← Real.rpow_mul hb]
  congr 1
  field_simp

/-- **Above a finite place there is an absolute value.** The witness is the `(e f)⁻¹`-th power of
the place of any prime of `𝓞 F` above the prime of `v`; it is a genuine finite place of `F` only
when that prime is unramified of inertia degree one, which is why the power has to be taken. -/
theorem exists_liesOver_finitePlace (v : FinitePlace K) :
    ∃ w : AbsoluteValue F ℝ, w.LiesOver v.1 := by
  obtain ⟨w, hw⟩ := exists_apply_algebraMap_eq_mk_rpow (F := F) v.maximalIdeal zero_lt_one
  refine ⟨w, ⟨AbsoluteValue.ext fun u => ?_⟩⟩
  rw [show (w.under K) u = w (algebraMap K F u) from rfl, hw u, Real.rpow_one,
    FinitePlace.mk_maximalIdeal]
  rfl

end NumberField
