/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

/-!
# The Arakelov height over a number field

Mathlib's `Height.mulHeight` measures a tuple by the **sup norm** at every place. In Arakelov
theory one instead uses the **ℓ² norm at the archimedean places** — the Fubini–Study metric on
`O(1)` — and keeps the sup norm at the finite places. The resulting height is the one in which
the constants of the Siegel-lemma literature (Bombieri–Vaaler, Schmidt) are stated.

This file defines that normalization over a number field `K` and proves the basic API that
`Mathlib.NumberTheory.Height.Basic` proves for `Height.mulHeight`.

## Main definitions

* `NumberField.arakelovMulHeight x` for `x : ι → K`: the multiplicative Arakelov height
  `∏_{v | ∞} (∑ i, v (x i)²)^{mult v / 2} · ∏ᶠ_{v ∤ ∞} ⨆ i, v (x i)`.
* `NumberField.arakelovLogHeight x`: its logarithm.
* `NumberField.arakelovMulHeight₁ x` and `NumberField.arakelovLogHeight₁ x` for `x : K`:
  the one-variable (affine) case, the height of the tuple `![x, 1]`.
* `Projectivization.arakelovMulHeight` and `Projectivization.arakelovLogHeight`: the descent
  of the above to `Projectivization K (ι → K)`, which the scaling invariance below justifies.

## Main results

* `NumberField.arakelovMulHeight_smul_eq`: invariance under scaling by a nonzero element of
  `K`, by the product formula. This is what makes the height projective.
* `NumberField.one_le_arakelovMulHeight`: the Arakelov height is at least `1`.
* `NumberField.arakelovMulHeight_comp_equiv`: invariance under reindexing.
* `NumberField.arakelovMulHeight_one` and `NumberField.arakelovMulHeight₁_one`: the values
  `#ι ^ (totalWeight K / 2)` and `2 ^ (totalWeight K / 2)` on the all-ones tuple and at `1`,
  where the sup-norm height is `1` — the two normalizations genuinely differ.
* `NumberField.arakelovLogHeight₁_eq`: the local formula for the affine logarithmic height,
  with `log⁺ (v x)` at the finite places.

## Implementation notes

As for `Height.mulHeight`, the zero tuple gets the junk value `1`: the displayed product is `0`
there, which would break `1 ≤ arakelovMulHeight` and the comparison with `Height.mulHeight`.
`NumberField.arakelovMulHeight_eq` recovers the displayed formula for a nonzero tuple, and every
statement below holds unconditionally with this convention.

The index type carries `Fintype` rather than `Finite` because the archimedean local factor is a
`Finset.sum` over `ι`; the value does not depend on the instance.

Only the archimedean factor differs from `NumberField.mulHeight_eq`. Accordingly the proof of
scaling invariance does not redo the product-formula bookkeeping at the finite places: the
transformation law of the finite part is *extracted* from Mathlib's
`Height.mulHeight_smul_eq_mulHeight`, which is the only place where the two normalizations
interact here.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
(2006), Definition 2.8.1 and 2.8.2–2.8.3, where `H_u` is the local factor above and `h_Ar` the
resulting height on projective space. Their `h_Ar` is the *absolute* height — its local
exponent is `[F_w : ℚ_p] / [F : ℚ]` — whereas `arakelovMulHeight` here is *relative* to `K`,
matching Mathlib's `Height.mulHeight`; the two differ by the exponent `[K : ℚ]`.

This is Layer 0.1 of the `ArithmeticHeights` roadmap.
-/

public section

namespace NumberField

open Finset Function Height Real

variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The **Arakelov height** of a tuple of elements of a number field: the ℓ² norm at the
archimedean places, weighted by `InfinitePlace.mult`, and the sup norm at the finite places.
For the zero tuple we take the junk value `1`, as `Height.mulHeight` does.

This is the normalization in which the constants of the Siegel-lemma literature are stated;
`Height.mulHeight` uses the sup norm at every place. Both live in the library and every bound
says which one it is in. -/
@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)

lemma arakelovMulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight x =
      (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp [arakelovMulHeight, hx]

@[simp]
lemma arakelovMulHeight_zero : arakelovMulHeight (0 : ι → K) = 1 := by
  simp [arakelovMulHeight]

/-- The logarithmic Arakelov height. As everywhere in this development, the logarithmic height
is *defined* as the logarithm of the multiplicative one and never independently. -/
@[expose] noncomputable def arakelovLogHeight (x : ι → K) : ℝ := log (arakelovMulHeight x)

lemma arakelovLogHeight_eq_log_arakelovMulHeight (x : ι → K) :
    arakelovLogHeight x = log (arakelovMulHeight x) :=
  rfl

@[simp]
lemma arakelovLogHeight_zero : arakelovLogHeight (0 : ι → K) = 0 := by
  simp [arakelovLogHeight_eq_log_arakelovMulHeight]

/-!
### Scaling invariance

The archimedean local factor scales by `v c ^ mult v` and the finite one by `v c`, so the
product formula makes the height invariant. The finite half of that computation is already in
Mathlib, inside `Height.mulHeight_smul_eq_mulHeight`; we read it off rather than redo it.
-/

section Smul

variable {κ : Type*}

omit [NumberField K] in
private lemma iSup_smul_eq {F : Type*} [FunLike F K ℝ] [MonoidWithZeroHomClass F K ℝ]
    [NonnegHomClass F K ℝ] (v : F) (c : K) (x : κ → K) :
    ⨆ i, v ((c • x) i) = v c * ⨆ i, v (x i) := by
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (apply_nonneg v c)]

/-- The transformation law of the *finite* part of the height under scaling, extracted from
Mathlib's `Height.mulHeight_smul_eq_mulHeight`. This is the product formula for `c`, applied to
the finite places only. -/
private lemma prod_infinitePlace_mul_finprod_iSup_smul [Finite κ] {x : κ → K} (hx : x ≠ 0)
    {c : K} (hc : c ≠ 0) :
    (∏ v : InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v ((c • x) i) =
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have hA : (0 : ℝ) < ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact prod_pos fun v _ ↦ pow_pos
      ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
  have h := Height.mulHeight_smul_eq_mulHeight x hc
  rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
  simp only [iSup_smul_eq, mul_pow, prod_mul_distrib] at h ⊢
  exact mul_left_cancel₀ hA.ne' (by linear_combination h)

/-- The Arakelov height is invariant under scaling, by the product formula, so it descends to
projective space exactly as `Height.mulHeight` does. -/
lemma arakelovMulHeight_smul_eq (x : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovMulHeight (c • x) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have harch (v : InfinitePlace K) :
      (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
        = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
    have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by simp [mul_pow]
    have hpow : ((v c) ^ 2) ^ (v.mult / 2 : ℝ) = v c ^ v.mult := by
      rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
        ← Real.rpow_mul (apply_nonneg v c)]
      congr 1
      push_cast
      ring
    rw [hsum, Real.mul_rpow (by positivity) (by positivity), hpow]
  rw [arakelovMulHeight_eq hcx, arakelovMulHeight_eq hx]
  simp only [harch, prod_mul_distrib]
  rw [mul_right_comm, prod_infinitePlace_mul_finprod_iSup_smul hx hc, mul_comm]

lemma arakelovLogHeight_smul_eq (x : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovLogHeight (c • x) = arakelovLogHeight x := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight,
    arakelovMulHeight_smul_eq x hc]

lemma arakelovMulHeight_neg (x : ι → K) : arakelovMulHeight (-x) = arakelovMulHeight x := by
  rw [← neg_one_smul K x, arakelovMulHeight_smul_eq x (neg_ne_zero.mpr one_ne_zero)]

lemma arakelovLogHeight_neg (x : ι → K) : arakelovLogHeight (-x) = arakelovLogHeight x := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_neg]

end Smul

/-!
### Positivity and reindexing
-/

/-- The Arakelov height of a tuple is always at least `1`. -/
lemma one_le_arakelovMulHeight (x : ι → K) : 1 ≤ arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
  have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
  have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
  rw [← arakelovMulHeight_smul_eq x (inv_ne_zero hi), arakelovMulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ ?_)
    (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
  have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
    le_trans (le_of_eq (by simp [hi']))
      (single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (mem_univ i))
  exact Real.one_le_rpow h1 (by positivity)

lemma arakelovMulHeight_pos (x : ι → K) : 0 < arakelovMulHeight x :=
  zero_lt_one.trans_le <| one_le_arakelovMulHeight x

lemma arakelovMulHeight_ne_zero (x : ι → K) : arakelovMulHeight x ≠ 0 :=
  (arakelovMulHeight_pos x).ne'

lemma arakelovLogHeight_nonneg (x : ι → K) : 0 ≤ arakelovLogHeight x :=
  log_nonneg <| one_le_arakelovMulHeight x

/-- The Arakelov height does not change under re-indexing. -/
lemma arakelovMulHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    arakelovMulHeight (x ∘ e) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : x ∘ e ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact ne_iff.mpr ⟨e.symm i, by simpa using hi⟩
  have hsum (v : InfinitePlace K) : ∑ i, v (x (e i)) ^ 2 = ∑ i, v (x i) ^ 2 :=
    e.sum_comp fun i ↦ v (x i) ^ 2
  have hsup (v : FinitePlace K) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) :=
    e.iSup_congr (congrFun rfl)
  rw [arakelovMulHeight_eq hx, arakelovMulHeight_eq hx']
  simp only [comp_apply, hsum, hsup]

lemma arakelovLogHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    arakelovLogHeight (x ∘ e) = arakelovLogHeight x := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_comp_equiv]

/-- Swapping the two coordinates leaves the Arakelov height of a pair unchanged. -/
lemma arakelovMulHeight_swap (x y : K) :
    arakelovMulHeight ![x, y] = arakelovMulHeight ![y, x] := by
  rw [show ![x, y] = ![y, x] ∘ Equiv.swap (0 : Fin 2) 1 from List.ofFn_inj.mp rfl]
  exact arakelovMulHeight_comp_equiv (Equiv.swap 0 1) ![y, x]

lemma arakelovLogHeight_swap (x y : K) :
    arakelovLogHeight ![x, y] = arakelovLogHeight ![y, x] := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_swap]

/-!
### Special values

`Height.mulHeight (1 : ι → K) = 1` by the product formula, but the Arakelov height of the same
tuple is `#ι ^ (totalWeight K / 2)`: these are the values that exhibit the difference between
the two normalizations without touching the junk value.
-/

/-- The Arakelov height of the all-ones tuple. Its sup-norm counterpart `Height.mulHeight_one`
has value `1`. -/
lemma arakelovMulHeight_one [Nonempty ι] :
    arakelovMulHeight (1 : ι → K) = (Fintype.card ι : ℝ) ^ ((totalWeight K : ℝ) / 2) := by
  have hne : (1 : ι → K) ≠ 0 := ne_iff.mpr ⟨Classical.arbitrary ι, by simp⟩
  have hfin : ∏ᶠ v : FinitePlace K, ⨆ i, v ((1 : ι → K) i) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by simp
  have harch (v : InfinitePlace K) :
      (∑ i, v ((1 : ι → K) i) ^ 2) ^ (v.mult / 2 : ℝ)
        = ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) ^ v.mult := by
    have h2 : ∑ i, v ((1 : ι → K) i) ^ 2 = (Fintype.card ι : ℝ) := by simp
    rw [h2, ← Real.rpow_natCast ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) v.mult,
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [arakelovMulHeight_eq hne, hfin, mul_one, Finset.prod_congr rfl fun v _ ↦ harch v,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq,
    ← Real.rpow_natCast ((Fintype.card ι : ℝ) ^ ((1 : ℝ) / 2)) (Module.finrank ℚ K),
    ← Real.rpow_mul (by positivity), totalWeight_eq_finrank]
  congr 1
  ring

/-- On a subsingleton index type every tuple has Arakelov height `1`, by the product formula.
This is the degenerate case in which the Arakelov and sup-norm normalizations agree. -/
@[simp]
lemma arakelovMulHeight_eq_one_of_subsingleton [Subsingleton ι] (x : ι → K) :
    arakelovMulHeight x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
  have : Nonempty ι := ⟨i⟩
  have hcard : Fintype.card ι = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr ‹_›) Fintype.card_pos
  have h1 : (x i)⁻¹ • x = 1 := funext fun j ↦ by
    rw [Subsingleton.elim j i]
    simp [inv_mul_cancel₀ hi]
  rw [← arakelovMulHeight_smul_eq x (inv_ne_zero hi), h1, arakelovMulHeight_one, hcard,
    Nat.cast_one, Real.one_rpow]

@[simp]
lemma arakelovLogHeight_eq_zero_of_subsingleton [Subsingleton ι] (x : ι → K) :
    arakelovLogHeight x = 0 := by
  simp [arakelovLogHeight_eq_log_arakelovMulHeight]

/-!
### The one-variable case

`arakelovMulHeight₁ x` is the Arakelov height of the point `(x : 1)` of the projective line.
Unlike the sup-norm normalization, its archimedean local factor is `((v x) ^ 2 + 1) ^ (mult v / 2)`
rather than `max (v x) 1 ^ mult v`, so it does **not** agree with `Height.mulHeight₁`.
-/

/-- The multiplicative Arakelov height of an element of a number field, i.e. of the point
`(x : 1)` of the projective line. -/
@[expose] noncomputable def arakelovMulHeight₁ (x : K) : ℝ := arakelovMulHeight ![x, 1]

/-- The logarithmic Arakelov height of an element of a number field. -/
@[expose] noncomputable def arakelovLogHeight₁ (x : K) : ℝ := log (arakelovMulHeight₁ x)

lemma arakelovMulHeight₁_eq_arakelovMulHeight (x : K) :
    arakelovMulHeight₁ x = arakelovMulHeight ![x, 1] :=
  rfl

lemma arakelovLogHeight₁_eq_log_arakelovMulHeight₁ (x : K) :
    arakelovLogHeight₁ x = log (arakelovMulHeight₁ x) :=
  rfl

lemma arakelovLogHeight₁_eq_arakelovLogHeight (x : K) :
    arakelovLogHeight₁ x = arakelovLogHeight ![x, 1] :=
  rfl

omit [NumberField K] in
private lemma iSup_cons_one {F : Type*} [FunLike F K ℝ] [MonoidWithZeroHomClass F K ℝ]
    (v : F) (x : K) : ⨆ i, v (![x, 1] i) = max (v x) 1 := by
  have h (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
  simp only [h]
  exact le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> simp)
    (max_le (Finite.le_ciSup_of_le 0 (by simp)) (Finite.le_ciSup_of_le 1 (by simp)))

/-- The familiar formula for the Arakelov height of a single element. -/
lemma arakelovMulHeight₁_eq (x : K) :
    arakelovMulHeight₁ x =
      (∏ v : InfinitePlace K, (v x ^ 2 + 1) ^ (v.mult / 2 : ℝ)) *
        ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  have hx : ![x, 1] ≠ 0 := by simp
  rw [arakelovMulHeight₁_eq_arakelovMulHeight, arakelovMulHeight_eq hx]
  simp only [iSup_cons_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_one, one_pow]

@[simp]
lemma arakelovMulHeight₁_zero : arakelovMulHeight₁ (0 : K) = 1 := by
  simp [arakelovMulHeight₁_eq]

@[simp]
lemma arakelovLogHeight₁_zero : arakelovLogHeight₁ (0 : K) = 0 := by
  simp [arakelovLogHeight₁_eq_log_arakelovMulHeight₁]

lemma one_le_arakelovMulHeight₁ (x : K) : 1 ≤ arakelovMulHeight₁ x :=
  one_le_arakelovMulHeight _

lemma arakelovMulHeight₁_pos (x : K) : 0 < arakelovMulHeight₁ x :=
  arakelovMulHeight_pos _

lemma arakelovMulHeight₁_ne_zero (x : K) : arakelovMulHeight₁ x ≠ 0 :=
  arakelovMulHeight_ne_zero _

lemma arakelovLogHeight₁_nonneg (x : K) : 0 ≤ arakelovLogHeight₁ x :=
  arakelovLogHeight_nonneg _

/-- The local formula for the affine logarithmic Arakelov height: the finite places contribute
`log⁺ (v x)`, the positive part of the logarithm. -/
lemma arakelovLogHeight₁_eq (x : K) :
    arakelovLogHeight₁ x =
      (∑ v : InfinitePlace K, (v.mult / 2 : ℝ) * log (v x ^ 2 + 1)) +
        ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  have harch (v : InfinitePlace K) : (0 : ℝ) < (v x ^ 2 + 1) ^ (v.mult / 2 : ℝ) := by positivity
  have hfin (v : FinitePlace K) : (0 : ℝ) < max (v x) 1 := lt_max_of_lt_right zero_lt_one
  have harchprod : (0 : ℝ) < ∏ v : InfinitePlace K, (v x ^ 2 + 1) ^ (v.mult / 2 : ℝ) :=
    Finset.prod_pos fun v _ ↦ harch v
  have hfinprod : (0 : ℝ) < ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    zero_lt_one.trans_le <| one_le_finprod fun v ↦ le_max_right _ _
  have hlog (v : InfinitePlace K) :
      log ((v x ^ 2 + 1) ^ (v.mult / 2 : ℝ)) = (v.mult / 2 : ℝ) * log (v x ^ 2 + 1) :=
    log_rpow (by positivity) _
  have hposlog : log (∏ᶠ v : FinitePlace K, max (v x) 1) = ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
    rw [Real.log_finprod hfin]
    exact finsum_congr fun v ↦ by simp [max_comm, posLog_eq_log_max_one]
  rw [arakelovLogHeight₁_eq_log_arakelovMulHeight₁, arakelovMulHeight₁_eq,
    log_mul harchprod.ne' hfinprod.ne', Real.log_prod fun v _ ↦ (harch v).ne', hposlog]
  simp_rw [hlog]

/-- The value of the affine Arakelov height at `1`: `2 ^ (totalWeight K / 2)`, not `1`. This is
the positive form of the warning that `arakelovMulHeight₁` is *not* `Height.mulHeight₁`; the two
one-variable heights are related only by the comparison lemmas of Layer 0.2. -/
lemma arakelovMulHeight₁_one :
    arakelovMulHeight₁ (1 : K) = 2 ^ ((totalWeight K : ℝ) / 2) := by
  rw [arakelovMulHeight₁_eq_arakelovMulHeight,
    show ![(1 : K), 1] = 1 from by ext i; fin_cases i <;> rfl, arakelovMulHeight_one]
  simp

lemma arakelovMulHeight₁_neg (x : K) : arakelovMulHeight₁ (-x) = arakelovMulHeight₁ x := by
  have h1 (v : InfinitePlace K) : v (-x) = v x := AbsoluteValue.map_neg v.1 x
  have h2 (v : FinitePlace K) : v (-x) = v x := AbsoluteValue.map_neg v.1 x
  simp only [arakelovMulHeight₁_eq, h1, h2]

lemma arakelovLogHeight₁_neg (x : K) : arakelovLogHeight₁ (-x) = arakelovLogHeight₁ x := by
  simp only [arakelovLogHeight₁_eq_log_arakelovMulHeight₁, arakelovMulHeight₁_neg]

/-- The affine Arakelov height is invariant under inversion: `H_Ar(x⁻¹ : 1) = H_Ar(x : 1)`,
since both are the height of the projective point `(x : 1) = (1 : x⁻¹)`. -/
lemma arakelovMulHeight₁_inv (x : K) : arakelovMulHeight₁ x⁻¹ = arakelovMulHeight₁ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  have h : ![x⁻¹, 1] = x⁻¹ • ![1, x] := by
    ext i
    fin_cases i <;> simp [inv_mul_cancel₀ hx]
  rw [arakelovMulHeight₁_eq_arakelovMulHeight, arakelovMulHeight₁_eq_arakelovMulHeight, h,
    arakelovMulHeight_smul_eq _ (inv_ne_zero hx), arakelovMulHeight_swap]

lemma arakelovLogHeight₁_inv (x : K) : arakelovLogHeight₁ x⁻¹ = arakelovLogHeight₁ x := by
  simp only [arakelovLogHeight₁_eq_log_arakelovMulHeight₁, arakelovMulHeight₁_inv]

end NumberField

/-!
### The descent to projective space

Scaling invariance makes the Arakelov height a well-defined function on
`Projectivization K (ι → K)`, exactly as for `Projectivization.mulHeight`.
-/

namespace Projectivization

open NumberField Real

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

private lemma arakelovMulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K)
    (h : a.val = t • b.val) :
    NumberField.arakelovMulHeight a.val = NumberField.arakelovMulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ arakelovMulHeight_smul_eq _ ht

private lemma arakelovLogHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K)
    (h : a.val = t • b.val) :
    NumberField.arakelovLogHeight a.val = NumberField.arakelovLogHeight b.val := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_aux a b t h]

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-- The multiplicative Arakelov height of a point of projective space over a number field. -/
noncomputable def arakelovMulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ NumberField.arakelovMulHeight r.val) arakelovMulHeight_aux

/-- The logarithmic Arakelov height of a point of projective space over a number field. -/
noncomputable def arakelovLogHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ NumberField.arakelovLogHeight r.val) arakelovLogHeight_aux

lemma arakelovMulHeight_mk {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight (mk K x hx) = NumberField.arakelovMulHeight x := by
  rfl

lemma arakelovLogHeight_mk {x : ι → K} (hx : x ≠ 0) :
    arakelovLogHeight (mk K x hx) = NumberField.arakelovLogHeight x := by
  rfl

lemma arakelovLogHeight_eq_log_arakelovMulHeight (x : Projectivization K (ι → K)) :
    arakelovLogHeight x = log (arakelovMulHeight x) := by
  rw [← x.mk_rep, arakelovMulHeight_mk, arakelovLogHeight_mk,
    NumberField.arakelovLogHeight_eq_log_arakelovMulHeight]

lemma one_le_arakelovMulHeight (x : Projectivization K (ι → K)) : 1 ≤ arakelovMulHeight x := by
  rw [← x.mk_rep, arakelovMulHeight_mk]
  exact NumberField.one_le_arakelovMulHeight _

lemma arakelovMulHeight_pos (x : Projectivization K (ι → K)) : 0 < arakelovMulHeight x :=
  zero_lt_one.trans_le <| one_le_arakelovMulHeight x

lemma arakelovMulHeight_ne_zero (x : Projectivization K (ι → K)) : arakelovMulHeight x ≠ 0 :=
  (arakelovMulHeight_pos x).ne'

lemma arakelovLogHeight_nonneg (x : Projectivization K (ι → K)) : 0 ≤ arakelovLogHeight x := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight]
  exact log_nonneg x.one_le_arakelovMulHeight

end Projectivization

/-!
### `positivity` extensions

The Arakelov heights are positive (multiplicative) resp. nonnegative (logarithmic), exactly as
their sup-norm counterparts in `Mathlib.NumberTheory.Height.Basic`.
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `NumberField.arakelovMulHeight` is always positive. -/
@[positivity NumberField.arakelovMulHeight _]
meta def evalArakelovMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovMulHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(NumberField.arakelovMulHeight_pos $a))
  | _, _, _ => throwError "not NumberField.arakelovMulHeight"

/-- Extension for the `positivity` tactic: `NumberField.arakelovLogHeight` is always
nonnegative. -/
@[positivity NumberField.arakelovLogHeight _]
meta def evalArakelovLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovLogHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(NumberField.arakelovLogHeight_nonneg $a))
  | _, _, _ => throwError "not NumberField.arakelovLogHeight"

/-- Extension for the `positivity` tactic: `NumberField.arakelovMulHeight₁` is always
positive. -/
@[positivity NumberField.arakelovMulHeight₁ _]
meta def evalArakelovMulHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovMulHeight₁ $K $KF $KNF $a) =>
    assertInstancesCommute
    pure (.positive q(NumberField.arakelovMulHeight₁_pos $a))
  | _, _, _ => throwError "not NumberField.arakelovMulHeight₁"

/-- Extension for the `positivity` tactic: `NumberField.arakelovLogHeight₁` is always
nonnegative. -/
@[positivity NumberField.arakelovLogHeight₁ _]
meta def evalArakelovLogHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovLogHeight₁ $K $KF $KNF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(NumberField.arakelovLogHeight₁_nonneg $a))
  | _, _, _ => throwError "not NumberField.arakelovLogHeight₁"

/-- Extension for the `positivity` tactic: `Projectivization.arakelovMulHeight` is always
positive. -/
@[positivity Projectivization.arakelovMulHeight _]
meta def evalProjArakelovMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.arakelovMulHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(Projectivization.arakelovMulHeight_pos $a))
  | _, _, _ => throwError "not Projectivization.arakelovMulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.arakelovLogHeight` is always
nonnegative. -/
@[positivity Projectivization.arakelovLogHeight _]
meta def evalProjArakelovLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.arakelovLogHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(Projectivization.arakelovLogHeight_nonneg $a))
  | _, _, _ => throwError "not Projectivization.arakelovLogHeight"

end Mathlib.Meta.Positivity

/-!
### Worked examples

Cheap checks that the definition means what it should. Over `ℚ` the two normalizations of the
height of the point `(1 : 1)` genuinely differ, so the `√N` factors in the Siegel-lemma
literature are not cosmetic and a proof that silently interchanges the two heights is wrong.
-/

section Examples

open Height NumberField

/-- The Arakelov height of `(1 : 1)` over `ℚ` is `√2`: the archimedean local factor is the
ℓ² norm `√(1² + 1²)`. -/
example : arakelovMulHeight ![(1 : ℚ), 1] = Real.sqrt 2 := by
  have hx : ![(1 : ℚ), 1] ≠ 0 := by simp
  have h1 (i : Fin 2) : ![(1 : ℚ), 1] i = 1 := by fin_cases i <;> rfl
  have hfin : ∏ᶠ v : FinitePlace ℚ, ⨆ i, v (![(1 : ℚ), 1] i) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by simp [h1]
  have harch (v : InfinitePlace ℚ) :
      (∑ i, v (![(1 : ℚ), 1] i) ^ 2) ^ (v.mult / 2 : ℝ) = Real.sqrt 2 ^ v.mult := by
    have h2 : ∑ i, v (![(1 : ℚ), 1] i) ^ 2 = (2 : ℝ) := by simp [h1]
    rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 2)) v.mult,
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [arakelovMulHeight_eq hx, hfin, mul_one, Finset.prod_congr rfl fun v _ ↦ harch v,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  simp

/-- …whereas the sup-norm height of the same tuple is `1`. -/
example : Height.mulHeight ![(1 : ℚ), 1] = 1 := by
  rw [show ![(1 : ℚ), 1] = 1 from by ext i; fin_cases i <;> rfl]
  exact Height.mulHeight_one

end Examples

end
