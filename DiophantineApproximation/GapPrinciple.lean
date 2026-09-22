/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Absolute
public import DiophantineApproximation.ApproximationClass
public import DiophantineApproximation.FundamentalInequality
public import DiophantineApproximation.Nonarchimedean
public import DiophantineApproximation.RothKeyInequality

-- Used only by the acceptance criteria.
import DiophantineApproximation.RationalPlaces

/-!
# The strong gap principle

Let `K` be a number field, `S` a finite set of places carried as two typed finsets, `F / K` a
finite extension, `w v` an absolute value of `F` over `v` and `α v ∈ F` a target for each
`v ∈ S`. Call `β ∈ K` a **solution** if `Λ(β) ≤ H(β) ^ (−κ)`, where `Λ(β)` is the product of the
local approximation factors `min 1 |β − α v|_v` of Roth's theorem. The **strong gap principle**
(Bombieri–Gubler, Theorem 6.5.4) says that two different solutions `β`, `β'` in one approximation
class of size `1 / N`, with `h(β) ≤ h(β')`, satisfy

```text
h(β')  ≥  ((1 − |S| / N) κ − 1) h(β) − log 4
```

in absolute logarithmic heights. Once `c = (1 − |S| / N) κ − 1 > 1`, the heights of the solutions
in one class grow at least geometrically (Remark 6.5.5), and that is what Layer 3.7 counts with.

The proof is the book's. At a place of `S` both `β` and `β'` are close to the same target, so
`|β − β'|_v` is at most `2 max (|β − α v|, |β' − α v|)` — the factor `2` only at the infinite
places — and the class bounds both by `H(β) ^ (−κ λ v)`. Multiplying over `S` gives an upper
bound `2 ^ [K : ℚ] H(β) ^ (−κ ∑ λ)` for the truncated product of `β − β'`; the fundamental
inequality bounds the same product below by `H(β − β') ^ (−1)`, and
`H(β − β') ≤ 2 ^ [K : ℚ] H(β) H(β')`.

## Main definitions

* `NumberField.approxClass`: **the approximation class** of `β` of size `1 / N`, as its label
  `c : S → ℕ` with `∑ c ≤ N` (Bombieri–Gubler 6.4.2), extended to the solutions equal to a target.

## Main results

* `NumberField.mul_logHeight₁_sub_le_of_localApprox_le`: **the strong gap principle** for any two
  different elements whose local factors are governed by one vector of exponents, in Mathlib's
  relative heights.
* `NumberField.mul_absLogHeight₁_sub_le_of_localApprox_le`: the same in absolute heights.
* `NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq`: **Theorem 6.5.4**, for two solutions
  in one approximation class.
* `NumberField.localApprox_le_rpow_approxClass` and
  `NumberField.one_sub_card_div_le_sum_approxClass`: the class governs the local factors of its
  members, the book's (6.9) and (6.10).

## Implementation notes

⚠ **The gap principle does not need the class, only its upper bounds.** The book's proof uses
of the class only the upper half of (6.9) and the lower bound (6.10) on `∑ λ`; so the statement
underneath takes any vector `λ ≥ 0` with `Λ_v(β), Λ_v(β') ≤ H ^ (−κ λ v)`. In particular the book's
first step — passing to the places where `|β − α v| < 1` — is not needed: at a place where
`λ v = 0` the bound `min 1 · ≤ 1` is free.

⚠ **A solution equal to a target lies in no class of the book, and here it lies in a corner.**
The book classifies the *non-trivial* approximations by the logarithmic profile
`log Λ_v(β) / log Λ(β)`, which is `0 / 0`-meaningless when `β = α v` for some `v ∈ S`. Such a
`β` is still a solution, and Lemma 6.5.6 counts every solution. `NumberField.approxClass` sends it
to the corner `N • e_v` of the simplex: its local factor at `v` is `0`, every other one is at most
`1`, and so the class bounds (6.9) and (6.10) hold for it with room to spare. Two different such
solutions in one corner would both equal `α v`, so the corners cost the count nothing.

⚠ **The constant `log 4` is `log 2` twice, and the second `log 2` needs the finite places to be
nonarchimedean over `F`.** One `log 2` is the triangle inequality at the infinite places, weighted
by `mult` and summing to `[K : ℚ] log 2` in relative heights; the other is
`H(β − β') ≤ 2 ^ [K : ℚ] H(β) H(β')`. At a finite place the extension `w v` is nonarchimedean
because it is at most `1` on `ℕ` (`AbsoluteValue.isNonarchimedean_of_natCast_le_one`, Layer 0.1);
without it every finite place of `S` would cost another `log 2`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.5.4 and Remark 6.5.5.

This is the first half of Layer 3.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- **The absolute logarithmic height is the relative one divided by the degree.** -/
theorem absLogHeight₁_eq_inv_mul_logHeight₁ (x : K) :
    absLogHeight₁ x = ((Module.finrank ℚ K : ℝ))⁻¹ * logHeight₁ x := by
  rw [← absLogHeight_eq_absLogHeight₁, absLogHeight_eq, ← logHeight₁_eq_logHeight]

/-- The relative logarithmic height is `[K : ℚ]` times the absolute one. -/
theorem logHeight₁_eq_totalWeight_mul_absLogHeight₁ (x : K) :
    logHeight₁ x = totalWeight K * absLogHeight₁ x := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [absLogHeight₁_eq_inv_mul_logHeight₁, totalWeight_eq_finrank]
  field_simp

/-! ### The local step -/

/-- The triangle-inequality constant of a place of `S`: `2` at an infinite place and `1` at a
finite one. -/
private noncomputable def triangleConst {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} (a : ↥Sinf ⊕ ↥Sfin) : ℝ :=
  a.elim (fun _ ↦ 2) fun _ ↦ 1

private theorem one_le_triangleConst {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} (a : ↥Sinf ⊕ ↥Sfin) : 1 ≤ triangleConst a := by
  cases a with
  | inl v => change (1 : ℝ) ≤ 2; norm_num
  | inr v => exact le_rfl

/-- **Two points close to one target are close to each other**, at a place of `S`: the distance
is at most the triangle constant times the larger of the two distances to the target. -/
private theorem apply_sub_le_triangleConst_mul {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (α : AbsoluteValue K ℝ → F) (a : ↥Sinf ⊕ ↥Sfin)
    (hw : (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a)) (β β' : K) :
    sPlaceAbsValue a (β - β') ≤ triangleConst a *
      max (w (sPlaceAbsValue a) (algebraMap K F β - α (sPlaceAbsValue a)))
        (w (sPlaceAbsValue a) (algebraMap K F β' - α (sPlaceAbsValue a))) := by
  set W := w (sPlaceAbsValue a) with hWdef
  set x := algebraMap K F β - α (sPlaceAbsValue a) with hxdef
  set y := algebraMap K F β' - α (sPlaceAbsValue a) with hydef
  have hlift : sPlaceAbsValue a (β - β') = W (x - y) := by
    rw [hxdef, hydef, sub_sub_sub_cancel_right, ← map_sub,
      show W (algebraMap K F (β - β')) = (W.under K) (β - β') from rfl,
      AbsoluteValue.LiesOver.under_eq W (sPlaceAbsValue a)]
  have hunder : ∀ z : K, W (algebraMap K F z) = sPlaceAbsValue a z := fun z ↦ by
    rw [show W (algebraMap K F z) = (W.under K) z from rfl,
      AbsoluteValue.LiesOver.under_eq W (sPlaceAbsValue a)]
  have hsub : W (x - y) = W (x + -y) := by rw [sub_eq_add_neg]
  rw [hlift, hsub]
  cases a with
  | inl v =>
      change W (x + -y) ≤ 2 * max (W x) (W y)
      have h1 := W.add_le x (-y)
      rw [W.map_neg] at h1
      linarith [le_max_left (W x) (W y), le_max_right (W x) (W y)]
  | inr v =>
      change W (x + -y) ≤ 1 * max (W x) (W y)
      have hv : ∀ n : ℕ, (v : FinitePlace K) (n : K) ≤ 1 := fun n ↦
        IsNonarchimedean.apply_natCast_le_one (by simp) (by simp)
          (fun s t ↦ FinitePlace.add_le (v : FinitePlace K) s t)
      have hna : IsNonarchimedean (W : F → ℝ) := by
        refine AbsoluteValue.isNonarchimedean_of_natCast_le_one fun n ↦ ?_
        rw [← map_natCast (algebraMap K F), hunder]
        exact hv n
      rw [one_mul, ← W.map_neg y]
      exact hna x (-y)

/-- **The truncation step**: if `x ≤ C max u u'` with `C ≥ 1`, then the `k`-th power of
`min 1 x` is at most `C ^ k` times the larger of the `k`-th powers of `min 1 u` and `min 1 u'`. -/
private theorem min_one_pow_le_mul_max {x C u u' : ℝ} (hx : 0 ≤ x) (hC : 1 ≤ C) (hu : 0 ≤ u)
    (hu' : 0 ≤ u') (hxC : x ≤ C * max u u') (k : ℕ) :
    min 1 x ^ k ≤ C ^ k * max (min 1 u ^ k) (min 1 u' ^ k) := by
  have hm : min 1 x ≤ C * max (min 1 u) (min 1 u') := by
    rcases le_or_gt (max u u') 1 with h | h
    · rw [min_eq_right (le_trans (le_max_left _ _) h), min_eq_right (le_trans (le_max_right _ _) h)]
      exact le_trans (min_le_right _ _) hxC
    · have hmax : max (min 1 u) (min 1 u') = 1 := by
        rcases lt_max_iff.mp h with h1 | h1
        · rw [min_eq_left h1.le]
          exact max_eq_left (min_le_left _ _)
        · rw [min_eq_left h1.le]
          exact max_eq_right (min_le_left _ _)
      rw [hmax, mul_one]
      exact le_trans (min_le_left _ _) hC
  have h0 : 0 ≤ min 1 x := le_min zero_le_one hx
  have hmaxpow : max (min 1 u) (min 1 u') ^ k = max (min 1 u ^ k) (min 1 u' ^ k) := by
    rcases le_total (min 1 u) (min 1 u') with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (le_min zero_le_one hu) h k)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (le_min zero_le_one hu') h k)]
  calc min 1 x ^ k ≤ (C * max (min 1 u) (min 1 u')) ^ k := pow_le_pow_left₀ h0 hm k
    _ = C ^ k * max (min 1 u ^ k) (min 1 u' ^ k) := by rw [mul_pow, hmaxpow]

/-! ### The strong gap principle -/

/-- **The strong gap principle** (Bombieri–Gubler, Theorem 6.5.4), in Mathlib's relative heights
and for any vector of exponents `λ ≥ 0` governing the local approximation factors of two different
elements `β`, `β'` of `K` with `h(β) ≤ h(β')`. -/
theorem mul_logHeight₁_sub_le_of_localApprox_le {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 ≤ κ) {lam : (↥Sinf ⊕ ↥Sfin) → ℝ}
    (hlam : ∀ a, 0 ≤ lam a) {β β' : K} (hne : β ≠ β') (hle : logHeight₁ β ≤ logHeight₁ β')
    (hβ : ∀ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ * lam a))
    (hβ' : ∀ a, localApprox Sinf Sfin w α a β' ≤ mulHeight₁ β' ^ (-κ * lam a)) :
    (κ * ∑ a, lam a - 1) * logHeight₁ β - totalWeight K * Real.log 4 ≤ logHeight₁ β' := by
  have hwA : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a) := by
    rintro (v | v)
    · exact hwInf v v.2
    · exact hwFin v v.2
  have hH : (0 : ℝ) < mulHeight₁ β := mulHeight₁_pos β
  have hH' : mulHeight₁ β ≤ mulHeight₁ β' := by
    rwa [logHeight₁_eq_log_mulHeight₁, logHeight₁_eq_log_mulHeight₁,
      Real.log_le_log_iff (mulHeight₁_pos _) (mulHeight₁_pos _)] at hle
  -- the local bound at every place of `S`
  have hloc : ∀ a, min 1 (sPlaceAbsValue a (β - β')) ^ sPlaceWeight a
      ≤ triangleConst a ^ sPlaceWeight a * mulHeight₁ β ^ (-κ * lam a) := by
    intro a
    have h1 := min_one_pow_le_mul_max ((sPlaceAbsValue a).nonneg _) (one_le_triangleConst a)
      ((w _).nonneg _) ((w _).nonneg _) (apply_sub_le_triangleConst_mul α a (hwA a) β β')
      (sPlaceWeight a)
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_
      (pow_nonneg (zero_le_one.trans (one_le_triangleConst a)) _))
    refine max_le (hβ a) (le_trans (hβ' a) ?_)
    exact Real.rpow_le_rpow_of_nonpos hH hH' (by nlinarith [hlam a])
  -- the product over `S`
  have hprod : (∏ a : ↥Sinf ⊕ ↥Sfin, min 1 (sPlaceAbsValue a (β - β')) ^ sPlaceWeight a)
      ≤ (∏ a : ↥Sinf ⊕ ↥Sfin, triangleConst a ^ sPlaceWeight a)
        * mulHeight₁ β ^ (-κ * ∑ a, lam a) := by
    calc (∏ a : ↥Sinf ⊕ ↥Sfin, min 1 (sPlaceAbsValue a (β - β')) ^ sPlaceWeight a)
        ≤ ∏ a : ↥Sinf ⊕ ↥Sfin,
            (triangleConst a ^ sPlaceWeight a * mulHeight₁ β ^ (-κ * lam a)) :=
          Finset.prod_le_prod₀
            (fun a _ ↦ pow_nonneg (le_min zero_le_one ((sPlaceAbsValue a).nonneg _)) _)
            fun a _ ↦ hloc a
      _ = (∏ a : ↥Sinf ⊕ ↥Sfin, triangleConst a ^ sPlaceWeight a)
          * mulHeight₁ β ^ (-κ * ∑ a, lam a) := by
          rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.rpow_sum_of_pos hH]
  have htri : (∏ a : ↥Sinf ⊕ ↥Sfin, triangleConst a ^ sPlaceWeight a)
      ≤ 2 ^ totalWeight K := by
    rw [Fintype.prod_sum_type]
    have hfin : (∏ v : ↥Sfin, triangleConst (Sinf := Sinf) (Sum.inr v)
        ^ sPlaceWeight (Sinf := Sinf) (Sum.inr v)) = 1 :=
      Finset.prod_eq_one fun v _ ↦ by
        rw [sPlaceWeight_inr, pow_one]
        rfl
    have hinf : (∏ v : ↥Sinf, triangleConst (Sfin := Sfin) (Sum.inl v)
        ^ sPlaceWeight (Sfin := Sfin) (Sum.inl v))
        = (2 : ℝ) ^ ∑ v : ↥Sinf, (v : InfinitePlace K).mult := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun v _ ↦ by rw [sPlaceWeight_inl]; rfl
    rw [hfin, mul_one, hinf]
    refine pow_le_pow_right₀ one_le_two ?_
    rw [totalWeight_eq_sum_mult, Finset.sum_coe_sort Sinf fun v : InfinitePlace K ↦ v.mult]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  -- the fundamental inequality from below
  have hne' : β - β' ≠ 0 := sub_ne_zero.mpr hne
  have hlow := inv_mulHeight₁_le_prod_min_one_apply Sinf Sfin hne'
  have hsplit : (∏ a : ↥Sinf ⊕ ↥Sfin, min 1 (sPlaceAbsValue a (β - β')) ^ sPlaceWeight a)
      = (∏ v ∈ Sinf, min 1 (v (β - β')) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v (β - β')) := by
    rw [Fintype.prod_sum_type]
    congr 1
    · rw [← Finset.prod_coe_sort Sinf fun v ↦ min 1 (v (β - β')) ^ v.mult]
      rfl
    · rw [← Finset.prod_coe_sort Sfin fun v ↦ min 1 (v (β - β'))]
      exact Finset.prod_congr rfl fun v _ ↦ pow_one _
  rw [← hsplit] at hlow
  have hlow' : (mulHeight₁ (β - β'))⁻¹ ≤ 2 ^ totalWeight K * mulHeight₁ β ^ (-κ * ∑ a, lam a) :=
    le_trans hlow (le_trans hprod (mul_le_mul_of_nonneg_right htri (by positivity)))
  have hlog := Real.log_le_log (inv_pos.mpr (mulHeight₁_pos _)) hlow'
  rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow hH] at hlog
  simp only [← logHeight₁_eq_log_mulHeight₁] at hlog
  have hsum := logHeight₁_sub_le β β'
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hexp : (κ * ∑ a, lam a - 1) * logHeight₁ β
      = κ * (∑ a, lam a) * logHeight₁ β - logHeight₁ β := by ring
  rw [hexp, h4]
  linarith

/-- **The strong gap principle in absolute heights** (Bombieri–Gubler, Theorem 6.5.4): the book's
constant `log 4` appears without the degree. -/
theorem mul_absLogHeight₁_sub_le_of_localApprox_le {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 ≤ κ) {lam : (↥Sinf ⊕ ↥Sfin) → ℝ}
    (hlam : ∀ a, 0 ≤ lam a) {β β' : K} (hne : β ≠ β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β')
    (hβ : ∀ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ * lam a))
    (hβ' : ∀ a, localApprox Sinf Sfin w α a β' ≤ mulHeight₁ β' ^ (-κ * lam a)) :
    (κ * ∑ a, lam a - 1) * absLogHeight₁ β - Real.log 4 ≤ absLogHeight₁ β' := by
  have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  have hle' : logHeight₁ β ≤ logHeight₁ β' := by
    rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁, logHeight₁_eq_totalWeight_mul_absLogHeight₁]
    exact mul_le_mul_of_nonneg_left hle hd.le
  have h := mul_logHeight₁_sub_le_of_localApprox_le hwInf hwFin α hκ hlam hne hle' hβ hβ'
  simp only [logHeight₁_eq_totalWeight_mul_absLogHeight₁] at h
  have h' : (totalWeight K : ℝ) * ((κ * ∑ a, lam a - 1) * absLogHeight₁ β - Real.log 4)
      ≤ (totalWeight K : ℝ) * absLogHeight₁ β' := by linarith
  exact le_of_mul_le_mul_left h' hd

/-! ### Approximation classes -/

variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
  (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)

open scoped Classical in
/-- **The approximation class of `β` of size `1 / N`** (Bombieri–Gubler 6.4.2), as its label: the
south-west corner, scaled by `N`, of the cell of side `1 / N` containing the logarithmic profile
`(log Λ_v(β) / log Λ(β))_v`. A `β` equal to a target at some place of `S` has no profile; it is
put in the corner `N • e_v` of that place. -/
noncomputable def approxClass (N : ℕ) (β : K) : (↥Sinf ⊕ ↥Sfin) → ℕ :=
  if h : ∃ a, localApprox Sinf Sfin w α a β = 0 then Pi.single h.choose N
  else Real.cellIndex N (Real.logProfile fun a ↦ localApprox Sinf Sfin w α a β)

/-- **Lemma 6.4.3, the label side**: the label of every class solves `∑ a, c a ≤ N`. -/
theorem sum_approxClass_le (N : ℕ) (β : K) : ∑ a, approxClass Sinf Sfin w α N β a ≤ N := by
  classical
  unfold approxClass
  split_ifs with h
  · simp
  · push Not at h
    set f : (↥Sinf ⊕ ↥Sfin) → ℝ := fun a ↦ localApprox Sinf Sfin w α a β with hfdef
    have hpos : ∀ a, 0 < f a := fun a ↦
      lt_of_le_of_ne (localApprox_nonneg Sinf Sfin w α a β) (h a).symm
    have hle : ∀ a, f a ≤ 1 := fun a ↦ localApprox_le_one Sinf Sfin w α a β
    rcases lt_or_eq_of_le (Finset.prod_le_one₀ (fun a _ ↦ (hpos a).le) fun a _ ↦ hle a) with
      hlt | heq
    · exact Real.sum_cellIndex_le (Real.logProfile_nonneg hpos hle hlt)
        (Real.sum_logProfile hpos hlt).le
    · have h0 : ∀ a, Real.logProfile f a = 0 := fun a ↦ by
        rw [Real.logProfile_apply, heq, Real.log_one, div_zero]
      simp [Real.cellIndex_apply, h0]

variable {Sinf Sfin w α}

/-- **The upper half of (6.9) for the class of a solution**: its label governs every local
approximation factor. -/
theorem localApprox_le_rpow_approxClass {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {β : K}
    (hsol : ∏ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ))
    (hH : 1 < mulHeight₁ β) (a : ↥Sinf ⊕ ↥Sfin) :
    localApprox Sinf Sfin w α a β
      ≤ mulHeight₁ β ^ (-κ * ((approxClass Sinf Sfin w α N β a : ℝ) / N)) := by
  classical
  have hH0 : (0 : ℝ) < mulHeight₁ β := by linarith
  unfold approxClass
  split_ifs with h
  · by_cases ha : a = h.choose
    · rw [ha, h.choose_spec]
      exact Real.rpow_nonneg hH0.le _
    · rw [Pi.single_eq_of_ne ha]
      simp only [Nat.cast_zero, zero_div, mul_zero, Real.rpow_zero]
      exact localApprox_le_one Sinf Sfin w α a β
  · push Not at h
    set f : (↥Sinf ⊕ ↥Sfin) → ℝ := fun a ↦ localApprox Sinf Sfin w α a β with hfdef
    have hpos : ∀ b, 0 < f b := fun b ↦
      lt_of_le_of_ne (localApprox_nonneg Sinf Sfin w α b β) (h b).symm
    have hle : ∀ b, f b ≤ 1 := fun b ↦ localApprox_le_one Sinf Sfin w α b β
    have hprod : ∏ b, f b < 1 :=
      lt_of_le_of_lt hsol (Real.rpow_lt_one_of_one_lt_of_neg hH (by linarith))
    have hprod0 : (0 : ℝ) < ∏ b, f b := Finset.prod_pos fun b _ ↦ hpos b
    refine le_trans (Real.le_rpow_cellIndex_div hN hpos hle hprod a) ?_
    calc (∏ b, f b) ^ ((Real.cellIndex N (Real.logProfile f) a : ℝ) / N)
        ≤ (mulHeight₁ β ^ (-κ)) ^ ((Real.cellIndex N (Real.logProfile f) a : ℝ) / N) :=
          Real.rpow_le_rpow hprod0.le hsol (by positivity)
      _ = mulHeight₁ β ^ (-κ * ((Real.cellIndex N (Real.logProfile f) a : ℝ) / N)) := by
          rw [← Real.rpow_mul hH0.le]

/-- **(6.10) for the class of a solution**: the exponents of its label sum to at least
`1 − |S| / N`. -/
theorem one_sub_card_div_le_sum_approxClass {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {β : K}
    (hsol : ∏ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ))
    (hH : 1 < mulHeight₁ β) :
    1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N
      ≤ ∑ a, (approxClass Sinf Sfin w α N β a : ℝ) / N := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = Sinf.card + Sfin.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  unfold approxClass
  split_ifs with h
  · have hone : ∑ a, (((Pi.single h.choose N : (↥Sinf ⊕ ↥Sfin) → ℕ) a : ℕ) : ℝ) / N = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum]
      simp only [Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte]
      exact div_self hN'.ne'
    rw [hone]
    have : (0 : ℝ) ≤ ((Sinf.card + Sfin.card : ℕ) : ℝ) / N := by positivity
    linarith
  · push Not at h
    set f : (↥Sinf ⊕ ↥Sfin) → ℝ := fun a ↦ localApprox Sinf Sfin w α a β with hfdef
    have hpos : ∀ b, 0 < f b := fun b ↦
      lt_of_le_of_ne (localApprox_nonneg Sinf Sfin w α b β) (h b).symm
    have hprod : ∏ b, f b < 1 :=
      lt_of_le_of_lt hsol (Real.rpow_lt_one_of_one_lt_of_neg hH (by linarith))
    have h610 := Real.one_sub_card_div_lt_sum_cellIndex_div hN (Real.sum_logProfile hpos hprod)
    rw [hcard] at h610
    exact h610.le

/-- **Theorem 6.5.4, the strong gap principle** (Bombieri–Gubler): two different solutions of
`Λ(β) ≤ H(β) ^ (−κ)` in one approximation class of size `1 / N`, with `h(β) ≤ h(β')`, satisfy
`h(β') ≥ ((1 − |S| / N) κ − 1) h(β) − log 4`, in absolute logarithmic heights. -/
theorem mul_absLogHeight₁_sub_le_of_approxClass_eq
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {β β' : K}
    (hsol : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ))
    (hsol' : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β' - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β' - α v.1)) ≤ mulHeight₁ β' ^ (-κ))
    (hne : β ≠ β') (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β') :
    ((1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) * absLogHeight₁ β - Real.log 4
      ≤ absLogHeight₁ β' := by
  rw [← prod_localApprox] at hsol hsol'
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hrel := logHeight₁_eq_totalWeight_mul_absLogHeight₁ (K := K)
  have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  -- a solution of height `1` makes the statement trivial
  rcases le_or_gt (mulHeight₁ β) 1 with hH | hH
  · have h0 : absLogHeight₁ β = 0 := by
      have h1 : logHeight₁ β = 0 := by
        rw [logHeight₁_eq_log_mulHeight₁, le_antisymm hH (one_le_mulHeight₁ β), Real.log_one]
      have := hrel β
      rw [h1] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h hd.ne'
      · exact h
    rw [h0, mul_zero, zero_sub]
    linarith [absLogHeight₁_nonneg β']
  have hH' : 1 < mulHeight₁ β' := by
    have hpos : 0 < absLogHeight₁ β := by
      rw [absLogHeight₁_eq_inv_mul_logHeight₁, logHeight₁_eq_log_mulHeight₁]
      exact mul_pos (inv_pos.mpr (by exact_mod_cast Module.finrank_pos)) (Real.log_pos hH)
    have hpos' : 0 < logHeight₁ β' := by
      rw [hrel]
      exact mul_pos hd (lt_of_lt_of_le hpos hle)
    rw [logHeight₁_eq_log_mulHeight₁] at hpos'
    exact (Real.log_pos_iff (mulHeight₁_pos _).le).mp hpos'
  set lam : (↥Sinf ⊕ ↥Sfin) → ℝ := fun a ↦ (approxClass Sinf Sfin w α N β a : ℝ) / N with hlamdef
  have hβ := localApprox_le_rpow_approxClass hκ hN hsol hH
  have hβ' := localApprox_le_rpow_approxClass hκ hN hsol' hH'
  rw [← hclass] at hβ'
  have hgap := mul_absLogHeight₁_sub_le_of_localApprox_le hwInf hwFin α hκ.le
    (lam := lam) (fun a ↦ by positivity) hne hle hβ hβ'
  have hsum := one_sub_card_div_le_sum_approxClass hκ hN hsol hH
  have hmono : ((1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) * absLogHeight₁ β
      ≤ (κ * ∑ a, lam a - 1) * absLogHeight₁ β := by
    refine mul_le_mul_of_nonneg_right ?_ (absLogHeight₁_nonneg β)
    nlinarith
  linarith

/-! ### Acceptance criteria -/

/-- **Conformance: at one place there is one class**, so the strong gap principle needs no class
hypothesis there — Davenport and Roth's setting. The profile of a non-trivial approximation at a
single place is `log Λ / log Λ = 1`, and a solution equal to the target sits in the only corner. -/
theorem approxClass_singleton_empty (v : InfinitePlace K)
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {α : AbsoluteValue K ℝ → F} {κ : ℝ} (hκ : 0 < κ)
    {N : ℕ} {β : K}
    (hsol : ∏ a, localApprox {v} ∅ w α a β ≤ mulHeight₁ β ^ (-κ)) (hH : 1 < mulHeight₁ β) :
    approxClass {v} ∅ w α N β = fun _ ↦ N := by
  classical
  have : Subsingleton (↥({v} : Finset (InfinitePlace K)) ⊕ ↥(∅ : Finset (FinitePlace K))) := by
    refine ⟨?_⟩
    rintro (⟨x, hx⟩ | ⟨y, hy⟩) (⟨x', hx'⟩ | ⟨y', hy'⟩)
    · rw [Finset.mem_singleton] at hx hx'
      subst hx hx'
      rfl
    · exact absurd hy' (Finset.notMem_empty _)
    · exact absurd hy (Finset.notMem_empty _)
    · exact absurd hy (Finset.notMem_empty _)
  funext a
  unfold approxClass
  split_ifs with h
  · rw [Subsingleton.elim a h.choose, Pi.single_eq_same]
  · push Not at h
    have hpos : 0 < localApprox {v} ∅ w α a β :=
      lt_of_le_of_ne (localApprox_nonneg _ _ _ _ a β) (h a).symm
    have hprod : ∏ b, localApprox {v} ∅ w α b β = localApprox {v} ∅ w α a β :=
      Fintype.prod_subsingleton _ a
    have hlt : localApprox {v} ∅ w α a β < 1 := by
      rw [← hprod]
      exact lt_of_le_of_lt hsol (Real.rpow_lt_one_of_one_lt_of_neg hH (by linarith))
    rw [Real.cellIndex_apply, Real.logProfile_apply, hprod,
      div_self (Real.log_neg hpos hlt).ne, mul_one, Nat.floor_natCast]

/-- **Conformance: Davenport and Roth's gap principle at one place**, with no class hypothesis:
two different solutions of height greater than `1` are always in one class. -/
example (v : InfinitePlace K) {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hw : (w v.1).LiesOver v.1) (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 < κ) {N : ℕ}
    (hN : 0 < N) {β β' : K}
    (hsol : min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult ≤ mulHeight₁ β ^ (-κ))
    (hsol' : min 1 (w v.1 (algebraMap K F β' - α v.1)) ^ v.mult ≤ mulHeight₁ β' ^ (-κ))
    (hH : 1 < mulHeight₁ β) (hH' : 1 < mulHeight₁ β') (hne : β ≠ β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β') :
    ((1 - (1 : ℝ) / N) * κ - 1) * absLogHeight₁ β - Real.log 4 ≤ absLogHeight₁ β' := by
  have hS : ∀ x : K, (∏ u ∈ ({v} : Finset (InfinitePlace K)),
      min 1 (w u.1 (algebraMap K F x - α u.1)) ^ u.mult) *
      ∏ u ∈ (∅ : Finset (FinitePlace K)), min 1 (w u.1 (algebraMap K F x - α u.1))
        = min 1 (w v.1 (algebraMap K F x - α v.1)) ^ v.mult := fun x ↦ by simp
  have h1 := mul_absLogHeight₁_sub_le_of_approxClass_eq (Sinf := {v}) (Sfin := ∅) (w := w) (α := α)
    (fun u hu ↦ by rwa [Finset.mem_singleton.mp hu]) (fun u hu ↦ absurd hu (Finset.notMem_empty u))
    hκ hN (β := β) (β' := β') ((hS β).trans_le hsol) ((hS β').trans_le hsol') hne ?_ hle
  · simpa using h1
  · have hs : ∀ x : K, min 1 (w v.1 (algebraMap K F x - α v.1)) ^ v.mult ≤ mulHeight₁ x ^ (-κ) →
        ∏ a, localApprox {v} ∅ w α a x ≤ mulHeight₁ x ^ (-κ) := fun x hx ↦ by
      rw [prod_localApprox, hS x]
      exact hx
    rw [approxClass_singleton_empty v hκ (hs β hsol) hH,
      approxClass_singleton_empty v hκ (hs β' hsol') hH']

/-- The places `∞` and `2` of `ℚ` are different. -/
private theorem finitePlace_val_ne_infinitePlace_val (p : Nat.Primes) :
    (Rat.finitePlace p).1 ≠ Rat.infinitePlace.1 := by
  rw [Rat.finitePlace_val]
  exact (Rat.infinitePlace_val_ne_padic _).symm

open scoped Classical in
/-- The targets `3` at `∞` and `5` at every finite place of `ℚ`. -/
private noncomputable def target35 : AbsoluteValue ℚ ℝ → ℚ :=
  fun v ↦ if v = Rat.infinitePlace.1 then 3 else 5

private theorem target35_inf : target35 Rat.infinitePlace.1 = 3 := by simp [target35]

private theorem target35_two : target35 (Rat.finitePlace ⟨2, Nat.prime_two⟩).1 = 5 := by
  have h := finitePlace_val_ne_infinitePlace_val ⟨2, Nat.prime_two⟩
  simp [target35, h]

/-- The absolute height of a positive integer, over `ℚ`. -/
private theorem absLogHeight₁_natCast_rat (n : ℕ) [NeZero n] :
    absLogHeight₁ (n : ℚ) = Real.log n := by
  rw [absLogHeight₁_eq_inv_mul_logHeight₁, Module.finrank_self, Rat.logHeight₁_natCast]
  simp

/-- `3` is a solution for every `κ`: it equals the target at `∞`. -/
private theorem sol_three (κ : ℝ) :
    (∏ v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)),
      min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1
        (algebraMap ℚ ℚ 3 - target35 v.1)) ^ v.mult) *
    ∏ v ∈ ({Rat.finitePlace ⟨2, Nat.prime_two⟩} : Finset (FinitePlace ℚ)),
      min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 3 - target35 v.1))
      ≤ mulHeight₁ (3 : ℚ) ^ (-κ) := by
  rw [Finset.prod_singleton, Finset.prod_singleton, id, target35_inf]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero, zero_lt_one,
    min_eq_right_of_lt, ne_eq, InfinitePlace.mult_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  positivity

/-- `5` is a solution for every `κ`: it equals the target at `2`. -/
private theorem sol_five (κ : ℝ) :
    (∏ v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)),
      min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1
        (algebraMap ℚ ℚ 5 - target35 v.1)) ^ v.mult) *
    ∏ v ∈ ({Rat.finitePlace ⟨2, Nat.prime_two⟩} : Finset (FinitePlace ℚ)),
      min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 5 - target35 v.1))
      ≤ mulHeight₁ (5 : ℚ) ^ (-κ) := by
  rw [Finset.prod_singleton, Finset.prod_singleton, id, id, target35_two]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero, zero_lt_one,
    min_eq_right_of_lt, mul_zero]
  positivity

/-- At `κ = 10` and `N = 4` the conclusion of the gap principle fails for `3` and `5`. -/
private theorem not_gap_three_five :
    ¬ (((1 - (((({Rat.infinitePlace} : Finset (InfinitePlace ℚ)).card
        + ({Rat.finitePlace ⟨2, Nat.prime_two⟩} : Finset (FinitePlace ℚ)).card) : ℕ) : ℝ)
          / (4 : ℕ)) * 10 - 1) * absLogHeight₁ (3 : ℚ) - Real.log 4
      ≤ absLogHeight₁ (5 : ℚ)) := by
  have h3 := absLogHeight₁_natCast_rat 3
  have h5 := absLogHeight₁_natCast_rat 5
  push_cast at h3 h5
  rw [h3, h5, Finset.card_singleton, Finset.card_singleton]
  push Not
  have h81 : 4 * Real.log 3 = Real.log 81 := by
    rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h20 : Real.log 4 + Real.log 5 = Real.log 20 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlt : Real.log 20 < Real.log 81 := Real.log_lt_log (by norm_num) (by norm_num)
  norm_num
  linarith

/-- **Rejection test: the class is load-bearing.** Over `ℚ` with `S = {∞, 2}`, targets `3` at `∞`
and `5` at `2`, both `3` and `5` are solutions for every `κ`, their heights `log 3` and `log 5` are
close, and at `κ = 10`, `N = 4` the conclusion of the gap principle fails for them. So the theorem
puts them in different classes — here the two corners — and without the class hypothesis it
would be false. -/
example : approxClass {Rat.infinitePlace} {Rat.finitePlace ⟨2, Nat.prime_two⟩}
      (id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) target35 4 3
    ≠ approxClass {Rat.infinitePlace} {Rat.finitePlace ⟨2, Nat.prime_two⟩}
      (id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) target35 4 5 := by
  intro hcl
  have hle : absLogHeight₁ (3 : ℚ) ≤ absLogHeight₁ (5 : ℚ) := by
    have h3 := absLogHeight₁_natCast_rat 3
    have h5 := absLogHeight₁_natCast_rat 5
    push_cast at h3 h5
    rw [h3, h5]
    exact Real.log_le_log (by norm_num) (by norm_num)
  refine not_gap_three_five (mul_absLogHeight₁_sub_le_of_approxClass_eq
    (fun v _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun v _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (by norm_num) (by norm_num) (sol_three 10) (sol_five 10) (by norm_num) hcl hle)

/-- **Rejection test: `β ≠ β'` is load-bearing.** The solution `3` is in its own class and its
height is at most its own, but `4 log 3 − log 4 > log 3`: a solution is not separated from
itself. -/
example : ¬ (((1 - (((({Rat.infinitePlace} : Finset (InfinitePlace ℚ)).card
        + ({Rat.finitePlace ⟨2, Nat.prime_two⟩} : Finset (FinitePlace ℚ)).card) : ℕ) : ℝ)
          / (4 : ℕ)) * 10 - 1) * absLogHeight₁ (3 : ℚ) - Real.log 4
      ≤ absLogHeight₁ (3 : ℚ)) := by
  have h3 := absLogHeight₁_natCast_rat 3
  push_cast at h3
  rw [h3, Finset.card_singleton, Finset.card_singleton]
  push Not
  have h27 : 3 * Real.log 3 = Real.log 27 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlt : Real.log 4 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
  norm_num
  linarith

end NumberField

end
