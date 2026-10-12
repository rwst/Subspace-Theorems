/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The `β`-expansion of a real number

For a real `β > 1`, Rényi's **`β`-transformation** is `T x = {β x}` on `[0, 1)`, and the
**`β`-digits** of `x ∈ [0, 1)` are `d k = ⌊β T^k x⌋`, the greedy digits. They satisfy
`0 ≤ d k < β` and `x = ∑ k, d k / β ^ (k + 1)`. For an integer `β = b` this is the base-`b`
expansion. Mathlib has the integer case (`Real.digits`, `Real.ofDigits`) but not this one.

## Main definitions

* `Real.betaTransform β x`: `{β x}`.
* `Real.betaDigits β x k`: `⌊β T^k x⌋₊`, the `k`-th digit (indexed from `0`).

## Main results

* `Real.iterate_betaTransform_mem_Ico`: the orbit of `x ∈ [0, 1)` stays in `[0, 1)`.
* `Real.betaDigits_lt`, `Real.betaDigits_le_floor`: the digits lie in `{0, …, ⌊β⌋}` and are
  `< β`.
* `Real.eq_sum_betaDigits_add`: `x = ∑_{k < n} d k / β ^ (k + 1) + T^n x / β ^ n`.
* `Real.hasSum_betaDigits`: the `β`-expansion converges to `x`.

## Implementation notes

⚠ **The digits are those of `x`, not of its fractional part.** Outside `[0, 1)` the definition
still makes sense but the digit bounds and the expansion do not hold; the statements take
`x ∈ Set.Ico 0 1`.

## References

A. Rényi, *Representations for real numbers and their ergodic properties*, Acta Math. Acad. Sci.
Hungar. **8** (1957), 477–493, §4. Adapted from `Tbeta` and `rem_phiBeta_eq_iterate` in
`RenyiBeta.lean` of the author's `Course` project, where the expansion comes out of Rényi's
general `f`-expansions; here it is proved directly.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {β x : ℝ}

/-- Rényi's **`β`-transformation** `x ↦ {β x}`. -/
noncomputable def betaTransform (β x : ℝ) : ℝ := Int.fract (β * x)

/-- The **`β`-digits** of `x`: the `k`-th one is `⌊β T^k x⌋₊`, with `T` the `β`-transformation. -/
noncomputable def betaDigits (β x : ℝ) (k : ℕ) : ℕ := ⌊β * (betaTransform β)^[k] x⌋₊

theorem betaTransform_mem_Ico (β x : ℝ) : betaTransform β x ∈ Set.Ico 0 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The orbit of a point of `[0, 1)` stays in `[0, 1)`. -/
theorem iterate_betaTransform_mem_Ico (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    (betaTransform β)^[k] x ∈ Set.Ico 0 1 := by
  cases k with
  | zero => exact hx
  | succ k => rw [Function.iterate_succ_apply']; exact betaTransform_mem_Ico _ _

/-- One step of the expansion: `β y = d + T y` for `y ≥ 0` and `β ≥ 0`, with `d = ⌊β y⌋₊`. -/
theorem mul_eq_floor_add_betaTransform (hβ : 0 ≤ β) {y : ℝ} (hy : 0 ≤ y) :
    β * y = ⌊β * y⌋₊ + betaTransform β y := by
  rw [betaTransform, natCast_floor_eq_intCast_floor (mul_nonneg hβ hy), Int.floor_add_fract]

/-- The digits are `< β`. -/
theorem betaDigits_lt (hβ : 0 < β) (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    (betaDigits β x k : ℝ) < β := by
  have hy := iterate_betaTransform_mem_Ico (β := β) hx k
  calc (betaDigits β x k : ℝ) ≤ β * (betaTransform β)^[k] x :=
        Nat.floor_le (mul_nonneg hβ.le hy.1)
    _ < β := by nlinarith [hy.2]

/-- The digits lie in `{0, …, ⌊β⌋}`. -/
theorem betaDigits_le_floor (hβ : 0 < β) (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    betaDigits β x k ≤ ⌊β⌋₊ :=
  Nat.le_floor (betaDigits_lt hβ hx k).le

/-- **The expansion with remainder**: `x = ∑_{k < n} d k / β ^ (k + 1) + T^n x / β ^ n`. -/
theorem eq_sum_betaDigits_add (hβ : 0 < β) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    x = ∑ k ∈ Finset.range n, (betaDigits β x k : ℝ) / β ^ (k + 1) +
      (betaTransform β)^[n] x / β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep :=
      mul_eq_floor_add_betaTransform hβ.le (iterate_betaTransform_mem_Ico (β := β) hx n).1
    rw [← Function.iterate_succ_apply' (betaTransform β)] at hstep
    have key : (betaTransform β)^[n] x / β ^ n = (betaDigits β x n : ℝ) / β ^ (n + 1) +
        (betaTransform β)^[n + 1] x / β ^ (n + 1) := by
      rw [← add_div, betaDigits, ← hstep, pow_succ]
      field_simp
    rw [Finset.sum_range_succ, add_assoc, ← key]
    exact ih

/-- **The `β`-expansion converges to `x`**: `∑ k, d k / β ^ (k + 1) = x` for `x ∈ [0, 1)`. -/
theorem hasSum_betaDigits (hβ : 1 < β) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    HasSum (fun k ↦ (betaDigits β x k : ℝ) / β ^ (k + 1)) x := by
  have hβ0 : 0 < β := one_pos.trans hβ
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ by positivity) x).mpr ?_
  -- the remainder `T^n x / β ^ n` lies in `[0, β⁻¹ ^ n)`
  have hrem : Tendsto (fun n ↦ (betaTransform β)^[n] x / β ^ n) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ ↦ (β⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hβ)
    refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hg
    · exact div_nonneg (iterate_betaTransform_mem_Ico hx n).1 (by positivity)
    · rw [inv_pow, div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (iterate_betaTransform_mem_Ico hx n).2.le
  have h := (tendsto_const_nhds (x := x)).sub hrem
  rw [sub_zero] at h
  refine h.congr fun n ↦ ?_
  rw [sub_eq_iff_eq_add, ← eq_sum_betaDigits_add hβ0 hx n]

end Real
