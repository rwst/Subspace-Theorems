/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rational enclosures of `log (1 + 1 / a)`

Mathlib has the series `log (1 + a⁻¹) = 2 ∑ₖ (2k + 1)⁻¹ y ^ (2k + 1)`, `y = 1 / (2a + 1)`
(`Real.hasSum_log_one_add_inv`, the series of `2 artanh y`), and decimal bounds for `log 2` and
`log 3`. This file turns the series into two-sided bounds by its partial sums, so that the
logarithm of any rational `> 1` has rational enclosures that `norm_num` checks: the `N`-th partial
sum from below, and the same plus `2 y ^ (2N + 1) / ((2N + 1)(1 - y²))` from above.

## Main results

* `Real.sum_range_le_log_one_add_inv`, `Real.log_one_add_inv_le_sum_range_add`: the partial sums
  of the series enclose `log (1 + a⁻¹)`.
* `Real.two_mul_div_two_add_le_log_one_add`: `2x / (2 + x) ≤ log (1 + x)` for `x ≥ 0`, the first
  term.
* `Real.log_one_add_le_mul_two_add_div`: `log (1 + x) ≤ x (2 + x) / (2 (1 + x))` for `x ≥ 0`, the
  first upper bound; both are sharper than `x / (1 + x) ≤ log (1 + x) ≤ x`.
-/

@[expose] public section

open Finset

namespace Real

/-- The partial sums of the series of `log (1 + a⁻¹)` are lower bounds. -/
theorem sum_range_le_log_one_add_inv {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ k ∈ range N, 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
      log (1 + a⁻¹) :=
  sum_le_hasSum _ (fun _ _ ↦ by positivity) (hasSum_log_one_add_inv ha)

/-- The partial sums of the series of `log (1 + a⁻¹)` plus the geometric bound of the tail,
`2 y ^ (2N + 1) / ((2N + 1)(1 - y²))` for `y = 1 / (2a + 1)`, are upper bounds. -/
theorem log_one_add_inv_le_sum_range_add {a : ℝ} (ha : 0 < a) (N : ℕ) :
    log (1 + a⁻¹) ≤
      ∑ k ∈ range N, 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) +
        2 * (1 / (2 * a + 1)) ^ (2 * N + 1) / ((2 * N + 1) * (1 - (1 / (2 * a + 1)) ^ 2)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := pow_lt_one₀ hy0 hy1 two_ne_zero
  set f : ℕ → ℝ := fun k ↦ 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) with hf
  have hs : HasSum f (log (1 + a⁻¹)) := hasSum_log_one_add_inv ha
  -- the tail from `N` on
  have htail : HasSum (fun k ↦ f (k + N)) (log (1 + a⁻¹) - ∑ k ∈ range N, f k) :=
    (hasSum_nat_add_iff' N).2 hs
  -- the geometric majorant
  set c : ℝ := 2 / (2 * N + 1) * y ^ (2 * N + 1) with hc
  have hg : HasSum (fun k : ℕ ↦ c * (y ^ 2) ^ k) (c * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left c
  have hle : ∀ k, f (k + N) ≤ c * (y ^ 2) ^ k := by
    intro k
    have hpow : y ^ (2 * (k + N) + 1) = y ^ (2 * N + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have hd : 1 / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
      gcongr
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hf, hc, hpow]
    have h0 : 0 ≤ y ^ (2 * N + 1) * (y ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (y ^ (2 * N + 1) * (y ^ 2) ^ k)
        ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (y ^ (2 * N + 1) * (y ^ 2) ^ k) := by gcongr
      _ = _ := by ring
  have := hasSum_le hle htail hg
  have hfin : c * (1 - y ^ 2)⁻¹ =
      2 * y ^ (2 * N + 1) / ((2 * N + 1) * (1 - y ^ 2)) := by
    rw [hc]
    have : (1 : ℝ) - y ^ 2 ≠ 0 := by linarith
    field_simp
  rw [hfin] at this
  linarith

/-- `2x / (2 + x) ≤ log (1 + x)` for `x ≥ 0`: the first term of the series of
`2 artanh (x / (2 + x))`. -/
theorem two_mul_div_two_add_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ log (1 + x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have h := sum_range_le_log_one_add_inv (inv_pos.2 hx) 1
  rw [inv_inv] at h
  refine le_of_eq_of_le ?_ h
  simp only [range_one, sum_singleton, CharP.cast_eq_zero, mul_zero, zero_add, div_one,
    mul_one, pow_one]
  field_simp

/-- `log (1 + x) ≤ x (2 + x) / (2 (1 + x))` for `x ≥ 0`: the series of `log (1 + x)` bounded by
the geometric one, `2y / (1 - y²)` for `y = x / (2 + x)`. -/
theorem log_one_add_le_mul_two_add_div {x : ℝ} (hx : 0 ≤ x) :
    log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have h := log_one_add_inv_le_sum_range_add (inv_pos.2 hx) 0
  rw [inv_inv] at h
  refine h.trans_eq ?_
  have hy : 1 / (2 * x⁻¹ + 1) = x / (2 + x) := by field_simp
  simp only [range_zero, sum_empty, CharP.cast_eq_zero, mul_zero, zero_add, pow_one, one_mul, hy]
  have h4 : (2 + x) ^ 2 - x ^ 2 = 2 ^ 2 * (1 + x) := by ring
  field_simp
  rw [h4, div_self (by positivity)]

end Real
