/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

-- Used only inside proofs.
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Repetitions in an expansion to a real base: Lemma 1

**Lemma 1 of Adamczewski–Bugeaud 2007, §4, and the bound (3).** For a real `β > 1` and a bounded
sequence of integers `a`, let `α = ∑ k, a k / β ^ (k + 1)`. The digit polynomial
`P_n = ∑_{k < n} a k X ^ (n - 1 - k)` has `P_n (β) = β ^ n (a 0 / β + ⋯ + a (n - 1) / β ^ n)`, so
`β ^ n α - P_n (β)` is the tail of the expansion after `n` digits
(`Real.pow_mul_tsum_sub_aeval_digitPoly`). A repetition `U V ^ w` at the start of `a`, with
`r = |U|` and `s = |V|`, then puts `(β ^ (r + s) - β ^ r) α` within `≪ β ^ (-(⌈w s⌉ - s))` of
`P_(r + s) (β) - P_r (β)` (`Real.abs_sub_le_of_periodic`). This is the paper's
`α_n = P_n (β) / (β ^ r (β ^ s - 1))` with the denominator multiplied out. At a conjugate of
modulus at most `1` the digit polynomial is at most `M n` (`Complex.norm_aeval_digitPoly_le`).

## Main results

* `Polynomial.digitPoly`: the digit polynomial `∑_{k < n} a k X ^ (n - 1 - k)`.
* `Real.abs_tsum_div_pow_le`: a tail `∑ d j / β ^ (j + 1)` whose first `t` terms vanish is at most
  `D / ((β - 1) β ^ t)`.
* `Real.pow_mul_tsum_sub_aeval_digitPoly`: `β ^ n α - P_n (β)` is the tail after `n` digits.
* `Real.abs_sub_le_of_periodic`: **the approximation given by a repetition**.
* `Real.abs_aeval_digitPoly_le`: `|P_n (β)| ≤ β ^ n (|α| + M / (β - 1))`.
* `Complex.norm_aeval_digitPoly_le`: `‖P_n (z)‖ ≤ M n` for `‖z‖ ≤ 1`.
* `Complex.norm_aeval_digitPoly_le_of_lt_one`: `‖P_n (z)‖ ≤ M / (1 - ‖z‖)` for `‖z‖ < 1`.
* `Real.pow_mul_sum_div_pow`: `β ^ n (a 0 / β + ⋯ + a (n - 1) / β ^ n) = P_n (β)`.

## Implementation notes

⚠ **The digits are integers and may be negative**, as in Theorem 5 of the paper; the base-`b`
digits `Fin b` of `DiophantineApproximation` are the special case `β = b`, `0 ≤ a k < b`. The
bound `M` is on `|a k|`, so a difference of two digits is at most `2 M`.

⚠ **The digits are indexed from `0`**: `α = ∑ k, a k / β ^ (k + 1)` is the paper's
`∑_{k ≥ 1} a_k β ^ (-k)` with `a_k` renamed `a (k - 1)`, as for `Real.ofDigits`.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §4, Lemma 1.
-/

@[expose] public section

open Finset

namespace Polynomial

/-- **The digit polynomial** `∑_{k < n} a k X ^ (n - 1 - k)`. At `β` it is `β ^ n` times the value
`a 0 / β + ⋯ + a (n - 1) / β ^ n` of the first `n` digits. -/
noncomputable def digitPoly (a : ℕ → ℤ) (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range n, C (a k) * X ^ (n - 1 - k)

theorem aeval_digitPoly {R : Type*} [CommRing R] (a : ℕ → ℤ) (n : ℕ) (x : R) :
    aeval x (digitPoly a n) = ∑ k ∈ range n, (a k : R) * x ^ (n - 1 - k) := by
  simp [digitPoly]

end Polynomial

open Polynomial

namespace Complex

/-- **The digit polynomial at a point of the closed unit disc** is at most `M n`, for digits of
modulus at most `M`. This is the bound at the conjugates of a Pisot or Salem number. -/
theorem norm_aeval_digitPoly_le {a : ℕ → ℤ} {M : ℝ} (hM : ∀ k, |(a k : ℝ)| ≤ M) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (n : ℕ) : ‖aeval z (digitPoly a n)‖ ≤ M * n := by
  rw [aeval_digitPoly]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range n, ‖(a k : ℂ) * z ^ (n - 1 - k)‖ ≤ ∑ _k ∈ range n, M :=
        sum_le_sum fun k _ ↦ by
          rw [norm_mul, norm_pow, norm_intCast]
          exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans
            (hM k)
    _ = M * n := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

/-- **The digit polynomial at a point of the open unit disc** is at most `M / (1 - ‖z‖)`, uniformly
in `n`. This is the bound at the conjugates of a Pisot number. -/
theorem norm_aeval_digitPoly_le_of_lt_one {a : ℕ → ℤ} {M : ℝ} (hM : ∀ k, |(a k : ℝ)| ≤ M)
    {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) : ‖aeval z (digitPoly a n)‖ ≤ M / (1 - ‖z‖) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hg := summable_geometric_of_lt_one (norm_nonneg z) hz
  rw [aeval_digitPoly]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range n, ‖(a k : ℂ) * z ^ (n - 1 - k)‖
      ≤ ∑ k ∈ range n, M * ‖z‖ ^ (n - 1 - k) := sum_le_sum fun k _ ↦ by
        rw [norm_mul, norm_pow, norm_intCast]
        exact mul_le_mul_of_nonneg_right (hM k) (pow_nonneg (norm_nonneg _) _)
    _ = M * ∑ j ∈ range n, ‖z‖ ^ j := by
        rw [← mul_sum, ← sum_range_reflect]
        refine congrArg _ (sum_congr rfl fun j hj ↦ ?_)
        have := mem_range.mp hj
        rw [show n - 1 - (n - 1 - j) = j by omega]
    _ ≤ M * ∑' j, ‖z‖ ^ j :=
        mul_le_mul_of_nonneg_left (hg.sum_le_tsum _ fun j _ ↦ pow_nonneg (norm_nonneg _) _) hM0
    _ = M / (1 - ‖z‖) := by rw [tsum_geometric_of_lt_one (norm_nonneg z) hz, div_eq_mul_inv]

end Complex

namespace Real

variable {β : ℝ}

/-- An expansion `∑ d j / β ^ (j + 1)` with bounded coefficients converges for `β > 1`. -/
theorem summable_div_pow (hβ : 1 < β) {d : ℕ → ℝ} {D : ℝ} (hd : ∀ j, |d j| ≤ D) :
    Summable fun j ↦ d j / β ^ (j + 1) := by
  have hβ0 : 0 < β := by linarith
  have hq : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ0.le
  have hq1 : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq hq1).mul_left (D * β⁻¹)) fun j ↦ ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hβ0 _), div_eq_mul_inv, ← inv_pow,
    pow_succ, ← mul_assoc, mul_right_comm D]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hd j) (by positivity)) hq

/-- **A tail of an expansion.** If the first `t` coefficients of `∑ d j / β ^ (j + 1)` vanish and
all are at most `D`, the sum is at most `D / ((β - 1) β ^ t)`. -/
theorem abs_tsum_div_pow_le (hβ : 1 < β) {d : ℕ → ℝ} {D : ℝ} (hd : ∀ j, |d j| ≤ D) {t : ℕ}
    (h0 : ∀ j < t, d j = 0) :
    |∑' j, d j / β ^ (j + 1)| ≤ D / ((β - 1) * β ^ t) := by
  have hβ0 : 0 < β := by linarith
  have hq : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ0.le
  have hq1 : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  rw [← (summable_div_pow hβ hd).sum_add_tsum_nat_add t,
    sum_eq_zero fun j hj ↦ by rw [h0 j (mem_range.mp hj), zero_div], zero_add]
  have hg := (hasSum_geometric_of_lt_one hq hq1).mul_left (D * β⁻¹ ^ (t + 1))
  rw [← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded (f := fun j ↦ d (j + t) / β ^ (j + t + 1)) hg
    fun j ↦ ?_).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hβ0 _), div_eq_mul_inv, ← inv_pow,
      mul_assoc, ← pow_add, show t + 1 + j = j + t + 1 by ring]
    exact mul_le_mul_of_nonneg_right (hd _) (by positivity)
  · have hβ1 : β - 1 ≠ 0 := by linarith
    simp only [inv_pow]
    field_simp
    ring

/-- **The first `n` digits, multiplied out**:
`β ^ n (a 0 / β + ⋯ + a (n - 1) / β ^ n) = P_n (β)`. -/
theorem pow_mul_sum_div_pow (hβ : β ≠ 0) (a : ℕ → ℤ) (n : ℕ) :
    β ^ n * ∑ k ∈ range n, (a k : ℝ) / β ^ (k + 1) = aeval β (digitPoly a n) := by
  rw [aeval_digitPoly, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk := mem_range.mp hk
  rw [show β ^ n = β ^ (n - 1 - k) * β ^ (k + 1) by rw [← pow_add]; congr 1; omega]
  field_simp

/-- **The tail after `n` digits.** `β ^ n α - P_n (β)` is the expansion `∑ a (j + n) / β ^ (j + 1)`
of the digits from position `n` on. -/
theorem pow_mul_tsum_sub_aeval_digitPoly (hβ : 1 < β) {a : ℕ → ℤ} {M : ℝ}
    (hM : ∀ k, |(a k : ℝ)| ≤ M) (n : ℕ) :
    β ^ n * ∑' k, (a k : ℝ) / β ^ (k + 1) - aeval β (digitPoly a n)
      = ∑' j, (a (j + n) : ℝ) / β ^ (j + 1) := by
  have hβ0 : β ≠ 0 := by linarith
  rw [← (summable_div_pow hβ hM).sum_add_tsum_nat_add n, mul_add, pow_mul_sum_div_pow hβ0,
    add_sub_cancel_left, ← tsum_mul_left]
  refine tsum_congr fun j ↦ ?_
  rw [show j + n + 1 = n + (j + 1) by ring, pow_add]
  field_simp

/-- **The approximation given by a repetition** (Adamczewski–Bugeaud 2007, (3)). A period `s` of
the digits on `[r, r + ⌈w s⌉)` puts `(β ^ (r + s) - β ^ r) α` within `2 M / ((β - 1) β ^ t)` of
`P_(r + s) (β) - P_r (β)`, with `t = ⌈w s⌉ - s`. -/
theorem abs_sub_le_of_periodic (hβ : 1 < β) {a : ℕ → ℤ} {M : ℝ} (hM : ∀ k, |(a k : ℝ)| ≤ M)
    {w : ℝ} {r s : ℕ} (h : ∀ i, r ≤ i → i + s < r + ⌈w * s⌉₊ → a (i + s) = a i) :
    |(β ^ (r + s) - β ^ r) * ∑' k, (a k : ℝ) / β ^ (k + 1)
        - (aeval β (digitPoly a (r + s)) - aeval β (digitPoly a r))|
      ≤ 2 * M / ((β - 1) * β ^ (⌈w * s⌉₊ - s)) := by
  have e1 := pow_mul_tsum_sub_aeval_digitPoly hβ hM (r + s)
  have e2 := pow_mul_tsum_sub_aeval_digitPoly hβ hM r
  have hs1 := summable_div_pow hβ (d := fun j ↦ (a (j + (r + s)) : ℝ)) fun j ↦ hM _
  have hs2 := summable_div_pow hβ (d := fun j ↦ (a (j + r) : ℝ)) fun j ↦ hM _
  have hdiff : (β ^ (r + s) - β ^ r) * ∑' k, (a k : ℝ) / β ^ (k + 1)
        - (aeval β (digitPoly a (r + s)) - aeval β (digitPoly a r))
      = ∑' j, ((a (j + (r + s)) : ℝ) - a (j + r)) / β ^ (j + 1) := by
    simp only [sub_div]
    rw [hs1.tsum_sub hs2]
    linear_combination e1 - e2
  rw [hdiff]
  refine abs_tsum_div_pow_le hβ (fun j ↦ ?_) fun j hj ↦ ?_
  · refine (abs_sub _ _).trans ?_
    linarith [hM (j + (r + s)), hM (j + r)]
  · rw [show j + (r + s) = j + r + s by ring, h (j + r) (by omega) (by omega), sub_self]

/-- **The size of the digit polynomial at `β`**: `|P_n (β)| ≤ β ^ n (|α| + M / (β - 1))`. -/
theorem abs_aeval_digitPoly_le (hβ : 1 < β) {a : ℕ → ℤ} {M : ℝ} (hM : ∀ k, |(a k : ℝ)| ≤ M)
    (n : ℕ) :
    |aeval β (digitPoly a n)|
      ≤ β ^ n * (|∑' k, (a k : ℝ) / β ^ (k + 1)| + M / (β - 1)) := by
  have e := pow_mul_tsum_sub_aeval_digitPoly hβ hM n
  have ht := abs_tsum_div_pow_le hβ (d := fun j ↦ (a (j + n) : ℝ)) (fun j ↦ hM _)
    (t := 0) fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  rw [pow_zero, mul_one] at ht
  have hp : 1 ≤ β ^ n := one_le_pow₀ hβ.le
  have hM0 : 0 ≤ M / (β - 1) := div_nonneg ((abs_nonneg _).trans (hM 0)) (by linarith)
  have hP : aeval β (digitPoly a n)
      = β ^ n * ∑' k, (a k : ℝ) / β ^ (k + 1) - ∑' j, (a (j + n) : ℝ) / β ^ (j + 1) := by
    linear_combination -e
  rw [hP]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith), mul_add]
  nlinarith

end Real
