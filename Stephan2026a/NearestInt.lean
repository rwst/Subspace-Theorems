/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor

/-!
# The distance from a rational number to the nearest integer

The paper writes `‖x‖ = min_{n ∈ ℤ} |x - n|`. Every number it applies `‖·‖` to is rational, so
the development computes it in `ℚ`, as `|x - round x|`; `round` breaks ties upward, which does
not change the distance.

## Main definitions

* `Rat.distToNearestInt x`: `|x - round x|`.

## Main results

* `Rat.distToNearestInt_le_abs_sub_intCast`: `round x` is a nearest integer.
* `Rat.distToNearestInt_add_intCast`: invariance under integer translation.
* `Rat.one_le_two_pow_mul_distToNearestInt`: **the dyadic floor** — if `2 ^ m x` is an odd integer
  and `m ≥ 1`, then `‖x‖ ≥ 2 ^ (-m)`. This is the source of the trivial repulsion floor,
  Lemma 2.8 of the paper.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §1,
"Setup and notation".
-/

@[expose] public section

namespace Rat

/-- The distance from a rational number to the nearest integer, `‖x‖ = |x - round x|`. -/
def distToNearestInt (x : ℚ) : ℚ := |x - round x|

theorem distToNearestInt_nonneg (x : ℚ) : 0 ≤ x.distToNearestInt := abs_nonneg _

/-- `round x` is a nearest integer: the distance to any integer is at least `‖x‖`. -/
theorem distToNearestInt_le_abs_sub_intCast (x : ℚ) (n : ℤ) : x.distToNearestInt ≤ |x - n| :=
  round_le x n

theorem distToNearestInt_le_abs (x : ℚ) : x.distToNearestInt ≤ |x| := by
  simpa using distToNearestInt_le_abs_sub_intCast x 0

@[simp] theorem distToNearestInt_add_intCast (x : ℚ) (n : ℤ) :
    (x + n).distToNearestInt = x.distToNearestInt := by
  unfold distToNearestInt
  rw [round_add_intCast]
  congr 1
  push_cast
  ring

/-- **The dyadic floor.** If `2 ^ m x` is an odd integer `O` and `m ≥ 1`, then `x` keeps distance
at least `2 ^ (-m)` from the integers, in the integer-certificate form `1 ≤ 2 ^ m ‖x‖`. -/
theorem one_le_two_pow_mul_distToNearestInt {x : ℚ} {m : ℕ} (hm : 1 ≤ m) {O : ℤ}
    (hO : O % 2 = 1) (hOx : (O : ℚ) = 2 ^ m * x) : 1 ≤ 2 ^ m * x.distToNearestInt := by
  set N : ℤ := O - 2 ^ m * round x with hN
  have hNodd : N % 2 = 1 := by
    have h2 : ((2 : ℤ) ^ m * round x) % 2 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [show (2 : ℤ) ^ (j + 1) * round x = 2 * (2 ^ j * round x) by ring]
      exact Int.mul_emod_right 2 _
    omega
  have h1 : (1 : ℤ) ≤ |N| := Int.one_le_abs (by omega)
  have hcast : (N : ℚ) = 2 ^ m * (x - round x) := by
    rw [hN]
    push_cast
    rw [hOx]
    ring
  calc (1 : ℚ) ≤ |(N : ℚ)| := by exact_mod_cast h1
    _ = 2 ^ m * |x - round x| := by
        rw [hcast, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ m)]
    _ = 2 ^ m * x.distToNearestInt := rfl

end Rat
