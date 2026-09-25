/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.StammeringWords
public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.NumberTheory.Real.Irrational

-- Used only inside proofs.
import Mathlib.Tactic.LinearCombination

/-!
# Expansions in an integer base

**Layer 7.4, the numbers.** For `a : ℕ → Fin b` the number `ξ = ∑ k, a k / b ^ (k + 1)` is
Mathlib's `Real.ofDigits a`. This file records the two facts about `ξ` that the transcendence
criteria need: the approximation of `ξ` by rationals with denominator `b ^ r (b ^ s - 1)` that a
repetition in the digits provides, and the irrationality of `ξ` when the digits are not eventually
periodic.

## Main definitions

* `Real.digitsPrefix a n`: the natural number whose base-`b` digits are `a 0, …, a (n - 1)`.

## Main results

* `Real.pow_mul_ofDigits`: `b ^ n ξ` is the number formed by the first `n` digits plus the tail.
* `Real.mul_ofDigits_shift`: `b` times the `k`-th tail is `a k` plus the `(k + 1)`-st tail.
* `Real.abs_mul_ofDigits_sub_le`: **the approximation by a repetition** — if the `t` digits after
  position `r + s` repeat those after position `r`, then
  `|(b ^ (r + s) - b ^ r) ξ - p| ≤ b ^ (-t)` for an explicit integer `p`.
* `Real.digitsPrefix_sub_mem`: that integer lies in `[0, b ^ r (b ^ s - 1)]`.
* `Real.irrational_ofDigits`: **a sequence of digits that is not eventually periodic has an
  irrational value**.

## Implementation notes

⚠ **The approximant is never written as a number.** The classical proof compares `ξ` with the
rational whose expansion is `U V V V ⋯`. Here the comparison is made directly on the linear form
`(b ^ (r + s) - b ^ r) ξ - p`: by `pow_mul_ofDigits` it is the difference of the tails of `a` at
positions `r + s` and `r`, and Mathlib's `Real.abs_ofDigits_sub_ofDigits_le` bounds it by
`b ^ (-t)` as soon as they share `t` digits. The periodic word and its value never appear, and
neither does the question of whether `p / (b ^ r (b ^ s - 1))` is in lowest terms.

⚠ **Irrationality needs no uniqueness of expansions.** A rational number can have two base-`b`
expansions, so "the expansion of a rational is eventually periodic" is not directly a statement
about an arbitrary `a` with that value. The proof here works with the tails `T k` of `a` itself:
`b T k = a k + T (k + 1)` with `0 ≤ T k ≤ 1`. A tail equal to `0` or to `1` forces all later
digits to be `0` or `b - 1`; otherwise every tail lies in `(0, 1)`, so `a k = ⌊b T k⌋` and
`T (k + 1)` is the fractional part of `b T k`, both functions of `T k`. For rational `ξ` the tails
have a common denominator and take finitely many values, so two of them agree and the digits
repeat from there.

This is part of Layer 7.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace Real

variable {b : ℕ}

/-- The natural number whose base-`b` digits are the first `n` digits of `a`, most significant
first: `a 0 * b ^ (n - 1) + ⋯ + a (n - 1)`. -/
def digitsPrefix (a : ℕ → Fin b) : ℕ → ℕ
  | 0 => 0
  | n + 1 => b * digitsPrefix a n + a n

@[simp] theorem digitsPrefix_zero (a : ℕ → Fin b) : digitsPrefix a 0 = 0 := rfl

theorem digitsPrefix_succ (a : ℕ → Fin b) (n : ℕ) :
    digitsPrefix a (n + 1) = b * digitsPrefix a n + a n := rfl

/-- The first `n` digits make a number below `b ^ n`. -/
theorem digitsPrefix_lt (a : ℕ → Fin b) (n : ℕ) : digitsPrefix a n < b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [digitsPrefix_succ, pow_succ]
    have ha : ((a n : ℕ)) < b := (a n).2
    nlinarith

/-- **Concatenation**: the first `m + n` digits are the first `m`, shifted by `n` places, followed
by the next `n`. -/
theorem digitsPrefix_add (a : ℕ → Fin b) (m n : ℕ) :
    digitsPrefix a (m + n) = b ^ n * digitsPrefix a m + digitsPrefix (fun i ↦ a (i + m)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, digitsPrefix_succ, ih, digitsPrefix_succ, pow_succ, add_comm m n]
    ring

/-- **Shifting by `n` places splits off an integer**: `b ^ n ξ` is the number formed by the first
`n` digits plus the tail `0.a n a (n + 1) …`. -/
theorem pow_mul_ofDigits (a : ℕ → Fin b) (n : ℕ) :
    (b : ℝ) ^ n * ofDigits a = digitsPrefix a n + ofDigits (fun i ↦ a (i + n)) := by
  have hb : (b : ℝ) ≠ 0 := by
    have : 0 < b := Fin.pos (a 0)
    positivity
  have hsum : ∀ n, (b : ℝ) ^ n * ∑ i ∈ Finset.range n, ofDigitsTerm a i = digitsPrefix a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ, mul_comm ((b : ℝ) ^ n) b, mul_assoc, ih,
        digitsPrefix_succ, ofDigitsTerm]
      push_cast
      field_simp
      ring
  rw [ofDigits_eq_sum_add_ofDigits a n, mul_add, hsum, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n hb), one_mul]

/-- **One digit at a time**: `b` times the `k`-th tail is the `k`-th digit plus the next tail. -/
theorem mul_ofDigits_shift (a : ℕ → Fin b) (k : ℕ) :
    (b : ℝ) * ofDigits (fun i ↦ a (i + k)) = a k + ofDigits (fun i ↦ a (i + (k + 1))) := by
  have h := pow_mul_ofDigits (fun i ↦ a (i + k)) 1
  simp only [pow_one, digitsPrefix_succ, digitsPrefix_zero, mul_zero, zero_add, zero_add] at h
  rw [h]
  congr 2
  funext i
  congr 1
  omega

/-- **A base-`b` expansion that is not eventually periodic has an irrational value.** Nothing is
assumed about the uniqueness of the expansion. -/
theorem irrational_ofDigits {a : ℕ → Fin b} (ha : ¬ Function.IsEventuallyPeriodic a) :
    Irrational (ofDigits a) := by
  set T : ℕ → ℝ := fun k ↦ ofDigits (fun i ↦ a (i + k)) with hT
  have hrec : ∀ k, (b : ℝ) * T k = a k + T (k + 1) := mul_ofDigits_shift a
  have hT0 : ∀ k, 0 ≤ T k := fun k ↦ ofDigits_nonneg _
  have hT1 : ∀ k, T k ≤ 1 := fun k ↦ ofDigits_le_one _
  have hab : ∀ k, ((a k : ℕ) : ℝ) + 1 ≤ b := fun k ↦ by
    have := (a k).2
    exact_mod_cast this
  -- a tail equal to `0` or `1` forces a constant tail of digits
  have hzero : ∀ k, T k = 0 → ∀ t, (a (k + t) : ℕ) = 0 ∧ T (k + t) = 0 := by
    intro k hk t
    induction t with
    | zero =>
      refine ⟨?_, hk⟩
      have h := hrec k
      rw [hk, mul_zero] at h
      have := hT0 (k + 1)
      have h' : ((a k : ℕ) : ℝ) = 0 := by linarith [(Nat.cast_nonneg (a k : ℕ) : (0 : ℝ) ≤ _)]
      exact_mod_cast h'
    | succ t ih =>
      have h := hrec (k + t)
      rw [ih.2, mul_zero] at h
      have h0 := hT0 (k + t + 1)
      have h1 : ((a (k + t) : ℕ) : ℝ) ≥ 0 := Nat.cast_nonneg _
      have hT' : T (k + (t + 1)) = 0 := by rw [← add_assoc]; linarith
      refine ⟨?_, hT'⟩
      have h2 := hrec (k + (t + 1))
      rw [hT', mul_zero] at h2
      have := hT0 (k + (t + 1) + 1)
      have h' : ((a (k + (t + 1)) : ℕ) : ℝ) = 0 := by
        linarith [(Nat.cast_nonneg (a (k + (t + 1)) : ℕ) : (0 : ℝ) ≤ _)]
      exact_mod_cast h'
  have hone : ∀ k, T k = 1 → ∀ t, (a (k + t) : ℕ) + 1 = b ∧ T (k + t) = 1 := by
    intro k hk t
    induction t with
    | zero =>
      refine ⟨?_, hk⟩
      have h := hrec k
      rw [hk, mul_one] at h
      have h' : ((a k : ℕ) : ℝ) + 1 = b := by linarith [hT1 (k + 1), hab k]
      exact_mod_cast h'
    | succ t ih =>
      have h := hrec (k + t)
      rw [ih.2, mul_one] at h
      have hT' : T (k + (t + 1)) = 1 := by
        rw [← add_assoc]; linarith [hT1 (k + t + 1), hab (k + t)]
      refine ⟨?_, hT'⟩
      have h2 := hrec (k + (t + 1))
      rw [hT', mul_one] at h2
      have h' : ((a (k + (t + 1)) : ℕ) : ℝ) + 1 = b := by
        linarith [hT1 (k + (t + 1) + 1), hab (k + (t + 1))]
      exact_mod_cast h'
  rintro ⟨q, hq⟩
  by_cases h0 : ∃ k, T k = 0
  · obtain ⟨k, hk⟩ := h0
    refine ha ⟨k, 1, one_pos, fun n hn ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact Fin.ext ((hzero k hk (t + 1)).1.trans (hzero k hk t).1.symm)
  by_cases h1 : ∃ k, T k = 1
  · obtain ⟨k, hk⟩ := h1
    refine ha ⟨k, 1, one_pos, fun n hn ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e1 := (hone k hk (t + 1)).1
    rw [← add_assoc] at e1
    have e2 := (hone k hk t).1
    exact Fin.ext (by omega)
  push Not at h0 h1
  have hpos : ∀ k, 0 < T k := fun k ↦ lt_of_le_of_ne (hT0 k) (h0 k).symm
  have hlt : ∀ k, T k < 1 := fun k ↦ lt_of_le_of_ne (hT1 k) (h1 k)
  have hfloor : ∀ k, ⌊(b : ℝ) * T k⌋₊ = (a k : ℕ) := fun k ↦ by
    rw [hrec, Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg _) (hT0 _))]
    constructor <;> linarith [hpos (k + 1), hlt (k + 1)]
  have hnext : ∀ k, T (k + 1) = (b : ℝ) * T k - ⌊(b : ℝ) * T k⌋₊ := fun k ↦ by
    rw [hfloor, hrec]; ring
  -- the tails are rationals with denominator `q.den`, so they take finitely many values
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  set J : ℕ → ℤ := fun k ↦ (b : ℤ) ^ k * q.num - q.den * (digitsPrefix a k : ℤ) with hJ
  have hJT : ∀ k, (J k : ℝ) = q.den * T k := fun k ↦ by
    have h := pow_mul_ofDigits a k
    rw [← hq] at h
    have hqd : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    simp only [hJ, hT]
    push_cast
    rw [← hqd]
    linear_combination (q.den : ℝ) * h
  have hJmem : ∀ k, J k ∈ Finset.Icc (0 : ℤ) q.den := fun k ↦ by
    rw [Finset.mem_Icc]
    constructor
    · have : (0 : ℝ) ≤ J k := by rw [hJT]; exact mul_nonneg hden.le (hT0 k)
      exact_mod_cast this
    · have : (J k : ℝ) ≤ q.den := by
        rw [hJT]; nlinarith [hT1 k]
      exact_mod_cast this
  have key : ∀ i j, i < j → T i = T j → False := by
    intro i j hij hTij
    have hshift : ∀ t, T (i + t) = T (j + t) := by
      intro t
      induction t with
      | zero => simpa using hTij
      | succ t ih => rw [← add_assoc, ← add_assoc, hnext, hnext, ih]
    refine ha ⟨i, j - i, by omega, fun n hn ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e := hfloor (i + t)
    rw [hshift t, show j + t = i + t + (j - i) by omega, hfloor] at e
    exact Fin.ext e
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k ↦ (⟨J k, hJmem k⟩ : Finset.Icc (0 : ℤ) q.den))
  have hTeq : T i = T j := by
    have h := congrArg (fun x : Finset.Icc (0 : ℤ) q.den ↦ ((x : ℤ) : ℝ)) hij
    simp only [hJT] at h
    exact mul_left_cancel₀ hden.ne' h
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key i j h hTeq
  · exact key j i h hTeq.symm

/-- **The approximation by a repetition.** If the `t` digits after position `r + s` repeat those
after position `r`, then `(b ^ (r + s) - b ^ r) ξ` is within `b ^ (-t)` of an integer. -/
theorem abs_mul_ofDigits_sub_le (a : ℕ → Fin b) {r s t : ℕ}
    (h : ∀ i < t, a (i + (r + s)) = a (i + r)) :
    |((b : ℝ) ^ (r + s) - b ^ r) * ofDigits a
        - ((digitsPrefix a (r + s) : ℝ) - digitsPrefix a r)| ≤ ((b : ℝ) ^ t)⁻¹ := by
  have h1 := pow_mul_ofDigits a (r + s)
  have h2 := pow_mul_ofDigits a r
  have h3 := abs_ofDigits_sub_ofDigits_le (x := fun i ↦ a (i + (r + s))) (y := fun i ↦ a (i + r)) h
  convert h3 using 2
  linear_combination h1 - h2

/-- The integer of the approximation lies between `0` and `b ^ r (b ^ s - 1)`: the rational
number it defines lies in `[0, 1]`. -/
theorem digitsPrefix_sub_mem (a : ℕ → Fin b) (r s : ℕ) :
    0 ≤ (digitsPrefix a (r + s) : ℤ) - digitsPrefix a r ∧
      (digitsPrefix a (r + s) : ℤ) - digitsPrefix a r ≤ (b : ℤ) ^ r * ((b : ℤ) ^ s - 1) := by
  have h := digitsPrefix_add a r s
  have h1 := digitsPrefix_lt a r
  have h2 := digitsPrefix_lt (fun i ↦ a (i + r)) s
  have hb : 1 ≤ b ^ s := Nat.one_le_pow _ _ (Fin.pos (a 0))
  zify at h h1 h2 hb
  rw [h]
  constructor <;> nlinarith

end Real

/-! ### Acceptance criteria -/

/-- **Conformance: the first digits make the expected number**, most significant first. -/
example : Real.digitsPrefix (fun n : ℕ ↦ (if n = 0 then 4 else 2 : Fin 10)) 3 = 422 := rfl

/-- **Rejection: an eventually periodic expansion can have a rational value**, so the hypothesis
of `Real.irrational_ofDigits` is not decoration: `0.000… = 0`. -/
example : ¬ Irrational (Real.ofDigits fun _ : ℕ ↦ (0 : Fin 10)) := by
  have h0 : Real.ofDigits (fun _ : ℕ ↦ (0 : Fin 10)) = 0 := by
    simp [Real.ofDigits, Real.ofDigitsTerm]
  rw [h0]
  exact fun h ↦ h ⟨0, by simp⟩

