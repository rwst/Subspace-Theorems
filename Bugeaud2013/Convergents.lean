/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.Real.Sqrt

-- Used only inside proofs.
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The convergents of a continued fraction `[0; a₁, a₂, …]` (Bugeaud 2013, §2)

For a sequence `a₁, a₂, …` of positive integers, the convergents `p_ℓ / q_ℓ = [0; a₁, …, a_ℓ]`
are given by `p₋₁ = q₀ = 1`, `q₋₁ = p₀ = 0` and the recursion (2.1)
`q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`, `p_ℓ = a_ℓ p_{ℓ-1} + p_{ℓ-2}`. The paper's `a_ℓ` is `a ℓ`; the
value `a 0` is never used. This file collects the elementary facts of §2 that do not involve the
limit `α = [0; a₁, a₂, …]`.

## Main definitions

* `Nat.contNum a ℓ`, `Nat.contDen a ℓ`: `p_ℓ` and `q_ℓ`, for `ℓ ≥ 0`.
* `List.cfValue l`: the finite continued fraction `[0; b₁, …, b_k]` of a list of naturals.

## Main results

* `Nat.contNum_mul_contDen_sub`: `p_{ℓ+1} q_ℓ - p_ℓ q_{ℓ+1} = (-1)^ℓ`.
* `Nat.coprime_contNum_contDen`, `Nat.coprime_contDen_succ`: `p_ℓ ⊥ q_ℓ` and `q_ℓ ⊥ q_{ℓ+1}`.
* `Nat.contDen_lt_contDen_succ`: `(q_ℓ)_{ℓ ≥ 1}` is increasing; `Nat.contNum_le_contDen`.
* `Nat.contDen_mul_sqrt_two_pow_le`: **(2.3)**, `q_{ℓ+h} ≥ q_ℓ √2^{h-1}`.
* `Nat.contDen_div_contDen_succ`: **the mirror formula (2.4)**,
  `q_{ℓ-1} / q_ℓ = [0; a_ℓ, a_{ℓ-1}, …, a₁]`.

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, §2; O. Perron, *Die Lehre von den Kettenbrüchen*, 1929.
-/

@[expose] public section

namespace List

/-- **The finite continued fraction** `[0; b₁, …, b_k] = 1 / (b₁ + [0; b₂, …, b_k])`, with
`[0;] = 0`. -/
def cfValue : List ℕ → ℚ
  | [] => 0
  | b :: l => ((b : ℚ) + cfValue l)⁻¹

@[simp] theorem cfValue_nil : cfValue [] = 0 := rfl

@[simp] theorem cfValue_cons (b : ℕ) (l : List ℕ) : cfValue (b :: l) = ((b : ℚ) + cfValue l)⁻¹ :=
  rfl

end List

namespace Nat

/-- **The numerators of the convergents** `p_ℓ` of `[0; a₁, a₂, …]`: `p₀ = 0`, `p₁ = 1`,
`p_ℓ = a_ℓ p_{ℓ-1} + p_{ℓ-2}`. -/
def contNum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 2) * contNum a (n + 1) + contNum a n

/-- **The denominators of the convergents** `q_ℓ` of `[0; a₁, a₂, …]`: `q₀ = 1`, `q₁ = a₁`,
`q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`. -/
def contDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * contDen a (n + 1) + contDen a n

variable {a : ℕ → ℕ}

@[simp] theorem contNum_zero (a : ℕ → ℕ) : contNum a 0 = 0 := rfl

@[simp] theorem contNum_one (a : ℕ → ℕ) : contNum a 1 = 1 := rfl

@[simp] theorem contDen_zero (a : ℕ → ℕ) : contDen a 0 = 1 := rfl

@[simp] theorem contDen_one (a : ℕ → ℕ) : contDen a 1 = a 1 := rfl

/-- **(2.1)** for the numerators. -/
theorem contNum_add_two (a : ℕ → ℕ) (n : ℕ) :
    contNum a (n + 2) = a (n + 2) * contNum a (n + 1) + contNum a n := rfl

/-- **(2.1)** `q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`. -/
theorem contDen_add_two (a : ℕ → ℕ) (n : ℕ) :
    contDen a (n + 2) = a (n + 2) * contDen a (n + 1) + contDen a n := rfl

/-- **The determinant of consecutive convergents**: `p_{ℓ+1} q_ℓ - p_ℓ q_{ℓ+1} = (-1)^ℓ`. -/
theorem contNum_mul_contDen_sub (a : ℕ → ℕ) (n : ℕ) :
    (contNum a (n + 1) : ℤ) * contDen a n - contNum a n * contDen a (n + 1) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [contNum_add_two, contDen_add_two]
    push_cast
    linear_combination -ih

/-- `p_ℓ` and `q_ℓ` are coprime. -/
theorem coprime_contNum_contDen (a : ℕ → ℕ) (n : ℕ) : Coprime (contNum a n) (contDen a n) := by
  rw [← Nat.isCoprime_iff_coprime]
  refine ⟨-(contDen a (n + 1) : ℤ) * (-1) ^ n, (contNum a (n + 1) : ℤ) * (-1) ^ n, ?_⟩
  have h := contNum_mul_contDen_sub a n
  have hs : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-1 : ℤ) ^ n * h + hs

/-- `q_ℓ` and `q_{ℓ+1}` are coprime. -/
theorem coprime_contDen_succ (a : ℕ → ℕ) (n : ℕ) : Coprime (contDen a n) (contDen a (n + 1)) := by
  rw [← Nat.isCoprime_iff_coprime]
  refine ⟨(contNum a (n + 1) : ℤ) * (-1) ^ n, -(contNum a n : ℤ) * (-1) ^ n, ?_⟩
  have h := contNum_mul_contDen_sub a n
  have hs : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-1 : ℤ) ^ n * h + hs

section Positive

/-! The partial quotients are positive integers: `a_ℓ ≥ 1` for `ℓ ≥ 1`. -/

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `q_ℓ ≤ q_{ℓ+1}`. -/
theorem contDen_le_contDen_succ (n : ℕ) : contDen a n ≤ contDen a (n + 1) := by
  rcases n with _ | n
  · simpa using ha 0
  · rw [contDen_add_two]
    have := ha (n + 1)
    nlinarith

/-- `q_ℓ ≥ 1`. -/
theorem one_le_contDen (n : ℕ) : 1 ≤ contDen a n := by
  induction n with
  | zero => simp
  | succ n ih => exact ih.trans (contDen_le_contDen_succ ha n)

theorem contDen_pos (n : ℕ) : 0 < contDen a n := one_le_contDen ha n

/-- **`(q_ℓ)_{ℓ ≥ 1}` is increasing.** -/
theorem contDen_lt_contDen_succ {n : ℕ} (hn : 1 ≤ n) : contDen a n < contDen a (n + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [contDen_add_two]
  have h1 := ha (n + 1)
  have h2 := one_le_contDen ha n
  nlinarith

/-- `q_{ℓ+2} ≥ 2 q_ℓ`. -/
theorem two_mul_contDen_le (n : ℕ) : 2 * contDen a n ≤ contDen a (n + 2) := by
  rw [contDen_add_two]
  have h1 := ha (n + 1)
  have h2 := contDen_le_contDen_succ ha n
  nlinarith

/-- `p_ℓ ≤ q_ℓ`, so `p_ℓ / q_ℓ ∈ [0, 1]`. -/
theorem contNum_le_contDen (n : ℕ) : contNum a n ≤ contDen a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simpa using ha 0
    | n + 2 =>
      rw [contNum_add_two, contDen_add_two]
      have := ih n (by omega)
      have := ih (n + 1) (by omega)
      gcongr

/-- **(2.3), squared**: `q_ℓ² 2^h ≤ q_{ℓ+h+1}²`. -/
theorem contDen_sq_mul_two_pow_le (l h : ℕ) :
    contDen a l ^ 2 * 2 ^ h ≤ contDen a (l + h + 1) ^ 2 := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    match h with
    | 0 => simpa using Nat.pow_le_pow_left (contDen_le_contDen_succ ha l) 2
    | 1 =>
      have := two_mul_contDen_le ha l
      have h2 : (2 * contDen a l) ^ 2 ≤ contDen a (l + 2) ^ 2 := Nat.pow_le_pow_left this 2
      rw [show l + 1 + 1 = l + 2 by ring]
      nlinarith
    | h + 2 =>
      have h1 := ih h (by omega)
      have h2 := two_mul_contDen_le ha (l + h + 1)
      have h3 : (2 * contDen a (l + h + 1)) ^ 2 ≤ contDen a (l + h + 1 + 2) ^ 2 :=
        Nat.pow_le_pow_left h2 2
      rw [show l + (h + 2) + 1 = l + h + 1 + 2 by ring]
      calc contDen a l ^ 2 * 2 ^ (h + 2) = 4 * (contDen a l ^ 2 * 2 ^ h) := by ring
        _ ≤ 4 * contDen a (l + h + 1) ^ 2 := by gcongr
        _ = (2 * contDen a (l + h + 1)) ^ 2 := by ring
        _ ≤ _ := h3

/-- **(2.3)** `q_{ℓ+h} ≥ q_ℓ (√2)^{h-1}` for `h ≥ 1` (the paper also asks `ℓ ≥ 1`, which is not
needed). -/
theorem contDen_mul_sqrt_two_pow_le (l : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    (contDen a l : ℝ) * √2 ^ (h - 1) ≤ contDen a (l + h) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le' hh
  have key : ((contDen a l ^ 2 * 2 ^ h : ℕ) : ℝ) ≤ (contDen a (l + h + 1) ^ 2 : ℕ) := by
    exact_mod_cast contDen_sq_mul_two_pow_le ha l h
  push_cast at key
  rw [show h + 1 - 1 = h by omega, show l + (h + 1) = l + h + 1 by ring]
  have hsq : ((contDen a l : ℝ) * √2 ^ h) ^ 2 = (contDen a l : ℝ) ^ 2 * 2 ^ h := by
    rw [mul_pow, ← pow_mul, mul_comm h 2, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, hsq]
  exact key

/-- **The mirror formula (2.4)**: `q_{ℓ-1} / q_ℓ = [0; a_ℓ, a_{ℓ-1}, …, a₁]` for `ℓ ≥ 1`, stated
at `ℓ + 1`. -/
theorem contDen_div_contDen_succ (l : ℕ) :
    (contDen a l : ℚ) / contDen a (l + 1) =
      ((List.range (l + 1)).reverse.map fun i ↦ a (i + 1)).cfValue := by
  induction l with
  | zero => simp [div_eq_inv_mul]
  | succ l ih =>
    rw [List.range_succ, List.reverse_append, List.map_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.singleton_append, List.cfValue_cons]
    rw [← ih, contDen_add_two]
    have hq : (contDen a (l + 1) : ℚ) ≠ 0 := by exact_mod_cast (contDen_pos ha (l + 1)).ne'
    push_cast
    field_simp

end Positive

end Nat
