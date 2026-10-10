/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Value

/-!
# Mirror images of continuants (Bugeaud 2013, §5)

For the quasi-palindromic criterion (§5, after Adamczewski–Bugeaud 2007, Lemmas 1 and 3), the
convergents of a finite word and of its mirror image are compared: the matrix
`[[q_N, q_{N-1}], [p_N, p_{N-1}]]` is the product of the `[[c_i, 1], [1, 0]]`, and transposing it
reverses the word. Only the first row is needed: for the mirror image `d = c_N … c_1`,
`q_N(d) = q_N(c)` and `p_N(d) = q_{N-1}(c)`. It is proved by induction from the tail formula
(`Nat.contDen_add`, `Nat.contNum_add` at `j = 0`), without matrices.

## Main results

* `Nat.contDen_rev`, `Nat.contNum_rev`: the mirror image has the same continuant, and its
  numerator is the previous continuant (the mirror formula (2.4) in integers).
* `Nat.abs_contFrac_sub_contConv_lt_three`: a finite continued fraction `[0; c₁, …, c_N]` whose
  first `m` partial quotients are those of `α` is within `3 / q_m²` of `α`.
-/

@[expose] public section

namespace Nat

variable {a : ℕ → ℕ}

/-- **The mirror image of a word, jointly**: for `d = c_{N+1} … c_1`, `q_{N+1}(d) = q_{N+1}(c)`
and `p_{N+1}(d) = q_N(c)`. -/
theorem contDen_rev_and_contNum_rev (c : ℕ → ℕ) (N : ℕ) :
    contDen (fun i ↦ c (N + 2 - i)) (N + 1) = contDen c (N + 1) ∧
      contNum (fun i ↦ c (N + 2 - i)) (N + 1) = contDen c N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have htail : (fun i ↦ (fun i ↦ c (N + 1 + 2 - i)) (i + (0 + 1))) = fun i ↦ c (N + 2 - i) := by
      funext i; dsimp only; congr 1; omega
    have hD := contDen_add (fun i ↦ c (N + 1 + 2 - i)) 0 (N + 1)
    have hN := contNum_add (fun i ↦ c (N + 1 + 2 - i)) 0 (N + 1)
    rw [htail, ih.1, ih.2, show 0 + 1 + (N + 1) = N + 1 + 1 by omega] at hD hN
    refine ⟨?_, ?_⟩
    · rw [hD, contDen_add_two, zero_add, contDen_one, contDen_zero, one_mul]
      rfl
    · rw [hN]
      simp

/-- **The mirror image has the same continuant**: `K(c_N, …, c_1) = K(c_1, …, c_N)`. -/
theorem contDen_rev (c : ℕ → ℕ) (N : ℕ) :
    contDen (fun i ↦ c (N + 1 - i)) N = contDen c N := by
  rcases N with _ | N
  · rfl
  · exact (contDen_rev_and_contNum_rev c N).1

/-- **The mirror formula in integers**: the numerator of `[0; c_{N+1}, …, c_1]` is `q_N(c)`. -/
theorem contNum_rev (c : ℕ → ℕ) (N : ℕ) :
    contNum (fun i ↦ c (N + 2 - i)) (N + 1) = contDen c N :=
  (contDen_rev_and_contNum_rev c N).2

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- **A finite continued fraction with the prefix of `α`**: if `c₁, …, c_N ≥ 1` and
`c_i = a_i` for `i ≤ m ≤ N`, then `|α - [0; c₁, …, c_N]| < 3 / q_m²`. -/
theorem abs_contFrac_sub_contConv_lt_three {c : ℕ → ℕ} {m N : ℕ}
    (hc : ∀ i, 1 ≤ i → i ≤ N → 1 ≤ c i) (hmN : m ≤ N) (h : ∀ i, 1 ≤ i → i ≤ m → a i = c i) :
    |contFrac a - contConv c N| < 3 / (contDen a m : ℝ) ^ 2 := by
  set e : ℕ → ℕ := fun i ↦ if i ≤ N then c i else 1 with he
  have he1 : ∀ n, 1 ≤ e (n + 1) := fun n ↦ by
    simp only [he]; split_ifs with h1
    · exact hc _ (by omega) h1
    · exact le_rfl
  have hce : ∀ i, 1 ≤ i → i ≤ N → c i = e i := fun i _ hi ↦ by simp only [he, hi, ite_true]
  have hae : ∀ i, 1 ≤ i → i ≤ m → a i = e i := fun i h1 hi ↦
    (h i h1 hi).trans (hce i h1 (hi.trans hmN))
  rw [contConv_eq_of_eqOn hce le_rfl]
  have h1 := abs_contFrac_sub_contFrac_lt ha he1 hae
  have h2 := abs_contFrac_sub_contConv_lt_sq he1 N
  have hq : (contDen a m : ℝ) ≤ contDen e N := by
    rw [contDen_eq_of_eqOn hae le_rfl]
    exact_mod_cast (monotone_nat_of_le_succ (contDen_le_contDen_succ he1)) hmN
  have hq0 : (0 : ℝ) < contDen a m := contDen_pos_real ha m
  have h3 : 1 / (contDen e N : ℝ) ^ 2 ≤ 1 / (contDen a m : ℝ) ^ 2 := by
    gcongr
  calc |contFrac a - contConv e N|
      ≤ |contFrac a - contFrac e| + |contFrac e - contConv e N| := abs_sub_le _ _ _
    _ < 2 / (contDen a m : ℝ) ^ 2 + 1 / (contDen a m : ℝ) ^ 2 := by linarith
    _ = 3 / (contDen a m : ℝ) ^ 2 := by ring

end Positive

end Nat
