/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import STForMathlib.RingTheory.MvPolynomial.Bezout
-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Tuple

/-!
# Lexicographic cancellation along a regular sequence

For a regular sequence `φ 0, …, φ (m - 1)` modulo `J`, write `φ ^ i = ∏ l, φ l ^ i l` for
`i : Fin m → ℕ`. If `φ ^ i q ≡ ∑_r φ ^ {j r} q_r` modulo `J` with every `j r` lexicographically
larger than `i`, then `q ∈ J + (φ)` (Corvaja–Zannier, *On a general Thue's equation*, Amer. J.
Math. 126 (2004), Lemma 2.2). This is the step that identifies the graded pieces of the
filtration of Corvaja–Zannier's §3.

## Main statements

* `MvPolynomial.mem_of_pow_mul_mem_of_colon_eq`: a nonzerodivisor modulo `J` cancels in powers.
* `MvPolynomial.mem_sup_span_range_of_prod_pow_mul_sub_sum_mem`: Lemma 2.2.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ K : Type*} [Field K]

/-- A nonzerodivisor `g` modulo `J` cancels in powers: `g ^ k x ∈ J` gives `x ∈ J`. -/
theorem mem_of_pow_mul_mem_of_colon_eq {J : Ideal (MvPolynomial σ K)} {g x : MvPolynomial σ K}
    (hg : J.colon {g} = J) (k : ℕ) (h : g ^ k * x ∈ J) : x ∈ J := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    refine ih ?_
    rw [← hg]
    refine Submodule.mem_colon_singleton.mpr ?_
    rw [smul_eq_mul, mul_comm, ← mul_assoc, ← pow_succ']
    exact h

/-- **Lexicographic cancellation** (Corvaja–Zannier 2004, Lemma 2.2). Along a regular sequence
`φ` modulo `J`, if `φ ^ i q - ∑_r φ ^ {j r} q_r ∈ J` with every `j r` lexicographically larger
than `i`, then `q ∈ J + (φ 0, …, φ (m - 1))`. -/
theorem mem_sup_span_range_of_prod_pow_mul_sub_sum_mem {ρ : Type*} :
    ∀ {m : ℕ} {J : Ideal (MvPolynomial σ K)} {φ : Fin m → MvPolynomial σ K},
      IsRegularSeq m J φ → ∀ {i : Fin m → ℕ} {q : MvPolynomial σ K} (s : Finset ρ)
        (j : ρ → Fin m → ℕ) (q' : ρ → MvPolynomial σ K),
        (∀ r ∈ s, Pi.Lex (· < ·) (· < ·) i (j r)) →
        (∏ l, φ l ^ i l) * q - ∑ r ∈ s, (∏ l, φ l ^ j r l) * q' r ∈ J →
        q ∈ J ⊔ Ideal.span (Set.range φ)
  | 0, J, φ, _, i, q, s, j, q', hj, h => by
    have hs : ∑ r ∈ s, (∏ l, φ l ^ j r l) * q' r = 0 :=
      sum_eq_zero fun r hr ↦ absurd (hj r hr) fun ⟨k, _⟩ ↦ k.elim0
    rw [hs, sub_zero, Fin.prod_univ_zero, one_mul] at h
    exact le_sup_left (α := Ideal (MvPolynomial σ K)) h
  | m + 1, J, φ, hφ, i, q, s, j, q', hj, h => by
    obtain ⟨-, hcol, hreg⟩ := hφ
    classical
    set a := i 0
    set s₁ := s.filter fun r ↦ j r 0 = a
    set s₂ := s.filter fun r ↦ ¬ j r 0 = a
    have hlex : ∀ r ∈ s, a < j r 0 ∨ a = j r 0 ∧
        Pi.Lex (· < ·) (· < ·) (Fin.tail i) (Fin.tail (j r)) := fun r hr ↦ by
      have := hj r hr
      rw [← Fin.cons_self_tail i, ← Fin.cons_self_tail (j r)] at this
      exact (Fin.pi_lex_lt_cons_cons (s := fun {_} x y ↦ x < y)).mp this
    have hgt : ∀ r ∈ s₂, a < j r 0 := fun r hr ↦ by
      obtain ⟨hr, hne⟩ := mem_filter.mp hr
      rcases hlex r hr with h | h
      · exact h
      · exact absurd h.1.symm hne
    set P : (Fin m → ℕ) → MvPolynomial σ K := fun e ↦ ∏ l : Fin m, φ l.succ ^ e l
    set y := P (Fin.tail i) * q - ∑ r ∈ s₁, P (Fin.tail (j r)) * q' r
    set z := ∑ r ∈ s₂, φ 0 ^ (j r 0 - a - 1) * P (Fin.tail (j r)) * q' r
    have hsplit : (∏ l, φ l ^ i l) * q - ∑ r ∈ s, (∏ l, φ l ^ j r l) * q' r =
        φ 0 ^ a * (y - φ 0 * z) := by
      rw [← sum_filter_add_sum_filter_not s (fun r ↦ j r 0 = a)]
      have h₁ : ∑ r ∈ s₁, (∏ l, φ l ^ j r l) * q' r =
          φ 0 ^ a * ∑ r ∈ s₁, P (Fin.tail (j r)) * q' r := by
        rw [mul_sum]
        refine sum_congr rfl fun r hr ↦ ?_
        rw [Fin.prod_univ_succ, (mem_filter.mp hr).2, mul_assoc]
        rfl
      have h₂ : ∑ r ∈ s₂, (∏ l, φ l ^ j r l) * q' r = φ 0 ^ a * (φ 0 * z) := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun r hr ↦ ?_
        have hr := hgt r hr
        rw [Fin.prod_univ_succ, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add,
          show a + 1 + (j r 0 - a - 1) = j r 0 by omega]
        rfl
      rw [h₁, h₂, Fin.prod_univ_succ]
      change φ 0 ^ a * P (Fin.tail i) * q - _ = _
      ring
    rw [hsplit] at h
    have hy : y ∈ J ⊔ Ideal.span {φ 0} := by
      have hx := mem_of_pow_mul_mem_of_colon_eq hcol a h
      have : y = (y - φ 0 * z) + φ 0 * z := by ring
      rw [this]
      exact Ideal.add_mem _ (le_sup_left (α := Ideal (MvPolynomial σ K)) hx)
        (le_sup_right (α := Ideal (MvPolynomial σ K))
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    have hj₁ : ∀ r ∈ s₁, Pi.Lex (· < ·) (· < ·) (Fin.tail i) (Fin.tail (j r)) := fun r hr ↦ by
      obtain ⟨hr, heq⟩ := mem_filter.mp hr
      rcases hlex r hr with h | h
      · exact absurd heq (by omega)
      · exact h.2
    have := mem_sup_span_range_of_prod_pow_mul_sub_sum_mem hreg s₁ (fun r ↦ Fin.tail (j r)) q'
      hj₁ hy
    rwa [← sup_span_range_succ] at this

end MvPolynomial
