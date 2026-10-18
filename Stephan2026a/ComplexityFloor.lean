/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.RepetitionIdentity
public import DiophantineApproximation.FactorComplexity

-- Used only inside proofs.
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat

/-!
# The complexity floor

The subword complexity `p_T(k)` of the steering word is `Function.complexity t k`, the number of
distinct factors of length `k` (DA Layer 7.5). The growth ceiling of Proposition 2.5 says that two
equal factors must lie about `k / log₂ (3/2)` apart, so the first `≈ 1.7095 k` windows are
pairwise distinct (Theorem 2.10). The slope `41/24` is the certified rounding of `1/log₂ (3/2)`
obtained from the integer certificate `3^41 ≤ 2^65`.

## Main results

* `SteeringWord.finite_factors`: finitely many factors of each length (the alphabet is
  `{-2, …, 2}`, so `Set.ncard` counts honestly).
* `SteeringWord.repetition_linear_bound`: a repetition of length `k` at `2 ≤ a < c` has
  `41 k ≤ 24 c + 24`.
* `SteeringWord.complexity_lower`: **Theorem 2.10**, `41 k ≤ 24 p_T(k) + 72`.
* `SteeringWord.parity_dichotomy`: **Proposition 2.12**, the parity dichotomy.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §2.
-/

public section

namespace SteeringWord

open Function

/-- Two windows agree exactly when they form a repetition. -/
theorem factor_eq_iff {a c k : ℕ} : factor t a k = factor t c k ↔ IsRepetition a c k :=
  factor_eq_factor_iff

/-- The steering word has finitely many factors of each length: its letters lie in `[-2, 2]`. -/
theorem finite_factors (k : ℕ) : (factors t k).Finite := by
  refine ((Set.Finite.pi' (t := fun _ : Fin k ↦ Set.Icc (-2 : ℤ) 2)
    fun _ ↦ Set.finite_Icc _ _).image List.ofFn).subset ?_
  rintro w ⟨a, rfl⟩
  exact ⟨_, fun i ↦ Set.mem_Icc.mpr (abs_le.mp (t_abs_le _)), rfl⟩

/-- A repetition of length `k` at `2 ≤ a < c` forces `41 k ≤ 24 c + 24`: Proposition 2.5 with the
certificate `3^41 ≤ 2^65`. -/
theorem repetition_linear_bound {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (h : IsRepetition a c k) : 41 * k ≤ 24 * c + 24 := by
  have h2 : (2 : ℕ) ^ ((k + c + 1) * 41) ≤ 3 ^ ((c + 1) * 41) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (repetition_pow_le ha hac h) 41
  have h3 : (3 : ℕ) ^ ((c + 1) * 41) ≤ 2 ^ ((c + 1) * 65) := by
    rw [mul_comm (c + 1) 41, mul_comm (c + 1) 65, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) (c + 1)
  have h5 : (k + c + 1) * 41 ≤ (c + 1) * 65 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans h2 h3)
  omega

/-- **Theorem 2.10, the complexity floor**: `41 k ≤ 24 p_T(k) + 72`, that is
`p_T(k) ≥ (41/24) k - 3`, strictly above the Morse–Hedlund floor `k + 1`. -/
theorem complexity_lower (k : ℕ) : 41 * k ≤ 24 * complexity t k + 72 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · omega
  set C : ℕ := (41 * k - 25) / 24 with hC
  have hCk : 24 * C + 24 < 41 * k := by omega
  have hinj : Set.InjOn (fun a ↦ factor t a k) ↑(Finset.Icc 2 C) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    by_contra hne
    rcases Nat.lt_or_ge x y with hlt | hge
    · have := repetition_linear_bound hx.1 hlt (factor_eq_iff.mp hxy)
      omega
    · have := repetition_linear_bound hy.1 (by omega) (factor_eq_iff.mp hxy.symm)
      omega
  have himg : ((Finset.Icc 2 C).image fun a ↦ factor t a k).card = C - 1 := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hsub : ((Finset.Icc 2 C).image fun a ↦ factor t a k) ⊆ (finite_factors k).toFinset := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact (Set.Finite.mem_toFinset _).mpr ⟨x, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hncard : complexity t k = (finite_factors k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (finite_factors k)
  omega

/-- **Proposition 2.12, the parity dichotomy.** A repetition of length `k` of the parity word at
`a`, `c` either lifts to a repetition of the steering word, or the two windows first disagree at
a step `j < k` at which the steering letters differ by a nonzero even amount. -/
theorem parity_dichotomy {a c k : ℕ} (hb : ∀ i < k, b (a + i) = b (c + i)) :
    IsRepetition a c k ∨
      ∃ j < k, (∀ i < j, t (a + i) = t (c + i)) ∧ t (a + j) ≠ t (c + j) ∧
        (t (c + j) - t (a + j)) % 2 = 0 := by
  classical
  by_cases h : IsRepetition a c k
  · exact Or.inl h
  right
  have hex : ∃ i, i < k ∧ t (a + i) ≠ t (c + i) := by
    by_contra hall
    push Not at hall
    exact h hall
  have hexP : ∃ i, t (a + i) ≠ t (c + i) := hex.imp fun _ h ↦ h.2
  refine ⟨Nat.find hexP, ?_, fun i hi ↦ not_not.mp (Nat.find_min hexP hi),
    Nat.find_spec hexP, ?_⟩
  · obtain ⟨i0, hi0k, hi0⟩ := hex
    exact lt_of_le_of_lt (Nat.find_min' hexP hi0) hi0k
  · have hjk : Nat.find hexP < k := by
      obtain ⟨i0, hi0k, hi0⟩ := hex
      exact lt_of_le_of_lt (Nat.find_min' hexP hi0) hi0k
    have h1 := t_emod_two (a + Nat.find hexP)
    have h2 := t_emod_two (c + Nat.find hexP)
    have h3 := hb (Nat.find hexP) hjk
    unfold b at h3
    omega

end SteeringWord
