/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ComplexityRepetitions
public import Stephan2026a.ComplexityFloor

/-!
# Kernel violators from a complexity bound `p_T(k) ≤ c k (log k)^u`

**Problem 5.2, step 1.** If `p_T(k) ≤ c k (log k)^u` for all large `k`, the combinatorial form of
Bugeaud–Evertse's Lemma 6.1 (`Function.exists_repetitions_of_complexity_le`, DA Layer 7.5) gives,
for every `v > u`, a doubling sequence of repetitions: positions `r_n < τ_n` with
`2 τ_n < τ_{n+1}` and `τ_n ≤ (2n + 2)^{C (n + 1)}` such that the `τ_n (log τ_n)^{-v}` letters
after `τ_n` repeat those after `r_n`. It is applied to the steering word shifted by two letters,
so that the repetitions sit at `2 ≤ r_n + 2 < τ_n + 2`, where the steering word's identities hold;
the shift has no more factors than `t` itself.

By Lemma 2.7 a repetition of length `L` at `a < c` gives `|ε_c - ε_a| ≤ (2/3)^L`; with
`log (3/2) ≥ log 3 / 3` this is `≤ (3^c)^{-ε}` as soon as `3 c ε ≤ L`
(`SteeringWord.abs_eps_sub_le_rpow`). So every repetition is a kernel violator with the
exponent `ε ≈ (log τ_n)^{-v} / 6`.

## Main results

* `SteeringWord.complexity_shift_le`: the shifted steering word has no more factors.
* `SteeringWord.exists_violators_of_complexity_le`: **the doubling sequence of repetitions**.
* `SteeringWord.abs_eps_sub_le_rpow`: **Lemma 2.7 in exponential form**.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, Problem 5.2;
Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Lemma 6.1.
-/

@[expose] public section

namespace SteeringWord

open Function

/-- The factors of the steering word shifted by `2` are factors of the steering word. -/
theorem factors_shift_subset (k : ℕ) : factors (fun n ↦ t (n + 2)) k ⊆ factors t k := by
  rintro _ ⟨i, rfl⟩
  refine ⟨i + 2, ?_⟩
  simp only [factor]
  congr 1
  funext j
  rw [add_right_comm]

/-- The steering word shifted by `2` has no more factors than the steering word. -/
theorem complexity_shift_le (k : ℕ) : complexity (fun n ↦ t (n + 2)) k ≤ complexity t k :=
  Set.ncard_le_ncard (factors_shift_subset k) (finite_factors k)

/-- **Problem 5.2, the doubling sequence of repetitions.** If `p_T(k) ≤ c k (log k)^u` for
`k ≥ n₀`, `0 ≤ u < v`, there are `r n < τ n` with `2 τ n < τ (n + 1)` and
`τ n ≤ (2 n + 2)^{C (n + 1)}` such that the `τ n (log τ n)^{-v}` letters after `τ n + 2` repeat
those after `r n + 2`. -/
theorem exists_violators_of_complexity_le {c u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (n₀ : ℕ)
    (hp : ∀ k ≥ n₀, (complexity t k : ℝ) ≤ c * k * Real.log k ^ u) :
    ∃ (C : ℕ) (r τ : ℕ → ℕ), (∀ n, r n < τ n) ∧ (∀ n, 2 * τ n < τ (n + 1)) ∧
      (∀ n, τ n ≤ (2 * n + 2) ^ (C * (n + 1))) ∧
      ∀ n, IsRepetition (r n + 2) (τ n + 2) ⌈τ n * Real.log (τ n) ^ (-v)⌉₊ := by
  obtain ⟨C, r, τ, hrt, hgap, hbd, -, hrep⟩ :=
    exists_repetitions_of_complexity_le (a := fun n ↦ t (n + 2))
      (fun k ↦ (finite_factors k).subset (factors_shift_subset k)) hu huv n₀
      fun k hk ↦ le_trans (by exact_mod_cast complexity_shift_le k) (hp k hk)
  refine ⟨C, r, τ, hrt, hgap, hbd, fun n i hi ↦ ?_⟩
  have h := hrep n i hi
  rw [show r n + 2 + i = i + r n + 2 by ring, show τ n + 2 + i = i + τ n + 2 by ring]
  exact h.symm

/-- **Lemma 2.7 in exponential form.** A repetition of length `L` at `a, c` with `3 c ε ≤ L`
gives `|ε_c - ε_a| ≤ (3^c)^{-ε}`: `(2/3)^L ≤ 3^{-L/3}` since `2^3 ≤ 3^2`. -/
theorem abs_eps_sub_le_rpow {a c L : ℕ} (h : IsRepetition a c L) {ε : ℝ}
    (hL : 3 * c * ε ≤ L) : |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) := by
  have h1 : |(eps c : ℝ) - eps a| ≤ (2 / 3 : ℝ) ^ L := by
    have h0 := (Rat.cast_le (K := ℝ)).mpr (abs_eps_sub_le_of_repetition h)
    rwa [Rat.cast_abs, Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_ofNat] at h0
  refine h1.trans ?_
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_pow, Real.log_div (by norm_num) (by norm_num)]
  have h89 : 3 * Real.log 2 ≤ 2 * Real.log 3 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 3) (by norm_num : (2 : ℝ) ^ 3 ≤ 3 ^ 2)
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hL0 : (0 : ℝ) ≤ L := L.cast_nonneg
  nlinarith [mul_le_mul_of_nonneg_left hL hl3.le]

end SteeringWord
