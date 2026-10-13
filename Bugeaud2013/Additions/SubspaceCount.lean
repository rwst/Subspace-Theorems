/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.RealFormCount

/-!
# The quantitative Subspace Theorem for real forms in `1, α, α²`

The bound on `δ` in (6.1) uses the quantitative Subspace Theorem three times, always for forms
whose coefficients are `b₀ + b₁ α + b₂ α²` with integers `bᵢ`, always at `∞` only, and always at
integer points. This file states what is used (`Real.SubspaceBound α a`: the solutions lie in at
most `K δ^{-a} (1 + log δ⁻¹)²` proper subspaces, above a threshold polynomial in `δ⁻¹` and linear
in the logarithms of the data) and proves it with `a = 3` as the case `S = ∅` of
`Real.subspaceBoundAt_three` (`QuantitativeSubspace/RealFormCount.lean`), which holds at `∞` and
any finite set of primes.

## Main definitions

* `Real.SubspaceBound α a`: the quantitative Subspace Theorem for such forms in `2 ≤ n ≤ 4`
  variables, with `δ^{-a}` subspaces.

## Main results

* `Real.subspaceBound_three`: **Evertse–Ferretti 2013**: `Real.SubspaceBound α 3` for every real
  algebraic `α`.
* `Real.SubspaceBound.mono`: a larger exponent is weaker; Evertse–Schlickewei 2002's
  `δ^{-n-4}` gives `Real.SubspaceBound α 8` in `n ≤ 4` variables.
-/

@[expose] public section

open Finset

namespace Real

/-- **The quantitative Subspace Theorem for forms in `1, α, α²`, with `δ^{-a}` subspaces.** For
`2 ≤ n ≤ 4` there is `K` such that: for forms `∑_k quadVal α (P i k) X_k` with integer data
`|P i k m| ≤ B` and determinant at least `γ` in absolute value, a constant `C ≥ 1` and exponents
`e i ≤ 1`, one of them `1`, of sum at most `-δ`, the nonzero integer points `x` with
`|∑_k quadVal α (P i k) x_k| ≤ C |x|^{e i}` for all `i` and
`log |x| ≥ K δ^{-K} (1 + log B + log C + log γ⁻¹)` lie in at most `K δ^{-a} (1 + log δ⁻¹)²` proper
subspaces of `ℚⁿ`. -/
def SubspaceBound (α a : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 0 < K ∧
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ i, e i ≤ 1) →
      (∃ i, e i = 1) → ∑ i, e i ≤ -δ →
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), (#T : ℝ) ≤ K * δ⁻¹ ^ a * (1 + log δ⁻¹) ^ 2 ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        K * δ⁻¹ ^ K * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        ∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U

/-- A larger exponent is a weaker statement. -/
theorem SubspaceBound.mono {α a b : ℝ} (h : SubspaceBound α a) (hab : a ≤ b) :
    SubspaceBound α b := by
  intro n hn2 hn4
  obtain ⟨K, hK, hT⟩ := h n hn2 hn4
  refine ⟨K, hK, fun P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum ↦ ?_⟩
  obtain ⟨T, hcard, hT, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum
  refine ⟨T, hcard.trans ?_, hT, hmem⟩
  have h1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have := Real.rpow_le_rpow_of_exponent_le h1 hab
  gcongr

/-- **The case `S = ∅`**: the statement at `∞` and the primes of `S` gives the one at `∞`. A
negative sum of the exponents at `∞` makes one of them negative. -/
theorem SubspaceBoundAt.subspaceBound {α a : ℝ} (h : SubspaceBoundAt α ∅ a) :
    SubspaceBound α a := by
  intro n hn2 hn4
  obtain ⟨K, hK, hT⟩ := h n hn2 hn4
  refine ⟨max K 1, by positivity, fun P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum ↦ ?_⟩
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have hK1 : K ≤ max K 1 := le_max_left _ _
  have he0 : ∃ i, e i ≤ 0 := by
    by_contra! hpos
    have : 0 < ∑ i, e i :=
      Finset.sum_pos (fun i _ ↦ hpos i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    linarith
  obtain ⟨T, hcard, htop, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e (fun _ _ ↦ 0) δ hδ hδ1
    he1 he he0 (by simp) (by simp) (by simpa using hsum)
  refine ⟨T, hcard.trans (by gcongr), htop, fun x hx hsol hlarge ↦
    hmem x hx hsol (by simp) (le_trans ?_ hlarge)⟩
  -- `δ⁻¹ ≤ δ⁻¹ ^ max K 1`
  have h2 : δ⁻¹ ≤ δ⁻¹ ^ max K 1 :=
    calc δ⁻¹ = δ⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ δ⁻¹ ^ max K 1 := Real.rpow_le_rpow_of_exponent_le hδi (le_max_right _ _)
  have : 0 ≤ 1 + log B + log C + log γ⁻¹ := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    linarith
  gcongr

/-- **The quantitative Subspace Theorem of Evertse–Ferretti 2013 for forms in `1, α, α²`**:
`δ^{-3} (1 + log δ⁻¹)²` subspaces. The case `S = ∅` of `Real.subspaceBoundAt_three`. -/
theorem subspaceBound_three {α : ℝ} (hα : IsAlgebraic ℚ α) : SubspaceBound α 3 :=
  (subspaceBoundAt_three hα ∅).subspaceBound

end Real
