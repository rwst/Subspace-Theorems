/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.SubspaceCount
public import QuantitativeSubspace.RealFormInterval

/-!
# The quantitative Subspace Theorem for real forms in `1, α, α²`, interval form

The interval form of `Real.SubspaceBound α 3` (`Bugeaud2013/Additions/SubspaceCount.lean`): the
solutions above the threshold lie in one proper subspace, or have `log |x|` in one of
`K δ⁻² (1 + log δ⁻¹)` intervals `[s, K δ⁻¹ s)` (`Real.SubspaceInterval α`). It is the case
`S = ∅` of `Real.subspaceIntervalAt_of_isAlgebraic`
(`QuantitativeSubspace/RealFormInterval.lean`). Points of doubling height put `O(log δ⁻¹)` of
themselves into an interval, which is what saves a power of `δ⁻¹` in the count of
`Bugeaud2013/Additions/CountThird.lean`.

## Main definitions

* `Real.SubspaceInterval α`: the interval form for such forms in `2 ≤ n ≤ 4` variables at `∞`.

## Main results

* `Real.subspaceInterval_of_isAlgebraic`: `Real.SubspaceInterval α` for every real algebraic `α`.
-/

@[expose] public section

open Finset

namespace Real

/-- **The interval form of the quantitative Subspace Theorem for forms in `1, α, α²`.** For
`2 ≤ n ≤ 4` there is `K ≥ 1` such that: for the data of `Real.SubspaceBound`, there are a proper
subspace `U` of `ℚⁿ` and at most `K δ⁻² (1 + log δ⁻¹)` reals `s` such that every solution `x`
with `log |x| ≥ K δ^{-K} (1 + log B + log C + log γ⁻¹)` lies in `U` or has
`s ≤ log |x| < K δ⁻¹ s` for one of them. -/
def SubspaceInterval (α : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 1 ≤ K ∧
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ i, e i ≤ 1) →
      (∃ i, e i = 1) → ∑ i, e i ≤ -δ →
    ∃ U : Submodule ℚ (Fin n → ℚ), U ≠ ⊤ ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        K * δ⁻¹ ^ K * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        (fun k ↦ (x k : ℚ)) ∈ U ∨
          ∃ s ∈ 𝒯, s ≤ log (⨆ k, |(x k : ℝ)|) ∧ log (⨆ k, |(x k : ℝ)|) < K * δ⁻¹ * s

/-- **The case `S = ∅`**: the interval form at `∞` and the primes of `S` gives the one at `∞`. -/
theorem SubspaceIntervalAt.subspaceInterval {α : ℝ} (h : SubspaceIntervalAt α ∅) :
    SubspaceInterval α := by
  intro n hn2 hn4
  obtain ⟨K, hK, hT⟩ := h n hn2 hn4
  refine ⟨K, hK, fun P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum ↦ ?_⟩
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have he0 : ∃ i, e i ≤ 0 := by
    by_contra! hpos
    have : 0 < ∑ i, e i :=
      Finset.sum_pos (fun i _ ↦ hpos i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    linarith
  obtain ⟨U, hU, 𝒯, hcard, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e (fun _ _ ↦ 0) δ hδ hδ1
    he1 he (exists_le_one_sub_div_of_exists_nonpos hn2 hδ1 he0)
    (by simp) (by simp) (by simpa using hsum)
  refine ⟨U, hU, 𝒯, hcard, fun x hx hsol hlarge ↦ hmem x hx hsol (by simp) (le_trans ?_ hlarge)⟩
  -- `δ⁻¹ ≤ δ⁻¹ ^ K`
  have h2 : δ⁻¹ ≤ δ⁻¹ ^ K :=
    calc δ⁻¹ = δ⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ δ⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hδi hK
  have : 0 ≤ 1 + log B + log C + log γ⁻¹ := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    linarith
  have : 0 ≤ K := by linarith
  gcongr

/-- **The interval form of Evertse–Ferretti 2013 for forms in `1, α, α²`**, for every real
algebraic `α`: the case `S = ∅` of `Real.subspaceIntervalAt_of_isAlgebraic`. -/
theorem subspaceInterval_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) : SubspaceInterval α :=
  (subspaceIntervalAt_of_isAlgebraic hα ∅).subspaceInterval

end Real
