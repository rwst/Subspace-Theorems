/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SimultaneousSubspaces

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# Schmidt's Subspace Theorem in the form of Bugeaud 2013, Theorem 2.1

The paper applies the Subspace Theorem to systems of linear forms with **real** algebraic
coefficients, and each time uses it in the same way: a sequence of integer points at which the
product of the forms is small has infinitely many members on one proper rational subspace, hence
satisfies a non-trivial linear relation infinitely often. This file packages both steps on top of
`Complex.exists_finset_submodule_of_prod_norm_le` (Layer 6.3 of `DiophantineApproximation`).

## Main results

* `Real.exists_finset_submodule_of_prod_abs_le`: **Theorem 2.1** for forms with real algebraic
  coefficients, linearly independent over `ℝ`.
* `Real.exists_ne_zero_frequently_sum_eq_zero`: if the product of the forms at `x n` is at most
  `(max_i |x n i|)^(-ε)` for all large `n`, then a non-zero rational relation `∑ y_i (x n)_i = 0`
  holds for infinitely many `n`.

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, Theorem 2.1; W. M. Schmidt, *Diophantine Approximation*,
LNM 785 (1980).
-/

@[expose] public section

open Filter

namespace Real

/-- Real rows that are linearly independent over `ℝ` stay linearly independent over `ℂ`. -/
theorem linearIndependent_ofReal {ι : Type*} [Finite ι] {c : ι → ι → ℝ}
    (h : LinearIndependent ℝ c) : LinearIndependent ℂ fun i k ↦ (c i k : ℂ) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hk (k : ι) : ∑ i, g i * (c i k : ℂ) = 0 := by
    simpa [Finset.sum_apply] using congrFun hg k
  have hre : ∀ i, (g i).re = 0 := h (fun i ↦ (g i).re) (funext fun k ↦ by
    simpa [Finset.sum_apply, Complex.re_sum] using congrArg Complex.re (hk k))
  have him : ∀ i, (g i).im = 0 := h (fun i ↦ (g i).im) (funext fun k ↦ by
    simpa [Finset.sum_apply, Complex.im_sum] using congrArg Complex.im (hk k))
  exact fun i ↦ Complex.ext (hre i) (him i)

variable {ι : Type*} [Fintype ι]

/-- **Theorem 2.1** (Schmidt's Subspace Theorem) for linear forms with real algebraic
coefficients: for linearly independent rows `c i` and `ε > 0`, the integer points `x ≠ 0` with
`∏_i |∑_k c i k x_k| ≤ (max_i |x_i|)^(-ε)` lie in finitely many proper subspaces of `ℚ^ι`. -/
theorem exists_finset_submodule_of_prod_abs_le [Nontrivial ι] {c : ι → ι → ℝ}
    (hc : ∀ i k, IsAlgebraic ℚ (c i k)) (hind : LinearIndependent ℝ c) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, |∑ k, c i k * (x k : ℝ)|) ≤ (⨆ i, |(x i : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  obtain ⟨T, hT, hmem⟩ := Complex.exists_finset_submodule_of_prod_norm_le
    (c := fun i k ↦ (c i k : ℂ)) (fun i k ↦ (hc i k).algebraMap (A := ℂ))
    (linearIndependent_ofReal hind) hε
  refine ⟨T, hT, fun x hx hle ↦ hmem x hx (le_trans (le_of_eq ?_) hle)⟩
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have : (∑ k, (c i k : ℂ) * ((x k : ℤ) : ℂ)) = ((∑ k, c i k * (x k : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- **The Subspace Theorem as the paper uses it.** If, for all large `n`, the integer point
`x n` is non-zero and `∏_i |∑_k c i k (x n)_k| ≤ (max_i |(x n)_i|)^(-ε)`, then there is a non-zero
rational vector `y` with `∑_i y_i (x n)_i = 0` for infinitely many `n`. -/
theorem exists_ne_zero_frequently_sum_eq_zero [Nontrivial ι] {c : ι → ι → ℝ}
    (hc : ∀ i k, IsAlgebraic ℚ (c i k)) (hind : LinearIndependent ℝ c) {ε : ℝ} (hε : 0 < ε)
    (x : ℕ → ι → ℤ)
    (hx : ∀ᶠ n in atTop, x n ≠ 0 ∧
      (∏ i, |∑ k, c i k * (x n k : ℝ)|) ≤ (⨆ i, |(x n i : ℝ)|) ^ (-ε)) :
    ∃ y : ι → ℚ, y ≠ 0 ∧ ∃ᶠ n in atTop, ∑ i, (y i : ℝ) * (x n i : ℝ) = 0 := by
  classical
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_prod_abs_le hc hind hε
  have hin : ∀ᶠ n in atTop, ∃ V ∈ T, (fun i ↦ (x n i : ℚ)) ∈ V := by
    filter_upwards [hx] with n hn
    refine hmem (x n) (fun h ↦ hn.1 (funext fun i ↦ ?_)) hn.2
    simpa using congrFun h i
  obtain ⟨V, hVT, hV⟩ : ∃ V ∈ T, ∃ᶠ n in atTop, (fun i ↦ (x n i : ℚ)) ∈ V := by
    by_contra hne
    push Not at hne
    have hall : ∀ᶠ n in atTop, ∀ V ∈ T, (fun i ↦ (x n i : ℚ)) ∉ V :=
      (eventually_all_finset T).2 fun V hV ↦ hne V hV
    obtain ⟨n, ⟨V, hV, hxV⟩, hn⟩ := (hin.and hall).exists
    exact hn V hV hxV
  obtain ⟨f, hf0, hfV⟩ := V.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 (hT V hVT))
  set y : ι → ℚ := fun i ↦ f fun j ↦ if i = j then 1 else 0
  have hfy (z : ι → ℚ) : f z = ∑ i, z i * y i := by
    rw [LinearMap.pi_apply_eq_sum_univ f z]; rfl
  refine ⟨y, fun hy ↦ hf0 (LinearMap.ext fun z ↦ ?_), hV.mono fun n hn ↦ ?_⟩
  · rw [hfy, hy]; simp
  · have h0 : f (fun i ↦ (x n i : ℚ)) = 0 := hfV hn
    rw [hfy] at h0
    have : (∑ i, y i * (x n i : ℚ)) = 0 := by
      rw [← h0]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    exact_mod_cast this

end Real
