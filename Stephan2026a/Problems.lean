/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.Kernel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The open problems of the paper

Section 5 of the paper poses four problems and Appendix A states one conjecture. This file states
each as a `Prop`, without proof: the library is `sorry`-free, so an open statement is a
definition, not a theorem. Where the paper proves part of a problem, or where the statement
contains a theorem proved here, that part is proved below, which also checks that the statement
says what it should.

* **Problem 5.1, effectivity.** Exhibit a `θ ∈ (0, 1)` and an effectively computable `A(θ)`
  such that every pair of `V(θ)` has `c ≤ A(θ)`. Lean's logic is classical, and "effectively
  computable" is not a property of a proposition; what the problem asks for is an explicit pair
  `(θ, A)` together with a proof of `SteeringWord.KernelBound θ A`. Theorem 4.5 gives an `A` for
  every `θ` (`SteeringWord.exists_kernelBound`), but not one that can be computed: its proof
  passes through the Subspace Theorem. Such a pair yields the explicit bound `p_T(k) > C k` for
  `k > A` whenever `θ^(C+2) ≥ 2/3` (`SteeringWord.lt_complexity_of_kernelBound`). To beat the
  slope `41/24` of Theorem 2.10 one needs `θ > (2/3)^(24/89) ≈ 0.896`.
* **Problem 5.2, quantitative form.** Make the analysis of the exceptional subspaces in
  Theorem 4.5 quantitative, and deduce `p_T(k) ≥ k (log k)^δ` for infinitely many `k`, for some
  `δ > 0`. The target is `SteeringWord.QuantitativeSuperlinear`.
* **Problem 5.3, generality.** Prove superlinearity of the steering word of `ξ (p/q)^n` for every
  `ξ ∈ ℚ^×` and all coprime `p > q ≥ 2`: `SteeringWord.SuperlinearGeneral`. The case `ξ = 1`,
  `p = 3`, `q = 2` is Theorem 1.1 (`SteeringWord.tendsto_complexity_div_steering_one_three_two`).
* **Problem 5.4, entropy.** Decide whether the topological entropy
  `h(T) = lim_k log p_T(k) / k` is positive, that is, prove `SteeringWord.PositiveEntropy` or its
  negation. The limit exists by subadditivity (Fekete), and `h(T) > 0` is equivalent to
  `p_T(k) ≥ c^k` for some `c > 1` and all large `k`, which is the form stated; neither fact is
  formalized here. Kopra's trace subshift gives `h(T) ≤ log 3`, and density of `(3/2)^n` modulo
  one would give `h(T) ≥ log (3/2)` (Corollary 1.3); neither is formalized here either.
* **Conjecture A.2.** `p_T(k) = 3^(k+1) - 2^(k+1)` for every `k ≥ 1`:
  `SteeringWord.ExactComplexity`. It would settle Problem 5.4 with `h(T) = log 3`.

## Main definitions

* `SteeringWord.KernelBound θ A`: every pair of `V(θ)` has `c ≤ A` (Problem 5.1).
* `SteeringWord.QuantitativeSuperlinear`: Problem 5.2.
* `SteeringWord.steeringOf ξ p q`: the steering word of `ξ (p/q)^n`;
  `SteeringWord.SuperlinearGeneral`: Problem 5.3.
* `SteeringWord.PositiveEntropy`: Problem 5.4.
* `SteeringWord.ExactComplexity`: Conjecture A.2.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §5 and
Appendix A.
-/

@[expose] public section

namespace SteeringWord

open Function Filter

/-! ### Problem 5.1 -/

/-- Every pair of `V(θ)` has `c ≤ A`. Problem 5.1 asks for an explicit `θ ∈ (0, 1)` and an
explicit `A` with a proof of `KernelBound θ A`. -/
def KernelBound (θ : ℚ) (A : ℕ) : Prop := ∀ p ∈ kernelViolators θ, p.2 ≤ A

/-- Theorem 4.5 gives a bound for every `θ`, ineffectively: this is what Problem 5.1 asks to make
effective. -/
theorem exists_kernelBound {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : ∃ A, KernelBound θ A := by
  obtain ⟨A, hA⟩ := ((finite_kernelViolators hθ0 hθ1).image Prod.snd).bddAbove
  exact ⟨A, fun p hp ↦ hA ⟨p, hp, rfl⟩⟩

/-- **The exchange rate.** An explicit bound `A` for `V(θ)` gives `p_T(k) > C k` for every
`k > A`, whenever `θ^(C+2) ≥ 2/3`. -/
theorem lt_complexity_of_kernelBound {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {C A : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ (C + 2)) (hA : KernelBound θ A) {k : ℕ} (hk : A < k) :
    C * k < complexity t k :=
  lt_complexity_of_forall_le hθ0 hθ1 hθpow hA hk

/-! ### Problem 5.2 -/

/-- **Problem 5.2**: `p_T(k) ≥ k (log k)^δ` for infinitely many `k`, for some `δ > 0`; the shape
of the bound of Bugeaud and Evertse for the complexity of algebraic numbers. -/
def QuantitativeSuperlinear : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ k : ℕ in atTop, (k : ℝ) * Real.log k ^ δ ≤ complexity t k

/-! ### Problem 5.3 -/

/-- The nearest integer to `ξ (p/q)^n`. -/
def mOf (ξ : ℚ) (p q n : ℕ) : ℤ := round (ξ * ((p : ℚ) / q) ^ n)

/-- The **steering word of `ξ (p/q)^n`**: `q m (n + 1) - p m n`, with `m n` the nearest integer to
`ξ (p/q)^n`. For `ξ = 1`, `p = 3`, `q = 2` it is the steering word `t`. -/
def steeringOf (ξ : ℚ) (p q : ℕ) (n : ℕ) : ℤ := q * mOf ξ p q (n + 1) - p * mOf ξ p q n

theorem steeringOf_one_three_two : steeringOf 1 3 2 = t := by
  funext n
  simp [steeringOf, mOf, t, m]

/-- **Problem 5.3**: the steering word of `ξ (p/q)^n` has superlinear complexity for every
`ξ ∈ ℚ^×` and all coprime `p > q ≥ 2`. -/
def SuperlinearGeneral : Prop :=
  ∀ ξ : ℚ, ξ ≠ 0 → ∀ p q : ℕ, 2 ≤ q → q < p → p.Coprime q →
    Tendsto (fun k : ℕ ↦ (complexity (steeringOf ξ p q) k : ℝ) / k) atTop atTop

/-- The case `ξ = 1`, `p = 3`, `q = 2` of Problem 5.3 is Theorem 1.1. -/
theorem tendsto_complexity_div_steering_one_three_two :
    Tendsto (fun k : ℕ ↦ (complexity (steeringOf 1 3 2) k : ℝ) / k) atTop atTop := by
  rw [steeringOf_one_three_two]
  exact tendsto_complexity_div

/-! ### Problem 5.4 and Conjecture A.2 -/

/-- **Problem 5.4**: the steering subshift has positive topological entropy, in the form
`p_T(k) ≥ c^k` for some `c > 1` and all large `k`. The problem is to prove this or its negation. -/
def PositiveEntropy : Prop := ∃ c : ℝ, 1 < c ∧ ∀ᶠ k : ℕ in atTop, c ^ k ≤ complexity t k

/-- **Conjecture A.2**: `p_T(k) = 3^(k+1) - 2^(k+1)` for every `k ≥ 1`. -/
def ExactComplexity : Prop := ∀ k : ℕ, 1 ≤ k → (complexity t k : ℤ) = 3 ^ (k + 1) - 2 ^ (k + 1)

end SteeringWord
