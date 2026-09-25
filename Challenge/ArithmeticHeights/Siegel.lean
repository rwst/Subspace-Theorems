/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Absolute
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.SiegelsLemma

public section
open Finset Height Matrix
attribute [local instance] Matrix.seminormedAddCommGroup
namespace Int.Matrix
variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
theorem exists_ne_zero_mulVec_eq_zero_iSup_abs_le {B : ℤ} (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ B)
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    ∃ x : β → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ((⨆ j, |x j| : ℤ) : ℝ) ≤ ((Fintype.card β : ℝ) * B) ^
        ((Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α)) := by
  sorry
end Int.Matrix
namespace NumberField
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
open scoped Classical in
theorem exists_forall_exists_ne_zero_mulVec_eq_zero_absMulHeight_le (K : Type*) [Field K]
    [NumberField K] :
    ∃ C : ℝ, ∀ (p q : ℕ) (a : Matrix (Fin p) (Fin q) (𝓞 K)) (A : ℝ), a ≠ 0 → 0 < p → p < q →
      (∀ k l, house ((a k l : K)) ≤ A) →
      ∃ ξ : Fin q → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        absMulHeight (fun l ↦ ((ξ l : K))) ≤ C * ((C * q * A) ^ ((p : ℝ) / (q - p))) := by
  sorry
end NumberField
