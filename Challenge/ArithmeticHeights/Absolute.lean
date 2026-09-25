/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Arakelov
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.Height.Projectivization

public section
namespace NumberField
open Function IntermediateField Module
section Def
variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Finite ι]
open scoped Classical in
@[expose] noncomputable def absMulHeight (x : ι → K) : ℝ :=
  if hx : ∀ i, IsIntegral ℚ (x i) then
    haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range x)) :=
      finiteDimensional_adjoin fun y hy ↦ by obtain ⟨i, rfl⟩ := hy; exact hx i
    haveI : NumberField (adjoin ℚ (Set.range x)) := {}
    Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))
      ^ ((finrank ℚ (adjoin ℚ (Set.range x)) : ℝ))⁻¹
  else 1
end Def
end NumberField
end
