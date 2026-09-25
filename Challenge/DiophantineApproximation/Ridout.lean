/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.RationalPlaces
public import Challenge.DiophantineApproximation.RothInfinity
public import Challenge.DiophantineApproximation.RothRational

@[expose] public section
open Height NumberField AbsoluteValue OnePoint IntermediateField
namespace Rat
variable {F : Type*} [Field F] [NumberField F]
theorem finite_setOf_apply_intCast_sub_le (p : Nat.Primes) (w : AbsoluteValue F ℝ)
    (hw : w.LiesOver (AbsoluteValue.padic (p : ℕ))) (α : F) {ε : ℝ} (hε : 0 < ε) :
    {n : ℤ | w ((n : F) - α) ≤ |(n : ℝ)| ^ (-1 - ε)}.Finite := by
  sorry
theorem finite_setOf_ridout {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) (S₁ S₂ : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    {β : ℚ | |ξ - (β : ℝ)| * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite := by
  sorry
end Rat
end
