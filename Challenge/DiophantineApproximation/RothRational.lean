/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.IrrationalityExponent
public import Challenge.DiophantineApproximation.RationalPlaces
public import Challenge.DiophantineApproximation.RothTheorem
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

@[expose] public section
open Height NumberField IntermediateField Filter
open scoped ENNReal NNReal
theorem Real.irrationalityExponent_eq_two {ξ : ℝ} (hirr : Irrational ξ)
    (halg : IsAlgebraic ℚ ξ) : irrationalityExponent ξ = 2 := by
  sorry
end
