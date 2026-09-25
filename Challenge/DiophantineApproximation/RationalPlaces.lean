/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Height.NumberField

@[expose] public section
open NumberField Height
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
end
