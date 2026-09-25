/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

public section
namespace NumberField
open Finset Function Height Real
variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']
@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
end NumberField
end
