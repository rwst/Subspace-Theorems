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
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic
public import Challenge.DiophantineApproximation.RothTheorem
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section
open Height OnePoint
namespace AbsoluteValue
variable {F : Type*} [Field F] (W : AbsoluteValue F ℝ)
noncomputable def onePointApprox : OnePoint F → F → ℝ
  | ∞, β => (max 1 (W β))⁻¹
  | (a : F), β => min 1 (W (β - a))
end AbsoluteValue
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
open AbsoluteValue
theorem finite_setOf_prod_onePointApprox_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  sorry
end NumberField
end
