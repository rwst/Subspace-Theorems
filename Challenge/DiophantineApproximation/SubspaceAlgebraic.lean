/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.ApproxProd
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Pi
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
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.RingTheory.RamificationInertia.Basic
public import Challenge.DiophantineApproximation.SubspaceTheorem
import Challenge.ArithmeticHeights.Arakelov
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure

@[expose] public section
open Finset Height Module NumberField
namespace NumberField
variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι]
section Extension
variable {F : Type*} [Field F] [NumberField F] [Algebra K F]
open scoped Classical in
theorem exists_finset_submodule_of_approxProd_le_extension [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  sorry
end Extension
end NumberField
