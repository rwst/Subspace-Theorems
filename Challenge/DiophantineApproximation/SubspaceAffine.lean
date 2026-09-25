/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.AffineProd
public import Challenge.DiophantineApproximation.SubspaceAlgebraic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic
import Challenge.DiophantineApproximation.ApproxProd
import Challenge.DiophantineApproximation.ApproximationDomain
import Challenge.ArithmeticHeights.Affine
import Challenge.ArithmeticHeights.Arakelov
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Challenge.DiophantineApproximation.RationalPlaces
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Integer

@[expose] public section
open Finset Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]
open scoped Classical in
theorem exists_finset_submodule_of_integer_of_affineProd_le [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        affineProd S w L x ≤ mulHeight x ^ (-ε) → ∃ W ∈ T, x ∈ W := by
  sorry
end NumberField
