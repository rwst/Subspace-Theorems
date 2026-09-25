/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.SubspaceSystem
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
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
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Integer
import Challenge.ArithmeticHeights.Absolute
import Mathlib.LinearAlgebra.Dual.Defs
import Challenge.DiophantineApproximation.ApproximationDomain
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Challenge.ArithmeticHeights.Plucker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Challenge.ArithmeticHeights.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Challenge.DiophantineApproximation.RationalPlaces
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.House
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]
theorem exists_finset_submodule_of_not_isLargeSolution (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
        4 * Fintype.card ι * Real.log (Real.log (4 * H))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, ¬ IsLargeSolution H δ x → ∃ U ∈ T, x ∈ U := by
  sorry
end NumberField
namespace Rat
open NumberField
variable {F : Type*} [Field F] [NumberField F] [Algebra ℚ F] {ι : Type*} [Fintype ι]
theorem exists_finset_submodule_of_not_isLargeSolution (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (w : AbsoluteValue ℚ ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual F (ι → F)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)),
      (T.card : ℝ) ≤ δ⁻¹ * (10 ^ (3 * Fintype.card ι) +
        4 * Fintype.card ι * Real.log (Real.log (4 * H))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, ¬ IsLargeSolution H δ x → ∃ U ∈ T, x ∈ U := by
  sorry
end Rat
