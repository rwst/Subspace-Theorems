/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Arakelov
public import Challenge.ArithmeticHeights.Plucker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
import Challenge.ArithmeticHeights.Matrix
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.NumberTheory.Height.NumberField
public import Challenge.DiophantineApproximation.ApproximationDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Challenge.DiophantineApproximation.RationalPlaces
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.House
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
open Finset Module Set
namespace Module.Dual
variable {F : Type*} [Field F] {ι κ : Type*}
def IsGeneralPosition (F : Type*) [Field F] {ι κ : Type*} (B : Finset κ)
    (M : κ → Dual F (ι → F)) : Prop :=
  ∀ s ⊆ B, s.card ≤ Nat.card ι → LinearIndependent F fun k : s ↦ M k
end Module.Dual
