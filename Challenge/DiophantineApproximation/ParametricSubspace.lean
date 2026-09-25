/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.ApproximationDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Arakelov
public import Challenge.ArithmeticHeights.Plucker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
import Challenge.ArithmeticHeights.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dual.Basis
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
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.NumberTheory.NumberField.Units.Regulator
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
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.Order.Northcott
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.MvPolynomial.Division
public import Challenge.ArithmeticHeights.Polynomial
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Challenge.ArithmeticHeights.BombieriVaalerEntries
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
open Filter Finset Module NumberField NumberField.mixedEmbedding exteriorPower
namespace NumberField
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
open scoped Classical in
theorem exists_finset_submodule_forall_approxDomain_subset [Nontrivial ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    (hc : approxWeight Sfin c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ Q₀ : ℝ, ∀ Q ≥ Q₀, ∃ W ∈ T, approxDomain Sfin L c Q ⊆ W := by
  sorry
end NumberField
