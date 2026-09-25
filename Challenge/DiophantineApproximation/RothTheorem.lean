/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Challenge.ArithmeticHeights.BombieriVaalerRelative
public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Polynomial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Nat.Choose.Bounds
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
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.AbsoluteValue.Equivalence
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
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Challenge.ArithmeticHeights.Arakelov
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.Analysis.Normed.Ring.WithAbs

@[expose] public section
open Height MvPolynomial Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
noncomputable def rothEps (κ : ℝ) : ℝ := (1 / 2 - 1 / κ) / 16
noncomputable def rothClassSize (κ : ℝ) (s : ℕ) : ℕ := ⌈2 * (s : ℝ) / (1 / 2 - 1 / κ)⌉₊ + 1
noncomputable def rothChainLength (κ : ℝ) (s r : ℕ) : ℕ :=
  ⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * rothEps κ ^ 2)⌉₊
noncomputable def rothRatio (κ : ℝ) (s r : ℕ) : ℝ := 2 / rothEps κ ^ 2 ^ rothChainLength κ s r
theorem finite_setOf_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  sorry
end NumberField
end
