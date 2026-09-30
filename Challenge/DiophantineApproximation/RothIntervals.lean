/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Absolute
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.AbsoluteValue.Equivalence
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
import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Normed.Ring.WithAbs
import Challenge.DiophantineApproximation.RationalPlaces
public import Challenge.DiophantineApproximation.RothTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Challenge.DiophantineApproximation.RothInfinity

@[expose] public section
open Height Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
noncomputable def mobiusShift (s : ℕ) : ℝ := Real.log (2 * ((s : ℝ) + 1))
noncomputable def rothOnePointBound (s r nF nK : ℕ) (Ht logC κ : ℝ) : ℝ :=
  max (max ((1 + Ht + s * mobiusShift s) / rothDelta ((κ + 2) / 2) s r nF)
      (Real.log 16 / ((1 - (s : ℝ) / rothClassSize ((κ + 2) / 2) s) * ((κ + 2) / 2) - 1 - 1)))
    ((2 * s * Real.log 2 + 4 * nF * (Ht + s * mobiusShift s) + logC + κ * nK * mobiusShift s)
      / ((κ - 2) / 2 * nK))
end NumberField
