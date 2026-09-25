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
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section
open Asymptotics Filter Height Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
theorem finite_setOf_prod_min_one_le_of_isLittleO (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) (α : ℕ → AbsoluteValue K ℝ → F) (β : ℕ → K)
    (hα : (fun j ↦ 1 + ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1))
      =o[atTop] fun j ↦ absLogHeight₁ (β j)) :
    {j : ℕ | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1))
          ≤ mulHeight₁ (β j) ^ (-κ)}.Finite := by
  sorry
end NumberField
end
