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
public import Challenge.DiophantineApproximation.RothInfinity
public import Challenge.DiophantineApproximation.SubspaceIntervals
import Challenge.DiophantineApproximation.ApproxProd
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.NumberTheory.Real.Irrational

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
theorem exists_finset_submodule_of_card_eq_two {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 2) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ X₀ : ℝ, ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ ((Fintype.card (InfinitePlace K) + S.card + 1 : ℕ) : ℝ) +
        ((rothChainLength (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F) *
          (rothClassSize (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) +
            (Fintype.card (InfinitePlace K) + S.card)).choose
              (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
          (1 + Real.log (3 * ((finrank K F * (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
            rothRatio (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F)) /
            Real.log (1 + δ / 4)) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, X₀ ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
        ∃ U ∈ T, x ∈ U := by
  sorry
end NumberField
