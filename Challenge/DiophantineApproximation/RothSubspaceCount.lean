/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.RothIntervals
public import Challenge.DiophantineApproximation.SubspaceIntervals
import Challenge.DiophantineApproximation.ApproxProd
import Challenge.ArithmeticHeights.Arakelov
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.NumberTheory.Real.Irrational
import Challenge.DiophantineApproximation.RothInfinity
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
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
noncomputable def systemRothThreshold (s r nF nK : ℕ) (δ H : ℝ) : ℝ :=
  Real.exp (((r * s : ℕ) : ℝ) * (max (rothOnePointBound s r nF nK (2 * (s : ℝ) * Real.log H)
      ((s : ℝ) * (Real.log 32 + 8 * (nF : ℝ) * Real.log H)) (2 + δ))
    (max (2 * mobiusShift s
        + (s : ℝ) * (((nF : ℝ) + 1) * Real.log 2 + 6 * (nF : ℝ) * Real.log H) / nK)
      (mobiusShift s + 4 / δ * Real.log 2)) + mobiusShift s + 1)
    + (s : ℝ) * (((nF : ℝ) + 1) * Real.log 2 + 6 * (nF : ℝ) * Real.log H) / nK)
theorem exists_finset_submodule_of_card_eq_two {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 2) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ ((Fintype.card (InfinitePlace K) + S.card + 1 : ℕ) : ℝ) +
        ((rothChainLength (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F) *
          (rothClassSize (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) +
            (Fintype.card (InfinitePlace K) + S.card)).choose
              (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
          (1 + Real.log (3 * ((finrank K F * (Fintype.card (InfinitePlace K) + S.card) : ℕ) : ℝ) *
            rothRatio (2 + δ / 2) (Fintype.card (InfinitePlace K) + S.card) (finrank K F)) /
            Real.log (1 + δ / 4)) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        systemRothThreshold (Fintype.card (InfinitePlace K) + S.card) (finrank K F)
          (finrank ℚ F) (finrank ℚ K) δ H ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) →
        ∃ U ∈ T, x ∈ U := by
  sorry
end NumberField
