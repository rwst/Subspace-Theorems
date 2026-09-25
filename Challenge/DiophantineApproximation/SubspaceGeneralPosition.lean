/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.SubspaceAlgebraic
public import Challenge.DiophantineApproximation.GeneralPosition
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Order.Northcott
import Mathlib.NumberTheory.Height.NumberField
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
import Challenge.DiophantineApproximation.RationalPlaces
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Integer

@[expose] public section
open Finset Height Module Module.Dual
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F] {ι κ : Type*}
noncomputable def generalProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ^ v.mult) *
    ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)
variable [NumberField F] [Fintype ι]
open scoped Classical in
theorem exists_finset_submodule_of_generalProd_le [Nontrivial ι] [Finite κ]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        generalProd Sinf Sfin w B L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  sorry
end NumberField
