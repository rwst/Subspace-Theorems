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

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]
theorem exists_finset_submodule_of_forall_mem_interval (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (U₀ : Submodule K (ι → K)) {m : ℕ}
    (Q : Fin m → ℝ) (hQ : ∀ i, (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q i) {ω : ℝ}
    (hω : 1 ≤ ω)
    (hint : ∀ x ∈ systemSet S w L C c, x ∉ U₀ → ∃ i, Q i ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) ∧
      mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q i ^ ω) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ m * (1 + Real.log ω / Real.log (1 + δ / (2 * Fintype.card ι))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, x ∉ U₀ → ∃ U ∈ T, x ∈ U := by
  sorry
end NumberField
