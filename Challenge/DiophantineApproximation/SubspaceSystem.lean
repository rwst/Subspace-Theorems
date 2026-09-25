/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Affine
public import Challenge.DiophantineApproximation.AffineProd
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.Height.NumberField
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
import Challenge.DiophantineApproximation.SubspaceAffine
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Challenge.ArithmeticHeights.Absolute
import Challenge.DiophantineApproximation.RationalPlaces

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]
noncomputable def systemPlace (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ S → AbsoluteValue K ℝ
  | .inl v => v.1
  | .inr v => (FinitePlace.mk v.1).1
noncomputable def systemMult (S : Finset (HeightOneSpectrum (𝓞 K))) : InfinitePlace K ⊕ S → ℕ
  | .inl v => v.mult
  | .inr _ => 1
noncomputable def systemAbs (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (p : InfinitePlace K ⊕ S) (a : F) : ℝ :=
  w (systemPlace S p) a ^ systemMult S p
noncomputable def systemValue (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (p : InfinitePlace K ⊕ S) (i : ι) (x : ι → K) : ℝ :=
  systemAbs S w p (L (systemPlace S p) i fun j ↦ algebraMap K F (x j))
def systemSet (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (C : InfinitePlace K ⊕ S → ℝ)
    (c : InfinitePlace K ⊕ S → ι → ℝ) : Set (ι → K) :=
  {x | (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
    ∀ p i, systemValue S w L p i x ≤ C p * mulHeightAff x ^ c p i}
noncomputable def systemWeight {S : Finset (HeightOneSpectrum (𝓞 K))}
    (c : InfinitePlace K ⊕ S → ι → ℝ) : ℝ :=
  ∑ p, ∑ i, c p i
noncomputable def systemConst {S : Finset (HeightOneSpectrum (𝓞 K))}
    (C : InfinitePlace K ⊕ S → ℝ) : ℝ :=
  ∏ p, C p
noncomputable def systemDet (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) :
    ℝ :=
  ∏ p, systemAbs S w p (LinearMap.det (LinearMap.pi (L (systemPlace S p))))
noncomputable def systemExponent (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ S → ℝ
  | .inl v => v.mult / finrank ℚ K
  | .inr _ => 0
structure IsNormalizedSystem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (C : InfinitePlace K ⊕ S → ℝ) (c : InfinitePlace K ⊕ S → ι → ℝ) (H : ℝ) (D R : ℕ)
    (δ : ℝ) : Prop where
  /-- The coefficients have absolute height at most `H`. -/
  height_le : ∀ p i j, absMulHeight₁ (L (systemPlace S p) i (Pi.basisFun F ι j)) ≤ H
  /-- The coefficients have degree at most `D` over `K`. -/
  degree_le : ∀ p i j, (minpoly K (L (systemPlace S p) i (Pi.basisFun F ι j))).natDegree ≤ D
  /-- At most `R` distinct forms occur. -/
  ncard_le : (Set.range fun q : (InfinitePlace K ⊕ S) × ι ↦ L (systemPlace S q.1) q.2).ncard ≤ R
  /-- The constants are positive. -/
  const_pos : ∀ p, 0 < C p
  /-- The product of the constants is at most `(∏ |det L v|_v) ^ (1 / n)`. -/
  const_le : systemConst C ≤ systemDet S w L ^ (Fintype.card ι : ℝ)⁻¹
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  /-- The weight is at most `-δ`. -/
  weight_le : systemWeight c ≤ -δ
  /-- No exponent exceeds the normalized local degree. -/
  exponent_le : ∀ p i, c p i ≤ systemExponent S p
  /-- Some exponent at every place attains it. -/
  exists_exponent_eq : ∀ p, ∃ i, c p i = systemExponent S p
def IsLargeSolution (H δ : ℝ) (x : ι → K) : Prop :=
  max (2 * H) ((Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ)) ≤
    mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)
open scoped Classical in
theorem exists_finset_submodule_of_systemWeight_neg [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {C : InfinitePlace K ⊕ S → ℝ} (hC : ∀ p, 0 ≤ C p) {c : InfinitePlace K ⊕ S → ι → ℝ}
    (hc : systemWeight c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, x ≠ 0 → ∃ W ∈ T, x ∈ W := by
  sorry
end NumberField
