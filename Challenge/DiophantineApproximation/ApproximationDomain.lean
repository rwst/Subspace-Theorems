/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

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
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Challenge.ArithmeticHeights.Absolute
import Challenge.ArithmeticHeights.Arakelov
import Challenge.ArithmeticHeights.Plucker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Challenge.ArithmeticHeights.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section
open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix Filter
  Topology
open scoped Pointwise
namespace NumberField
variable {K : Type*} [Field K] [NumberField K] {ι : Type*}
def approxDomain (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Set (ι → K) :=
  {x | (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    (∀ v ∈ Sfin, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ Sfin → ∀ j : ι, v (x j) ≤ 1}
variable [Fintype ι]
noncomputable def approxWeight (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ℝ :=
  ∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ Sfin, ∑ i, c v.1 i
end NumberField
