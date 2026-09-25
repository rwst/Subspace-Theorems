/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.DiophantineApproximation.ApproxProd
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
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Localization.Integer

@[expose] public section
open Height IsDedekindDomain Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]
noncomputable def affineProd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v : InfinitePlace K, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
    ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
      (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j))
end NumberField
