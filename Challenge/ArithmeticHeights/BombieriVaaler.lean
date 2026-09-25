/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Arakelov
public import Challenge.ArithmeticHeights.Plucker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
import Challenge.ArithmeticHeights.Matrix
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.RingTheory.Localization.Integer
public import Challenge.ArithmeticHeights.Siegel

public section
open Finset MeasureTheory Module Submodule Matrix exteriorPower
open scoped ENNReal Pointwise
namespace Int.Matrix
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
noncomputable def minorGcd (A : _root_.Matrix (Fin m) ι ℤ) : ℤ :=
  (univ : Finset (Set.powersetCard ι m)).gcd (plucker m A.row)
theorem exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ x : Fin (Fintype.card ι - m) → (ι → ℤ), LinearIndependent ℤ x ∧ (∀ l, A *ᵥ x l = 0) ∧
      (∏ l, ((⨆ i, |x l i| : ℤ) : ℝ)) ≤
        Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
  sorry
theorem exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hmn : m < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ((⨆ i, |x i| : ℤ) : ℝ) ≤
        (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ)) ^
          (((Fintype.card ι : ℝ) - m)⁻¹) := by
  sorry
end Int.Matrix
