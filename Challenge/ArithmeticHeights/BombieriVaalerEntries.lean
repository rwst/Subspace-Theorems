/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Arakelov
public import Challenge.ArithmeticHeights.Plucker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Challenge.ArithmeticHeights.Matrix
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Fintype.Order
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Basic.Real.Pointwise
import Mathlib.LinearAlgebra.Matrix.Adjugate

public section
open Finset Matrix Module NumberField Real
namespace NumberField
variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
open scoped Classical in
theorem exists_ne_zero_mem_ker_absMulHeight_le (A : Matrix (Fin m) ι K)
    (hm : A.rank < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^
              ((A.rank : ℝ) / (Fintype.card ι - A.rank)) := by
  sorry
end NumberField
end
