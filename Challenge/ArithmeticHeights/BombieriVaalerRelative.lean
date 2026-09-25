/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.BombieriVaalerEntries
public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Arakelov
public import Challenge.ArithmeticHeights.Plucker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Challenge.ArithmeticHeights.Matrix
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
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
variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
open scoped Classical in
theorem exists_linearIndependent_mem_ker_prod_absMulHeight_le (A : Matrix (Fin m) ι F)
    (hmn : finrank K F * m < Fintype.card ι) :
    ∃ x : Fin (Fintype.card ι - finrank K F * m) → (ι → K),
      LinearIndependent K x ∧
      (∀ l, A.mulVec (fun j ↦ algebraMap K F (x l j)) = 0) ∧
      (∀ l j, IsIntegral ℤ (x l j)) ∧
      (∏ l, absMulHeight (x l)) ≤
        |(NumberField.discr K : ℝ)| ^
            ((Fintype.card ι - finrank K F * m : ℝ) / (2 * finrank ℚ K))
          * ∏ i, (arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ finrank K F := by
  sorry
end NumberField
end
