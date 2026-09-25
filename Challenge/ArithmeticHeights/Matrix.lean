/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Arakelov
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Challenge.ArithmeticHeights.Affine
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section
open Finset Function Height AdmissibleAbsValues Real
namespace Matrix
variable {K : Type*} [Field K] [AdmissibleAbsValues K] {m n p m' n' : Type*}
@[expose] noncomputable def mulHeight (A : Matrix m n K) : ℝ :=
  Height.mulHeight fun q : m × n ↦ A q.1 q.2
end Matrix
end
