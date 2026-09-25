/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Arakelov
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff

public section
namespace MvPolynomial
open Height
section General
variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}
@[expose] noncomputable def mulHeight (p : MvPolynomial σ K) : ℝ := Finsupp.mulHeight p.coeff
end General
end MvPolynomial
end
