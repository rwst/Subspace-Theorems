/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Challenge.ArithmeticHeights.Absolute
public import Challenge.ArithmeticHeights.Polynomial
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.RingTheory.MvPolynomial.Basic

public section
open Finsupp Height Module
namespace Finsupp
variable {σ : Type*}
instance instFiniteSubtypeDegreeLE [Finite σ] (D : ℕ) : Finite {m : σ →₀ ℕ // m.degree ≤ D} :=
  (Finsupp.finite_of_degree_le D).to_subtype
noncomputable instance instFintypeSubtypeDegreeLE [Finite σ] (D : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree ≤ D} :=
  Fintype.ofFinite _
end Finsupp
