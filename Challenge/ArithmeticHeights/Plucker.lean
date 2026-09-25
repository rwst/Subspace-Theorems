/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic

public section
open Module
namespace exteriorPower
section Plucker
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]
@[expose] noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)
end Plucker
end exteriorPower
