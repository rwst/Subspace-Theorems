/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!
# Base change of a quotient module

If `h : M → N` is a base change by `S`, then so is the induced map `M ⧸ P → N ⧸ S·h(P)` for every
submodule `P` of `M` (`IsBaseChange.quotient`), by right exactness of the tensor product.
-/

@[expose] public section

namespace IsBaseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] (h : M →ₗ[R] N) (P : Submodule R M)

/-- The map `M ⧸ P → N ⧸ S·h(P)` induced by `h`. -/
noncomputable def quotientMap : M ⧸ P →ₗ[R] N ⧸ Submodule.span S (h '' P) :=
  P.liftQ (((Submodule.span S (h '' P)).mkQ.restrictScalars R) ∘ₗ h) fun x hx ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

@[simp]
theorem quotientMap_mk (x : M) :
    quotientMap S h P (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x) :=
  rfl

variable {S h} in
/-- **Base change of a quotient**: if `h : M → N` is a base change by `S`, so is the induced map
`M ⧸ P → N ⧸ S·h(P)`. -/
theorem quotient (hb : IsBaseChange S h) : IsBaseChange S (quotientMap S h P) := by
  refine IsBaseChange.of_right_exact S (TensorProduct.mk R S P 1) h (quotientMap S h P)
    (f := P.subtype) (g := P.mkQ) (f' := (h ∘ₗ P.subtype).liftBaseChange S)
    (g' := (Submodule.span S (h '' P)).mkQ) ?_ ?_ (TensorProduct.isBaseChange R P S) hb
    (LinearMap.exact_subtype_mkQ P) (Submodule.mkQ_surjective P) ?_
    (Submodule.mkQ_surjective _)
  · ext x
    simp
  · ext x
    rfl
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, LinearMap.range_liftBaseChange,
      LinearMap.range_comp, Submodule.range_subtype, Submodule.map_coe]

end IsBaseChange
