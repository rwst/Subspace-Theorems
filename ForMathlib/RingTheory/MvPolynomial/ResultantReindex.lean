/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantDegree
public import ForMathlib.RingTheory.MvPolynomial.Splitting

/-!
# Reindexing resultant forms

The resultant form `res_d(I)` does not depend on how the generic forms are numbered: for
`f : κ' ≃ κ`, renaming the coefficients of `res_{d ∘ f}(I)` along `f` gives `res_d(I)` up to a
unit (`MvPolynomial.associated_reindexEquiv_resForm`). The proof is the base change of the
pieces along the isomorphism `K[d ∘ f] ≃ K[d]`, a trivial localization.
-/

@[expose] public section

namespace MvPolynomial

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ κ' : Type u} [Finite κ]

/-- **Reindexing the generic forms** along `f : κ' ≃ κ`: `res_d(I)` is the image of
`res_{d ∘ f}(I)` up to a unit, for `deg H_I + 1 ≤ #κ`. -/
theorem associated_reindexEquiv_resForm (f : κ' ≃ κ) (d : κ → ι → ℕ)
    (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) :
    Associated (reindexEquiv b K f d (resForm b K (d ∘ f) I)) (resForm b K d I) := by
  have := Finite.of_equiv _ f.symm
  set e := reindexEquiv b K f d
  have : IsLocalization (⊥ : Submonoid (MvPolynomial (GenericVar b (d ∘ f)) K))
      (MvPolynomial (GenericVar b (d ∘ f)) K) := IsLocalization.of_le_isUnit bot_le
  have hloc := IsLocalization.isLocalization_of_base_ringEquiv ⊥
    (MvPolynomial (GenericVar b (d ∘ f)) K) e
  let : Algebra (MvPolynomial (GenericVar b d) K) (MvPolynomial (GenericVar b (d ∘ f)) K) :=
    ((RingHom.id (MvPolynomial (GenericVar b (d ∘ f)) K)).comp e.symm.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (GenericVar b d) K)
      (MvPolynomial (GenericVar b (d ∘ f)) K) p = e.symm p := fun _ ↦ rfl
  have hS : (⊥ : Submonoid (MvPolynomial (GenericVar b (d ∘ f)) K)).map e ≤ nonZeroDivisors _ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submonoid.mem_bot] at hx
    subst hx
    rw [map_one]
    exact one_mem _
  have hG : (genericIdeal K b d I).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (MvPolynomial (GenericVar b (d ∘ f)) K))) = genericIdeal K b (d ∘ f) I := by
    rw [← map_reindexEquiv_genericIdeal f d, Ideal.map_map]
    convert Ideal.map_id _
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun x ↦ e.symm_apply_eq.mpr rfl
  have hdim' : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ' := by
    rwa [Nat.card_congr f]
  obtain ⟨⟨k₀, hk₀⟩, -⟩ := associated_resForm_prod (d := d) hb hI hdim
  obtain ⟨⟨k₁, hk₁⟩, -⟩ := associated_resForm_prod (d := d ∘ f) hb hI hdim'
  set k := k₀ ⊔ k₁
  have h0 := hk₀ k le_sup_left
  have hann : Module.annihilator (MvPolynomial (GenericVar b d) K) (genPiece b K d I k) ≠ ⊥ :=
    fun h ↦ resForm_ne_zero hb hI hdim
      (h0.symm.eq_zero_iff.mpr (Module.charForm_of_annihilator_eq_bot h))
  have hbc := gradedPiece.isBaseChange (R' := MvPolynomial (GenericVar b (d ∘ f)) K)
    (genericIdeal K b d I) (isWeightedHomogeneous_genericIdeal hI) k
  have eq : gradedPiece b ((genericIdeal K b d I).map (map (algebraMap
      (MvPolynomial (GenericVar b d) K) (MvPolynomial (GenericVar b (d ∘ f)) K)))) k
      ≃ₗ[MvPolynomial (GenericVar b (d ∘ f)) K] genPiece b K (d ∘ f) I k :=
    Submodule.quotEquivOfEq _ _ (by rw [hG])
  have hassoc := Module.associated_charForm_of_isBaseChange _ hS
    (hbc.comp (IsBaseChange.ofEquiv eq)) hann
  have h1 : Associated (resForm b K (d ∘ f) I) (e.symm (resForm b K d I)) :=
    (hk₁ k le_sup_right).symm.trans (hassoc.trans (h0.map e.symm.toRingHom))
  simpa using h1.map e.toRingHom

end MvPolynomial
