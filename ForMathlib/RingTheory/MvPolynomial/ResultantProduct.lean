/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantSection

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Separation of variables for resultant forms

Specializing the first generic form `U₀` of multidegree `e + e'` to a product `V W` of generic
forms of multidegrees `e` and `e'` sends `res_d(I)` to `res_{(e, d')}(I) · res_{(e', d')}(I)`, up
to a nonzero constant (G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon
(eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001), Prop. 3.5, two-factor
form; iterating gives Rémond's product of linear forms).

Rémond compares zero sets over an algebraic closure. Here, as for Prop. 3.6: the pieces of
`(I, VW, U_1, …)` are a base change of those of `I[d]`, so `ω(res_d(I))` divides their `χ`;
the exact sequence of multiplication by `V` bounds that `χ` by the product of the `χ` for
`(I, V, …)` and `(I, W, …)`, which are the resultant forms with dummy variables adjoined; and
both sides have the same degree in every group of variables (Prop. 3.4).

## Main statements

* `MvPolynomial.exists_rename_eq_of_dvd`: divisors of polynomials in a subset of the variables
  lie in that subset.
* `MvPolynomial.productMap`: the specialization `ω : K[d] → K[(e', e, d')]`, `U₀ ↦ V W`.
* `MvPolynomial.associated_charForm_rename`: adjoining dummy variables does not change `χ`.
* `MvPolynomial.charForm_dvd_mul_of_mul`: `χ` of a section by `V W` divides the product.
* `MvPolynomial.associated_productMap_resForm`: **Prop. 3.5**, two factors.
* `MvPolynomial.exists_productMap_resForm_eq`: the same, with the constant `λ ∈ Kˣ` explicit.
-/

@[expose] public section

open scoped Finset

namespace MvPolynomial

section Rename

variable {τ υ R : Type*} [CommRing R] [IsDomain R]

/-- **Divisors of polynomials in fewer variables**: over a domain, a divisor of `rename f a`,
`a ≠ 0`, is itself the image of a polynomial under `rename f`. -/
theorem exists_rename_eq_of_dvd {f : τ → υ} (hf : Function.Injective f)
    {a : MvPolynomial τ R} (ha : a ≠ 0) {c' : MvPolynomial υ R} (h : c' ∣ rename f a) :
    ∃ c, c' = rename f c := by
  classical
  obtain ⟨q, hq⟩ := h
  have hra : rename f a ≠ 0 := (map_ne_zero_iff _ (rename_injective f hf)).mpr ha
  have hc' : c' ≠ 0 := left_ne_zero_of_mul (hq ▸ hra)
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hra)
  have hvars : (c'.vars : Set υ) ⊆ Set.range f := by
    intro x hx
    have hx' : x ∈ (rename f a).vars := by
      rw [hq, mem_vars_iff_degreeOf_ne_zero, degreeOf_mul_eq hc' hq0]
      have := mem_vars_iff_degreeOf_ne_zero.mp hx
      omega
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (vars_rename f a hx')
    exact ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := exists_rename_eq_of_vars_subset_range c' f hf hvars
  exact ⟨c, hc.symm⟩

end Rename

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type*} [Field K]

section Generic

variable {R : Type*} [CommRing R] {κ : Type*} {d : κ → ι → ℕ}

/-- The coefficients of a generic form are forms of degree one in its own group. -/
theorem isWeightedHomogeneous_coeff_genericForm [DecidableEq κ] (l : κ) (x : κ)
    (a : σ →₀ ℕ) :
    IsWeightedHomogeneous (groupWeight b d x) ((genericForm R b d l).coeff a)
      (if l = x then 1 else 0) := by
  classical
  simp only [genericForm, coeff_sum, coeff_monomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun m _ ↦ ?_
  by_cases h : (m : σ →₀ ℕ) = a
  · simp only [h, ↓reduceIte]
    convert isWeightedHomogeneous_X R (groupWeight b d x) ⟨l, m⟩ using 1
    unfold groupWeight
    split_ifs <;> simp_all
  · simp only [h, ↓reduceIte]
    exact isWeightedHomogeneous_zero _ _ _

theorem isWeightedHomogeneous_coeff_mul_genericForm [DecidableEq κ] (l l' x : κ)
    (a : σ →₀ ℕ) :
    IsWeightedHomogeneous (groupWeight b d x)
      ((genericForm R b d l * genericForm R b d l').coeff a)
      ((if l = x then 1 else 0) + (if l' = x then 1 else 0)) := by
  classical
  rw [coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun p _ ↦
    (isWeightedHomogeneous_coeff_genericForm l x p.1).mul
      (isWeightedHomogeneous_coeff_genericForm l' x p.2)

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- Every polynomial is homogeneous of degree `0` for the zero weight. -/
theorem isWeightedHomogeneous_zero_weight {τ : Type*} (p : MvPolynomial τ R) :
    IsWeightedHomogeneous (0 : τ → ℕ) p 0 := fun c _ ↦ by
  simp [Finsupp.weight_apply]

/-- A ring hom sending the coefficients `u^{(l)}_m` to the coefficients of a form `P` of
multidegree `d l` sends `U_l` to `P`. -/
theorem map_genericForm_of_forall {S : Type*} [CommRing S]
    (φ : MvPolynomial (GenericVar b d) R →+* S) (l : κ) {P : MvPolynomial σ S}
    (hP : IsWeightedHomogeneous (multiWeight b) P (d l))
    (hφ : ∀ m : blockMonomials b (d l), φ (X ⟨l, m⟩) = P.coeff (m : σ →₀ ℕ)) :
    map φ (genericForm R b d l) = P := by
  classical
  refine MvPolynomial.ext _ _ fun α ↦ ?_
  simp only [genericForm, map_sum, map_monomial, hφ, coeff_sum, coeff_monomial]
  rw [Finset.sum_coe_sort (blockMonomials b (d l)) fun x ↦ if x = α then P.coeff x else 0,
    Finset.sum_ite_eq']
  by_cases hα : α ∈ blockMonomials b (d l)
  · simp only [hα, ↓reduceIte]
  · simp only [hα, ↓reduceIte]
    by_contra h0
    exact hα (mem_blockMonomials.mpr (hP (Ne.symm h0)))

end Generic

section Diff

variable {κ : Type*}

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem diffPoly_erase_none [Fintype κ] [DecidableEq κ] (d₀ : Option κ → ι → ℕ)
    (H : MvPolynomial ι ℚ) :
    diffPoly d₀ (Finset.univ.erase none) H = diffPoly (fun l ↦ d₀ (some l)) Finset.univ H := by
  have : Finset.univ.erase none = (Finset.univ : Finset κ).map Function.Embedding.some := by
    ext (_ | l) <;> simp
  rw [this, diffPoly_map]
  rfl

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- **Additivity of the degree of Prop. 3.4 in the first multidegree**: `#s` differences of
`Δ_{e+e'} H` are those of `Δ_e H` plus those of `Δ_{e'} H`, when `deg H ≤ #s + 1`. -/
theorem diffPoly_sub_shiftPoly_add [Finite ι] (d' : κ → ι → ℕ) (s : Finset κ) (e e' : ι → ℕ)
    {H : MvPolynomial ι ℚ} (hH : H.totalDegree ≤ #s + 1) :
    diffPoly d' s (H - shiftPoly (e + e') H) =
      diffPoly d' s (H - shiftPoly e H) + diffPoly d' s (H - shiftPoly e' H) := by
  set G := H - shiftPoly e' H
  have hid : H - shiftPoly (e + e') H = (H - shiftPoly e H) + G - (G - shiftPoly e G) := by
    simp only [G, shiftPoly_sub, shiftPoly_shiftPoly]
    ring
  have h0 : diffPoly d' s (G - shiftPoly e G) = 0 := by
    have hG : G.totalDegree ≤ H.totalDegree - 1 := totalDegree_sub_shiftPoly_le e' H
    by_cases hG0 : G.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C.mp hG0, shiftPoly_C, sub_self, diffPoly_zero]
    · refine diffPoly_eq_zero_of_totalDegree_lt d' ?_
      have : (G - shiftPoly e G).totalDegree ≤ G.totalDegree - 1 :=
        totalDegree_sub_shiftPoly_le e G
      omega
  rw [hid, diffPoly_sub, h0, sub_zero]
  simp only [diffPoly, ← Finset.sum_add_distrib, shiftPoly, map_add, smul_add]

end Diff

section Indices

variable {κ : Type*} (e e' : ι → ℕ) (d' : κ → ι → ℕ)

/-- The index `(e + e', d')`. -/
def sumIndex : Option κ → ι → ℕ := fun y ↦ y.elim (e + e') d'

/-- The index `(e, d')`. -/
def leftIndex : Option κ → ι → ℕ := fun y ↦ y.elim e d'

/-- The index `(e', e, d')` of the target ring: `none` is `W`, `some none` is `V`. -/
def pairIndex : Option (Option κ) → ι → ℕ := fun x ↦ x.elim e' fun y ↦ y.elim e d'

/-- `K[(e, d')] → K[(e', e, d')]`, the variables of `V` and `U_l`. -/
def leftVar : GenericVar b (leftIndex e d') → GenericVar b (pairIndex e e' d') :=
  fun v ↦ ⟨some v.1, v.2⟩

/-- `K[(e', d')] → K[(e', e, d')]`, the variables of `W` and `U_l`. -/
def rightVar : GenericVar b (leftIndex e' d') → GenericVar b (pairIndex e e' d')
  | ⟨none, m⟩ => ⟨none, m⟩
  | ⟨some l, m⟩ => ⟨some (some l), m⟩

theorem leftVar_injective : Function.Injective (leftVar (b := b) e e' d') := by
  rintro ⟨y, m⟩ ⟨y', m'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : y = y' := Option.some.inj h1
  exact congrArg (Sigma.mk y) (eq_of_heq h2)

theorem rightVar_injective : Function.Injective (rightVar (b := b) e e' d') := by
  rintro ⟨_ | l, m⟩ ⟨_ | l', m'⟩ h <;> obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  · rw [eq_of_heq h2]
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · obtain rfl : l = l' := by simpa using h1
    rw [eq_of_heq h2]

variable (K b)

/-- **The product specialization** `ω : K[(e + e', d')] → K[(e', e, d')]`: `u^{(0)}_m ↦ [X^m](V W)`
and `u^{(l)}_m ↦ u^{(l)}_m` (Rémond, LNM 1752, Ch. 5, §3.4). -/
noncomputable def productMap :
    MvPolynomial (GenericVar b (sumIndex e e' d')) K →+*
      MvPolynomial (GenericVar b (pairIndex e e' d')) K :=
  (aeval fun v ↦ match v with
    | ⟨none, m⟩ => (genericForm K b (pairIndex e e' d') (some none) *
        genericForm K b (pairIndex e e' d') none).coeff (m : σ →₀ ℕ)
    | ⟨some l, m⟩ => X ⟨some (some l), m⟩).toRingHom

end Indices

section Ideals

variable {κ : Type*} {e e' : ι → ℕ} {d' : κ → ι → ℕ}

local notation "V" => genericForm K b (pairIndex e e' d') (some none)
local notation "W" => genericForm K b (pairIndex e e' d') none

variable (K b e e' d') in
/-- The ideal `(I, U_l : l ∈ κ)` of `K[(e', e, d')][X]`. -/
noncomputable def baseIdeal (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ (MvPolynomial (GenericVar b (pairIndex e e' d')) K)) :=
  I.map (map C) ⊔
    Ideal.span (Set.range fun l : κ ↦ genericForm K b (pairIndex e e' d') (some (some l)))

theorem map_productMap_genericForm_none :
    map (productMap b K e e' d') (genericForm K b (sumIndex e e' d') none) = V * W :=
  map_genericForm_of_forall _ none
    ((isWeightedHomogeneous_genericForm (some none)).mul (isWeightedHomogeneous_genericForm none))
    fun m ↦ by simp [productMap]

theorem map_productMap_genericForm_some (l : κ) :
    map (productMap b K e e' d') (genericForm K b (sumIndex e e' d') (some l)) =
      genericForm K b (pairIndex e e' d') (some (some l)) := by
  simp [genericForm, map_monomial, productMap]
  rfl

theorem map_productMap_comp_map_C :
    (map (productMap b K e e' d') : MvPolynomial σ _ →+* _).comp (map C) = map C := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, map_map]
  exact congrArg (fun φ ↦ map φ p) (RingHom.ext fun a ↦ by simp [productMap])

/-- `ω(I[d]) = (I, V W, U_l)`. -/
theorem map_productMap_genericIdeal (I : Ideal (MvPolynomial σ K)) :
    (genericIdeal K b (sumIndex e e' d') I).map (map (productMap b K e e' d')) =
      baseIdeal b K e e' d' I ⊔ Ideal.span {V * W} := by
  rw [genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, map_productMap_comp_map_C,
    Option.range_eq, Set.image_insert_eq, ← Set.range_comp, map_productMap_genericForm_none,
    Ideal.span_insert, baseIdeal]
  rw [show ⇑(map (productMap b K e e' d')) ∘ genericForm K b (sumIndex e e' d') ∘ some =
    fun l ↦ genericForm K b (pairIndex e e' d') (some (some l)) from
    funext map_productMap_genericForm_some]
  ac_rfl

theorem map_rename_leftVar_genericForm (y : Option κ) :
    map (rename (leftVar (b := b) e e' d')).toRingHom (genericForm K b (leftIndex e d') y) =
      genericForm K b (pairIndex e e' d') (some y) := by
  simp [genericForm, map_monomial, leftVar]
  rfl

theorem map_rename_rightVar_genericForm_none :
    map (rename (rightVar (b := b) e e' d')).toRingHom
      (genericForm K b (leftIndex e' d') none) = W := by
  simp [genericForm, map_monomial, rightVar]
  rfl

theorem map_rename_rightVar_genericForm_some (l : κ) :
    map (rename (rightVar (b := b) e e' d')).toRingHom
      (genericForm K b (leftIndex e' d') (some l)) =
      genericForm K b (pairIndex e e' d') (some (some l)) := by
  simp [genericForm, map_monomial, rightVar]
  rfl

omit [Fintype σ] in
theorem map_rename_comp_map_C {τ υ : Type*} (f : τ → υ) :
    (map (rename f).toRingHom : MvPolynomial σ (MvPolynomial τ K) →+* _).comp (map C) = map C := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, map_map]
  exact congrArg (fun φ ↦ map φ p) (RingHom.ext fun a ↦ rename_C f a)

/-- The generic ideal of index `(e, d')` becomes `(I, V, U_l)`. -/
theorem map_rename_leftVar_genericIdeal (I : Ideal (MvPolynomial σ K)) :
    (genericIdeal K b (leftIndex e d') I).map (map (rename (leftVar (b := b) e e' d')).toRingHom) =
      baseIdeal b K e e' d' I ⊔ Ideal.span {V} := by
  rw [genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, map_rename_comp_map_C,
    Option.range_eq, Set.image_insert_eq, ← Set.range_comp, map_rename_leftVar_genericForm,
    Ideal.span_insert, baseIdeal]
  rw [show ⇑(map (rename (leftVar (b := b) e e' d')).toRingHom) ∘
    genericForm K b (leftIndex e d') ∘ some =
    fun l ↦ genericForm K b (pairIndex e e' d') (some (some l)) from
    funext fun l ↦ map_rename_leftVar_genericForm (some l)]
  ac_rfl

/-- The generic ideal of index `(e', d')` becomes `(I, W, U_l)`. -/
theorem map_rename_rightVar_genericIdeal (I : Ideal (MvPolynomial σ K)) :
    (genericIdeal K b (leftIndex e' d') I).map
        (map (rename (rightVar (b := b) e e' d')).toRingHom) =
      baseIdeal b K e e' d' I ⊔ Ideal.span {W} := by
  rw [genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, map_rename_comp_map_C,
    Option.range_eq, Set.image_insert_eq, ← Set.range_comp, map_rename_rightVar_genericForm_none,
    Ideal.span_insert, baseIdeal]
  rw [show ⇑(map (rename (rightVar (b := b) e e' d')).toRingHom) ∘
    genericForm K b (leftIndex e' d') ∘ some =
    fun l ↦ genericForm K b (pairIndex e e' d') (some (some l)) from
    funext map_rename_rightVar_genericForm_some]
  ac_rfl

end Ideals

section CharForm

/-- **Adjoining dummy variables does not change `χ`**: if `J ⊆ K[d₂][X]` is the image of `I[d₁]`
under an injective renaming of the coefficient variables, then `χ((K[d₂][X]/J)_k)` is the image of
`χ((K[d₁][X]/I[d₁])_k)`. -/
theorem associated_charForm_rename {κ₁ κ₂ : Type*} {d₁ : κ₁ → ι → ℕ} {d₂ : κ₂ → ι → ℕ}
    {f : GenericVar b d₁ → GenericVar b d₂} (hf : Function.Injective f)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    {J : Ideal (MvPolynomial σ (MvPolynomial (GenericVar b d₂) K))}
    (hJ : (genericIdeal K b d₁ I).map (map (rename f).toRingHom) = J) (k : ι → ℕ) :
    Associated (Module.charForm (MvPolynomial (GenericVar b d₂) K) (gradedPiece b J k))
      (rename f (Module.charForm (MvPolynomial (GenericVar b d₁) K) (genPiece b K d₁ I k))) := by
  let : Algebra (MvPolynomial (GenericVar b d₁) K) (MvPolynomial (GenericVar b d₂) K) :=
    (rename f).toRingHom.toAlgebra
  have hbc := gradedPiece.isBaseChange (R' := MvPolynomial (GenericVar b d₂) K)
    (genericIdeal K b d₁ I) (isWeightedHomogeneous_genericIdeal hI) k
  have e : gradedPiece b ((genericIdeal K b d₁ I).map (map (algebraMap
      (MvPolynomial (GenericVar b d₁) K) (MvPolynomial (GenericVar b d₂) K)))) k ≃ₗ[_]
      gradedPiece b J k := Submodule.quotEquivOfEq _ _ (by rw [← hJ]; rfl)
  exact Module.associated_charForm_of_isBaseChange_of_retraction (killCompl hf).toRingHom
    (fun a ↦ killCompl_rename_app hf a) (fun a ha c' hc' ↦ exists_rename_eq_of_dvd hf ha hc')
    (hbc.comp (IsBaseChange.ofEquiv e))

omit [Fintype σ] [Fintype ι] in
/-- **`χ` of a product section**: for a form `V` of multidegree `e`,
`χ((A[X]/(J, VW))_{k+e}) ∣ χ((A[X]/(J, W))_k) χ((A[X]/(J, V))_{k+e})`, by the exact sequence of
multiplication by `V`. -/
theorem charForm_dvd_mul_of_mul [Finite σ] [Finite ι] {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A] {J : Ideal (MvPolynomial σ A)}
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) {V W : MvPolynomial σ A} {e e' : ι → ℕ}
    (hV : IsWeightedHomogeneous (multiWeight b) V e)
    (hW : IsWeightedHomogeneous (multiWeight b) W e') (k : ι → ℕ) :
    Module.charForm A (gradedPiece b (J ⊔ Ideal.span {V * W}) (k + e)) ∣
      Module.charForm A (gradedPiece b (J ⊔ Ideal.span {W}) k) *
        Module.charForm A (gradedPiece b (J ⊔ Ideal.span {V}) (k + e)) := by
  set I := J ⊔ Ideal.span {V * W}
  have hI : I.IsWeightedHomogeneous (multiWeight b) :=
    hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e + e', (Set.mem_singleton_iff.mp hx) ▸
      hV.mul hW⟩)
  have hcol : ∀ g ∈ I.colon {V}, g * V ∈ I := fun g hg ↦ by
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg
    exact hg
  have hex := gradedPiece.exact_mulMap_factor hI hV hcol k
  have hassoc := Module.associated_charForm_of_exact _ _
    (gradedPiece.mulMap_injective hV hcol fun g _ hg ↦ by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact hg)
    (gradedPiece.factor_surjective _ _) hex
  have hle : J ⊔ Ideal.span {W} ≤ I.colon {V} := sup_le
    (fun x hx ↦ by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact I.mul_mem_right _ (le_sup_left (a := J) hx))
    (Ideal.span_le.mpr fun x hx ↦ by
      rw [Set.mem_singleton_iff.mp hx, SetLike.mem_coe, Submodule.mem_colon_singleton,
        smul_eq_mul, mul_comm]
      exact le_sup_right (a := J) (Ideal.mem_span_singleton_self _))
  have hsup : I ⊔ Ideal.span {V} = J ⊔ Ideal.span {V} := by
    refine le_antisymm (sup_le (sup_le le_sup_left ?_) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    exact (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right V W)).trans le_sup_right
  have e1 : gradedPiece b (I ⊔ Ideal.span {V}) (k + e) ≃ₗ[A]
      gradedPiece b (J ⊔ Ideal.span {V}) (k + e) := Submodule.quotEquivOfEq _ _ (by rw [hsup])
  rw [Module.charForm_congr e1] at hassoc
  exact hassoc.dvd.trans (mul_dvd_mul_right
    (Module.charForm_dvd_of_surjective _ (gradedPiece.factor_surjective hle k)) _)

end CharForm

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Fintype κ] {e e' : ι → ℕ} {d' : κ → ι → ℕ}

local notation "V" => genericForm K b (pairIndex e e' d') (some none)
local notation "W" => genericForm K b (pairIndex e e' d') none

/-- **Rémond's Prop. 3.5** (LNM 1752, Ch. 5, separation of variables, two factors): for a
multihomogeneous ideal `I` with `deg H_I ≤ r - 1`, specializing the first generic form of
multidegree `e + e'` to the product `V W` of generic forms of multidegrees `e` and `e'` sends
`res_{(e + e', d')}(I)` to `res_{(e, d')}(I) · res_{(e', d')}(I)`, up to a nonzero constant. -/
theorem associated_productMap_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) :
    Associated (productMap b K e e' d' (resForm b K (sumIndex e e' d') I))
      (rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
        rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I)) := by
  classical
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  have hcard' : (hilbertPoly b I).totalDegree + 1 ≤ Fintype.card (Option κ) := by
    rwa [← Nat.card_eq_fintype_card]
  -- `ω(res_d(I)) ∣ res_{(e, d')}(I) · res_{(e', d')}(I)`.
  have hdvd : productMap b K e e' d' (resForm b K (sumIndex e e' d') I) ∣
      rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
        rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I) := by
    obtain ⟨⟨kD, hkD⟩, -⟩ := associated_resForm_prod (d := sumIndex e e' d') hb hI hcard
    obtain ⟨⟨kE, hkE⟩, -⟩ := associated_resForm_prod (d := leftIndex e d') hb hI hcard
    obtain ⟨⟨kE', hkE'⟩, -⟩ := associated_resForm_prod (d := leftIndex e' d') hb hI hcard
    set k := kD ⊔ kE ⊔ kE'
    have hk : k ≤ k + e := le_self_add
    have hJ0 : (baseIdeal b K e e' d' I).IsWeightedHomogeneous (multiWeight b) :=
      (hI.map C).sup (isWeightedHomogeneous_span fun x ⟨l, hl⟩ ↦
        ⟨pairIndex e e' d' (some (some l)), by
          rw [← hl]
          exact isWeightedHomogeneous_genericForm _⟩)
    let : Algebra (MvPolynomial (GenericVar b (sumIndex e e' d')) K)
        (MvPolynomial (GenericVar b (pairIndex e e' d')) K) := (productMap b K e e' d').toAlgebra
    have hbc := gradedPiece.isBaseChange (R' := MvPolynomial (GenericVar b (pairIndex e e' d')) K)
      (genericIdeal K b (sumIndex e e' d') I) (isWeightedHomogeneous_genericIdeal hI) (k + e)
    have eq : gradedPiece b ((genericIdeal K b (sumIndex e e' d') I).map (map (algebraMap
        (MvPolynomial (GenericVar b (sumIndex e e' d')) K)
        (MvPolynomial (GenericVar b (pairIndex e e' d')) K)))) (k + e) ≃ₗ[_]
        gradedPiece b (baseIdeal b K e e' d' I ⊔ Ideal.span {V * W}) (k + e) :=
      Submodule.quotEquivOfEq _ _ (by rw [← map_productMap_genericIdeal]; rfl)
    have h1 := Module.algebraMap_charForm_dvd_of_isBaseChange
      (hbc.comp (IsBaseChange.ofEquiv eq))
    have h2 := charForm_dvd_mul_of_mul hJ0 (isWeightedHomogeneous_genericForm (some none))
      (isWeightedHomogeneous_genericForm none) k
    have h3 := associated_charForm_rename (leftVar_injective e e' d') hI
      (map_rename_leftVar_genericIdeal I) (k + e)
    have h4 := associated_charForm_rename (rightVar_injective e e' d') hI
      (map_rename_rightVar_genericIdeal I) k
    have hD := (hkD (k + e) ((le_sup_left.trans le_sup_left).trans hk)).map
      (productMap b K e e' d')
    have hE := (hkE (k + e) ((le_sup_right.trans le_sup_left).trans hk)).map
      (rename (leftVar (b := b) e e' d'))
    have hE' := (hkE' k le_sup_right).map (rename (rightVar (b := b) e e' d'))
    refine hD.symm.dvd.trans (h1.trans (h2.trans ?_))
    rw [mul_comm]
    exact mul_dvd_mul (h3.dvd.trans hE.dvd) (h4.dvd.trans hE'.dvd)
  -- Equal degrees in every group (Prop. 3.4).
  obtain ⟨nD, hnD, hD⟩ := exists_isWeightedHomogeneous_resForm (d := sumIndex e e' d') hb none hI
    hcard'
  obtain ⟨nE, hnE, hE⟩ := exists_isWeightedHomogeneous_resForm (d := leftIndex e d') hb none hI
    hcard'
  obtain ⟨nE', hnE', hE'⟩ := exists_isWeightedHomogeneous_resForm (d := leftIndex e' d') hb none
    hI hcard'
  rw [diffPoly_erase_none] at hnD hnE hnE'
  obtain rfl : nE = nD := by exact_mod_cast hnE.trans hnD.symm
  obtain rfl : nE' = nE := by exact_mod_cast hnE'.trans hnE.symm
  have hpm : ∀ (x : Option (Option κ)) (l₀ : Option κ),
      (∀ m : blockMonomials b (e + e'), groupWeight b (sumIndex e e' d') l₀ ⟨none, m⟩ =
        (if some none = x then 1 else 0) + (if none = x then 1 else 0)) →
      (∀ l (m : blockMonomials b (d' l)),
        groupWeight b (sumIndex e e' d') l₀ ⟨some l, m⟩ =
          groupWeight b (pairIndex e e' d') x ⟨some (some l), m⟩) →
      ∀ {p : MvPolynomial (GenericVar b (sumIndex e e' d')) K} {n : ℕ},
        IsWeightedHomogeneous (groupWeight b (sumIndex e e' d') l₀) p n →
        IsWeightedHomogeneous (groupWeight b (pairIndex e e' d') x)
          (productMap b K e e' d' p) n := by
    intro x l₀ hnone hsome p n hp
    refine hp.map_of_forall _ (fun r ↦ ?_) fun v ↦ ?_
    · simpa [productMap] using isWeightedHomogeneous_C (groupWeight b (pairIndex e e' d') x) r
    · obtain ⟨_ | l, m⟩ := v
      · rw [hnone m]
        simpa [productMap] using isWeightedHomogeneous_coeff_mul_genericForm (R := K)
          (d := pairIndex e e' d') (some none) none x (m : σ →₀ ℕ)
      · rw [hsome l m]
        simpa [productMap] using isWeightedHomogeneous_X K
          (groupWeight b (pairIndex e e' d') x) ⟨some (some l), m⟩
  have hren : ∀ {κ₁ : Type u} {d₁ : κ₁ → ι → ℕ}
      (f : GenericVar b d₁ → GenericVar b (pairIndex e e' d'))
      (w : GenericVar b d₁ → ℕ) (x : Option (Option κ)),
      (∀ v, w v = groupWeight b (pairIndex e e' d') x (f v)) →
      ∀ {p : MvPolynomial (GenericVar b d₁) K} {n : ℕ}, IsWeightedHomogeneous w p n →
        IsWeightedHomogeneous (groupWeight b (pairIndex e e' d') x) (rename f p) n := by
    intro κ₁ d₁ f w x hw p n hp
    refine hp.map_of_forall (rename f).toRingHom (fun r ↦ ?_) fun v ↦ ?_
    · simpa using isWeightedHomogeneous_C (groupWeight b (pairIndex e e' d') x) r
    · rw [hw v]
      simpa using isWeightedHomogeneous_X K (groupWeight b (pairIndex e e' d') x) (f v)
  have key : ∀ x : Option (Option κ), ∃ n : ℕ,
      IsWeightedHomogeneous (groupWeight b (pairIndex e e' d') x)
        (productMap b K e e' d' (resForm b K (sumIndex e e' d') I)) n ∧
      IsWeightedHomogeneous (groupWeight b (pairIndex e e' d') x)
        (rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
          rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I)) n := by
    rintro (_ | _ | l)
    · -- the group of `W`
      refine ⟨nE', hpm none none (fun m ↦ by simp [groupWeight])
        (fun l m ↦ by simp [groupWeight]) hD, ?_⟩
      have := (hren (leftVar e e' d') 0 none (fun v ↦ by simp [groupWeight, leftVar])
        (isWeightedHomogeneous_zero_weight (resForm b K (leftIndex e d') I))).mul
        (hren (rightVar e e' d') _ none (fun v ↦ by
          obtain ⟨_ | l, m⟩ := v <;> simp [groupWeight, rightVar]) hE')
      simpa using this
    · -- the group of `V`
      refine ⟨nE', hpm (some none) none (fun m ↦ by simp [groupWeight])
        (fun l m ↦ by simp [groupWeight]) hD, ?_⟩
      have := (hren (leftVar e e' d') _ (some none) (fun v ↦ by
          obtain ⟨_ | l, m⟩ := v <;> simp [groupWeight, leftVar]) hE).mul
        (hren (rightVar e e' d') 0 (some none) (fun v ↦ by
          obtain ⟨_ | l, m⟩ := v <;> simp [groupWeight, rightVar])
          (isWeightedHomogeneous_zero_weight (resForm b K (leftIndex e' d') I)))
      simpa using this
    · -- the group of `U_l`
      obtain ⟨n₁, hn₁, h₁⟩ := exists_isWeightedHomogeneous_resForm (d := sumIndex e e' d') hb
        (some l) hI hcard'
      obtain ⟨n₂, hn₂, h₂⟩ := exists_isWeightedHomogeneous_resForm (d := leftIndex e d') hb
        (some l) hI hcard'
      obtain ⟨n₃, hn₃, h₃⟩ := exists_isWeightedHomogeneous_resForm (d := leftIndex e' d') hb
        (some l) hI hcard'
      rw [diffPoly_option] at hn₁ hn₂ hn₃
      have hsum : (n₁ : ℚ) = n₂ + n₃ := by
        have : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨l⟩
        have hadd := diffPoly_sub_shiftPoly_add d' (Finset.univ.erase l) e e'
          (H := hilbertPoly b I) (by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
            omega)
        rw [hn₁, hn₂, hn₃]
        change (diffPoly d' _ (hilbertPoly b I - shiftPoly (e + e') (hilbertPoly b I))).coeff 0 =
          (diffPoly d' _ (hilbertPoly b I - shiftPoly e (hilbertPoly b I))).coeff 0 +
            (diffPoly d' _ (hilbertPoly b I - shiftPoly e' (hilbertPoly b I))).coeff 0
        simp [hadd]
      have hsum' : n₁ = n₂ + n₃ := by exact_mod_cast hsum
      refine ⟨n₁, hpm (some (some l)) (some l) (fun m ↦ by simp [groupWeight])
        (fun l' m ↦ by simp [groupWeight]) h₁, ?_⟩
      rw [hsum']
      exact (hren (leftVar e e' d') _ (some (some l)) (fun v ↦ by
          obtain ⟨_ | l', m⟩ := v <;> simp [groupWeight, leftVar]) h₂).mul
        (hren (rightVar e e' d') _ (some (some l)) (fun v ↦ by
          obtain ⟨_ | l', m⟩ := v <;> simp [groupWeight, rightVar]) h₃)
  choose n hn using key
  have hne : rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
      rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I) ≠ 0 :=
    mul_ne_zero
      ((map_ne_zero_iff _ (rename_injective _ (leftVar_injective e e' d'))).mpr
        (resForm_ne_zero hb hI hcard))
      ((map_ne_zero_iff _ (rename_injective _ (rightVar_injective e e' d'))).mpr
        (resForm_ne_zero hb hI hcard))
  exact associated_of_dvd_of_isHomogeneous hdvd hne
    (isHomogeneous_of_forall_groupWeight fun x ↦ (hn x).1)
    (isHomogeneous_of_forall_groupWeight fun x ↦ (hn x).2)

/-- **Prop. 3.5** with the constant: `ω(res_d(I)) = λ res_{(e, d')}(I) res_{(e', d')}(I)` for
some `λ ∈ Kˣ`. -/
theorem exists_productMap_resForm_eq (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) :
    ∃ c : K, c ≠ 0 ∧ productMap b K e e' d' (resForm b K (sumIndex e e' d') I) =
      C c * (rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
        rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I)) := by
  obtain ⟨u, hu⟩ := associated_productMap_resForm (e := e) (e' := e') (d' := d') hb hI hdim
  obtain ⟨μ, hμ, hμu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  have hμ0 : μ ≠ 0 := hμ.ne_zero
  refine ⟨μ⁻¹, inv_ne_zero hμ0, ?_⟩
  rw [← hu, hμu, mul_comm (C μ⁻¹), mul_assoc, ← C_mul, mul_inv_cancel₀ hμ0, C_1, mul_one]

end Main

end MvPolynomial
