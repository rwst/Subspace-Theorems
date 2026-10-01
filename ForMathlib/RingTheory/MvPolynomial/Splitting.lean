/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.GenericSection

-- Used only inside proofs.
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Splitting off one generic form

For an index `d = (d₀, d')` (`d : Option κ → ι → ℕ`, `d₀ = d none`), the coefficient ring of
the generic forms splits as `R[d] ≅ R[u^{(0)}][d']` (`MvPolynomial.splitEquiv`), and under this
isomorphism `𝔄_d(I) = 𝔄_{d'}(𝔄_{(d₀)}(I))` (`MvPolynomial.map_splitEquiv_charIdeal`, over a
Noetherian ring). Characteristic ideals commute with localization of the coefficients
(`MvPolynomial.map_charIdeal_of_isLocalization`), so with `L = Frac(K[u^{(0)}])` and
`𝔮 = 𝔄_{(d₀)}(𝔭) L[X]`:

* `𝔄_{d'}(𝔮) = 𝔄_d(𝔭) L[d'][X]` (`MvPolynomial.charIdeal_map_charIdeal`);
* `𝔈_{d'}(𝔮) = 𝔈_d(𝔭) L[d']` (`MvPolynomial.elimIdeal_map_charIdeal`).

These are the third and fourth assertions of G. Rémond's Lemma 2.12 (*Élimination
multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.), *Introduction to algebraic
independence theory*, LNM 1752 (2001)), the induction step of Thm 2.13 and Prop. 3.4. The key
point is `𝔄_{d'}(J : 𝔪^∞) = 𝔄_{d'}(J)` (`MvPolynomial.saturation_genericIdeal_saturation`): over a
Noetherian ring `J : 𝔪^∞ = J : 𝔪^k`, and `(J : 𝔪^k)[d'] ⊆ J[d'] : 𝔪^k`.

## Main statements

* `MvPolynomial.map_saturation_of_equiv`: saturation commutes with isomorphisms of coefficients.
* `MvPolynomial.map_map_genericIdeal`, `MvPolynomial.map_charIdeal_of_isLocalization`: generic
  and characteristic ideals under maps and localizations of the coefficients.
* `MvPolynomial.comap_C_map_map_of_equiv`, `MvPolynomial.comap_C_map_map_of_isLocalization`:
  intersecting with the constants commutes with them.
* `MvPolynomial.saturation_genericIdeal_saturation`, `MvPolynomial.map_splitEquiv_charIdeal`.
* `MvPolynomial.charIdeal_map_charIdeal`, `MvPolynomial.elimIdeal_map_charIdeal`.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Saturation can only grow under a map of coefficients. -/
theorem map_saturation_le (f : R →+* S) (J : Ideal (MvPolynomial σ R)) :
    (saturation b J).map (map f) ≤ saturation b (J.map (map f)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨n, hn⟩ := mem_saturation.mp hx
  refine mem_saturation.mpr ⟨n, fun g hg ↦ ?_⟩
  have hle : (irrelevantIdeal R b ^ n).map (map f) ≤ (J.map (map f)).colon {map f x} := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hn g hg)
  rw [← map_irrelevantIdeal f, ← Ideal.map_pow] at hg
  have := hle hg
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this

/-- **Saturation commutes with isomorphisms of the coefficients.** -/
theorem map_saturation_of_equiv (e : R ≃+* S) (J : Ideal (MvPolynomial σ R)) :
    (saturation b J).map (map e.toRingHom) = saturation b (J.map (map e.toRingHom)) := by
  refine le_antisymm (map_saturation_le _ J) ?_
  have hinv : ∀ I : Ideal (MvPolynomial σ R),
      (I.map (map e.toRingHom)).map (map e.symm.toRingHom) = I := by
    intro I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun a ↦ by simp
  have h := map_saturation_le (b := b) e.symm.toRingHom (J.map (map e.toRingHom))
  rw [hinv] at h
  have h2 := Ideal.map_mono (f := map e.toRingHom) h
  have hinv' : ∀ I : Ideal (MvPolynomial σ S),
      (I.map (map e.symm.toRingHom)).map (map e.toRingHom) = I := by
    intro I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun a ↦ by simp
  rwa [hinv'] at h2

end Map

section Saturate

variable {R : Type*} [CommRing R] {κ : Type*} {d : κ → ι → ℕ}

theorem saturation_mono {I J : Ideal (MvPolynomial σ R)} (h : I ≤ J) :
    saturation b I ≤ saturation b J := fun _ hf ↦
  let ⟨n, hn⟩ := mem_saturation.mp hf
  mem_saturation.mpr ⟨n, fun g hg ↦ h (hn g hg)⟩

theorem genericIdeal_mono {I J : Ideal (MvPolynomial σ R)} (h : I ≤ J) :
    genericIdeal R b d I ≤ genericIdeal R b d J :=
  sup_le_sup_right (Ideal.map_mono h) _

/-- `(J : 𝔪^k)[d] ⊆ J[d] : 𝔪^k`. -/
theorem genericIdeal_colon_le (J : Ideal (MvPolynomial σ R)) (k : ℕ) :
    genericIdeal R b d (J.colon (irrelevantIdeal R b ^ k : Set _)) ≤
      (genericIdeal R b d J).colon
        (irrelevantIdeal (MvPolynomial (GenericVar b d) R) b ^ k : Set _) := by
  have hJ : genericIdeal R b d J ≤ (genericIdeal R b d J).colon
      (irrelevantIdeal (MvPolynomial (GenericVar b d) R) b ^ k : Set _) :=
    fun x hx ↦ Submodule.mem_colon.mpr fun g _ ↦ by
      rw [smul_eq_mul, mul_comm]
      exact Ideal.mul_mem_left _ g hx
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf ↦ ?_) (le_sup_right.trans hJ)
  rw [Ideal.mem_comap, mem_colon_irrelevantIdeal_pow_iff]
  intro c hc
  have h1 := mem_colon_irrelevantIdeal_pow_iff.mp hf c hc
  have : monomial c (1 : MvPolynomial (GenericVar b d) R) * map C f =
      map C (monomial c 1 * f) := by
    simp [map_monomial]
  rw [this]
  exact le_sup_left (a := J.map (map C)) (Ideal.mem_map_of_mem _ h1)

variable [IsNoetherianRing R]

/-- **Saturating before adding generic forms changes nothing**: `𝔄_d(J : 𝔪^∞) = 𝔄_d(J)`. -/
theorem saturation_genericIdeal_saturation (J : Ideal (MvPolynomial σ R)) :
    saturation b (genericIdeal R b d (saturation b J)) = saturation b (genericIdeal R b d J) := by
  refine le_antisymm ?_ (saturation_mono (genericIdeal_mono (le_saturation J)))
  obtain ⟨k, hk⟩ := exists_saturation_eq_colon (b := b) J
  intro x hx
  obtain ⟨n, hn⟩ := mem_saturation.mp hx
  refine mem_saturation.mpr ⟨k + n, fun g hg ↦ ?_⟩
  rw [pow_add] at hg
  refine Submodule.mul_induction_on hg (fun a ha c hc ↦ ?_)
    (fun a c ha hc ↦ by rw [add_mul]; exact Ideal.add_mem _ ha hc)
  have h1 : c * x ∈ (genericIdeal R b d J).colon
      (irrelevantIdeal (MvPolynomial (GenericVar b d) R) b ^ k : Set _) :=
    genericIdeal_colon_le J k (hk ▸ hn c hc)
  rw [Submodule.mem_colon] at h1
  have := h1 a ha
  rw [smul_eq_mul, mul_comm] at this
  rwa [mul_assoc]

end Saturate

section Generic

variable {R S : Type*} [CommRing R] [CommRing S] {κ : Type*} {d : κ → ι → ℕ}

theorem map_map_genericForm (f : R →+* S) (l : κ) :
    map (map f) (genericForm R b d l) = genericForm S b d l := by
  simp [genericForm, map_monomial]

theorem map_map_genericIdeal (f : R →+* S) (I : Ideal (MvPolynomial σ R)) :
    (genericIdeal R b d I).map (map (map f)) = genericIdeal S b d (I.map (map f)) := by
  rw [genericIdeal, genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, Ideal.map_map]
  congr 1
  · congr 1
    refine RingHom.ext fun p ↦ ?_
    simp only [RingHom.comp_apply, map_map]
    congr 2
    exact RingHom.ext fun a ↦ by simp
  · rw [← Set.range_comp]
    congr 2
    exact funext (map_map_genericForm f)

variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M in
attribute [local instance] algebraMvPolynomial in
/-- **Characteristic ideals commute with localization of the coefficients.** -/
theorem map_charIdeal_of_isLocalization (I : Ideal (MvPolynomial σ R)) :
    (charIdeal R b d I).map (map (map (algebraMap R S))) =
      charIdeal S b d (I.map (map (algebraMap R S))) := by
  rw [charIdeal_eq_saturation, charIdeal_eq_saturation, ← map_map_genericIdeal]
  exact map_saturation (M.map (C (σ := GenericVar b d))) _

end Generic

section Comap

omit [Fintype σ] in
/-- Constants commute with isomorphisms of the coefficients. -/
theorem comap_C_map_map_of_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (J : Ideal (MvPolynomial σ A)) :
    (J.map (map e.toRingHom)).comap C = (J.comap C).map e.toRingHom := by
  have h1 : J.map (map e.toRingHom) = J.comap (map e.symm.toRingHom) :=
    Ideal.map_comap_of_equiv (I := J) (mapEquiv σ e)
  have h2 : (J.comap C).map e.toRingHom = (J.comap C).comap (e.symm : B →+* A) :=
    Ideal.map_comap_of_equiv e
  rw [h1, h2, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  exact RingHom.ext fun a ↦ by simp

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
  [IsLocalization M B]

omit [Fintype σ] in
include M in
attribute [local instance] algebraMvPolynomial in
/-- **Constants commute with localization of the coefficients.** -/
theorem comap_C_map_map_of_isLocalization (J : Ideal (MvPolynomial σ A)) :
    (J.map (map (algebraMap A B))).comap C = (J.comap C).map (algebraMap A B) := by
  refine le_antisymm (fun y hy ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
  · obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    rw [Ideal.mem_comap, isLocalization_C_mk' M] at hy
    obtain ⟨_, ⟨t, ht, rfl⟩, hta⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff
      (M.map (C (σ := σ))) (MvPolynomial σ B) J _ _).mp hy
    rw [← map_mul] at hta
    exact (IsLocalization.mk'_mem_map_algebraMap_iff M B _ _ _).mpr ⟨t, ht, hta⟩
  · rw [Ideal.mem_comap, Ideal.mem_comap, ← map_C]
    exact Ideal.mem_map_of_mem _ hx

end Comap

section Split

variable {R : Type*} [CommRing R] {κ : Type*} (d : Option κ → ι → ℕ)

variable (b) in
/-- The coefficients of the generic forms of index `d = (d₀, d')`, split into those of `d'` and
those of `d₀ = d none`. -/
def splitVar : GenericVar b d ≃
    GenericVar b (fun l : κ ↦ d (some l)) ⊕ GenericVar b (fun _ : Unit ↦ d none) where
  toFun
    | ⟨none, m⟩ => .inr ⟨(), m⟩
    | ⟨some l, m⟩ => .inl ⟨l, m⟩
  invFun
    | .inl ⟨l, m⟩ => ⟨some l, m⟩
    | .inr ⟨(), m⟩ => ⟨none, m⟩
  left_inv := by rintro ⟨_ | l, m⟩ <;> rfl
  right_inv := by rintro (⟨l, m⟩ | ⟨⟨⟩, m⟩) <;> rfl

variable (R b) in
/-- `R[d] ≅ R[d₀][d']`. -/
noncomputable def splitEquiv : MvPolynomial (GenericVar b d) R ≃+*
    MvPolynomial (GenericVar b (fun l : κ ↦ d (some l)))
      (MvPolynomial (GenericVar b (fun _ : Unit ↦ d none)) R) :=
  (renameEquiv R (splitVar b d)).toRingEquiv.trans (sumRingEquiv R _ _)

theorem splitEquiv_C (r : R) : splitEquiv b R d (C r) = C (C r) := by
  simp [splitEquiv, sumRingEquiv_C]

theorem splitEquiv_X_some (l : κ) (m : blockMonomials b (d (some l))) :
    splitEquiv b R d (X ⟨some l, m⟩) = X ⟨l, m⟩ := by
  simp [splitEquiv, splitVar, sumRingEquiv_X_inl]

theorem splitEquiv_X_none (m : blockMonomials b (d none)) :
    splitEquiv b R d (X ⟨none, m⟩) = C (X ⟨(), m⟩) := by
  simp [splitEquiv, splitVar, sumRingEquiv_X_inr]

theorem map_splitEquiv_genericForm_some (l : κ) :
    map (splitEquiv b R d).toRingHom (genericForm R b d (some l)) =
      genericForm _ b (fun l : κ ↦ d (some l)) l := by
  simp [genericForm, map_monomial, splitEquiv_X_some]

theorem map_splitEquiv_genericForm_none :
    map (splitEquiv b R d).toRingHom (genericForm R b d none) =
      map C (genericForm R b (fun _ : Unit ↦ d none) ()) := by
  simp [genericForm, map_monomial, splitEquiv_X_none]

theorem map_splitEquiv_comp_map_C :
    (map (splitEquiv b R d).toRingHom).comp (map C : MvPolynomial σ R →+* _) =
      (map C).comp (map C) := by
  refine RingHom.ext fun p ↦ ?_
  simp only [RingHom.comp_apply, map_map]
  congr 2
  exact RingHom.ext fun a ↦ by simp [splitEquiv_C]

/-- `R[d]`-generic ideal, split: `I[d] = (I[d₀])[d']`. -/
theorem map_splitEquiv_genericIdeal (I : Ideal (MvPolynomial σ R)) :
    (genericIdeal R b d I).map (map (splitEquiv b R d).toRingHom) =
      genericIdeal _ b (fun l : κ ↦ d (some l)) (genericIdeal R b (fun _ : Unit ↦ d none) I) := by
  have hA : ⇑(map (splitEquiv b R d).toRingHom) '' Set.range (genericForm R b d) =
      insert (map C (genericForm R b (fun _ : Unit ↦ d none) ()))
        (Set.range (genericForm _ b (fun l : κ ↦ d (some l)))) := by
    rw [Option.range_eq, Set.image_insert_eq, map_splitEquiv_genericForm_none d, ← Set.range_comp]
    congr 2
    exact funext (map_splitEquiv_genericForm_some d)
  have hB : ⇑(map (C : MvPolynomial (GenericVar b fun _ : Unit ↦ d none) R →+*
        MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) _)) ''
        Set.range (genericForm R b (fun _ : Unit ↦ d none)) =
      {map C (genericForm R b (fun _ : Unit ↦ d none) ())} := by
    rw [← Set.range_comp, Set.range_unique]
    rfl
  rw [genericIdeal, genericIdeal, genericIdeal, Ideal.map_sup, Ideal.map_sup, Ideal.map_span,
    Ideal.map_span, Ideal.map_map, map_splitEquiv_comp_map_C d, ← Ideal.map_map, hA, hB,
    Ideal.span_insert, sup_assoc]

variable [IsNoetherianRing R]

/-- **Splitting the characteristic ideal**: `𝔄_d(I) = 𝔄_{d'}(𝔄_{(d₀)}(I))` under
`R[d] ≅ R[d₀][d']`. -/
theorem map_splitEquiv_charIdeal (I : Ideal (MvPolynomial σ R)) :
    (charIdeal R b d I).map (map (splitEquiv b R d).toRingHom) =
      charIdeal _ b (fun l : κ ↦ d (some l)) (charIdeal R b (fun _ : Unit ↦ d none) I) := by
  rw [charIdeal_eq_saturation, map_saturation_of_equiv, map_splitEquiv_genericIdeal,
    charIdeal_eq_saturation, charIdeal_eq_saturation, saturation_genericIdeal_saturation]

/-- **Eliminating fewer forms**: if `𝔈_d(I) = 0`, then `𝔈_{(d₀)}(I) = 0`. -/
theorem elimIdeal_none_eq_bot {I : Ideal (MvPolynomial σ R)} (h : elimIdeal R b d I = ⊥) :
    elimIdeal R b (fun _ : Unit ↦ d none) I = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  have h1 : (C (C c) : MvPolynomial σ (MvPolynomial (GenericVar b fun l : κ ↦ d (some l))
      (MvPolynomial (GenericVar b fun _ : Unit ↦ d none) R))) ∈
      (charIdeal R b d I).map (map (splitEquiv b R d).toRingHom) := by
    rw [map_splitEquiv_charIdeal]
    refine le_saturation _ ((le_sup_left : _ ≤ genericIdeal _ b _ _) ?_)
    have : (C (C c) : MvPolynomial σ (MvPolynomial (GenericVar b fun l : κ ↦ d (some l))
        (MvPolynomial (GenericVar b fun _ : Unit ↦ d none) R))) = map C (C c) := by
      rw [map_C]
    rw [this]
    exact Ideal.mem_map_of_mem _ hc
  have h2 : C c ∈ ((charIdeal R b d I).map (map (splitEquiv b R d).toRingHom)).comap C := h1
  rw [comap_C_map_map_of_equiv, ← elimIdeal, h, Ideal.map_bot, Ideal.mem_bot] at h2
  rw [Ideal.mem_bot]
  exact C_injective _ _ (h2.trans C_0.symm)

end Split

section Reindex

variable {R : Type*} [CommRing R] {κ κ' : Type*} (f : κ' ≃ κ) (d : κ → ι → ℕ)

variable (R b) in
/-- Reindexing the generic forms along `f : κ' ≃ κ`. -/
noncomputable def reindexEquiv : MvPolynomial (GenericVar b (d ∘ f)) R ≃+*
    MvPolynomial (GenericVar b d) R :=
  (renameEquiv R (Equiv.sigmaCongrLeft f (β := fun l ↦ blockMonomials b (d l)))).toRingEquiv

theorem map_reindexEquiv_genericForm (l : κ') :
    map (reindexEquiv b R f d).toRingHom (genericForm R b (d ∘ f) l) = genericForm R b d (f l) := by
  simp [genericForm, map_monomial, reindexEquiv]

theorem map_reindexEquiv_genericIdeal (I : Ideal (MvPolynomial σ R)) :
    (genericIdeal R b (d ∘ f) I).map (map (reindexEquiv b R f d).toRingHom) =
      genericIdeal R b d I := by
  rw [genericIdeal, genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, ← Set.range_comp]
  congr 1
  · congr 1
    refine RingHom.ext fun p ↦ ?_
    simp only [RingHom.comp_apply, map_map]
    congr 2
    exact RingHom.ext fun a ↦ by simp [reindexEquiv]
  · congr 1
    rw [show ⇑(map (reindexEquiv b R f d).toRingHom) ∘ genericForm R b (d ∘ f) =
      genericForm R b d ∘ f from funext (map_reindexEquiv_genericForm f d)]
    exact f.surjective.range_comp _

theorem map_reindexEquiv_charIdeal (I : Ideal (MvPolynomial σ R)) :
    (charIdeal R b (d ∘ f) I).map (map (reindexEquiv b R f d).toRingHom) = charIdeal R b d I := by
  rw [charIdeal_eq_saturation, map_saturation_of_equiv, map_reindexEquiv_genericIdeal,
    charIdeal_eq_saturation]

theorem map_reindexEquiv_elimIdeal (I : Ideal (MvPolynomial σ R)) :
    (elimIdeal R b (d ∘ f) I).map (reindexEquiv b R f d).toRingHom = elimIdeal R b d I := by
  rw [elimIdeal, elimIdeal, ← comap_C_map_map_of_equiv, map_reindexEquiv_charIdeal]

theorem elimIdeal_comp_eq_bot_iff (I : Ideal (MvPolynomial σ R)) :
    elimIdeal R b (d ∘ f) I = ⊥ ↔ elimIdeal R b d I = ⊥ := by
  rw [← map_reindexEquiv_elimIdeal f d I]
  exact (Ideal.map_eq_bot_iff_of_injective (reindexEquiv b R f d).injective).symm

end Reindex

section Field

variable {K : Type*} [Field K] {κ : Type*} (d : Option κ → ι → ℕ) (𝔭 : Ideal (MvPolynomial σ K))

/-- **Rémond's Lemma 2.12, third assertion**: with `L = Frac(K[u^{(0)}])` and
`𝔮 = 𝔄_{(d₀)}(𝔭) L[X]`, `𝔄_{d'}(𝔮) = 𝔄_d(𝔭) L[d'][X]` under `K[d] ≅ K[u^{(0)}][d']`. -/
theorem charIdeal_map_charIdeal :
    charIdeal (FractionRing (GenericRing K b (d none))) b (fun l : κ ↦ d (some l))
      ((charIdeal K b (fun _ : Unit ↦ d none) 𝔭).map
        (map (algebraMap (GenericRing K b (d none)) (FractionRing (GenericRing K b (d none)))))) =
      ((charIdeal K b d 𝔭).map (map (splitEquiv b K d).toRingHom)).map
        (map (map (algebraMap (GenericRing K b (d none))
          (FractionRing (GenericRing K b (d none)))))) := by
  rw [map_splitEquiv_charIdeal,
    map_charIdeal_of_isLocalization (nonZeroDivisors (GenericRing K b (d none)))]

attribute [local instance] algebraMvPolynomial in
/-- **Rémond's Lemma 2.12, fourth assertion**: `𝔈_{d'}(𝔮) = 𝔈_d(𝔭) L[d']`. -/
theorem elimIdeal_map_charIdeal :
    elimIdeal (FractionRing (GenericRing K b (d none))) b (fun l : κ ↦ d (some l))
      ((charIdeal K b (fun _ : Unit ↦ d none) 𝔭).map
        (map (algebraMap (GenericRing K b (d none)) (FractionRing (GenericRing K b (d none)))))) =
      ((elimIdeal K b d 𝔭).map (splitEquiv b K d).toRingHom).map
        (map (algebraMap (GenericRing K b (d none))
          (FractionRing (GenericRing K b (d none))))) := by
  have h := comap_C_map_map_of_isLocalization (σ := σ)
    (B := MvPolynomial (GenericVar b fun l : κ ↦ d (some l))
      (FractionRing (GenericRing K b (d none))))
    ((nonZeroDivisors (GenericRing K b (d none))).map C)
    ((charIdeal K b d 𝔭).map (map (splitEquiv b K d).toRingHom))
  rw [elimIdeal, charIdeal_map_charIdeal]
  refine h.trans ?_
  rw [comap_C_map_map_of_equiv]
  rfl

end Field

end MvPolynomial

end
