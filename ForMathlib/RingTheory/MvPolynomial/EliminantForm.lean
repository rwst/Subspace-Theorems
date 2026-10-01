/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Principality

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Eliminant forms

The eliminant form `elim_d(𝔭)` of a multihomogeneous prime and Rémond's Corollary 2.15
(G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.),
*Introduction to algebraic independence theory*, LNM 1752 (2001), Def. 2.14, Cor. 2.15).

## Main results

* `rename_mem_elimIdeal`: `𝔈_{d ∘ f}(I) ⊆ 𝔈_d(I)` for a subfamily of the forms.
* `elimForm`: a generator of `𝔈_d(I)` when this ideal is principal and proper, `1` otherwise.
  Unlike Rémond's choice of representatives of the irreducibles, it is only determined up to a
  nonzero constant.
* Cor. 2.15, with `e_J(𝔭) ≥ r_J(d)` written `r_J(d) + |J| ≤ blockRank 𝔭 b J`:
  * `elimForm_eq_zero_iff_forall`: `elim_d(𝔭) = 0` if and only if `𝔪 ⊄ 𝔭` and
    `e_J(𝔭) ≥ r_J(d)` for all `J`.
  * `span_elimForm`: if `e_J(𝔭) ≥ r_J(d) - 1` for all `J`, then `elim_d(𝔭)` generates `𝔈_d(𝔭)`.
  * `elimForm_eq_one`: otherwise `elim_d(𝔭) = 1`. If `𝔪 ⊄ 𝔭`, then `𝔈_d(𝔭)` is not principal
    (`not_isPrincipal_elimIdeal`): a generator divides nonzero elements of `𝔈_{d'}(𝔭)` for
    each family `d'` of all forms but one, so it is constant.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

section Sub

variable {R : Type*} [CommRing R] {κ κ' : Type*} (f : κ' → κ) (d : κ → ι → ℕ)

/-- The coefficients of the generic forms of a subfamily `d ∘ f` among those of `d`. -/
def subVar : GenericVar b (d ∘ f) → GenericVar b d := fun v ↦ ⟨f v.1, v.2⟩

theorem subVar_injective (hf : Function.Injective f) :
    Function.Injective (subVar (b := b) f d) := by
  rintro ⟨a, m⟩ ⟨a', m'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := hf h1
  exact Sigma.ext rfl h2

theorem map_rename_genericForm (l : κ') :
    map (rename (subVar (b := b) f d)).toRingHom (genericForm R b (d ∘ f) l) =
      genericForm R b d (f l) := by
  simp [genericForm, map_monomial, subVar]

theorem map_genericIdeal_le (I : Ideal (MvPolynomial σ R)) :
    (genericIdeal R b (d ∘ f) I).map (map (rename (subVar (b := b) f d)).toRingHom) ≤
      genericIdeal R b d I := by
  rw [genericIdeal, genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map]
  refine sup_le_sup (le_of_eq ?_) (Ideal.span_mono ?_)
  · congr 1
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map]
    exact congrArg (fun φ ↦ map φ p) (RingHom.ext fun c ↦ by simp)
  · rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨f l, (map_rename_genericForm f d l).symm⟩

/-- **Eliminating fewer forms**: `𝔈_{d ∘ f}(I) ⊆ 𝔈_d(I)`. -/
theorem rename_mem_elimIdeal {I : Ideal (MvPolynomial σ R)}
    {g : MvPolynomial (GenericVar b (d ∘ f)) R} (hg : g ∈ elimIdeal R b (d ∘ f) I) :
    rename (subVar f d) g ∈ elimIdeal R b d I := by
  have h1 : (C g : MvPolynomial σ _) ∈ saturation b (genericIdeal R b (d ∘ f) I) := hg
  have h2 := map_saturation_le (b := b) (rename (subVar (b := b) f d)).toRingHom _
    (Ideal.mem_map_of_mem _ h1)
  change C (rename (subVar f d) g) ∈ saturation b (genericIdeal R b d I)
  refine saturation_mono (map_genericIdeal_le f d I) ?_
  rwa [map_C] at h2

end Sub

section Constant

variable {W K : Type*} [Field K]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- A divisor of a nonzero polynomial without the variable `v` does not involve `v`. -/
theorem degreeOf_eq_zero_of_dvd {F g : MvPolynomial W K} (hFg : F ∣ g) (hg : g ≠ 0) {v : W}
    (hv : degreeOf v g = 0) : degreeOf v F = 0 := by
  obtain ⟨h, rfl⟩ := hFg
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hg) (right_ne_zero_of_mul hg)] at hv
  omega

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem degreeOf_rename_of_notMem_range {W' : Type*} {e : W' → W} {v : W} (hv : v ∉ Set.range e)
    (g : MvPolynomial W' K) : degreeOf v (rename e g) = 0 := by
  classical
  rw [degreeOf_def, Multiset.count_eq_zero]
  intro hmem
  have : v ∈ (rename e g).vars := (mem_vars_iff_mem_support v).mpr (by
    obtain ⟨m, hm, hmv⟩ := mem_degrees.mp hmem
    exact ⟨m, mem_support_iff.mpr hm, hmv⟩)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (vars_rename e g this)
  exact hv ⟨w, rfl⟩

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem eq_C_of_forall_degreeOf_eq_zero {F : MvPolynomial W K} (h : ∀ v, degreeOf v F = 0) :
    F = C (F.coeff 0) := by
  rw [← totalDegree_eq_zero_iff_eq_C, totalDegree_eq_zero_iff]
  intro m hm v
  have := monomial_le_degreeOf v hm
  rw [h v] at this
  omega

end Constant

section Form

open scoped Classical in
/-- **The eliminant form** `elim_d(I)` (Rémond, LNM 1752, Ch. 5, Def. 2.14, for primes): a
generator of `𝔈_d(I)` when this ideal is principal and proper, `1` otherwise. Rémond fixes the
generator by a choice of representatives of the irreducibles; here it is only determined up to a
nonzero constant. -/
noncomputable def elimForm (K : Type*) [Field K] (b : σ → ι) {κ : Type*} (d : κ → ι → ℕ)
    (I : Ideal (MvPolynomial σ K)) : MvPolynomial (GenericVar b d) K :=
  if h : (elimIdeal K b d I).IsPrincipal ∧ elimIdeal K b d I ≠ ⊤ then
    @Submodule.IsPrincipal.generator _ _ _ _ _ (elimIdeal K b d I) h.1
  else 1

variable {K : Type*} [Field K] {κ : Type*} {d : κ → ι → ℕ} {I : Ideal (MvPolynomial σ K)}

theorem span_elimForm_of_isPrincipal (h : (elimIdeal K b d I).IsPrincipal) :
    Ideal.span {elimForm K b d I} = elimIdeal K b d I := by
  classical
  by_cases ht : elimIdeal K b d I = ⊤
  · rw [elimForm, dite_eq_right (fun h' ↦ h'.2 ht), ht, Ideal.span_singleton_one]
  · rw [elimForm, dite_eq_left ⟨h, ht⟩]
    exact Ideal.span_singleton_generator _

theorem elimForm_eq_zero_iff : elimForm K b d I = 0 ↔ elimIdeal K b d I = ⊥ := by
  classical
  constructor
  · intro h0
    by_cases h : (elimIdeal K b d I).IsPrincipal
    · rw [← span_elimForm_of_isPrincipal h, h0, Ideal.span_singleton_eq_bot]
    · rw [elimForm, dite_eq_right (fun h' ↦ h h'.1)] at h0
      exact absurd h0 one_ne_zero
  · intro h
    have hp : (elimIdeal K b d I).IsPrincipal := h ▸ bot_isPrincipal
    have := span_elimForm_of_isPrincipal hp
    rwa [h, Ideal.span_singleton_eq_bot] at this

end Form

section Corollary

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {κ : Type u} [Finite κ] {K : Type u} [Field K] {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]

/-- **Rémond's Cor. 2.15 (1)**: `elim_d(𝔭) = 0` if and only if `𝔪 ⊄ 𝔭` and
`e_J(𝔭) ≥ r_J(d)` for all `J`. -/
theorem elimForm_eq_zero_iff_forall (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ) :
    elimForm K b d 𝔭 = 0 ↔ ¬irrelevantIdeal K b ≤ 𝔭 ∧
      ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J := by
  rw [elimForm_eq_zero_iff, elimIdeal_eq_bot_iff hb h𝔭]

/-- **Rémond's Cor. 2.15 (2)**: if `e_J(𝔭) ≥ r_J(d) - 1` for all `J`, then `elim_d(𝔭)`
generates `𝔈_d(𝔭)`. -/
theorem span_elimForm (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ)
    (h : ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J + 1) :
    Ideal.span {elimForm K b d 𝔭} = elimIdeal K b d 𝔭 :=
  span_elimForm_of_isPrincipal (isPrincipal_elimIdeal hb h𝔭 d h)

/-- **Dropping one form loses at most one from each `r_J`**, so the criterion of
Thm 2.13 (1) fails for `d` minus one form when `e_J(𝔭) ≤ r_J(d) - 2` for some `J`. -/
theorem elimIdeal_subtype_ne_bot (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ) (l : κ) {J : Finset ι}
    (hJ : blockRank 𝔭 b J + 2 ≤ numForms d J + #J) :
    elimIdeal K b (d ∘ ((↑) : {l' // l' ≠ l} → κ)) 𝔭 ≠ ⊥ := by
  classical
  intro h0
  have h1 := ((elimIdeal_eq_bot_iff hb h𝔭 _).mp h0).2 J
  have h2 : numForms d J ≤ numForms (d ∘ ((↑) : {l' // l' ≠ l} → κ)) J + 1 := by
    rw [← numForms_comp_equiv (Equiv.optionSubtypeNe l), numForms_option]
    refine Nat.add_le_add_left ?_ _
    by_cases hs : ∀ i, (d ∘ Equiv.optionSubtypeNe l) none i ≠ 0 → i ∈ (J : Set ι)
    · rw [Set.indicator_of_mem (by exact hs)]
      rfl
    · rw [Set.indicator_of_notMem (by exact hs)]
      exact Nat.zero_le _
  omega

/-- **Rémond's Cor. 2.15 (3)**, the key step: if `𝔪 ⊄ 𝔭` and `e_J(𝔭) ≤ r_J(d) - 2` for some
`J`, then `𝔈_d(𝔭)` is not principal. A generator would divide nonzero elements of each
`𝔈_{d'}(𝔭) ⊆ 𝔈_d(𝔭)`, `d'` the forms other than one, so it would be a constant. -/
theorem not_isPrincipal_elimIdeal (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ)
    (hm : ¬irrelevantIdeal K b ≤ 𝔭) {J : Finset ι}
    (hJ : blockRank 𝔭 b J + 2 ≤ numForms d J + #J) : ¬(elimIdeal K b d 𝔭).IsPrincipal := by
  rintro ⟨F, hF⟩
  have hF' : elimIdeal K b d 𝔭 = Ideal.span {F} := hF
  have hdeg : ∀ v, degreeOf v F = 0 := by
    rintro ⟨l, m⟩
    obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (elimIdeal_subtype_ne_bot hb h𝔭 d l hJ)
    have hmem := rename_mem_elimIdeal _ d hg
    rw [hF', Ideal.mem_span_singleton] at hmem
    have hne : rename (subVar (b := b) ((↑) : {l' // l' ≠ l} → κ) d) g ≠ 0 := fun h0 ↦
      hg0 (rename_injective _ (subVar_injective _ d Subtype.val_injective) (h0.trans
        (map_zero _).symm))
    refine degreeOf_eq_zero_of_dvd hmem hne (degreeOf_rename_of_notMem_range ?_ g)
    rintro ⟨⟨l', m'⟩, h⟩
    exact l'.2 (Sigma.mk.inj_iff.mp h).1
  have hC := eq_C_of_forall_degreeOf_eq_zero hdeg
  have hbot : elimIdeal K b d 𝔭 ≠ ⊥ := fun h0 ↦ by
    have := ((elimIdeal_eq_bot_iff hb h𝔭 d).mp h0).2 J
    have hcard := card_le_blockRank hb h𝔭 (hilbertPoly_ne_zero_of_not_le hb h𝔭 hm) J
    omega
  have hc0 : F.coeff 0 ≠ 0 := fun h0 ↦ hbot (by
    rw [hF', hC, h0, map_zero, Ideal.span_singleton_eq_bot])
  have := (isPrime_elimIdeal (d := d) hm).ne_top
  rw [hF', hC] at this
  exact this (Ideal.span_singleton_eq_top.mpr ((isUnit_iff_ne_zero.mpr hc0).map C))

/-- **Rémond's Cor. 2.15 (3)**: if `e_J(𝔭) ≤ r_J(d) - 2` for some `J`, then `elim_d(𝔭) = 1`. -/
theorem elimForm_eq_one (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ) {J : Finset ι}
    (hJ : blockRank 𝔭 b J + 2 ≤ numForms d J + #J) : elimForm K b d 𝔭 = 1 := by
  classical
  rw [elimForm, dite_eq_right]
  rintro ⟨hp, ht⟩
  by_cases hm : irrelevantIdeal K b ≤ 𝔭
  · exact ht (elimIdeal_eq_top_of_le hm)
  · exact not_isPrincipal_elimIdeal hb h𝔭 d hm hJ hp

end Corollary

end MvPolynomial

end
