/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.EliminantCriterion
public import ForMathlib.RingTheory.Polynomial.PrimeOverZero

/-!
# Principality of eliminant ideals

Rémond's principality theorem for eliminant ideals of primes (G. Rémond, *Élimination
multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.), *Introduction to algebraic independence
theory*, LNM 1752 (2001), Theorem 2.13 (2)): if `e_J(𝔭) ≥ r_J(d) - 1` for every set `J` of
blocks, in terms of ranks `r_J(d) + |J| ≤ blockRank 𝔭 b J + 1`, then `𝔈_d(𝔭)` is principal
(`isPrincipal_elimIdeal`).

## Main results

* `ker_substMod`: `𝔈_d(𝔭)` is the kernel of Rémond's substitution taken modulo `𝔭`,
  `u^{(l)}_m ↦ ∑_{m'} (s_{m,m'} - s_{m',m}) x^{m'}` (Lemma 2.3).
* `eq_zero_of_rename_mem_elimIdeal`: if `𝔈_{d'}(𝔭) = 0` for the forms other than the first and
  `x^{m₀} ∉ 𝔭`, then `𝔈_d(𝔭)` contains no nonzero polynomial free of `Z = u^{(0)}_{m₀}`. The
  specialization `s^{(0)}_{m, m₀} ↦ Y_m` turns the substitution into `u^{(0)}_m ↦ x^{m₀} Y_m`,
  injective on the other variables.
* `isPrincipal_of_rename_mem_eq_zero`: a prime of `K[W]` meeting `K[W ∖ Z]` only in `0` is
  principal, by Gauss's lemma in `K[W ∖ Z][Z]`.
* `isPrincipal_elimIdeal`: Thm 2.13 (2). The sets `J` with `e_J(𝔭) = r_J(d) - 1` are stable
  under intersection (`J ↦ blockRank` is submodular, `J ↦ r_J(d)` supermodular). A form
  supported in the smallest one is dropped: the remaining forms satisfy the criterion of
  Thm 2.13 (1) (`elimIdeal_eq_bot_iff`), and the previous two results apply.

Unlike Rémond, the field `K` need not be infinite.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
variable {K : Type*} [Field K] {κ : Type*}

section Generic

variable {B D : Type*} [CommRing D]

/-- Scaling the variables, `X_m ↦ c X_m`. -/
noncomputable def scaleX (c : D) : MvPolynomial B D →+* MvPolynomial B D :=
  eval₂Hom C fun m ↦ C c * X m

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem coeff_scaleX (c : D) (p : MvPolynomial B D) (k : B →₀ ℕ) :
    (scaleX c p).coeff k = c ^ k.degree * p.coeff k := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial k' a =>
    have : scaleX c (monomial k' a) = monomial k' (c ^ k'.degree * a) := by
      rw [scaleX, eval₂Hom_monomial, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
      rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, ← mul_assoc, ← map_mul,
        mul_comm a, ← Finsupp.prod, ← monomial_eq]
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [hp, hq, mul_add]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem scaleX_injective [IsDomain D] {c : D} (hc : c ≠ 0) :
    Function.Injective (scaleX (B := B) c) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  ext k
  have := coeff_scaleX c p k
  rw [hp] at this
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hc)

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem sumRingEquiv_symm_C {R S₁ S₂ : Type*} [CommRing R] (p : MvPolynomial S₂ R) :
    (sumRingEquiv R S₁ S₂).symm (C p) = rename Sum.inr p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [sumRingEquiv_symm_C_C, rename_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, sumRingEquiv_symm_C_X, map_mul, rename_X]

end Generic

section SubstMod

variable (b) (d : κ → ι → ℕ) (𝔭 : Ideal (MvPolynomial σ K))

/-- Rémond's substitution modulo `𝔭`: `u^{(l)}_m ↦ ∑_{m'} (s_{m,m'} - s_{m',m}) x^{m'}` with
`x = X mod 𝔭`, a map `K[d] → (K[X]/𝔭)[s]`. -/
noncomputable def substMod :
    MvPolynomial (GenericVar b d) K →+* MvPolynomial (PairVar b d) (MvPolynomial σ K ⧸ 𝔭) :=
  eval₂Hom (C.comp (algebraMap K _)) fun v ↦ ∑ m' : blockMonomials b (d v.1),
    C (Ideal.Quotient.mk 𝔭 (monomial (m' : σ →₀ ℕ) 1)) * (X ⟨v.1, v.2, m'⟩ - X ⟨v.1, m', v.2⟩)

theorem substMod_eq :
    substMod b d 𝔭 = (map (Ideal.Quotient.mk 𝔭)).comp
      ((commAlgEquiv K (PairVar b d) σ).symm.toRingEquiv.toRingHom.comp (substCoeff K b d)) := by
  have key : ∀ (m : σ →₀ ℕ) (w : PairVar b d), (commAlgEquiv K (PairVar b d) σ).symm
      (monomial m (X w)) = C (monomial m 1) * X w := by
    intro m w
    rw [AlgEquiv.symm_apply_eq, map_mul, commAlgEquiv_C, commAlgEquiv_X, map_monomial, map_one,
      mul_comm, C_mul_monomial, mul_one]
  have key0 : ∀ a : K, (commAlgEquiv K (PairVar b d) σ).symm (C (C a)) = C (C a) := by
    intro a
    rw [AlgEquiv.symm_apply_eq, commAlgEquiv_C, map_C]
  refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
  · simp [substMod, substCoeff, key0]
    rfl
  · simp only [substMod, substCoeff, eval₂Hom_X', RingHom.coe_comp, Function.comp_apply,
      map_sum, map_sub]
    refine Finset.sum_congr rfl fun m' _ ↦ ?_
    change _ = map (Ideal.Quotient.mk 𝔭) ((commAlgEquiv K (PairVar b d) σ).symm _) -
      map (Ideal.Quotient.mk 𝔭) ((commAlgEquiv K (PairVar b d) σ).symm _)
    rw [key, key]
    simp only [map_mul, map_C, map_X]
    ring

/-- **The eliminant ideal is the kernel of Rémond's substitution modulo `𝔭`** (Lemma 2.3). -/
theorem ker_substMod [𝔭.IsPrime] (hm : ¬irrelevantIdeal K b ≤ 𝔭) :
    RingHom.ker (substMod b d 𝔭) = elimIdeal K b d 𝔭 := by
  have h1 : (𝔭.map (C : MvPolynomial σ K →+* MvPolynomial (PairVar b d) (MvPolynomial σ K))).comap
      (commAlgEquiv K (PairVar b d) σ).symm.toRingEquiv.toRingHom = 𝔭.map (map C) := by
    rw [map_map_C_eq]
    exact (Ideal.map_comap_of_equiv _).symm
  rw [substMod_eq, ← RingHom.comap_ker, ker_map, Ideal.mk_ker, ← Ideal.comap_comap, h1,
    elimIdeal, charIdeal_eq_comap_subst hm, Ideal.comap_comap]
  congr 1
  exact RingHom.ext fun f ↦ by simp [subst]

end SubstMod

section Transport

variable {W : Type*}

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- A prime of a ring `A ≅ R[X]`, `R` a unique factorization domain, meeting `R` only in `0` is
principal. -/
theorem isPrincipal_of_ringEquiv {A R : Type*} [CommRing A] [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (φ : A ≃+* Polynomial R) {P : Ideal A} [P.IsPrime]
    (h : ∀ r : R, φ.symm (Polynomial.C r) ∈ P → r = 0) : P.IsPrincipal := by
  set P' := P.comap (φ.symm : Polynomial R →+* A)
  have hmem : ∀ y, y ∈ P ↔ φ y ∈ P' := fun y ↦ by
    rw [Ideal.mem_comap]
    change _ ↔ φ.symm (φ y) ∈ P
    rw [RingEquiv.symm_apply_apply]
  by_cases hP : P' = ⊥
  · refine ⟨0, ?_⟩
    ext y
    rw [hmem, hP, Ideal.mem_bot, Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot.mpr rfl,
      Ideal.mem_bot, map_eq_zero_iff φ φ.injective]
  obtain ⟨x, hxP, hx⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.comap_isPrime _ P) hP
  have hP' : P'.comap (Polynomial.C : R →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    exact (Ideal.mem_bot).mpr (h r hr)
  have hspan := Ideal.eq_span_singleton_of_comap_C_eq_bot hP' hxP hx
  refine ⟨φ.symm x, ?_⟩
  ext y
  rw [hmem, hspan, Ideal.mem_span_singleton, Ideal.submodule_span_eq, Ideal.mem_span_singleton,
    ← map_dvd_iff φ, RingEquiv.apply_symm_apply]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- **A prime of `K[W]` meeting `K[W ∖ Z]` only in `0` is principal**, by Gauss's lemma in
`K[W ∖ Z][Z]`. -/
theorem isPrincipal_of_rename_mem_eq_zero (Z : W) {P : Ideal (MvPolynomial W K)} [P.IsPrime]
    (h : ∀ f : MvPolynomial {w // w ≠ Z} K, rename Subtype.val f ∈ P → f = 0) :
    P.IsPrincipal := by
  classical
  let e : MvPolynomial W K ≃ₐ[K] Polynomial (MvPolynomial {w // w ≠ Z} K) :=
    (renameEquiv K (Equiv.optionSubtypeNe Z).symm).trans (optionEquivLeft K _)
  have he : ∀ f, e (rename Subtype.val f) = Polynomial.C f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [e]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p w hp =>
      rw [map_mul, map_mul, hp, map_mul, rename_X]
      congr 1
      simp [e, Equiv.optionSubtypeNe_symm_of_ne w.2]
  refine isPrincipal_of_ringEquiv e.toRingEquiv fun f hf ↦ h f ?_
  have : e.toRingEquiv.symm (Polynomial.C f) = rename Subtype.val f := by
    rw [← he]
    exact e.symm_apply_apply _
  rwa [this] at hf

end Transport

section Special

variable {κ : Type*} (d : Option κ → ι → ℕ) (𝔭 : Ideal (MvPolynomial σ K))
  (m₀ : blockMonomials b (d none))

open scoped Classical in
/-- The specialization of the `s`-variables: `s^{(0)}_{m, m₀} ↦ Y_m` for `m ≠ m₀`, the other
`s^{(0)}` to `0`, and the `s^{(l)}`, `l ≠ 0`, to themselves. -/
noncomputable def specVar : PairVar b d →
    MvPolynomial ({m : blockMonomials b (d none) // m ≠ m₀} ⊕
      PairVar b (fun l : κ ↦ d (some l))) (MvPolynomial σ K ⧸ 𝔭)
  | ⟨none, (m, m')⟩ => if h : m' = m₀ ∧ m ≠ m₀ then X (Sum.inl ⟨m, h.2⟩) else 0
  | ⟨some l, (m, m')⟩ => X (Sum.inr ⟨l, (m, m')⟩)

/-- The variables of `K[d]` other than `Z = u^{(0)}_{m₀}`. -/
def restEquiv : {v : GenericVar b d // v ≠ ⟨none, m₀⟩} ≃
    {m : blockMonomials b (d none) // m ≠ m₀} ⊕ GenericVar b (fun l : κ ↦ d (some l)) where
  toFun
    | ⟨⟨none, m⟩, h⟩ => .inl ⟨m, fun h' ↦ h (h' ▸ rfl)⟩
    | ⟨⟨some l, m⟩, _⟩ => .inr ⟨l, m⟩
  invFun
    | .inl ⟨m, h⟩ => ⟨⟨none, m⟩, fun h' ↦ h (eq_of_heq (Sigma.mk.inj h').2)⟩
    | .inr ⟨l, m⟩ => ⟨⟨some l, m⟩, fun h' ↦ Option.some_ne_none l (Sigma.mk.inj h').1⟩
  left_inv := by rintro ⟨⟨_ | l, m⟩, h⟩ <;> rfl
  right_inv := by rintro (⟨m, h⟩ | ⟨l, m⟩) <;> rfl

/-- The composite of Rémond's substitution modulo `𝔭`, restricted to the variables other than
`Z`, with the specialization. -/
noncomputable def specHom : MvPolynomial {v : GenericVar b d // v ≠ ⟨none, m₀⟩} K →+*
    MvPolynomial ({m : blockMonomials b (d none) // m ≠ m₀} ⊕
      PairVar b (fun l : κ ↦ d (some l))) (MvPolynomial σ K ⧸ 𝔭) :=
  (sumRingEquiv _ _ _).symm.toRingHom.comp
    ((scaleX (C (Ideal.Quotient.mk 𝔭 (monomial (m₀ : σ →₀ ℕ) 1)))).comp
      ((map (substMod b (fun l : κ ↦ d (some l)) 𝔭)).comp
        ((sumRingEquiv K _ _).toRingHom.comp (rename (restEquiv d m₀)).toRingHom)))

theorem eval₂Hom_specVar_comp :
    (eval₂Hom C (specVar d 𝔭 m₀)).comp ((substMod b d 𝔭).comp (rename Subtype.val).toRingHom) =
      specHom d 𝔭 m₀ := by
  classical
  refine ringHom_ext (fun a ↦ ?_) ?_
  · simp [specHom, substMod, scaleX]
  · rintro ⟨⟨_ | l, m⟩, h⟩
    · have hm : m ≠ m₀ := fun h' ↦ h (h' ▸ rfl)
      simp only [specHom, substMod, RingHom.coe_comp, Function.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, eval₂Hom_X', map_sum, map_mul,
        map_sub, eval₂Hom_C, RingEquiv.toRingHom_eq_coe, scaleX]
      have hr : restEquiv d m₀ ⟨⟨none, m⟩, h⟩ = Sum.inl ⟨m, hm⟩ := rfl
      rw [hr, sumRingEquiv_X_inl, map_X, eval₂Hom_X', map_mul, sumRingEquiv_symm_C_C,
        sumRingEquiv_symm_X]
      rw [Finset.sum_eq_single m₀ (fun m' _ hm' ↦ by simp [specVar, hm', hm]) (by simp)]
      have h1 : specVar d 𝔭 m₀ ⟨none, (m, m₀)⟩ = X (Sum.inl ⟨m, hm⟩) := by simp [specVar, hm]
      have h2 : specVar d 𝔭 m₀ ⟨none, (m₀, m)⟩ = 0 := by simp [specVar]
      rw [h1, h2]
      ring
    · simp only [specHom, substMod, RingHom.coe_comp, Function.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, eval₂Hom_X', map_sum, map_mul,
        map_sub, eval₂Hom_C, RingEquiv.toRingHom_eq_coe, scaleX]
      have hr : restEquiv d m₀ ⟨⟨some l, m⟩, h⟩ = Sum.inr ⟨l, m⟩ := rfl
      rw [hr, sumRingEquiv_X_inr, map_C, eval₂Hom_C, sumRingEquiv_symm_C, eval₂Hom_X']
      simp [specVar]

/-- **`𝔈_d(𝔭) ∩ K[d ∖ Z] = 0`** (Rémond, LNM 1752, Ch. 5, proof of Thm 2.13 (2)): if
`𝔈_{d'}(𝔭) = 0` and `x^{m₀} ∉ 𝔭`, no nonzero polynomial without `Z = u^{(0)}_{m₀}` lies in
`𝔈_d(𝔭)`. Rémond's substitution followed by the specialization `s^{(0)}_{m, m₀} ↦ Y_m` sends
`u^{(0)}_m ↦ x^{m₀} Y_m` and is injective on `K[d'][u^{(0)}_m : m ≠ m₀]`. -/
theorem eq_zero_of_rename_mem_elimIdeal [𝔭.IsPrime] (hm : ¬irrelevantIdeal K b ≤ 𝔭)
    (hd' : elimIdeal K b (fun l : κ ↦ d (some l)) 𝔭 = ⊥)
    (hm₀ : monomial (m₀ : σ →₀ ℕ) (1 : K) ∉ 𝔭)
    {f : MvPolynomial {v : GenericVar b d // v ≠ ⟨none, m₀⟩} K}
    (hf : rename Subtype.val f ∈ elimIdeal K b d 𝔭) : f = 0 := by
  have h0 : substMod b d 𝔭 (rename Subtype.val f) = 0 := by
    rw [← RingHom.mem_ker, ker_substMod b d 𝔭 hm]
    exact hf
  have h1 : specHom d 𝔭 m₀ f = 0 := by
    rw [← eval₂Hom_specVar_comp]
    simp [h0]
  have hsub : Function.Injective (substMod b (fun l : κ ↦ d (some l)) 𝔭) := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    rw [← RingHom.mem_ker, ker_substMod b _ 𝔭 hm, hd', Ideal.mem_bot] at hg
    exact hg
  have hc : (C (Ideal.Quotient.mk 𝔭 (monomial (m₀ : σ →₀ ℕ) 1)) :
      MvPolynomial (PairVar b fun l : κ ↦ d (some l)) (MvPolynomial σ K ⧸ 𝔭)) ≠ 0 := by
    rw [Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hm₀
  have hinj : Function.Injective (specHom d 𝔭 m₀) :=
    (sumRingEquiv _ _ _).symm.injective.comp ((scaleX_injective hc).comp
      ((map_injective _ hsub).comp ((sumRingEquiv K _ _).injective.comp
        (rename_injective _ (restEquiv d m₀).injective))))
  exact hinj (h1.trans (map_zero _).symm)

end Special

/-- If `𝔪 ⊆ 𝔭`, then `𝔈_d(𝔭)` is the whole ring. -/
theorem elimIdeal_eq_top_of_le {d : κ → ι → ℕ} {𝔭 : Ideal (MvPolynomial σ K)}
    (hm : irrelevantIdeal K b ≤ 𝔭) : elimIdeal K b d 𝔭 = ⊤ := by
  have h1 : (1 : MvPolynomial σ (MvPolynomial (GenericVar b d) K)) ∈ charIdeal K b d 𝔭 := by
    rw [charIdeal_eq_saturation, mem_saturation]
    refine ⟨1, fun g hg ↦ ?_⟩
    rw [pow_one, ← map_irrelevantIdeal (C : K →+* MvPolynomial (GenericVar b d) K)] at hg
    rw [mul_one]
    exact Ideal.mem_sup_left (Ideal.map_mono hm hg)
  rw [elimIdeal, (Ideal.eq_top_iff_one _).mpr h1, Ideal.comap_top]

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- **Rémond's Thm 2.13 (2)**: if `e_J(𝔭) ≥ r_J(d) - 1` for every set `J` of blocks, i.e.
`r_J(d) + |J| ≤ blockRank 𝔭 b J + 1`, then the eliminant ideal `𝔈_d(𝔭)` is principal. The
sets `J` with equality are stable under intersection; a form `d_{l₀}` supported in the
smallest one can be dropped, `𝔈_{d'}(𝔭) = 0` for the others by Thm 2.13 (1), so `𝔈_d(𝔭)` is a
prime meeting `K[d ∖ Z]` only in `0` and is principal by Gauss's lemma. -/
theorem isPrincipal_elimIdeal (hb : Function.Surjective b) {κ : Type u} [Finite κ]
    {K : Type u} [Field K] {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : κ → ι → ℕ)
    (h : ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J + 1) :
    (elimIdeal K b d 𝔭).IsPrincipal := by
  classical
  by_cases hm : irrelevantIdeal K b ≤ 𝔭
  · rw [elimIdeal_eq_top_of_le hm]
    exact top_isPrincipal
  by_cases hall : ∀ J : Finset ι, numForms d J + #J ≤ blockRank 𝔭 b J
  · rw [(elimIdeal_eq_bot_iff hb h𝔭 d).mpr ⟨hm, hall⟩]
    exact bot_isPrincipal
  push Not at hall
  -- the tight sets `J`, with `r_J(d) + |J| = blockRank 𝔭 b J + 1`, are stable under `∩`
  have hinter : ∀ J J' : Finset ι, blockRank 𝔭 b J < numForms d J + #J →
      blockRank 𝔭 b J' < numForms d J' + #J' →
      blockRank 𝔭 b ↑(J ∩ J') < numForms d ↑(J ∩ J') + #(J ∩ J') := by
    intro J J' hJ hJ'
    have h1 := blockRank_inter_add_blockRank_union_le (𝔭 := 𝔭) b J J'
    have h2 := numForms_add_numForms_le d J J'
    have h3 := Finset.card_union_add_card_inter J J'
    have h4 := h (J ∪ J')
    have h5 := h (J ∩ J')
    rw [Finset.coe_union, Finset.coe_inter] at *
    omega
  obtain ⟨J₁, hJ₁⟩ := hall
  obtain ⟨J₀, hJ₀, hmin⟩ := (Finset.univ.filter fun J : Finset ι ↦
    blockRank 𝔭 b J < numForms d J + #J).exists_min_image Finset.card
    ⟨J₁, by simpa using hJ₁⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ₀ hmin
  have hsub : ∀ J : Finset ι, blockRank 𝔭 b J < numForms d J + #J → J₀ ⊆ J := fun J hJ ↦ by
    have := hmin _ (hinter J₀ J hJ₀ hJ)
    rw [← Finset.eq_of_subset_of_card_le Finset.inter_subset_left this]
    exact Finset.inter_subset_right
  -- a form supported in `J₀`
  have hcard := card_le_blockRank hb h𝔭 (hilbertPoly_ne_zero_of_not_le hb h𝔭 hm) J₀
  have hpos : 0 < numForms d J₀ := by omega
  obtain ⟨⟨l₀, hl₀⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  set f := Equiv.optionSubtypeNe l₀
  -- `𝔈_{d'}(𝔭) = 0` for the other forms
  have hd' : elimIdeal K b (fun l ↦ (d ∘ f) (some l)) 𝔭 = ⊥ := by
    refine (elimIdeal_eq_bot_iff hb h𝔭 _).mpr ⟨hm, fun J ↦ ?_⟩
    have hJ := h J
    by_cases hJ0 : ∀ i, (d ∘ f) none i ≠ 0 → i ∈ (J : Set ι)
    · have := numForms_option_of_subset (d ∘ f) hJ0
      rw [numForms_comp_equiv] at this
      omega
    · have := numForms_option_of_not_subset (d ∘ f) hJ0
      rw [numForms_comp_equiv] at this
      have hnt : ¬blockRank 𝔭 b J < numForms d J + #J := fun hlt ↦
        hJ0 fun i hi ↦ hsub J hlt (hl₀ i hi)
      omega
  obtain ⟨m₀, hm₀, hm₀𝔭⟩ := exists_monomial_notMem_of_not_le hm (d l₀)
  have : (elimIdeal K b (d ∘ f) 𝔭).IsPrime := isPrime_elimIdeal hm
  obtain ⟨x, hx⟩ := isPrincipal_of_rename_mem_eq_zero (⟨none, ⟨m₀, hm₀⟩⟩ : GenericVar b (d ∘ f))
    fun g hg ↦ eq_zero_of_rename_mem_elimIdeal (d ∘ f) 𝔭 ⟨m₀, hm₀⟩ hm hd' hm₀𝔭 hg
  refine ⟨reindexEquiv b K f d x, ?_⟩
  rw [← map_reindexEquiv_elimIdeal f d 𝔭, hx, Ideal.submodule_span_eq, Ideal.map_span,
    Set.image_singleton, Ideal.submodule_span_eq]
  rfl

end Main

end MvPolynomial

end
