/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantDegree

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Resultant forms of hypersurface sections

Let `I` be a multihomogeneous ideal with `deg H_I ≤ r - 1`, and `P` a form of multidegree `d₀`
that is not a zero divisor modulo `I`. Specializing the coefficients `u^{(0)}` of the first
generic form to the coefficients of `P` sends `res_d(I)` to `res_{d'}(I + (P))`, up to a nonzero
constant (G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.),
*Introduction to algebraic independence theory*, LNM 1752 (2001), Prop. 3.6).

The proof follows Rémond: `(B[d']/J[d'])_k` is the base change of `(B[d]/I[d])_k` along the
specialization, so `ρ(res_d(I))` divides `res_{d'}(J)` (`χ` is the gcd of the maximal minors of a
presentation); both are forms with the same degree in every group of variables (Prop. 3.4 and
`H_J = Δ_{d₀} H_I`), hence associated.

## Main statements

* `MvPolynomial.sectionMap`: the specialization `ρ : K[d] → K[d']`, `u^{(0)} ↦ P`.
* `MvPolynomial.map_sectionMap_genericIdeal`: `ρ(I[d]) = (I + (P))[d']`.
* `MvPolynomial.associated_sectionMap_resForm`: **Prop. 3.6**.
-/

@[expose] public section

open scoped Finset

namespace MvPolynomial

section Homogeneous

variable {V R : Type*} [Field R]

/-- A divisor of a nonzero form of the same degree is an associate. -/
theorem associated_of_dvd_of_isHomogeneous {f g : MvPolynomial V R} {n : ℕ} (hfg : f ∣ g)
    (hg0 : g ≠ 0) (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) : Associated f g := by
  obtain ⟨h, rfl⟩ := hfg
  have hf0 : f ≠ 0 := left_ne_zero_of_mul hg0
  have hh0 : h ≠ 0 := right_ne_zero_of_mul hg0
  have hdeg := hg.totalDegree hg0
  rw [totalDegree_mul_of_isDomain hf0 hh0, hf.totalDegree hf0] at hdeg
  have hC : h = C (h.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (by omega)
  have hc : h.coeff 0 ≠ 0 := fun h' ↦ hh0 (by rw [hC, h', C_0])
  rw [hC]
  exact associated_mul_unit_right _ _ ((isUnit_iff_ne_zero.mpr hc).map C)

end Homogeneous

section Defs

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type*} [Field K]

section Groups

variable {κ : Type*} [Fintype κ] {d : κ → ι → ℕ}

/-- A polynomial in `K[d]` homogeneous in every group of variables is homogeneous of the total
degree. -/
theorem isHomogeneous_of_forall_groupWeight {p : MvPolynomial (GenericVar b d) K} {n : κ → ℕ}
    (h : ∀ l, IsWeightedHomogeneous (groupWeight b d l) p (n l)) :
    p.IsHomogeneous (∑ l, n l) := by
  classical
  intro c hc
  rw [← Finset.sum_congr rfl fun l _ ↦ h l hc]
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp [groupWeight]

end Groups

section Section

variable {κ : Type*} (d : Option κ → ι → ℕ)

variable (b) in
/-- **The specialization of the first generic form to `P`**: the ring hom
`ρ : K[d] → K[d']` with `ρ(u^{(0)}_m) = [X^m] P` and `ρ(u^{(l)}_m) = u^{(l)}_m` for `l ≠ 0`
(Rémond, LNM 1752, Ch. 5, Prop. 3.6). -/
noncomputable def sectionMap (P : MvPolynomial σ K) :
    MvPolynomial (GenericVar b d) K →+* MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K :=
  (map (eval fun v : GenericVar b (fun _ : Unit ↦ d none) ↦ P.coeff (v.2 : σ →₀ ℕ))).comp
    (splitEquiv b K d).toRingHom

variable {d}

@[simp]
theorem sectionMap_C (P : MvPolynomial σ K) (a : K) : sectionMap b d P (C a) = C a := by
  simp [sectionMap, splitEquiv_C]

@[simp]
theorem sectionMap_X_some (P : MvPolynomial σ K) (l : κ) (m : blockMonomials b (d (some l))) :
    sectionMap b d P (X ⟨some l, m⟩) = X ⟨l, m⟩ := by
  simp [sectionMap, splitEquiv_X_some]

@[simp]
theorem sectionMap_X_none (P : MvPolynomial σ K) (m : blockMonomials b (d none)) :
    sectionMap b d P (X ⟨none, m⟩) = C (P.coeff (m : σ →₀ ℕ)) := by
  simp [sectionMap, splitEquiv_X_none]

/-- Specializing the generic form of multidegree `e` to a form `P` of multidegree `e` gives `P`. -/
theorem map_eval_genericForm {e : ι → ℕ} {P : MvPolynomial σ K}
    (hP : IsWeightedHomogeneous (multiWeight b) P e) :
    map (eval fun v : GenericVar b (fun _ : Unit ↦ e) ↦ P.coeff (v.2 : σ →₀ ℕ))
      (genericForm K b (fun _ : Unit ↦ e) ()) = P := by
  classical
  refine MvPolynomial.ext _ _ fun α ↦ ?_
  simp only [genericForm, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
  rw [Finset.sum_coe_sort (blockMonomials b e) fun x ↦ if x = α then P.coeff x else 0,
    Finset.sum_ite_eq']
  by_cases hα : α ∈ blockMonomials b e
  · simp only [hα, ↓reduceIte]
  · simp only [hα, ↓reduceIte]
    by_contra h0
    exact hα (mem_blockMonomials.mpr (hP (Ne.symm h0)))

/-- **`ρ(I[d]) = (I + (P))[d']`**: specializing `U_0` to `P` turns the generic ideal of `I` of
index `d` into that of `I + (P)` of index `d'`. -/
theorem map_sectionMap_genericIdeal {P : MvPolynomial σ K}
    (hP : IsWeightedHomogeneous (multiWeight b) P (d none)) (I : Ideal (MvPolynomial σ K)) :
    (genericIdeal K b d I).map (map (sectionMap b d P)) =
      genericIdeal K b (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P}) := by
  set c := fun v : GenericVar b (fun _ : Unit ↦ d none) ↦ P.coeff (v.2 : σ →₀ ℕ)
  have hmap : (map (sectionMap b d P) : MvPolynomial σ (MvPolynomial (GenericVar b d) K) →+* _) =
      (map (map (eval c))).comp (map (splitEquiv b K d).toRingHom) := by
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map]
    rfl
  rw [hmap, ← Ideal.map_map, map_splitEquiv_genericIdeal, map_map_genericIdeal]
  congr 1
  rw [genericIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, ← Set.range_comp,
    Set.range_unique]
  congr 1
  · convert Ideal.map_id I
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun a ↦ by simp
  · simp only [Function.comp_apply]
    rw [map_eval_genericForm hP]

end Section

end Defs

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Fintype κ] {d : Option κ → ι → ℕ}

/-- **Rémond's Prop. 3.6** (LNM 1752, Ch. 5): let `I` be multihomogeneous with
`deg H_I ≤ r - 1`, and `P` a form of multidegree `d₀` that is not a zero divisor modulo `I`.
Specializing the coefficients of the first generic form to those of `P` sends `res_d(I)` to
`res_{d'}(I + (P))`, up to a nonzero constant. -/
theorem associated_sectionMap_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    {P : MvPolynomial σ K} (hP : IsWeightedHomogeneous (multiWeight b) P (d none)) (hP0 : P ≠ 0)
    (hcol : I.colon {P} = I) (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) :
    Associated (sectionMap b d P (resForm b K d I))
      (resForm b K (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P})) := by
  classical
  have hJ : (I ⊔ Ideal.span {P}).IsWeightedHomogeneous (multiWeight b) :=
    hI.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨d none, (Set.mem_singleton_iff.mp hx) ▸ hP⟩)
  have hHJ : hilbertPoly b (I ⊔ Ideal.span {P}) =
      hilbertPoly b I - shiftPoly (d none) (hilbertPoly b I) :=
    hilbertPoly_sup_span_singleton_of_colon_eq hb hI hP hP0 hcol
  have hcardI : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  -- `H_J` vanishes, or `J` has the right dimension for `d'`.
  have hdegJ : hilbertPoly b (I ⊔ Ideal.span {P}) = 0 ∨
      (hilbertPoly b (I ⊔ Ideal.span {P})).totalDegree + 1 ≤ Fintype.card κ := by
    by_cases h0 : (hilbertPoly b I).totalDegree = 0
    · left
      rw [hHJ, totalDegree_eq_zero_iff_eq_C.mp h0, shiftPoly_C, sub_self]
    · right
      have := totalDegree_sub_shiftPoly_le (d none) (hilbertPoly b I)
      rw [hHJ]
      omega
  -- `res_{d'}(J)` is the eventual value of `χ`.
  have hresJ : ∃ k₁ : ι → ℕ, ∀ k, k₁ ≤ k →
      Associated (Module.charForm _ (genPiece b K (fun l : κ ↦ d (some l))
        (I ⊔ Ideal.span {P}) k)) (resForm b K (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P})) := by
    rcases hdegJ with hJ0 | hJd
    · obtain ⟨k₁, hu⟩ := isUnit_charForm_genPiece_of_forall (d := fun l : κ ↦ d (some l)) hb hJ
        fun 𝔮 _ h𝔮 hJ𝔮 ↦ Or.inl (by
          by_contra hm
          exact hilbertPoly_ne_zero_of_le hb hJ h𝔮 hJ𝔮
            (hilbertPoly_ne_zero_of_not_le hb h𝔮 hm) hJ0)
      have h1 := associated_resForm_of ⟨k₁, fun k hk ↦ associated_one_iff_isUnit.mpr (hu k hk)⟩
      exact ⟨k₁, fun k hk ↦ (associated_one_iff_isUnit.mpr (hu k hk)).trans h1.symm⟩
    · exact (associated_resForm_prod hb hJ (by rwa [Nat.card_eq_fintype_card])).1
  -- `ρ(res_d(I)) ∣ res_{d'}(J)`: the pieces of `J` are base changes of those of `I`.
  have hdvd : sectionMap b d P (resForm b K d I) ∣
      resForm b K (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P}) := by
    obtain ⟨⟨k₀, hk₀⟩, -⟩ := associated_resForm_prod (d := d) hb hI hcardI
    obtain ⟨k₁, hk₁⟩ := hresJ
    set k := k₀ ⊔ k₁
    let : Algebra (MvPolynomial (GenericVar b d) K)
        (MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K) := (sectionMap b d P).toAlgebra
    have hbc := gradedPiece.isBaseChange
      (R' := MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K) (genericIdeal K b d I)
      (isWeightedHomogeneous_genericIdeal hI) k
    have e : gradedPiece b ((genericIdeal K b d I).map (map (algebraMap
        (MvPolynomial (GenericVar b d) K)
        (MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K)))) k ≃ₗ[_]
        genPiece b K (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P}) k :=
      Submodule.quotEquivOfEq _ _ (by rw [← map_sectionMap_genericIdeal hP I]; rfl)
    have h := Module.algebraMap_charForm_dvd_of_isBaseChange (hbc.comp (IsBaseChange.ofEquiv e))
    exact (((hk₀ k le_sup_left).map (sectionMap b d P)).symm.dvd.trans h).trans
      (hk₁ k le_sup_right).dvd
  rcases hdegJ with hJ0 | hJd
  · -- `res_{d'}(J)` is a unit.
    obtain ⟨k₁, hk₁⟩ := hresJ
    obtain ⟨k₂, hu⟩ := isUnit_charForm_genPiece_of_forall (d := fun l : κ ↦ d (some l)) hb hJ
      fun 𝔮 _ h𝔮 hJ𝔮 ↦ Or.inl (by
        by_contra hm
        exact hilbertPoly_ne_zero_of_le hb hJ h𝔮 hJ𝔮 (hilbertPoly_ne_zero_of_not_le hb h𝔮 hm) hJ0)
    have hunit := (hk₁ (k₁ ⊔ k₂) le_sup_left).isUnit_iff.mp (hu _ le_sup_right)
    exact associated_of_dvd_dvd hdvd hunit.dvd
  -- Both forms have the same degree in every group `u^{(l)}`, `l ≠ 0` (Prop. 3.4).
  have key : ∀ l : κ, ∃ n : ℕ,
      IsWeightedHomogeneous (groupWeight b (fun l : κ ↦ d (some l)) l)
        (sectionMap b d P (resForm b K d I)) n ∧
      IsWeightedHomogeneous (groupWeight b (fun l : κ ↦ d (some l)) l)
        (resForm b K (fun l : κ ↦ d (some l)) (I ⊔ Ideal.span {P})) n := by
    intro l
    obtain ⟨n, hn, hhom⟩ := exists_isWeightedHomogeneous_resForm (d := d) hb (some l) hI
      (by rw [Fintype.card_option]; omega)
    obtain ⟨n', hn', hhom'⟩ := exists_isWeightedHomogeneous_resForm
      (d := fun l : κ ↦ d (some l)) hb l hJ hJd
    rw [diffPoly_option, ← hHJ, ← hn'] at hn
    obtain rfl : n = n' := by exact_mod_cast hn
    refine ⟨n, hhom.map_of_forall _ (fun r ↦ ?_) (fun v ↦ ?_), hhom'⟩
    · rw [sectionMap_C]
      exact isWeightedHomogeneous_C _ _
    · obtain ⟨_ | l', m⟩ := v
      · rw [sectionMap_X_none]
        simpa [groupWeight] using isWeightedHomogeneous_C
          (groupWeight b (fun l : κ ↦ d (some l)) l) (P.coeff (m : σ →₀ ℕ))
      · rw [sectionMap_X_some]
        have hw : groupWeight b d (some l) ⟨some l', m⟩ =
            groupWeight b (fun l : κ ↦ d (some l)) l ⟨l', m⟩ := by
          unfold groupWeight
          split_ifs <;> simp_all
        rw [hw]
        exact isWeightedHomogeneous_X K _ _
  choose n hn using key
  exact associated_of_dvd_of_isHomogeneous hdvd
    (resForm_ne_zero hb hJ (by rwa [Nat.card_eq_fintype_card]))
    (isHomogeneous_of_forall_groupWeight fun l ↦ (hn l).1)
    (isHomogeneous_of_forall_groupWeight fun l ↦ (hn l).2)

end Main

end MvPolynomial
