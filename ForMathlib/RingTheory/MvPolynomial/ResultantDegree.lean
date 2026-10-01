/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.GradedPieceBaseChange
public import ForMathlib.RingTheory.MvPolynomial.ResultantForm

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Degrees of resultant forms

The resultant form `res_d(𝔭)` of a multihomogeneous prime of dimension `r - 1` is homogeneous in
the coefficients `u^{(l₀)}` of each generic form, of degree `(∏_{l ≠ l₀} Δ_{d_l}) H_𝔭`, where
`Δ_e H = H - H(T - e)` (G. Rémond, *Élimination multihomogène*, Chapter 5 of
Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001),
Prop. 3.4: `deg(𝔭) * d_2 * ⋯ * d_r`).

## Main statements

* `Matrix.isWeightedHomogeneous_det`: a determinant of forms of degree one.
* `MvPolynomial.IsWeightedHomogeneous.of_map`: homogeneity can be tested after an injective
  graded ring hom.
* `MvPolynomial.diffPoly`: the iterated differences `∏_{l ∈ s} Δ_{d_l}`.
* `MvPolynomial.exists_isWeightedHomogeneous_charForm_of_isLocalization`: homogeneity of `χ`
  descends from a localization of the coefficients.
* `MvPolynomial.exists_isWeightedHomogeneous_charForm_genPiece_of_unique`: one form; `χ` is the
  determinant of the multiplication by the generic form.
* `MvPolynomial.exists_isWeightedHomogeneous_charForm_genPiece_option`: the induction step,
  removing one form via Lemma 2.12.
* `MvPolynomial.exists_isWeightedHomogeneous_resForm`: **Prop. 3.4**.
-/

@[expose] public section

open scoped Finset

section Weighted

open MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

/-- **A determinant of forms of degree one** is a form of degree the size of the matrix. -/
theorem Matrix.isWeightedHomogeneous_det {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial σ R)) (h : ∀ i j, IsWeightedHomogeneous w (M i j) 1) :
    IsWeightedHomogeneous w M.det (Fintype.card n) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun τ _ ↦ ?_
  have := IsWeightedHomogeneous.prod Finset.univ (fun i ↦ M (τ i) i) (fun _ ↦ 1)
    fun i _ ↦ h _ _
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at this
  rw [Units.smul_def]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr this) _)

/-- Over a reduced ring, an associate of a form is a form of the same degree. -/
theorem Associated.isWeightedHomogeneous [IsReduced R] {p q : MvPolynomial σ R} {n : ℕ}
    (h : Associated p q) (hq : IsWeightedHomogeneous w q n) : IsWeightedHomogeneous w p n := by
  obtain ⟨u, hu⟩ := h.symm
  obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  rw [← hu, hr]
  simpa using hq.mul (isWeightedHomogeneous_C w r)

namespace MvPolynomial

variable {σ' R' : Type*} [CommRing R'] {w' : σ' → ℕ}
  (φ : MvPolynomial σ R →+* MvPolynomial σ' R')

/-- A ring hom sending constants to degree `0` and `X_v` to degree `w v` preserves forms. -/
theorem IsWeightedHomogeneous.map_of_forall {p : MvPolynomial σ R} {n : ℕ}
    (hC : ∀ r, IsWeightedHomogeneous w' (φ (C r)) 0)
    (hX : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (hp : IsWeightedHomogeneous w p n) :
    IsWeightedHomogeneous w' (φ p) n := by
  classical
  rw [p.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun c hc ↦ ?_
  have hcn : Finsupp.weight w c = n := hp (mem_support_iff.mp hc)
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, ← hcn, ← zero_add (Finsupp.weight w c)]
  refine (hC _).mul ?_
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ ↦ ?_
  rw [map_pow]
  exact (hX v).pow _

/-- **Homogeneity can be tested after an injective graded ring hom.** -/
theorem IsWeightedHomogeneous.of_map (hinj : Function.Injective φ)
    (hC : ∀ r, IsWeightedHomogeneous w' (φ (C r)) 0)
    (hX : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {p : MvPolynomial σ R} {n : ℕ}
    (h : IsWeightedHomogeneous w' (φ p) n) : IsWeightedHomogeneous w p n := by
  classical
  intro c hc
  by_contra hcn
  set j := Finsupp.weight w c
  have hcomp : ∀ i, weightedHomogeneousComponent w' j (φ (weightedHomogeneousComponent w i p)) =
      if i = j then φ (weightedHomogeneousComponent w i p) else 0 := fun i ↦ by
    have := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) i p).map_of_forall φ hC hX
    split_ifs with hij
    · rw [← hij]
      exact this.weightedHomogeneousComponent_same
    · exact this.weightedHomogeneousComponent_ne j (Ne.symm hij)
  have hφj : φ (weightedHomogeneousComponent w j p) = 0 := by
    have h1 := congrArg (weightedHomogeneousComponent w' j ∘ φ)
      (sum_weightedHomogeneousComponent_image (w := w) p)
    simp only [Function.comp_apply, map_sum, hcomp, Finset.sum_ite_eq'] at h1
    rw [h.weightedHomogeneousComponent_ne j hcn] at h1
    split_ifs at h1 with hj
    · exact h1
    · exact absurd (Finset.mem_image_of_mem _ (mem_support_iff.mpr hc)) hj
  have h0 := congrArg (fun q ↦ q.coeff c) ((map_eq_zero_iff φ hinj).mp hφj)
  exact hc (by simpa [coeff_weightedHomogeneousComponent, j] using h0)

end MvPolynomial

end Weighted

namespace MvPolynomial

section Diff

variable {ι κ : Type*}

theorem shiftPoly_shiftPoly (a e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    shiftPoly e (shiftPoly a P) = shiftPoly (e + a) P := by
  rw [shiftPoly, shiftPoly, shiftPoly]
  change (aeval fun i ↦ X i - C (e i : ℚ)).comp (aeval fun i ↦ X i - C (a i : ℚ)) P = _
  rw [comp_aeval]
  refine congrArg (fun f ↦ aeval f P) (funext fun i ↦ ?_)
  simp only [map_sub, aeval_X, aeval_C, Pi.add_apply, Nat.cast_add, map_add, algebraMap_eq]
  ring

theorem shiftPoly_sub (a : ι → ℕ) (P Q : MvPolynomial ι ℚ) :
    shiftPoly a (P - Q) = shiftPoly a P - shiftPoly a Q :=
  map_sub (aeval fun i ↦ X i - C (a i : ℚ)) P Q

/-- The iterated differences `(∏_{l ∈ s} Δ_{d_l}) H`, `Δ_e H = H - H(T - e)`. -/
noncomputable def diffPoly (d : κ → ι → ℕ) (s : Finset κ) (H : MvPolynomial ι ℚ) :
    MvPolynomial ι ℚ :=
  ∑ t ∈ s.powerset, (-1 : ℚ) ^ #t • shiftPoly (∑ l ∈ t, d l) H

variable (d : κ → ι → ℕ)

@[simp]
theorem diffPoly_empty (H : MvPolynomial ι ℚ) : diffPoly d ∅ H = H := by
  simp [diffPoly, shiftPoly]

theorem diffPoly_insert [DecidableEq κ] {a : κ} {s : Finset κ} (ha : a ∉ s)
    (H : MvPolynomial ι ℚ) :
    diffPoly d (insert a s) H = diffPoly d s (H - shiftPoly (d a) H) := by
  rw [diffPoly, Finset.sum_powerset_insert ha, diffPoly, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hat : a ∉ t := fun h ↦ ha (Finset.mem_powerset.mp ht h)
  rw [Finset.card_insert_of_notMem hat, Finset.sum_insert hat, shiftPoly_sub, shiftPoly_shiftPoly,
    pow_succ, smul_sub, add_comm (d a)]
  module

theorem totalDegree_diffPoly_le [Finite ι] (s : Finset κ)
    (H : MvPolynomial ι ℚ) : (diffPoly d s H).totalDegree ≤ H.totalDegree - #s := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert a s ha ih =>
    rw [diffPoly_insert d ha, Finset.card_insert_of_notMem ha]
    have := totalDegree_sub_shiftPoly_le (d a) H
    have := ih (H - shiftPoly (d a) H)
    omega

@[simp]
theorem diffPoly_zero (s : Finset κ) : diffPoly d s 0 = 0 := by
  simp [diffPoly, shiftPoly]

theorem diffPoly_map {κ' : Type*} (f : κ' ↪ κ) (s : Finset κ') (H : MvPolynomial ι ℚ) :
    diffPoly d (s.map f) H = diffPoly (d ∘ f) s H := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.map_insert, diffPoly_insert d (by simpa using ha), diffPoly_insert _ ha, ih]
    rfl

/-- Splitting off the difference `Δ_{d₀}` of the form `none`. -/
theorem diffPoly_option [Fintype κ] [DecidableEq κ] (d : Option κ → ι → ℕ) (l₀ : κ)
    (H : MvPolynomial ι ℚ) :
    diffPoly d (Finset.univ.erase (some l₀)) H =
      diffPoly (fun l ↦ d (some l)) (Finset.univ.erase l₀) (H - shiftPoly (d none) H) := by
  have : Finset.univ.erase (some l₀) =
      insert none ((Finset.univ.erase l₀).map Function.Embedding.some) := by
    ext (_ | l) <;> simp
  rw [this, diffPoly_insert d (by simp), diffPoly_map]
  rfl

theorem diffPoly_sub (s : Finset κ) (P Q : MvPolynomial ι ℚ) :
    diffPoly d s (P - Q) = diffPoly d s P - diffPoly d s Q := by
  simp [diffPoly, shiftPoly_sub, smul_sub, Finset.sum_sub_distrib]

theorem diffPoly_sum_smul {τ : Type*} (s : Finset κ) (u : Finset τ) (c : τ → ℚ)
    (P : τ → MvPolynomial ι ℚ) :
    diffPoly d s (∑ j ∈ u, c j • P j) = ∑ j ∈ u, c j • diffPoly d s (P j) := by
  simp only [diffPoly, shiftPoly, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- `#s` differences kill polynomials of degree `< #s`. -/
theorem diffPoly_eq_zero_of_totalDegree_lt [Finite ι] {s : Finset κ} {P : MvPolynomial ι ℚ}
    (h : P.totalDegree < #s) : diffPoly d s P = 0 := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty => simp at h
  | insert a s ha ih =>
    rw [diffPoly_insert d ha]
    rw [Finset.card_insert_of_notMem ha] at h
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C.mp h0, shiftPoly_C, sub_self, diffPoly_zero]
    · exact ih ((totalDegree_sub_shiftPoly_le (d a) P).trans_lt (by omega))

/-- `#s` differences only see the coefficients of degree `≥ #s`. -/
theorem diffPoly_eq_zero_of_coeff [Finite ι] {s : Finset κ} {P : MvPolynomial ι ℚ}
    (h : ∀ α : ι →₀ ℕ, #s ≤ α.degree → P.coeff α = 0) : diffPoly d s P = 0 := by
  by_cases hP : P = 0
  · rw [hP, diffPoly_zero]
  refine diffPoly_eq_zero_of_totalDegree_lt d ?_
  obtain ⟨α, hα, hdeg⟩ := exists_coeff_ne_zero_degree_eq hP
  by_contra hle
  exact hα (h α (by omega))

end Diff

section Pieces

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

omit [Fintype σ] [Fintype ι] in
theorem finrank_gradedPiece [Finite σ] [Finite ι] {K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (k : ι → ℕ) :
    Module.finrank K (gradedPiece b I k) = hilbertFunction b I k := by
  set W := weightedHomogeneousSubmodule K (multiWeight b) k
  rw [hilbertFunction, Submodule.finrank_quotient]
  congr 1
  have : (I.restrictScalars K).comap W.subtype = (I.restrictScalars K ⊓ W).comap W.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [this]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

/-- `(R[X]/I)_k = 0` for `𝔪 ⊆ I` and `k ≥ (1, …, 1)`. -/
theorem subsingleton_gradedPiece {R : Type*} [CommRing R] {I : Ideal (MvPolynomial σ R)}
    (hm : irrelevantIdeal R b ≤ I) {k : ι → ℕ} (hk : ∀ i, 1 ≤ k i) :
    Subsingleton (gradedPiece b I k) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : ∀ g : weightedHomogeneousSubmodule R (multiWeight b) k, (g : MvPolynomial σ R) ∈ I :=
    fun g ↦ hm (by simpa using mem_irrelevantIdeal_pow hk g.2)
  exact I.sub_mem (hmem x) (hmem y)

/-- `H_I = 0` when `I` contains the irrelevant ideal. -/
theorem hilbertPoly_eq_zero_of_le (hb : Function.Surjective b) {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hm : irrelevantIdeal K b ≤ I) : hilbertPoly b I = 0 := by
  refine hilbertPoly_eq_of_forall_le hb hI (d₀ := 1) fun k hk ↦ ?_
  have := subsingleton_gradedPiece (b := b) hm (k := k) fun i ↦ by simpa using hk i
  rw [← finrank_gradedPiece, Module.finrank_zero_of_subsingleton]
  simp

/-- Over a domain, units are forms of degree `0`. -/
theorem isWeightedHomogeneous_of_isUnit {V R : Type*} [CommRing R] [IsDomain R] {w : V → ℕ}
    {p : MvPolynomial V R} (h : IsUnit p) : IsWeightedHomogeneous w p 0 := by
  obtain ⟨r, -, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp h
  exact isWeightedHomogeneous_C _ _

end Pieces

section Transfer

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type*} [Field K] {κ : Type*} {d : κ → ι → ℕ}

local notation "Kd" => MvPolynomial (GenericVar b d) K

variable (b d) in
open Classical in
/-- The weight counting the coefficients `u^{(l₀)}` of the generic form `l₀`. -/
noncomputable def groupWeight (l₀ : κ) : GenericVar b d → ℕ := fun v ↦ if v.1 = l₀ then 1 else 0

/-- **Homogeneity of `χ` along a localization of the coefficients.** Let `A'' = L[V]` be a
localization of `K[d]` by a graded map, and `J ⊆ A''[X]` an ideal with the same pieces as `I[d] A''`
in large multidegrees. If `χ((A''[X]/J)_k)` is eventually a form of degree `n`, then so is
`χ((K[d][X]/I[d])_k)`. -/
theorem exists_isWeightedHomogeneous_charForm_of_isLocalization {V L : Type*} [Field L]
    {w : GenericVar b d → ℕ} {w'' : V → ℕ} [Algebra Kd (MvPolynomial V L)] (S : Submonoid Kd)
    [IsLocalization S (MvPolynomial V L)] (hS : S ≤ nonZeroDivisors Kd)
    (hC : ∀ r, IsWeightedHomogeneous w'' (algebraMap Kd (MvPolynomial V L) (C r)) 0)
    (hX : ∀ v, IsWeightedHomogeneous w'' (algebraMap Kd (MvPolynomial V L) (X v)) (w v))
    {𝔭 : Ideal (MvPolynomial σ K)} (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    {J : Ideal (MvPolynomial σ (MvPolynomial V L))}
    (hJ : ∃ k₁ : ι → ℕ, ∀ k, k₁ ≤ k → ∀ g ∈ weightedHomogeneousSubmodule _ (multiWeight b) k,
      g ∈ J ↔ g ∈ (genericIdeal K b d 𝔭).map (map (algebraMap Kd (MvPolynomial V L))))
    {n : ℕ} (hn : ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      IsWeightedHomogeneous w'' (Module.charForm (MvPolynomial V L) (gradedPiece b J k)) n) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      IsWeightedHomogeneous w (Module.charForm Kd (genPiece b K d 𝔭 k)) n := by
  obtain ⟨k₁, hk₁⟩ := hJ
  obtain ⟨k₀, hk₀⟩ := hn
  refine ⟨k₀ ⊔ k₁, fun k hk ↦ ?_⟩
  by_cases hann : Module.annihilator Kd (genPiece b K d 𝔭 k) = ⊥
  · rw [Module.charForm_of_annihilator_eq_bot hann]
    exact isWeightedHomogeneous_zero _ _ _
  have hbc := gradedPiece.isBaseChange (R' := MvPolynomial V L) (genericIdeal K b d 𝔭)
    (isWeightedHomogeneous_genericIdeal h𝔭) k
  have e : gradedPiece b ((genericIdeal K b d 𝔭).map (map (algebraMap Kd (MvPolynomial V L)))) k
      ≃ₗ[MvPolynomial V L] gradedPiece b J k := Submodule.quotEquivOfEq _ _ (by
    ext g
    exact (hk₁ k (le_sup_right.trans hk) g g.2).symm)
  have hassoc := Module.associated_charForm_of_isBaseChange S hS
    (hbc.comp (IsBaseChange.ofEquiv e)) hann
  exact IsWeightedHomogeneous.of_map (algebraMap Kd (MvPolynomial V L))
    (IsLocalization.injective _ hS) hC hX
    (hassoc.symm.isWeightedHomogeneous (hk₀ k (le_sup_left.trans hk)))

end Transfer

section Split

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type*} [Field K] {κ : Type*} [Finite κ]

attribute [local instance] algebraMvPolynomial

/-- **Splitting off one generic form** (Rémond, LNM 1752, Ch. 5, proof of Prop. 3.4). With
`L = Frac(K[u^{(0)}])` and `𝔮 = 𝔄_{(d₀)}(𝔭) L[X]`, if `χ((L[d'][X]/𝔮[d'])_k)` is eventually a form
of degree `n` in `u^{(l₀)}`, then so is `χ((K[d][X]/𝔭[d])_k)`. -/
theorem exists_isWeightedHomogeneous_charForm_genPiece_of_split (d : Option κ → ι → ℕ) (l₀ : κ)
    {𝔭 : Ideal (MvPolynomial σ K)} (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) {n : ℕ}
    (hn : ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      IsWeightedHomogeneous (groupWeight b (fun l : κ ↦ d (some l)) l₀)
        (Module.charForm (MvPolynomial (GenericVar b (fun l : κ ↦ d (some l)))
          (FractionRing (GenericRing K b (d none))))
          (genPiece b (FractionRing (GenericRing K b (d none)))
          (fun l : κ ↦ d (some l)) ((charIdeal K b (fun _ : Unit ↦ d none) 𝔭).map
            (map (algebraMap (GenericRing K b (d none))
              (FractionRing (GenericRing K b (d none)))))) k)) n) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsWeightedHomogeneous (groupWeight b d (some l₀))
      (Module.charForm (MvPolynomial (GenericVar b d) K) (genPiece b K d 𝔭 k)) n := by
  set A := GenericRing K b (d none)
  set L := FractionRing A
  set V := GenericVar b (fun l : κ ↦ d (some l))
  have : IsLocalization ((nonZeroDivisors A).map (C (σ := V))) (MvPolynomial V L) :=
    MvPolynomial.isLocalization _ _
  have hloc := IsLocalization.isLocalization_of_base_ringEquiv
    ((nonZeroDivisors A).map (C (σ := V))) (MvPolynomial V L) (splitEquiv b K d).symm
  let : Algebra (MvPolynomial (GenericVar b d) K) (MvPolynomial V L) :=
    ((algebraMap (MvPolynomial V A) (MvPolynomial V L)).comp
      (splitEquiv b K d).symm.symm.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (GenericVar b d) K) (MvPolynomial V L) p =
      map (algebraMap A L) (splitEquiv b K d p) := fun _ ↦ rfl
  set S : Submonoid (MvPolynomial (GenericVar b d) K) :=
    ((nonZeroDivisors A).map (C (σ := V))).map (splitEquiv b K d).symm
  have hS : S ≤ nonZeroDivisors _ := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, map_eq_zero_iff _ (splitEquiv b K d).symm.injective, C_eq_zero]
    exact nonZeroDivisors.ne_zero ha
  set q := (charIdeal K b (fun _ : Unit ↦ d none) 𝔭).map (map (algebraMap A L))
  have hq : q.IsWeightedHomogeneous (multiWeight b) := isWeightedHomogeneous_map_charIdeal h𝔭
  have hJh := isWeightedHomogeneous_genericIdeal (d := fun l : κ ↦ d (some l)) hq
  have hGh := (isWeightedHomogeneous_genericIdeal (d := d) h𝔭).map
    (algebraMap (MvPolynomial (GenericVar b d) K) (MvPolynomial V L))
  have hsat : saturation b (genericIdeal L b (fun l : κ ↦ d (some l)) q) =
      saturation b ((genericIdeal K b d 𝔭).map
        (map (algebraMap (MvPolynomial (GenericVar b d) K) (MvPolynomial V L)))) := by
    rw [← charIdeal_eq_saturation, charIdeal_map_charIdeal, ← map_saturation S,
      ← charIdeal_eq_saturation, Ideal.map_map]
    congr 1
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map]
    rfl
  obtain ⟨kJ, hkJ⟩ := exists_forall_le_mem_of_mem_saturation hJh
  obtain ⟨kG, hkG⟩ := exists_forall_le_mem_of_mem_saturation hGh
  refine exists_isWeightedHomogeneous_charForm_of_isLocalization S hS (fun r ↦ ?_) (fun v ↦ ?_)
    h𝔭 ⟨kJ ⊔ kG, fun k hk g hg ↦ ?_⟩ hn
  · rw [halg, splitEquiv_C, map_C]
    exact isWeightedHomogeneous_C _ _
  · obtain ⟨_ | l, m⟩ := v
    · rw [halg, splitEquiv_X_none, map_C]
      simpa [groupWeight] using isWeightedHomogeneous_C (groupWeight b (fun l : κ ↦ d (some l)) l₀)
        (algebraMap A L (X ⟨(), m⟩))
    · rw [halg, splitEquiv_X_some, map_X]
      have hw : groupWeight b d (some l₀) ⟨some l, m⟩ =
          groupWeight b (fun l : κ ↦ d (some l)) l₀ ⟨l, m⟩ := by
        unfold groupWeight
        split_ifs <;> simp_all
      rw [hw]
      exact isWeightedHomogeneous_X L _ _
  have hg' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hg
  exact ⟨fun h ↦ hkG k (le_sup_right.trans hk) g (hsat ▸ le_saturation _ h) hg',
    fun h ↦ hkJ k (le_sup_left.trans hk) g (hsat ▸ le_saturation _ h) hg'⟩

/-- **Reindexing the generic forms** along `f : κ' ≃ κ` preserves the degree statement. -/
theorem exists_isWeightedHomogeneous_charForm_genPiece_of_reindex {κ' : Type*} (f : κ' ≃ κ)
    (d : κ → ι → ℕ) (l₀ : κ') {𝔭 : Ideal (MvPolynomial σ K)}
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) {n : ℕ}
    (hn : ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsWeightedHomogeneous (groupWeight b (d ∘ f) l₀)
      (Module.charForm (MvPolynomial (GenericVar b (d ∘ f)) K) (genPiece b K (d ∘ f) 𝔭 k)) n) :
    ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsWeightedHomogeneous (groupWeight b d (f l₀))
      (Module.charForm (MvPolynomial (GenericVar b d) K) (genPiece b K d 𝔭 k)) n := by
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
  have hG : (genericIdeal K b d 𝔭).map (map (algebraMap (MvPolynomial (GenericVar b d) K)
      (MvPolynomial (GenericVar b (d ∘ f)) K))) = genericIdeal K b (d ∘ f) 𝔭 := by
    rw [← map_reindexEquiv_genericIdeal f d, Ideal.map_map]
    convert Ideal.map_id _
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, map_map, RingHom.id_apply]
    convert map_id p
    exact RingHom.ext fun x ↦ e.symm_apply_apply x
  have hfst : ∀ v : GenericVar b d, f ((Equiv.sigmaCongrLeft f
      (β := fun l ↦ blockMonomials b (d l))).symm v).1 = v.1 := fun v ↦
    congrArg Sigma.fst
      ((Equiv.sigmaCongrLeft f (β := fun l ↦ blockMonomials b (d l))).apply_symm_apply v)
  refine exists_isWeightedHomogeneous_charForm_of_isLocalization _ hS (fun r ↦ ?_) (fun v ↦ ?_)
    h𝔭 ⟨0, fun k _ g _ ↦ by rw [hG]⟩ hn
  · rw [halg, show e.symm (C r) = C r from e.symm_apply_eq.mpr (by simp [e, reindexEquiv])]
    exact isWeightedHomogeneous_C _ _
  · rw [halg, show e.symm (X v) = X ((Equiv.sigmaCongrLeft f
        (β := fun l ↦ blockMonomials b (d l))).symm v) from
      e.symm_apply_eq.mpr (by simp [e, reindexEquiv])]
    have hw : groupWeight b (d ∘ f) l₀ ((Equiv.sigmaCongrLeft f
        (β := fun l ↦ blockMonomials b (d l))).symm v) = groupWeight b d (f l₀) v := by
      unfold groupWeight
      rw [← hfst v, f.injective.eq_iff]
    rw [← hw]
    exact isWeightedHomogeneous_X K _ _

end Split

section Base

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} {d : κ → ι → ℕ}

local notation "Kd" => MvPolynomial (GenericVar b d) K

/-- **Multiplication by the generic form** `U = ∑_m u_m X^m` on `(K[d][X]/𝔭 K[d][X])_k`, on
elements coming from `(K[X]/𝔭)_k`. -/
theorem mulMap_genericForm_baseChangeMap {𝔭 : Ideal (MvPolynomial σ K)}
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (l : κ)
    (hmul : ∀ g ∈ 𝔭.map (map (algebraMap K Kd)), g * genericForm K b d l ∈
      𝔭.map (map (algebraMap K Kd))) (k : ι → ℕ) (y : gradedPiece b 𝔭 k) :
    gradedPiece.mulMap (isWeightedHomogeneous_genericForm l) hmul k
        (gradedPiece.baseChangeMap b Kd 𝔭 h𝔭 k y) =
      ∑ m : blockMonomials b (d l), (X ⟨l, m⟩ : Kd) •
        gradedPiece.baseChangeMap b Kd 𝔭 h𝔭 (k + d l)
          (gradedPiece.mulMap (isWeightedHomogeneous_monomial _ (m : σ →₀ ℕ) (1 : K)
            (mem_blockMonomials.mp m.2)) (fun _ hg ↦ 𝔭.mul_mem_right _ hg) k y) := by
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
  simp only [Submodule.mkQ_apply, gradedPiece.baseChangeMap_mk, gradedPiece.mulMap_mk,
    ← Submodule.Quotient.mk_smul]
  simp only [← Submodule.mkQ_apply, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, gradedPiece.coe_polyMap, genericForm,
    Finset.mul_sum, map_mul, map_monomial, map_one, smul_eq_C_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [mul_left_comm, C_mul_monomial, mul_one]

/-- **Rémond's Prop. 3.4 for one form.** For a single generic form `U` of multidegree `e` and a
multihomogeneous prime `𝔭` with constant Hilbert polynomial `H_𝔭 = n`, `χ((B[u]/(𝔭, U))_k)` is
eventually a form of degree `n` in `u`: it is the determinant of the multiplication by `U`,
`(B/𝔭)_{k-e} ⊗ K[u] → (B/𝔭)_k ⊗ K[u]`, an `n × n` matrix of linear forms. -/
theorem exists_isWeightedHomogeneous_charForm_genPiece_of_unique [Unique κ]
    (hb : Function.Surjective b) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hdeg : (hilbertPoly b 𝔭).totalDegree = 0) :
    ∃ n : ℕ, (n : ℚ) = (hilbertPoly b 𝔭).coeff 0 ∧ ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
      IsWeightedHomogeneous (groupWeight b d default)
        (Module.charForm Kd (genPiece b K d 𝔭 k)) n := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, hilbertPoly b 𝔭 = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp hdeg⟩
  obtain ⟨k₂, hk₂⟩ := exists_forall_le_hilbertFunction_eq_hilbertPoly hb h𝔭
  simp only [hc, eval_C] at hk₂
  have hn : (hilbertFunction b 𝔭 k₂ : ℚ) = c := hk₂ k₂ le_rfl
  have hdim : ∀ k, k₂ ≤ k → Module.finrank K (gradedPiece b 𝔭 k) = hilbertFunction b 𝔭 k₂ :=
    fun k hk ↦ by
      rw [finrank_gradedPiece]
      exact_mod_cast (hk₂ k hk).trans hn.symm
  refine ⟨hilbertFunction b 𝔭 k₂, by simp [hn, hc], ?_⟩
  by_cases hm : irrelevantIdeal K b ≤ 𝔭
  · obtain ⟨k₀, hk₀⟩ := isUnit_charForm_genPiece_of_small (d := d) hb h𝔭 (Or.inl hm)
    have hn0 : hilbertFunction b 𝔭 k₂ = 0 := by
      rw [← hdim (k₂ ⊔ 1) le_sup_left]
      have := subsingleton_gradedPiece (b := b) hm (k := k₂ ⊔ 1) fun i ↦
        (le_sup_right : (1 : ℕ) ≤ k₂ i ⊔ 1)
      exact Module.finrank_zero_of_subsingleton
    refine ⟨k₀, fun k hk ↦ ?_⟩
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp (hk₀ k hk)
    rw [hr, hn0]
    exact isWeightedHomogeneous_C _ _
  set l : κ := default
  set 𝔭u := 𝔭.map (map (algebraMap K Kd))
  have h𝔭u : 𝔭u.IsWeightedHomogeneous (multiWeight b) := h𝔭.map _
  have h𝔭up : 𝔭u.IsPrime := by
    have := isPrime_map_map_C (P := GenericVar b d) (I := 𝔭)
    rwa [← algebraMap_eq] at this
  have hU𝔭 : genericForm K b d l ∉ 𝔭u := by
    obtain ⟨m, hm', hm𝔭⟩ := exists_monomial_notMem_of_not_le hm (d l)
    have := genericForm_notMem_map_map_C (d := d) (l := l) hm' hm𝔭
    rwa [← algebraMap_eq] at this
  have hmul : ∀ g ∈ 𝔭u, g * genericForm K b d l ∈ 𝔭u := fun g hg ↦ 𝔭u.mul_mem_right _ hg
  have hgen : genericIdeal K b d 𝔭 = 𝔭u ⊔ Ideal.span {genericForm K b d l} := by
    rw [genericIdeal, Set.range_unique, ← algebraMap_eq]
  refine ⟨k₂ + d l, fun k hk ↦ ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + d l :=
    ⟨k - d l, (tsub_add_cancel_of_le (le_add_self.trans hk)).symm⟩
  have hk' : k₂ ≤ k' := le_of_add_le_add_right hk
  set φ := gradedPiece.mulMap (isWeightedHomogeneous_genericForm l) hmul k' with hφ
  have hex := gradedPiece.exact_mulMap_factor h𝔭u (isWeightedHomogeneous_genericForm l) hmul k'
  have e1 : genPiece b K d 𝔭 (k' + d l) ≃ₗ[Kd]
      gradedPiece b (𝔭u ⊔ Ideal.span {genericForm K b d l}) (k' + d l) :=
    Submodule.quotEquivOfEq _ _ (by rw [hgen])
  rw [Module.charForm_congr (e1.trans (hex.linearEquivOfSurjective
    (gradedPiece.factor_surjective _ _)).symm)]
  have hbc0 := gradedPiece.isBaseChange (R' := Kd) 𝔭 h𝔭 k'
  have hbc1 := gradedPiece.isBaseChange (R' := Kd) 𝔭 h𝔭 (k' + d l)
  set b0 := Module.finBasisOfFinrankEq K _ (hdim k' hk')
  set b1 := Module.finBasisOfFinrankEq K _ (hdim (k' + d l) (hk'.trans le_self_add))
  refine (Module.associated_charForm_quotient_range (IsBaseChange.basis b0 hbc0)
    (IsBaseChange.basis b1 hbc1) φ).isWeightedHomogeneous ?_
  have hentry : ∀ i j, IsWeightedHomogeneous (groupWeight b d l)
      (LinearMap.toMatrix (IsBaseChange.basis b0 hbc0) (IsBaseChange.basis b1 hbc1) φ i j) 1 := by
    intro i j
    rw [LinearMap.toMatrix_apply, IsBaseChange.basis_apply, hφ,
      mulMap_genericForm_baseChangeMap, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine IsWeightedHomogeneous.sum _ _ _ fun m _ ↦ ?_
    rw [map_smul, Finsupp.smul_apply, IsBaseChange.basis_repr_comp_apply, smul_eq_mul,
      algebraMap_eq]
    have key : ∀ a : K, IsWeightedHomogeneous (groupWeight b d l) (X ⟨l, m⟩ * C a : Kd) 1 :=
      fun a ↦ by simpa [groupWeight] using (isWeightedHomogeneous_X K (groupWeight b d l)
        ⟨l, m⟩).mul (isWeightedHomogeneous_C (groupWeight b d l) a)
    exact key _
  have := Matrix.isWeightedHomogeneous_det _ hentry
  rwa [Fintype.card_fin] at this

/-- **Induction step of Rémond's Prop. 3.4**: removing the form `none`. -/
theorem exists_isWeightedHomogeneous_charForm_genPiece_option {κ : Type u} [Fintype κ]
    [DecidableEq κ] (hb : Function.Surjective b) (d : Option κ → ι → ℕ) (l₀ : κ)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    {N : ℕ} (hdeg : (hilbertPoly b 𝔭).totalDegree ≤ N + 1)
    (ih : ∀ (𝔮 : Ideal (MvPolynomial σ (FractionRing (GenericRing K b (d none))))) [𝔮.IsPrime],
      𝔮.IsWeightedHomogeneous (multiWeight b) → (hilbertPoly b 𝔮).totalDegree ≤ N →
      ∃ n : ℕ, (n : ℚ) = (diffPoly (fun l : κ ↦ d (some l)) (Finset.univ.erase l₀)
        (hilbertPoly b 𝔮)).coeff 0 ∧ ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k →
          IsWeightedHomogeneous (groupWeight b (fun l : κ ↦ d (some l)) l₀)
            (Module.charForm (MvPolynomial (GenericVar b (fun l : κ ↦ d (some l)))
              (FractionRing (GenericRing K b (d none))))
              (genPiece b _ (fun l : κ ↦ d (some l)) 𝔮 k)) n) :
    ∃ n : ℕ, (n : ℚ) = (diffPoly d (Finset.univ.erase (some l₀)) (hilbertPoly b 𝔭)).coeff 0 ∧
      ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsWeightedHomogeneous (groupWeight b d (some l₀))
        (Module.charForm (MvPolynomial (GenericVar b d) K) (genPiece b K d 𝔭 k)) n := by
  by_cases hm : irrelevantIdeal K b ≤ 𝔭
  · refine ⟨0, by simp [hilbertPoly_eq_zero_of_le hb h𝔭 hm], ?_⟩
    obtain ⟨k₀, hk₀⟩ := isUnit_charForm_genPiece_of_small (d := d) hb h𝔭 (Or.inl hm)
    exact ⟨k₀, fun k hk ↦ isWeightedHomogeneous_of_isUnit (hk₀ k hk)⟩
  have hH := hilbertPoly_map_charIdeal hb h𝔭 hm (d none)
  rw [diffPoly_option, ← hH]
  by_cases he : elimIdeal K b (fun _ : Unit ↦ d none) 𝔭 = ⊥
  · have := isPrime_map_charIdeal he
    have hdeg' := totalDegree_sub_shiftPoly_le (d none) (hilbertPoly b 𝔭)
    obtain ⟨n, hn, hk⟩ := ih _ (isWeightedHomogeneous_map_charIdeal h𝔭) (by rw [hH]; omega)
    exact ⟨n, hn, exists_isWeightedHomogeneous_charForm_genPiece_of_split d l₀ h𝔭 hk⟩
  have htop := map_charIdeal_eq_top he
  refine ⟨0, by rw [htop, hilbertPoly_top' hb]; simp,
    exists_isWeightedHomogeneous_charForm_genPiece_of_split d l₀ h𝔭 ⟨0, fun k _ ↦ ?_⟩⟩
  rw [htop]
  exact isWeightedHomogeneous_of_isUnit (isUnit_charForm_genPiece_top k)

/-- **Rémond's Prop. 3.4 for primes**, by induction on the number of forms. -/
theorem exists_isWeightedHomogeneous_charForm_genPiece_of_card (hb : Function.Surjective b)
    (N : ℕ) : ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] {K : Type u} [Field K]
      (d : κ → ι → ℕ) (l₀ : κ) (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
      𝔭.IsWeightedHomogeneous (multiWeight b) → Fintype.card κ = N + 1 →
      (hilbertPoly b 𝔭).totalDegree ≤ N →
      ∃ n : ℕ, (n : ℚ) = (diffPoly d (Finset.univ.erase l₀) (hilbertPoly b 𝔭)).coeff 0 ∧
        ∃ k₀ : ι → ℕ, ∀ k, k₀ ≤ k → IsWeightedHomogeneous (groupWeight b d l₀)
          (Module.charForm (MvPolynomial (GenericVar b d) K) (genPiece b K d 𝔭 k)) n := by
  induction N with
  | zero =>
    intro κ _ _ K _ d l₀ 𝔭 _ h𝔭 hκ hdeg
    obtain ⟨_⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hκ
    obtain rfl : l₀ = default := Subsingleton.elim _ _
    obtain ⟨n, hn, hk⟩ := exists_isWeightedHomogeneous_charForm_genPiece_of_unique (d := d) hb h𝔭
      (Nat.le_zero.mp hdeg)
    refine ⟨n, ?_, hk⟩
    rw [hn]
    simp
  | succ N ih =>
    intro κ _ _ K _ d l₀ 𝔭 _ h𝔭 hκ hdeg
    obtain ⟨l₁, hl₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) l₀
    set f := Equiv.optionSubtypeNe l₁
    have hκ' : Fintype.card {l // l ≠ l₁} = N + 1 := by
      have := Fintype.card_congr f
      rw [Fintype.card_option] at this
      omega
    have hfl : f (some ⟨l₀, hl₁.symm⟩) = l₀ := rfl
    obtain ⟨n, hn, hk⟩ := exists_isWeightedHomogeneous_charForm_genPiece_option hb (d ∘ f)
      ⟨l₀, hl₁.symm⟩ h𝔭 hdeg fun 𝔮 _ h𝔮 h𝔮deg ↦ ih _ _ 𝔮 h𝔮 hκ' h𝔮deg
    refine ⟨n, ?_, ?_⟩
    · rw [hn, show d ∘ ⇑f = d ∘ ⇑f.toEmbedding from rfl, ← diffPoly_map]
      rw [Finset.map_erase, Finset.map_univ_equiv, Equiv.coe_toEmbedding, hfl]
    · rw [← hfl]
      exact exists_isWeightedHomogeneous_charForm_genPiece_of_reindex f d _ h𝔭 hk

end Base

section Final

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Fintype κ] [DecidableEq κ] {d : κ → ι → ℕ}

/-- **Rémond's Prop. 3.4 for primes**: for a multihomogeneous prime `𝔭` with
`deg H_𝔭 ≤ r - 1`, `res_d(𝔭)` is a form in `u^{(l₀)}` of degree `(∏_{l ≠ l₀} Δ_{d_l}) H_𝔭`. -/
theorem exists_isWeightedHomogeneous_resForm_of_isPrime (hb : Function.Surjective b) (l₀ : κ)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hdeg : (hilbertPoly b 𝔭).totalDegree + 1 ≤ Fintype.card κ) :
    ∃ n : ℕ, (n : ℚ) = (diffPoly d (Finset.univ.erase l₀) (hilbertPoly b 𝔭)).coeff 0 ∧
      IsWeightedHomogeneous (groupWeight b d l₀) (resForm b K d 𝔭) n := by
  obtain ⟨n, hn, k₀, hk₀⟩ := exists_isWeightedHomogeneous_charForm_genPiece_of_card hb
    (Fintype.card κ - 1) d l₀ 𝔭 h𝔭 (by have := Fintype.card_pos_iff.mpr ⟨l₀⟩; omega)
    (by omega)
  obtain ⟨⟨k₁, hk₁⟩, -⟩ := associated_resForm_prod (d := d) hb h𝔭
    (by rwa [Nat.card_eq_fintype_card])
  exact ⟨n, hn, (hk₁ (k₀ ⊔ k₁) le_sup_right).symm.isWeightedHomogeneous
    (hk₀ _ le_sup_left)⟩

/-- **Rémond's Prop. 3.4** (LNM 1752, Ch. 5): for a multihomogeneous ideal `I` with
`deg H_I ≤ r - 1` (`ht I ≥ n - r + 1`), the resultant form `res_d(I)` is a form in the
coefficients `u^{(l₀)}` of the generic form `l₀`, of degree `(∏_{l ≠ l₀} Δ_{d_l}) H_I`, where
`Δ_e H = H - H(T - e)`; i.e. `deg(I) * d_2 * ⋯ * d_r` for `l₀ = 1`. -/
theorem exists_isWeightedHomogeneous_resForm (hb : Function.Surjective b) (l₀ : κ)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdeg : (hilbertPoly b I).totalDegree + 1 ≤ Fintype.card κ) :
    ∃ n : ℕ, (n : ℚ) = (diffPoly d (Finset.univ.erase l₀) (hilbertPoly b I)).coeff 0 ∧
      IsWeightedHomogeneous (groupWeight b d l₀) (resForm b K d I) n := by
  classical
  obtain ⟨-, S, ℓ, hS, hℓ, hassoc⟩ := associated_resForm_prod (d := d) hb hI
    (by rwa [Nat.card_eq_fintype_card])
  rw [Nat.card_eq_fintype_card] at hS
  have hprime : ∀ 𝔭 ∈ S, ∃ n : ℕ,
      (n : ℚ) = (diffPoly d (Finset.univ.erase l₀) (hilbertPoly b 𝔭)).coeff 0 ∧
        IsWeightedHomogeneous (groupWeight b d l₀) (resForm b K d 𝔭) n := fun 𝔭 h𝔭 ↦ by
    obtain ⟨_, h𝔭h, -, -, h𝔭d⟩ := (hS 𝔭).mp h𝔭
    exact exists_isWeightedHomogeneous_resForm_of_isPrime hb l₀ h𝔭h h𝔭d.le
  choose! n hn hhom using hprime
  refine ⟨∑ 𝔭 ∈ S, ℓ 𝔭 * n 𝔭, ?_, hassoc.isWeightedHomogeneous ?_⟩
  · -- The top-degree part of `H_I` is `∑ ℓ_𝔭 H_𝔭` (associativity formula).
    have hcoeff : ∀ α : ι →₀ ℕ, #(Finset.univ.erase l₀) ≤ α.degree →
        (hilbertPoly b I - ∑ 𝔭 ∈ S, (ℓ 𝔭 : ℚ) • hilbertPoly b 𝔭).coeff α = 0 := by
      intro α hα
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hα
      rw [coeff_sub, coeff_sum, sub_eq_zero]
      simp only [coeff_smul, smul_eq_mul]
      by_cases hlt : (hilbertPoly b I).totalDegree + 1 < Fintype.card κ
      · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun 𝔭 h𝔭 ↦ by
          obtain ⟨_, h𝔭h, hI𝔭, -, h𝔭d⟩ := (hS 𝔭).mp h𝔭
          have := totalDegree_hilbertPoly_le_of_le hb hI h𝔭h hI𝔭
          omega
        have : α.degree = ∑ i ∈ α.support, α i := rfl
        rw [hS0, Finset.sum_empty, coeff_eq_zero_of_totalDegree_lt (by omega)]
      obtain ⟨P, ℓ', hP, hℓ', hH⟩ := coeff_hilbertPoly_eq_sum_localLength hb hI
      have hPS : P = S := Finset.ext fun 𝔭 ↦ by
        rw [hP, hS]
        constructor
        · rintro ⟨hp, h𝔭h, hI𝔭, hne, h𝔭d⟩
          exact ⟨hp, h𝔭h, hI𝔭, fun hm ↦ hne (hilbertPoly_eq_zero_of_le hb h𝔭h hm), by omega⟩
        · rintro ⟨hp, h𝔭h, hI𝔭, hm, h𝔭d⟩
          exact ⟨hp, h𝔭h, hI𝔭, hilbertPoly_ne_zero_of_not_le hb h𝔭h hm, by
            have := totalDegree_hilbertPoly_le_of_le hb hI h𝔭h hI𝔭; omega⟩
      rw [hH α (by omega), hPS]
      refine Finset.sum_congr rfl fun 𝔭 h𝔭 ↦ ?_
      have := ((hS 𝔭).mp h𝔭).1
      have h1 := hℓ 𝔭 h𝔭
      rw [← hPS] at h𝔭
      rw [hℓ' 𝔭 h𝔭] at h1
      rw [Nat.cast_inj.mp h1]
    have h0 := diffPoly_eq_zero_of_coeff d hcoeff
    rw [diffPoly_sub, diffPoly_sum_smul, sub_eq_zero] at h0
    rw [h0, coeff_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun 𝔭 h𝔭 ↦ ?_
    rw [coeff_smul, ← hn 𝔭 h𝔭, smul_eq_mul, Nat.cast_mul]
  · have := IsWeightedHomogeneous.prod S (fun 𝔭 ↦ resForm b K d 𝔭 ^ ℓ 𝔭)
      (fun 𝔭 ↦ ℓ 𝔭 • n 𝔭) fun 𝔭 h𝔭 ↦ (hhom 𝔭 h𝔭).pow (ℓ 𝔭)
    simpa only [smul_eq_mul] using this

end Final

end MvPolynomial
