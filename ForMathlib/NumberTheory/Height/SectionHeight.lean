/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerSpecialization
public import ForMathlib.NumberTheory.Height.BombieriHeight
public import ForMathlib.NumberTheory.Height.ResultantHeight
public import ForMathlib.RingTheory.MvPolynomial.ResultantDegree

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Specializing a resultant form to a hypersurface: local bounds

Let `f = res_d(I)` and `ρ : K[d] → K[d']` the specialization of the coefficients `u^{(0)}` of the
first generic form to those of a form `P` of multidegree `δ = d₀` (`MvPolynomial.sectionMap`;
`ρ(f)` is `res_{d'}(I + (P))` up to a constant, Rémond's Prop. 3.6). If `f` has degree `D` in
`u^{(0)}`, then at every place `ρ(f)` is bounded by `f` times the `D`-th power of the norm of
`P` (LNM 1752, Ch. 7, Lemma 2.1 (2) and Prop. 2.16):

* at an embedding `φ : K → ℂ`, `log M(α ρ(f)) ≤ log M(α f) + D log ‖P‖_φ`, with
  `‖P‖_φ² = ∑_m |φ(p_m)|² / C(δ, m)`;
* at a nonarchimedean `v`, `‖ρ(f)‖_v ≤ ‖f‖_v ‖P‖_v^D` for the Gauss norms.

## Main results

* `MvPolynomial.gaussLogMahler_sectionMap_le`, `MvPolynomial.maxNorm_sectionMap_le`.
* `MvPolynomial.gaussHeight_sectionMap_le`: `h(α ρ(f)) ≤ h(α f) + D h_m(P)`.
* `MvPolynomial.gaussHeight_resForm_sup_le`: **the intersection inequality**
  `h(α res_{d'}(I + (P))) ≤ ∑_i δ_i h(α res_{(ε_i, d')}(I)) + D h_m(P)`.
* `MvPolynomial.sectionMap_eq_aeval`: `ρ` as a substitution.
-/

@[expose] public section

open Real

namespace MvPolynomial

section Subst

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type*} [Field K]
  {κ : Type*} {d : Option κ → ι → ℕ}

variable (b d) in
/-- The variables of `K[d]`, those of `u^{(0)}` first. -/
def sectionVar : GenericVar b d ≃
    GenericVar b (fun _ : Unit ↦ d none) ⊕ GenericVar b (fun l : κ ↦ d (some l)) where
  toFun
    | ⟨none, m⟩ => .inl ⟨(), m⟩
    | ⟨some l, m⟩ => .inr ⟨l, m⟩
  invFun
    | .inl ⟨_, m⟩ => ⟨none, m⟩
    | .inr ⟨l, m⟩ => ⟨some l, m⟩
  left_inv := by rintro ⟨_ | l, m⟩ <;> rfl
  right_inv := by rintro (⟨_, m⟩ | ⟨l, m⟩) <;> rfl

variable (d) in
/-- The substitution of `sectionMap`: `u^{(0)}_m ↦ p_m`, `u^{(l)}_m ↦ u^{(l)}_m`. -/
noncomputable def sectionSubst (P : MvPolynomial σ K) :
    GenericVar b d → MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K
  | ⟨none, m⟩ => C (P.coeff (m : σ →₀ ℕ))
  | ⟨some l, m⟩ => X ⟨l, m⟩

theorem sectionMap_eq_aeval (P : MvPolynomial σ K) (F : MvPolynomial (GenericVar b d) K) :
    sectionMap b d P F = aeval (sectionSubst d P) F := by
  have h : sectionMap b d P = (aeval (sectionSubst (b := b) d P)).toRingHom := by
    refine ringHom_ext (fun a ↦ by simp) fun v ↦ ?_
    rcases v with ⟨_ | l, m⟩ <;> simp [sectionSubst]
  rw [h]
  rfl

/-- **The nonarchimedean bound**: `‖ρ(f)‖_v ≤ ‖f‖_v ‖P‖_v^D` if `f` has degree `D` in `u^{(0)}`. -/
theorem maxNorm_sectionMap_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (P : MvPolynomial σ K) {F : MvPolynomial (GenericVar b d) K} {D : ℕ}
    (hD : IsWeightedHomogeneous (groupWeight b d none) F D) :
    maxNorm v (sectionMap b d P F) ≤ maxNorm v F * maxNorm v P ^ D := by
  classical
  rw [sectionMap_eq_aeval]
  refine maxNorm_aeval_le hv _ F (mul_nonneg (maxNorm_nonneg _) (pow_nonneg (maxNorm_nonneg _) _))
    fun m hm ↦ mul_le_mul (le_maxNorm F m) ?_
      (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (maxNorm_nonneg _) _) (maxNorm_nonneg F)
  have hg : ∀ x, maxNorm v (sectionSubst d P x) ≤ maxNorm v P ^ groupWeight b d none x := by
    rintro ⟨_ | l, m'⟩
    · simpa [sectionSubst, groupWeight] using le_maxNorm P _
    · simp [sectionSubst, groupWeight]
  calc m.prod (fun x k ↦ maxNorm v (sectionSubst d P x) ^ k)
      ≤ m.prod (fun x k ↦ (maxNorm v P ^ groupWeight b d none x) ^ k) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg (maxNorm_nonneg _) _)
          fun x _ ↦ pow_le_pow_left₀ (maxNorm_nonneg _) (hg x) _
    _ = maxNorm v P ^ D := by
        rw [← hD (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
        simp_rw [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum]
        simp [mul_comm]

end Subst

section Arch

variable {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type} [Field K]
  {κ : Type} [Fintype κ] {d : Option κ → ι → ℕ}

/-- **The archimedean bound** (Rémond's Lemma 2.1 (2) with Prop. 2.16): if `f = res_d(I)` has
degree `D` in `u^{(0)}`, then `log M(α ρ(f)) ≤ log M(α f) + D log ‖P‖_φ`. -/
theorem gaussLogMahler_sectionMap_le (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) (P : MvPolynomial σ K)
    (φ : K →+* ℂ) {D : ℕ} (hD : IsWeightedHomogeneous (groupWeight b d none) (resForm b K d I) D)
    (hne : sectionMap b d P (resForm b K d I) ≠ 0) :
    gaussLogMahler (scaleVars remodelWeight (map φ (sectionMap b d P (resForm b K d I)))) ≤
      gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K d I))) +
        D * log √(∑ v : GenericVar b (fun _ : Unit ↦ d none),
          ‖φ (P.coeff (v.2 : σ →₀ ℕ))‖ ^ 2 / blockMultinomial b (v.2 : σ →₀ ℕ)) := by
  classical
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  set f := resForm b K d I
  set G := rename (sectionVar b d) (scaleVars remodelWeight (map φ f))
  set a : GenericVar b (fun _ : Unit ↦ d none) → ℂ := fun v ↦ φ (P.coeff v.2) / remodelWeight v
  have h1 : specLeft a G = scaleVars remodelWeight (map φ (sectionMap b d P f)) := by
    have h : (specLeft a).toRingHom.comp ((rename (sectionVar b d)).toRingHom.comp
        ((scaleVars remodelWeight).toRingHom.comp (map φ))) =
        (scaleVars remodelWeight).toRingHom.comp ((map φ).comp (sectionMap b d P)) := by
      refine ringHom_ext (fun k ↦ by simp [specLeft, scaleVars]) fun v ↦ ?_
      rcases v with ⟨_ | l, m⟩
      · simp only [specLeft, scaleVars, sectionVar, a, AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
          RingHom.coe_coe, Function.comp_apply, map_X, sectionMap_X_none, map_C, algHom_C,
          algebraMap_eq, aeval_X, rename_X, map_mul, Equiv.coe_fn_mk, Sum.elim_inl]
        rw [← C_mul]
        congr 1
        exact mul_div_cancel₀ _ (remodelWeight_ne_zero
          (⟨(), m⟩ : GenericVar b (fun _ : Unit ↦ d none)))
      · simp [specLeft, scaleVars, sectionVar]
        rfl
    exact RingHom.congr_fun h f
  have h2 : IsWeightedHomogeneous (Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)) G D := by
    refine IsWeightedHomogeneous.rename (w := groupWeight b d none) (fun v ↦ ?_) ?_
    · rcases v with ⟨_ | l, m⟩ <;> simp [sectionVar, groupWeight]
    · exact (hD.map φ).aeval_of_algebra _ fun v ↦ (isWeightedHomogeneous_X ℂ _ v).C_mul _
  have h3 : ∀ z, ∃ (c : ℂ) (Z : Multiset (GenericVar b (fun _ : Unit ↦ d none) → ℂ)),
      specRight z G = C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod := by
    intro z
    set y : GenericVar b (fun l : κ ↦ d (some l)) → ℂ := fun v ↦ remodelWeight v * z v
    have hs : specRight z G = scaleVars remodelWeight (specEval b φ y f) := by
      have h : (specRight z).toRingHom.comp ((rename (sectionVar b d)).toRingHom.comp
          ((scaleVars remodelWeight).toRingHom.comp (map φ))) =
          (scaleVars remodelWeight).toRingHom.comp (specEval b φ y) := by
        refine ringHom_ext (fun k ↦ by simp [specRight, scaleVars, specEval]) fun v ↦ ?_
        rcases v with ⟨_ | l, m⟩
        · simp [specRight, scaleVars, sectionVar, specEval]
          rfl
        · simp only [specRight, scaleVars, sectionVar, specEval, y, AlgHom.toRingHom_eq_coe,
            RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, aeval_X, rename_X,
            map_mul, aeval_C, rename_C, Equiv.coe_fn_mk, Sum.elim_inr, algebraMap_eq,
            coe_eval₂Hom, eval₂_X]
          rfl
      exact RingHom.congr_fun h f
    obtain ⟨c, Z, -, hcZ⟩ := exists_specEval_resForm_eq hb hI hcard φ y
    refine ⟨c, Z.map fun x v ↦ remodelWeight v * ∏ s, x s ^ (v.2 : σ →₀ ℕ) s, ?_⟩
    rw [hs, hcZ, map_mul, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    · simp [scaleVars]
    · congr 1
      refine Multiset.map_congr rfl fun x _ ↦ ?_
      exact scaleVars_pointForm _ x
  have ha : specLeft a G ≠ 0 := by
    rw [h1]
    exact scaleVars_ne_zero remodelWeight_ne_zero fun h ↦
      hne (map_injective φ φ.injective (by rw [h, map_zero]))
  have key := gaussLogMahler_specLeft_le_of_isWeightedHomogeneous a h2 h3 ha
  rw [h1, gaussLogMahler_rename (sectionVar b d).injective] at key
  refine key.trans_eq ?_
  congr 4
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [a, remodelWeight, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem bombieriNorm_eq_sqrt_sum {δ : ι → ℕ} {P : MvPolynomial σ K}
    (hP : IsWeightedHomogeneous (multiWeight b) P δ) {φ : K →+* ℂ} {v : AbsoluteValue K ℝ}
    (hv : ∀ x, v x = ‖φ x‖) :
    bombieriNorm b v P = √(∑ u : GenericVar b (fun _ : Unit ↦ δ),
      ‖φ (P.coeff (u.2 : σ →₀ ℕ))‖ ^ 2 / blockMultinomial b (u.2 : σ →₀ ℕ)) := by
  rw [bombieriNorm, ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.univ_unique,
    Finset.sum_singleton, Finset.sum_coe_sort (blockMonomials b δ)
      (fun m ↦ ‖φ (P.coeff m)‖ ^ 2 / blockMultinomial b m)]
  congr 1
  refine Finset.sum_subset (fun m hm ↦ mem_blockMonomials.2 (hP (mem_support_iff.1 hm)))
    (fun m _ hm ↦ by rw [notMem_support_iff.1 hm]; simp) |>.trans ?_
  simp [hv]

end Arch

section Global

open Height Height.AdmissibleAbsValues

variable {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type} [Field K]
  [AdmissibleAbsValues K] {κ : Type} [Fintype κ] {d : Option κ → ι → ℕ}

/-- **The height of a hypersurface section** (Rémond, LNM 1752, Ch. 7, proof of Thm 3.4): if
`f = res_d(I)` has degree `D` in `u^{(0)}` and `P` is a form of multidegree `d₀`, then
`h(α ρ(f)) ≤ h(α f) + D h_m(P)`. -/
theorem gaussHeight_sectionMap_le (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {P : MvPolynomial σ K}
    (hP : IsWeightedHomogeneous (multiWeight b) P (d none)) (hP0 : P ≠ 0) {D : ℕ}
    (hD : IsWeightedHomogeneous (groupWeight b d none) (resForm b K d I) D)
    (hne : sectionMap b d P (resForm b K d I) ≠ 0) :
    gaussHeight remodelWeight (sectionMap b d P (resForm b K d I)) ≤
      gaussHeight remodelWeight (resForm b K d I) + D * bombieriLogHeight b P := by
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  set f := resForm b K d I
  have hf0 : f ≠ 0 := resForm_ne_zero hb hI hcard
  simp only [gaussHeight, hne, hf0, ↓reduceIte, bombieriLogHeight_of_ne_zero b hP0]
  have hpos : ∀ F : MvPolynomial (GenericVar b fun l : κ ↦ d (some l)) K, F ≠ 0 →
      0 < (archAbsVal.map fun v ↦ archMahler remodelWeight v F).prod := fun F _ ↦
    Multiset.prod_pos fun _ hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
      exact archMahler_pos _ _ _
  have hposf : 0 < (archAbsVal.map fun v ↦ archMahler remodelWeight v f).prod :=
    Multiset.prod_pos fun _ hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
      exact archMahler_pos _ _ _
  have hB : 0 < (archAbsVal.map fun v ↦ bombieriNorm b v P).prod :=
    Multiset.prod_pos fun _ hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
      exact bombieriNorm_pos b v hP0
  have hNP : 0 < ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val P := finprod_maxNorm_pos hP0
  -- the archimedean places
  have hA : (archAbsVal.map fun v ↦ archMahler remodelWeight v (sectionMap b d P f)).prod ≤
      (archAbsVal.map fun v ↦ archMahler remodelWeight v f).prod *
        (archAbsVal.map fun v ↦ bombieriNorm b v P).prod ^ D := by
    rw [← Multiset.prod_map_pow, ← Multiset.prod_map_mul]
    refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ (archMahler_pos _ _ _).le)
      fun v hv ↦ ?_
    have h := hK v hv
    rw [archMahler_of h, archMahler_of h, bombieriNorm_eq_sqrt_sum hP h.choose_spec]
    have key := gaussLogMahler_sectionMap_le hb hI hdim P h.choose hD hne
    have hs := bombieriNorm_eq_sqrt_sum hP h.choose_spec ▸ bombieriNorm_pos b v hP0
    calc exp (gaussLogMahler (scaleVars remodelWeight (map h.choose (sectionMap b d P f))))
        ≤ exp (gaussLogMahler (scaleVars remodelWeight (map h.choose f)) +
            D * log √(∑ u : GenericVar b (fun _ : Unit ↦ d none),
              ‖h.choose (P.coeff (u.2 : σ →₀ ℕ))‖ ^ 2 / blockMultinomial b (u.2 : σ →₀ ℕ))) :=
          exp_le_exp.2 key
      _ = _ := by rw [exp_add, exp_nat_mul, exp_log hs]
  -- the nonarchimedean places
  have hN : ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val (sectionMap b d P f) ≤
      (∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val f) *
        (∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val P) ^ D := by
    have h1 := hasFiniteMulSupport_maxNorm (K := K) hne
    have h2 := hasFiniteMulSupport_maxNorm (K := K) hf0
    have h3 := hasFiniteMulSupport_maxNorm (K := K) hP0
    set S := (h1.union (h2.union h3)).toFinset
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun x hx ↦ by simp [S, hx],
      finprod_eq_prod_of_mulSupport_subset _ (s := S) fun x hx ↦ by simp [S, hx],
      finprod_eq_prod_of_mulSupport_subset _ (s := S) fun x hx ↦ by simp [S, hx],
      ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ maxNorm_nonneg _) fun v _ ↦
      maxNorm_sectionMap_le (isNonarchimedean _ v.2) P hD
  have hNf : 0 < ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val f := finprod_maxNorm_pos hf0
  have hN' : 0 < ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val (sectionMap b d P f) :=
    finprod_maxNorm_pos hne
  change log (_ * _) ≤ log (_ * _) + D * log (_ * ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val P)
  rw [← log_pow, ← log_mul (mul_pos hposf hNf).ne' (pow_pos (mul_pos hB hNP) _).ne']
  refine log_le_log (mul_pos (hpos _ hne) hN') ?_
  calc _ ≤ ((archAbsVal.map fun v ↦ archMahler remodelWeight v f).prod *
        (archAbsVal.map fun v ↦ bombieriNorm b v P).prod ^ D) *
        ((∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val f) *
          (∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val P) ^ D) :=
        mul_le_mul hA hN hN'.le (mul_pos hposf (pow_pos hB _)).le
    _ = _ := by ring

/-- **The arithmetic intersection inequality for resultant forms** (Rémond, LNM 1752, Ch. 7,
Thm 3.4 with Cor. 3.6): let `P` be a form of multidegree `δ ≠ 0`, not a zero divisor modulo `I`,
and `D` the degree of `res_{(δ, d')}(I)` in its first form. Then
`h(α res_{d'}(I + (P))) ≤ ∑_i δ_i h(α res_{(ε_i, d')}(I)) + D h_m(P)`. -/
theorem gaussHeight_resForm_sup_le (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) [Nonempty κ]
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {δ : ι → ℕ} (hδ : δ ≠ 0)
    {d' : κ → ι → ℕ} {P : MvPolynomial σ K} (hP : IsWeightedHomogeneous (multiWeight b) P δ)
    (hP0 : P ≠ 0) (hcol : I.colon {P} = I) {D : ℕ}
    (hD : IsWeightedHomogeneous (groupWeight b (leftIndex δ d') none)
      (resForm b K (leftIndex δ d') I) D) :
    gaussHeight remodelWeight (resForm b K d' (I ⊔ Ideal.span {P})) ≤
      ∑ i, (δ i : ℝ) *
          gaussHeight remodelWeight (resForm b K (leftIndex (Pi.single i 1) d') I) +
        D * bombieriLogHeight b P := by
  have hJ : (I ⊔ Ideal.span {P}).IsWeightedHomogeneous (multiWeight b) :=
    hI.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨δ, (Set.mem_singleton_iff.mp hx) ▸ hP⟩)
  have hHJ : hilbertPoly b (I ⊔ Ideal.span {P}) =
      hilbertPoly b I - shiftPoly δ (hilbertPoly b I) :=
    hilbertPoly_sup_span_singleton_of_colon_eq hb hI hP hP0 hcol
  have hcardJ : (hilbertPoly b (I ⊔ Ideal.span {P})).totalDegree + 1 ≤ Nat.card κ := by
    rw [Nat.card_eq_fintype_card]
    by_cases h0 : (hilbertPoly b I).totalDegree = 0
    · rw [hHJ, totalDegree_eq_zero_iff_eq_C.mp h0, shiftPoly_C, sub_self, totalDegree_zero]
      exact Fintype.card_pos
    · have := totalDegree_sub_shiftPoly_le δ (hilbertPoly b I)
      rw [hHJ]
      omega
  have hres : resForm b K d' (I ⊔ Ideal.span {P}) ≠ 0 := resForm_ne_zero hb hJ hcardJ
  obtain ⟨u, hu₀⟩ := associated_sectionMap_resForm (d := leftIndex δ d') hb hI hP hP0 hcol hdim
  have hu : sectionMap b (leftIndex δ d') P (resForm b K (leftIndex δ d') I) * ↑u =
      resForm b K d' (I ⊔ Ideal.span {P}) := hu₀
  obtain ⟨c, hc, hcu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  have hne : sectionMap b (leftIndex δ d') P (resForm b K (leftIndex δ d') I) ≠ 0 := fun h0 ↦
    hres (by rw [← hu, h0, zero_mul]; rfl)
  have heq : resForm b K d' (I ⊔ Ideal.span {P}) =
      C c * sectionMap b (leftIndex δ d') P (resForm b K (leftIndex δ d') I) := by
    rw [← hu, hcu, mul_comm]
    rfl
  have hw : ∀ t : GenericVar b d', remodelWeight t ≠ 0 := remodelWeight_ne_zero
  calc gaussHeight remodelWeight (resForm b K d' (I ⊔ Ideal.span {P}))
      = gaussHeight remodelWeight
          (sectionMap b (leftIndex δ d') P (resForm b K (leftIndex δ d') I)) := by
        rw [heq]
        exact gaussHeight_C_mul hK hw hc.ne_zero _
    _ ≤ gaussHeight remodelWeight (resForm b K (leftIndex δ d') I) + D * bombieriLogHeight b P :=
        gaussHeight_sectionMap_le hK hb hI hdim hP hP0 hD hne
    _ = _ := by rw [gaussHeight_resForm_leftIndex hK hb hI hdim hδ]

end Global

end MvPolynomial
