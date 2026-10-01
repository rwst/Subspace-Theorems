/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerMeasure
public import ForMathlib.RingTheory.MvPolynomial.BlockMultinomial
public import ForMathlib.RingTheory.MvPolynomial.ResultantPair
public import ForMathlib.RingTheory.MvPolynomial.ResultantSpecialization

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Mahler measures of resultant forms

Rémond's Theorem 2.2 (LNM 1752, Ch. 7) at an archimedean place, in two-factor form: after the
remodeling `α : u_m ↦ √C(δ, m) u_m` of the coefficients, the product specialization
`U₀ ↦ V W` of Prop. 3.5 does not change the Mahler measure of a resultant form.

The proof averages over the forms `U_l`, `l ∈ κ` (Lemma 2.1 (1)). After specializing them,
the resultant form is `c ∏_j U(x_j)` (Prop. 2.16), and `M(α U(x)) = ∏_i ‖x^{(i)}‖^{δ_i}` by the
block multinomial theorem, which is multiplicative in `δ`.

## Main definitions

* `MvPolynomial.scaleVars w`: `X_t ↦ w_t X_t`.
* `MvPolynomial.remodelWeight`: `√C(δ, m)` on the variable `u_m`.
-/

@[expose] public section

open MeasureTheory Real

namespace MvPolynomial

section Scale

variable {τ : Type*}

/-- Scaling the variables: `X_t ↦ w_t X_t`. -/
noncomputable def scaleVars (w : τ → ℂ) : MvPolynomial τ ℂ →ₐ[ℂ] MvPolynomial τ ℂ :=
  aeval fun t ↦ C (w t) * X t

theorem eval_scaleVars (w z : τ → ℂ) (P : MvPolynomial τ ℂ) :
    eval z (scaleVars w P) = eval (fun t ↦ w t * z t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [scaleVars]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [scaleVars, hp] at *

end Scale

theorem scaleVars_monomial {τ : Type*} (w : τ → ℂ) (m : τ →₀ ℕ) (c : ℂ) :
    scaleVars w (monomial m c) = monomial m ((m.prod fun t k ↦ w t ^ k) * c) := by
  refine MvPolynomial.funext fun z ↦ ?_
  rw [eval_scaleVars, eval_monomial, eval_monomial]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  ring

theorem coeff_scaleVars {τ : Type*} (w : τ → ℂ) (P : MvPolynomial τ ℂ) (m : τ →₀ ℕ) :
    (scaleVars w P).coeff m = (m.prod fun t k ↦ w t ^ k) * P.coeff m := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  simp_rw [scaleVars_monomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single m (fun n _ hn ↦ by simp [hn]) fun hm ↦ by
    simp [notMem_support_iff.1 hm]]
  simp

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- The remodeling weight `√C(d_l, m)` of the variable `u^{(l)}_m`. -/
noncomputable def remodelWeight {κ : Type*} {d : κ → ι → ℕ} (v : GenericVar b d) : ℂ :=
  (√(blockMultinomial b (v.2 : σ →₀ ℕ) : ℝ) : ℂ)

/-- `‖x^{(i)}‖²`, the squared norm of the block `i` of `x`. -/
noncomputable def blockNormSq (b : σ → ι) (x : σ → ℂ) (i : ι) : ℝ :=
  ∑ s ∈ ({s | b s = i} : Finset σ), ‖x s‖ ^ 2

omit [Fintype ι] in
theorem blockNormSq_pos {x : σ → ℂ} {i : ι} (h : ∃ s, b s = i ∧ x s ≠ 0) :
    0 < blockNormSq b x i := by
  obtain ⟨s, hs, hx⟩ := h
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun s ↦ ‖x s‖ ^ 2)
    (fun _ _ ↦ by positivity) (by simpa using hs))

theorem scaleVars_pointForm (e : ι → ℕ) (x : σ → ℂ) :
    scaleVars remodelWeight (pointForm b e x) =
      ∑ v : GenericVar b (fun _ : Unit ↦ e),
        C (remodelWeight v * ∏ s, x s ^ (v.2 : σ →₀ ℕ) s) * X v := by
  rw [pointForm_eq, map_sum, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp only [Finset.univ_unique, Finset.sum_singleton, scaleVars, map_mul, aeval_C, aeval_X,
    algebraMap_eq]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [PUnit.default_eq_unit]
  ring

theorem sum_norm_sq_remodelWeight (e : ι → ℕ) (x : σ → ℂ) :
    ∑ v : GenericVar b (fun _ : Unit ↦ e),
      ‖remodelWeight v * ∏ s, x s ^ (v.2 : σ →₀ ℕ) s‖ ^ 2 = ∏ i, blockNormSq b x i ^ e i := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp_rw [blockNormSq]
  rw [← sum_blockMultinomial_mul_prod_pow b e fun s ↦ ‖x s‖ ^ 2,
    ← Finset.sum_coe_sort (blockMonomials b e)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [norm_mul, mul_pow, remodelWeight, Complex.norm_real, Real.norm_of_nonneg (sqrt_nonneg _),
    sq_sqrt (Nat.cast_nonneg _), norm_prod, ← Finset.prod_pow]
  simp only [norm_pow, ← pow_mul, mul_comm (2 : ℕ)]

theorem remodelWeight_mul_ne_zero (e : ι → ℕ) {x : σ → ℂ} (hx : ∀ i, ∃ s, b s = i ∧ x s ≠ 0) :
    (fun v : GenericVar b (fun _ : Unit ↦ e) ↦ remodelWeight v * ∏ s, x s ^ (v.2 : σ →₀ ℕ) s)
      ≠ 0 := by
  intro h0
  have hpos : 0 < ∏ i, blockNormSq b x i ^ e i :=
    Finset.prod_pos fun i _ ↦ pow_pos (blockNormSq_pos (hx i)) _
  rw [← sum_norm_sq_remodelWeight] at hpos
  have h0' : ∀ v : GenericVar b (fun _ : Unit ↦ e),
      remodelWeight v * ∏ s, x s ^ (v.2 : σ →₀ ℕ) s = 0 := fun v ↦ congrFun h0 v
  simp only [h0', norm_zero] at hpos
  simp at hpos

/-- **The Mahler measure of a remodeled point form**:
`M(α U(x)) = ∏_i ‖x^{(i)}‖^{e_i}` (block multinomial theorem). -/
theorem gaussLogMahler_scaleVars_pointForm (e : ι → ℕ) {x : σ → ℂ}
    (hx : ∀ i, ∃ s, b s = i ∧ x s ≠ 0) :
    gaussLogMahler (scaleVars remodelWeight (pointForm b e x)) =
      log √(∏ i, blockNormSq b x i ^ e i) := by
  rw [scaleVars_pointForm, gaussLogMahler_linear (remodelWeight_mul_ne_zero e hx),
    sum_norm_sq_remodelWeight]

theorem remodelWeight_ne_zero {κ : Type*} {d : κ → ι → ℕ} (v : GenericVar b d) :
    remodelWeight v ≠ 0 := by
  rw [remodelWeight, Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  exact_mod_cast blockMultinomial_pos b _

theorem one_le_norm_remodelWeight {κ : Type*} {d : κ → ι → ℕ} (v : GenericVar b d) :
    1 ≤ ‖remodelWeight v‖ := by
  rw [remodelWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.one_le_sqrt]
  exact_mod_cast blockMultinomial_pos b _

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
theorem scaleVars_ne_zero {τ : Type*} {w : τ → ℂ} (hw : ∀ t, w t ≠ 0) {P : MvPolynomial τ ℂ}
    (hP : P ≠ 0) : scaleVars w P ≠ 0 := by
  refine fun h ↦ hP (MvPolynomial.funext fun z ↦ ?_)
  have := congrArg (eval fun t ↦ (w t)⁻¹ * z t) h
  rw [eval_scaleVars] at this
  simpa [mul_inv_cancel_left₀ (hw _)] using this

theorem scaleVars_pointForm_ne_zero (e : ι → ℕ) {x : σ → ℂ}
    (hx : ∀ i, ∃ s, b s = i ∧ x s ≠ 0) : scaleVars remodelWeight (pointForm b e x) ≠ 0 := by
  rw [scaleVars_pointForm]
  exact linear_ne_zero (remodelWeight_mul_ne_zero e hx)

section Product

variable {K : Type*} [Field K] (φ : K →+* ℂ) {κ : Type*} {e e' : ι → ℕ} {d' : κ → ι → ℕ}

theorem log_sqrt_prod_add {x : σ → ℂ} (hx : ∀ i, ∃ s, b s = i ∧ x s ≠ 0) :
    log √(∏ i, blockNormSq b x i ^ (e + e') i) =
      log √(∏ i, blockNormSq b x i ^ e i) + log √(∏ i, blockNormSq b x i ^ e' i) := by
  have h : ∀ f : ι → ℕ, 0 < ∏ i, blockNormSq b x i ^ f i := fun f ↦
    Finset.prod_pos fun i _ ↦ pow_pos (blockNormSq_pos (hx i)) _
  simp_rw [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [sqrt_mul (h e).le, Real.log_mul (sqrt_pos.2 (h e)).ne' (sqrt_pos.2 (h e')).ne']

/-- **Rémond's Theorem 2.2 at an archimedean place**, comparison step: if every specialization
of the forms `U_l` sends `F` to a product of point forms, the product specialization
`U₀ ↦ V W` does not change the remodeled Mahler measure. -/
theorem gaussLogMahler_scaleVars_map_productMap [Fintype κ]
    (F : MvPolynomial (GenericVar b (sumIndex e e' d')) K)
    (hF : ∀ y : GenericVar b d' → ℂ,
      specEval (d := sumIndex e e' d') b φ y F ∈ pointSubmonoid b ℂ (e + e')) :
    gaussLogMahler (scaleVars remodelWeight (map φ (productMap b K e e' d' F))) =
      gaussLogMahler (scaleVars remodelWeight (map φ F)) := by
  rw [gaussLogMahler_eq_integral_split (splitPair e e' d'),
    gaussLogMahler_eq_integral_split (splitSum e e' d')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  set y' : GenericVar b d' → ℂ := fun v ↦ remodelWeight v * (gaussScale * y v) with hy'
  obtain ⟨c, Z, hZ, hG⟩ := hF y'
  obtain ⟨G, hGdef⟩ : ∃ G : MvPolynomial (GenericVar b fun _ : Unit ↦ e + e') ℂ,
      G = specEval (d := sumIndex e e' d') b φ y' F := ⟨_, rfl⟩
  have hG' : G = C c * (Z.map (pointForm b (e + e'))).prod := hGdef.trans hG
  set H : MvPolynomial (GenericVar b (fun _ : Unit ↦ e) ⊕ GenericVar b (fun _ : Unit ↦ e')) ℂ :=
    C c * (Z.map fun x ↦ rename Sum.inl (scaleVars remodelWeight (pointForm b e x)) *
      rename Sum.inr (scaleVars remodelWeight (pointForm b e' x))).prod with hH
  have hA : ∀ u, eval (gaussScale • (Sum.elim u y ∘ splitSum e e' d'))
      (scaleVars remodelWeight (map φ F)) = eval (gaussScale • u) (scaleVars remodelWeight G) := by
    intro u
    rw [eval_scaleVars, eval_map, eval_scaleVars, hGdef]
    exact (eval_specEval_eq (d := sumIndex e e' d') φ y' _
      (g := fun v ↦ remodelWeight v * (gaussScale • (Sum.elim u y ∘ splitSum e e' d')) v)
      (fun m ↦ rfl) (fun l m ↦ rfl) F).symm
  have hB : ∀ vw, eval (gaussScale • (Sum.elim vw y ∘ splitPair e e' d'))
      (scaleVars remodelWeight (map φ (productMap b K e e' d' F))) =
        eval (gaussScale • vw) H := by
    intro vw
    set gB := fun v ↦ remodelWeight v * (gaussScale • (Sum.elim vw y ∘ splitPair e e' d')) v
    set ψ : GenericVar b (fun _ : Unit ↦ e + e') → ℂ := fun v ↦
      eval₂ φ gB ((genericForm K b (pairIndex e e' d') (some none) *
        genericForm K b (pairIndex e e' d') none).coeff (v.2 : σ →₀ ℕ))
    set g0 : GenericVar b (sumIndex e e' d') → ℂ := fun v ↦
      (splitSum e e' d' v).elim ψ y'
    have hψ : eval₂ φ g0 F = eval ψ G := by
      rw [hGdef]
      exact (eval_specEval_eq (d := sumIndex e e' d') φ y' ψ (g := g0) (fun m ↦ rfl)
        (fun l m ↦ rfl) F).symm
    rw [eval_scaleVars, eval_map, eval₂_productMap_eq φ gB (g' := g0) (fun m ↦ rfl)
      (fun l m ↦ rfl), hψ, hG', hH, map_mul, map_mul, eval_C, eval_C, map_multiset_prod,
      map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun x _ ↦ ?_
    simp only [Function.comp_apply, map_mul, eval_rename, eval_scaleVars, eval_pointForm_eq]
    have h := sum_eval₂_coeff_mul φ gB x
    rw [← Finset.sum_coe_sort (blockMonomials b (e + e'))] at h
    exact h
  simp_rw [hA, hB]
  change gaussLogMahler H = gaussLogMahler (scaleVars remodelWeight G)
  by_cases hc : c = 0
  · simp [hH, hG', hc]
  have hne : ∀ f : ι → ℕ, ∀ x ∈ Z, scaleVars remodelWeight (pointForm b f x) ≠ 0 :=
    fun f x hx ↦ scaleVars_pointForm_ne_zero f (hZ x hx)
  rw [hG', map_mul, show scaleVars remodelWeight (C c) = C c from aeval_C _ _, map_multiset_prod,
    Multiset.map_map, hH, gaussLogMahler_C_mul hc, gaussLogMahler_C_mul hc,
    gaussLogMahler_multiset_prod, gaussLogMahler_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  · congr 2
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    simp only [Function.comp_apply]
    have hx' := hZ x hx
    rw [gaussLogMahler_mul ((rename_injective _ Sum.inl_injective).ne_iff.2 (hne e x hx))
        ((rename_injective _ Sum.inr_injective).ne_iff.2 (hne e' x hx)),
      gaussLogMahler_rename Sum.inl_injective, gaussLogMahler_rename Sum.inr_injective,
      gaussLogMahler_scaleVars_pointForm _ hx', gaussLogMahler_scaleVars_pointForm _ hx',
      gaussLogMahler_scaleVars_pointForm _ hx', log_sqrt_prod_add hx']
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hP
    exact hne _ x hx
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hP
    exact mul_ne_zero ((rename_injective _ Sum.inl_injective).ne_iff.2 (hne e x hx))
      ((rename_injective _ Sum.inr_injective).ne_iff.2 (hne e' x hx))
  · exact Multiset.prod_ne_zero fun h ↦ by
      obtain ⟨x, hx, h0⟩ := Multiset.mem_map.1 h
      exact hne _ x hx h0
  · refine Multiset.prod_ne_zero fun h ↦ ?_
    obtain ⟨x, hx, h0⟩ := Multiset.mem_map.1 h
    exact mul_ne_zero ((rename_injective _ Sum.inl_injective).ne_iff.2 (hne e x hx))
      ((rename_injective _ Sum.inr_injective).ne_iff.2 (hne e' x hx)) h0

end Product

section Theorem22

theorem scaleVars_map_rename {K : Type*} [Field K] (φ : K →+* ℂ) {τ υ : Type*} {f : τ → υ}
    {w : τ → ℂ} {w' : υ → ℂ} (hw : ∀ t, w' (f t) = w t) (P : MvPolynomial τ K) :
    scaleVars w' (map φ (rename f P)) = rename f (scaleVars w (map φ P)) := by
  refine MvPolynomial.funext fun z ↦ ?_
  rw [eval_scaleVars, eval_map, eval₂_rename, eval_rename, eval_scaleVars, eval_map]
  congr 1
  funext t
  simp [hw]

variable {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {K : Type} [Field K]
  {κ : Type} [Fintype κ] {e e' : ι → ℕ} {d' : κ → ι → ℕ}

/-- **Rémond's Theorem 2.2 at an archimedean place, two factors**: if
`ω(res_{(e + e', d')}(I)) = c res_{(e, d')}(I) res_{(e', d')}(I)`, then at every embedding
`φ : K → ℂ`, `log M(α res_{(e + e', d')}(I)) = log |φ c| + log M(α res_{(e, d')}(I)) +
log M(α res_{(e', d')}(I))`. -/
theorem gaussLogMahler_resForm_sumIndex_of_eq (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) {c : K} (hc0 : c ≠ 0)
    (hc : productMap b K e e' d' (resForm b K (sumIndex e e' d') I) =
      C c * (rename (leftVar (b := b) e e' d') (resForm b K (leftIndex e d') I) *
        rename (rightVar (b := b) e e' d') (resForm b K (leftIndex e' d') I)))
    (φ : K →+* ℂ) :
    gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (sumIndex e e' d') I))) =
      log ‖φ c‖ +
        gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (leftIndex e d') I))) +
        gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (leftIndex e' d') I))) := by
  classical
  have hcard : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  have hne : ∀ f : Option κ → ι → ℕ, resForm b K f I ≠ 0 := fun f ↦
    resForm_ne_zero hb hI hcard
  have hX : ∀ {τ : Type} [Fintype τ] {w : τ → ℂ}, (∀ t, w t ≠ 0) → ∀ {P : MvPolynomial τ K},
      P ≠ 0 → scaleVars w (map φ P) ≠ 0 := fun hw P hP ↦
    scaleVars_ne_zero hw fun h ↦ hP (map_injective φ φ.injective (by rw [h, map_zero]))
  set F₁ := resForm b K (leftIndex e d') I
  set F₂ := resForm b K (leftIndex e' d') I
  have h₁ : scaleVars remodelWeight (map φ (rename (leftVar (b := b) e e' d') F₁)) =
      rename (leftVar (b := b) e e' d') (scaleVars remodelWeight (map φ F₁)) :=
    scaleVars_map_rename φ (fun _ ↦ rfl) F₁
  have h₂ : scaleVars remodelWeight (map φ (rename (rightVar (b := b) e e' d') F₂)) =
      rename (rightVar (b := b) e e' d') (scaleVars remodelWeight (map φ F₂)) :=
    scaleVars_map_rename φ (fun v ↦ by rcases v with ⟨_ | l, m⟩ <;> rfl) F₂
  have hA₁ := hX remodelWeight_ne_zero (hne (leftIndex e d'))
  have hA₂ := hX remodelWeight_ne_zero (hne (leftIndex e' d'))
  have hR₁ := (rename_injective _ (leftVar_injective (b := b) e e' d')).ne_iff.2 hA₁
  have hR₂ := (rename_injective _ (rightVar_injective (b := b) e e' d')).ne_iff.2 hA₂
  rw [map_zero] at hR₁ hR₂
  refine (gaussLogMahler_scaleVars_map_productMap (e := e) (e' := e') (d' := d') φ _ fun y ↦
      exists_specEval_resForm_eq (d := sumIndex e e' d') hb hI hcard φ y).symm.trans ?_
  rw [hc, map_mul, map_mul, map_mul, map_mul, map_C, show scaleVars remodelWeight (C (φ c)) =
      C (φ c) from aeval_C _ _, h₁, h₂,
    gaussLogMahler_C_mul ((map_ne_zero φ).2 hc0) (mul_ne_zero hR₁ hR₂),
    gaussLogMahler_mul hR₁ hR₂, gaussLogMahler_rename (leftVar_injective e e' d'),
    gaussLogMahler_rename (rightVar_injective e e' d'), add_assoc]

/-- **Rémond's Theorem 2.2 at the archimedean places, two factors**: for `deg H_I ≤ r - 1`
there is `λ ∈ Kˣ` such that at every embedding `φ : K → ℂ`,
`log M(α res_{(e + e', d')}(I)) = log |φ λ| + log M(α res_{(e, d')}(I)) +
log M(α res_{(e', d')}(I))`. -/
theorem exists_gaussLogMahler_resForm_sumIndex (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) :
    ∃ c : K, c ≠ 0 ∧ ∀ φ : K →+* ℂ,
      gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (sumIndex e e' d') I))) =
        log ‖φ c‖ +
          gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (leftIndex e d') I))) +
          gaussLogMahler (scaleVars remodelWeight (map φ (resForm b K (leftIndex e' d') I))) := by
  obtain ⟨c, hc0, hc⟩ := exists_productMap_resForm_eq (e := e) (e' := e') (d' := d') hb hI hdim
  exact ⟨c, hc0, gaussLogMahler_resForm_sumIndex_of_eq hb hI hdim hc0 hc⟩

end Theorem22

end MvPolynomial
