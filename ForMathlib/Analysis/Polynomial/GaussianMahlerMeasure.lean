/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Probability.ComplexGaussian
public import Mathlib.Algebra.MvPolynomial.Rename

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The Gaussian Mahler measure of a polynomial in several variables

For `F ∈ ℂ[X_s : s ∈ σ]` we set `log M(F) = ∫ log |F(e^{-c} z)| dγ(z)`, with
`γ = complexGaussian σ` the product of standard complex Gaussians and `c = ∫ log |w| dγ₁(w)`.
The rescaling makes `∫ log |w| = 0`, so no degree term is needed. For multihomogeneous `F` this
is the sphere Mahler measure of G. Rémond (LNM 1752, Ch. 7, §2.1), by the polar decomposition
of `γ`; we never need this. The Gaussian is a product measure, which makes dummy variables and
Fubini easy, and it is unitarily invariant, which gives `M(∑ a_s X_s) = ‖a‖₂`.

## Main definitions

* `ProbabilityTheory.gaussLogMean`: `c = ∫ log |w| dγ₁(w)`.
* `MvPolynomial.gaussLogMahler F`: `log M(F)`.
* `MvPolynomial.specRight z`: the specialization `P ↦ P(·, z)` of `ℂ[τ ⊕ σ]` at `z ∈ ℂ^σ`.

## Main results

* `ProbabilityTheory.map_comp_complexGaussian`: forgetting coordinates maps `complexGaussian`
  to `complexGaussian`.
* `MvPolynomial.gaussLogMahler_mul`: `log M(F G) = log M(F) + log M(G)` for `F, G ≠ 0`.
* `MvPolynomial.gaussLogMahler_C`, `MvPolynomial.gaussLogMahler_rename` (dummy variables).
* `MvPolynomial.gaussLogMahler_linear`: `log M(∑ a_s X_s) = log ‖a‖₂`.
* `MvPolynomial.gaussLogMahler_eq_integral_specRight`: Rémond's Lemma 2.1 (1), `log M(P)` is
  the average of the `log M(P(·, z))`; hence `gaussLogMahler_eq_of_specRight`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace ProbabilityTheory

/-- The mean `∫ log |w| dγ₁(w)` of `log |w|` for the standard complex Gaussian. -/
noncomputable def gaussLogMean : ℝ := ∫ w, log ‖w‖ ∂stdGaussian ℂ

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- **Dummy variables**: forgetting the coordinates outside the image of an injection maps
`complexGaussian` to `complexGaussian`. -/
theorem map_comp_complexGaussian {f : σ → τ} (hf : Function.Injective f) :
    (complexGaussian τ).map (fun z ↦ z ∘ f) = complexGaussian σ := by
  classical
  have hm : Measurable fun z : τ → ℂ ↦ z ∘ f := measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have hpre : (fun z : τ → ℂ ↦ z ∘ f) ⁻¹' univ.pi s =
      univ.pi (Function.extend f s fun _ ↦ univ) := by
    ext z
    simp only [mem_preimage, mem_univ_pi, Function.comp_apply]
    refine ⟨fun h t ↦ ?_, fun h i ↦ by simpa [hf.extend_apply] using h (f i)⟩
    by_cases ht : ∃ i, f i = t
    · obtain ⟨i, rfl⟩ := ht
      simpa [hf.extend_apply] using h i
    · simp [Function.extend_apply' _ _ _ ht]
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, complexGaussian, Measure.pi_pi]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map ⟨f, hf⟩)) fun t _ ht ↦ by
    have ht' : ¬∃ i, f i = t := fun ⟨i, hi⟩ ↦ ht (by simp [← hi])
    simp [Function.extend_apply' _ _ _ ht']]
  simp [hf.extend_apply]

theorem integrable_log_norm_stdGaussian : Integrable (fun w : ℂ ↦ log ‖w‖) (stdGaussian ℂ) :=
  have h : ∫⁻ w, ‖log ‖w‖‖ₑ ∂stdGaussian ℂ ≤ ENNReal.ofReal (log⁺ ‖(0 : ℂ)‖) + gaussLogConst := by
    simpa using lintegral_enorm_log_norm_sub_le 0
  ⟨(measurable_norm.log).aestronglyMeasurable,
    h.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, gaussLogConst_lt_top⟩)⟩

end ProbabilityTheory

namespace MvPolynomial

open ProbabilityTheory

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- The scale `e^{-c}`, which makes `∫ log |e^{-c} w| dγ₁(w) = 0`. -/
noncomputable def gaussScale : ℂ := (rexp (-gaussLogMean) : ℝ)

theorem gaussScale_ne_zero : gaussScale ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

/-- Rescaling all variables by `gaussScale`. -/
noncomputable def gaussRescale : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun s ↦ C gaussScale * X s

omit [Fintype σ] in
theorem eval_gaussRescale (z : σ → ℂ) (F : MvPolynomial σ ℂ) :
    eval z (gaussRescale F) = eval (gaussScale • z) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [gaussRescale]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [gaussRescale, hp] at *

omit [Fintype σ] in
theorem gaussRescale_ne_zero {F : MvPolynomial σ ℂ} (hF : F ≠ 0) : gaussRescale F ≠ 0 := by
  refine fun h ↦ hF (MvPolynomial.funext fun w ↦ ?_)
  have := congrArg (eval (gaussScale⁻¹ • w)) h
  rw [eval_gaussRescale, smul_smul, mul_inv_cancel₀ gaussScale_ne_zero, one_smul] at this
  simpa using this

/-- The **Gaussian log-Mahler measure** `∫ log |F(e^{-c} z)| dγ(z)` of a complex polynomial. -/
noncomputable def gaussLogMahler (F : MvPolynomial σ ℂ) : ℝ :=
  ∫ z, log ‖eval (gaussScale • z) F‖ ∂complexGaussian σ

theorem gaussLogMahler_eq (F : MvPolynomial σ ℂ) :
    gaussLogMahler F = ∫ z, log ‖eval z (gaussRescale F)‖ ∂complexGaussian σ := by
  simp_rw [gaussLogMahler, eval_gaussRescale]

@[simp]
theorem gaussLogMahler_C (c : ℂ) : gaussLogMahler (C c : MvPolynomial σ ℂ) = log ‖c‖ := by
  simp [gaussLogMahler]

@[simp]
theorem gaussLogMahler_zero : gaussLogMahler (0 : MvPolynomial σ ℂ) = 0 := by
  simp [gaussLogMahler]

theorem gaussLogMahler_mul {F G : MvPolynomial σ ℂ} (hF : F ≠ 0) (hG : G ≠ 0) :
    gaussLogMahler (F * G) = gaussLogMahler F + gaussLogMahler G := by
  have h : (fun z ↦ log ‖eval z (gaussRescale (F * G))‖) =ᵐ[complexGaussian σ]
      fun z ↦ log ‖eval z (gaussRescale F)‖ + log ‖eval z (gaussRescale G)‖ := by
    filter_upwards [ae_eval_ne_zero (gaussRescale_ne_zero hF),
      ae_eval_ne_zero (gaussRescale_ne_zero hG)] with z hzF hzG
    rw [map_mul, eval_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 hzF) (norm_ne_zero_iff.2 hzG)]
  rw [gaussLogMahler_eq, integral_congr_ae h, integral_add (integrable_log_norm_eval _)
    (integrable_log_norm_eval _), gaussLogMahler_eq, gaussLogMahler_eq]

theorem gaussLogMahler_prod {α : Type*} (s : Finset α) {F : α → MvPolynomial σ ℂ}
    (hF : ∀ a ∈ s, F a ≠ 0) : gaussLogMahler (∏ a ∈ s, F a) = ∑ a ∈ s, gaussLogMahler (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ← C_1, gaussLogMahler_C, norm_one, log_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, gaussLogMahler_mul (hF a
      (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun b hb ↦ hF b
      (Finset.mem_insert_of_mem hb)), ih fun b hb ↦ hF b (Finset.mem_insert_of_mem hb)]

theorem gaussLogMahler_pow {F : MvPolynomial σ ℂ} (hF : F ≠ 0) (n : ℕ) :
    gaussLogMahler (F ^ n) = n * gaussLogMahler F := by
  simpa using gaussLogMahler_prod (Finset.range n) (F := fun _ ↦ F) fun _ _ ↦ hF

theorem gaussLogMahler_multiset_prod (s : Multiset (MvPolynomial σ ℂ)) (hs : ∀ F ∈ s, F ≠ 0) :
    gaussLogMahler s.prod = (s.map gaussLogMahler).sum := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, ← C_1, gaussLogMahler_C]; simp
  | cons F s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      gaussLogMahler_mul (hs F (Multiset.mem_cons_self F s)) (Multiset.prod_ne_zero fun h ↦
        hs 0 (Multiset.mem_cons_of_mem h) rfl), ih fun G hG ↦ hs G (Multiset.mem_cons_of_mem hG)]

theorem gaussLogMahler_C_mul {c : ℂ} (hc : c ≠ 0) {F : MvPolynomial σ ℂ} (hF : F ≠ 0) :
    gaussLogMahler (C c * F) = log ‖c‖ + gaussLogMahler F := by
  rw [gaussLogMahler_mul (C_ne_zero.2 hc) hF, gaussLogMahler_C]

omit [Fintype σ] in
theorem continuous_eval_gaussScale_smul (F : MvPolynomial σ ℂ) :
    Continuous fun z : σ → ℂ ↦ eval (gaussScale • z) F :=
  (MvPolynomial.continuous_eval F).comp (continuous_const_smul _)

theorem gaussLogMahler_rename {f : σ → τ} (hf : Function.Injective f) (F : MvPolynomial σ ℂ) :
    gaussLogMahler (rename f F) = gaussLogMahler F := by
  have hm : Measurable fun z : τ → ℂ ↦ z ∘ f := measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  have hc : ∀ z : τ → ℂ, (gaussScale • z) ∘ f = gaussScale • (z ∘ f) := fun z ↦ rfl
  rw [gaussLogMahler, gaussLogMahler]
  simp_rw [eval_rename, hc]
  rw [← integral_map (f := fun z ↦ log ‖eval (gaussScale • z) F‖) hm.aemeasurable
    (continuous_eval_gaussScale_smul F).measurable.norm.log.aestronglyMeasurable,
    map_comp_complexGaussian hf]

/-- The Gaussian Mahler measure of a **linear form** is the `ℓ²` norm of its coefficients. -/
theorem gaussLogMahler_linear {a : σ → ℂ} (ha : a ≠ 0) :
    gaussLogMahler (∑ s, C (a s) * X s : MvPolynomial σ ℂ) = log √(∑ s, ‖a s‖ ^ 2) := by
  set r := √(∑ s, ‖a s‖ ^ 2)
  have hr : 0 < r := by
    obtain ⟨s, hs⟩ := Function.ne_iff.1 ha
    refine Real.sqrt_pos.2 (lt_of_lt_of_le (by positivity : 0 < ‖a s‖ ^ 2)
      (Finset.single_le_sum (f := fun s ↦ ‖a s‖ ^ 2) (fun _ _ ↦ by positivity)
        (Finset.mem_univ s)))
  set a' : σ → ℂ := fun s ↦ gaussScale * a s
  have hr' : √(∑ s, ‖a' s‖ ^ 2) = rexp (-gaussLogMean) * r := by
    simp_rw [a', norm_mul, gaussScale, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
  have hm : Measurable fun z : σ → ℂ ↦ ∑ s, a' s * z s :=
    Finset.measurable_sum _ fun s _ ↦ (measurable_pi_apply s).const_mul _
  have heval : ∀ z : σ → ℂ, eval (gaussScale • z) (∑ s, C (a s) * X s) = ∑ s, a' s * z s :=
    fun z ↦ by simp [a', mul_left_comm, mul_assoc]
  set r' := rexp (-gaussLogMean) * r
  have hr'0 : 0 < r' := mul_pos (Real.exp_pos _) hr
  rw [gaussLogMahler]
  simp_rw [heval]
  rw [← integral_map (f := fun x : ℂ ↦ log ‖x‖) hm.aemeasurable
    measurable_norm.log.aestronglyMeasurable, map_sum_mul_complexGaussian, hr',
    integral_map (by fun_prop) measurable_norm.log.aestronglyMeasurable]
  have hae : (fun w : ℂ ↦ log ‖(r' : ℂ) * w‖) =ᵐ[stdGaussian ℂ] fun w ↦ log r' + log ‖w‖ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := stdGaussian ℂ) 0)]
      with w hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr'0.le,
      Real.log_mul hr'0.ne' (norm_ne_zero_iff.2 hw)]
  rw [integral_congr_ae hae, integral_add (integrable_const _) integrable_log_norm_stdGaussian,
    integral_const, ← gaussLogMean, Real.log_mul (Real.exp_pos _).ne' hr.ne', Real.log_exp]
  simp

theorem linear_ne_zero {a : σ → ℂ} (ha : a ≠ 0) : (∑ s, C (a s) * X s : MvPolynomial σ ℂ) ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.1 ha
  intro h
  have := congrArg (fun p : MvPolynomial σ ℂ ↦ p.coeff (Finsupp.single t 1)) h
  exact ht (by simpa [coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff] using this)

/-! ### Averaging over specializations (Rémond, Lemma 2.1 (1)) -/

section Fubini

omit [Fintype σ] [Fintype τ] in
/-- The specialization `P(·, z)` of `P ∈ ℂ[τ ⊕ σ]` at `z ∈ ℂ^σ`. -/
noncomputable def specRight (z : σ → ℂ) : MvPolynomial (τ ⊕ σ) ℂ →ₐ[ℂ] MvPolynomial τ ℂ :=
  aeval (Sum.elim X fun s ↦ C (z s))

omit [Fintype σ] [Fintype τ] in
theorem eval_specRight (z : σ → ℂ) (w : τ → ℂ) (P : MvPolynomial (τ ⊕ σ) ℂ) :
    eval w (specRight z P) = eval (Sum.elim w z) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [specRight]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [specRight, hp] at *

/-- `complexGaussian (τ ⊕ σ)` is the product of `complexGaussian τ` and `complexGaussian σ`. -/
theorem integral_complexGaussian_sum {f : (τ ⊕ σ → ℂ) → ℝ}
    (hf : Integrable f (complexGaussian (τ ⊕ σ))) :
    ∫ x, f x ∂complexGaussian (τ ⊕ σ) =
      ∫ z, ∫ w, f (Sum.elim w z) ∂complexGaussian τ ∂complexGaussian σ := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm (fun _ : τ ⊕ σ ↦ stdGaussian ℂ)
  have hf' : Integrable (f ∘ (MeasurableEquiv.sumPiEquivProdPi fun _ : τ ⊕ σ ↦ ℂ).symm)
      ((complexGaussian τ).prod (complexGaussian σ)) :=
    hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.2 hf
  rw [complexGaussian, ← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) f]
  exact integral_prod_symm _ hf'

/-- **Rémond's Lemma 2.1 (1)**, Gaussian form: `log M(P)` is the average of the
`log M(P(·, z))` over the rescaled Gaussian. -/
theorem gaussLogMahler_eq_integral_specRight (P : MvPolynomial (τ ⊕ σ) ℂ) :
    gaussLogMahler P =
      ∫ z, gaussLogMahler (specRight (gaussScale • z) P) ∂complexGaussian σ := by
  have hP : Integrable (fun x ↦ log ‖eval (gaussScale • x) P‖) (complexGaussian (τ ⊕ σ)) := by
    simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale P)
  rw [gaussLogMahler, integral_complexGaussian_sum hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  have hs : ∀ w : τ → ℂ, gaussScale • Sum.elim w z =
      Sum.elim (gaussScale • w) (gaussScale • z) := fun w ↦ by
    ext (s | s) <;> rfl
  simp_rw [gaussLogMahler, eval_specRight, hs]

/-- **Lemma 2.1 (1) along a splitting** `V ≃ τ ⊕ σ` of the variables. -/
theorem gaussLogMahler_eq_integral_split {V : Type*} [Fintype V] (eqv : V ≃ τ ⊕ σ)
    (P : MvPolynomial V ℂ) :
    gaussLogMahler P = ∫ y, ∫ u, log ‖eval (gaussScale • (Sum.elim u y ∘ eqv)) P‖
      ∂complexGaussian τ ∂complexGaussian σ := by
  have hP : Integrable (fun x ↦ log ‖eval (gaussScale • x) (rename eqv P)‖)
      (complexGaussian (τ ⊕ σ)) := by
    simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale (rename eqv P))
  rw [← gaussLogMahler_rename eqv.injective P, gaussLogMahler, integral_complexGaussian_sum hP]
  simp_rw [eval_rename]
  rfl

/-- **Comparison by specializations**: if `P(·, z)` and `Q(·, z)` have the same Mahler measure for
every `z`, so do `P` and `Q`. -/
theorem gaussLogMahler_eq_of_specRight {τ' : Type*} [Fintype τ'] {P : MvPolynomial (τ ⊕ σ) ℂ}
    {Q : MvPolynomial (τ' ⊕ σ) ℂ}
    (h : ∀ z, gaussLogMahler (specRight z P) = gaussLogMahler (specRight z Q)) :
    gaussLogMahler P = gaussLogMahler Q := by
  rw [gaussLogMahler_eq_integral_specRight, gaussLogMahler_eq_integral_specRight]
  simp_rw [h]

end Fubini

end MvPolynomial
