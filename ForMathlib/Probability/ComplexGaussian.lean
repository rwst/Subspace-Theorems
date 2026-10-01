/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Products of complex Gaussians

`complexGaussian σ` is the product over a finite type `σ` of copies of the standard Gaussian
`stdGaussian ℂ` on `ℂ = ℝ²`. It is the measure behind the Gaussian Mahler measure of a
polynomial.

## Main results

* `ProbabilityTheory.map_sum_mul_complexGaussian`: the law of `∑ s, a s * z s` is that of
  `‖a‖₂ * w`, `w` standard Gaussian. This is the unitary invariance that the sphere measure of
  Rémond provides.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped RealInnerProductSpace ComplexConjugate ENNReal

namespace ProbabilityTheory

variable (σ : Type*) [Fintype σ]

/-- The product of standard Gaussians on `σ → ℂ`. -/
noncomputable def complexGaussian : Measure (σ → ℂ) :=
  Measure.pi fun _ : σ ↦ stdGaussian ℂ

instance : IsProbabilityMeasure (complexGaussian σ) := by
  rw [complexGaussian]
  infer_instance

variable {σ}

open Complex in
theorem inner_mul_left_complex (a z w : ℂ) : ⟪a * z, w⟫ = ⟪z, conj a * w⟫ := by
  simp [Complex.inner]
  ring

open Complex in
/-- The **law of a linear form** under `complexGaussian`: `∑ s, a s * z s` has the law of
`‖a‖₂ * w` with `w` standard Gaussian. -/
theorem map_sum_mul_complexGaussian (a : σ → ℂ) :
    (complexGaussian σ).map (fun z ↦ ∑ s, a s * z s) =
      (stdGaussian ℂ).map (fun w ↦ (√(∑ s, ‖a s‖ ^ 2) : ℂ) * w) := by
  apply Measure.ext_of_charFun
  ext t
  have hm : Measurable fun z : σ → ℂ ↦ ∑ s, a s * z s :=
    Finset.measurable_sum _ fun s _ ↦ (measurable_pi_apply s).const_mul _
  rw [charFun_apply, charFun_apply, integral_map hm.aemeasurable (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_mul_left_complex, sum_inner, inner_mul_left_complex, ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  rw [complexGaussian, integral_fintype_prod_eq_prod
    (f := fun s x ↦ cexp (⟪x, conj (a s) * t⟫ * I))]
  simp_rw [← charFun_apply, charFun_stdGaussian, ← Complex.exp_sum]
  congr 1
  simp only [conj_ofReal, norm_mul, ofReal_mul, mul_pow, RCLike.norm_conj, ← Finset.sum_div]
  have h : ((√(∑ s, ‖a s‖ ^ 2) : ℝ) : ℂ) ^ 2 = ∑ s, (‖a s‖ : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ by positivity)]
    push_cast
    rfl
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), h, Finset.sum_mul,
    Finset.sum_neg_distrib]

/-! ### The real part, and a uniform bound for `log ‖w - a‖` -/

/-- The real part of a standard complex Gaussian is a standard real Gaussian. -/
theorem map_re_stdGaussian : (stdGaussian ℂ).map Complex.re = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_gaussianReal]
  have h : ∀ w : ℂ, ⟪w.re, t⟫ = ⟪w, (t : ℂ)⟫ := fun w ↦ by simp [Complex.inner, mul_comm]
  simp_rw [h, ← charFun_apply, charFun_stdGaussian]
  rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  simp [neg_div]

/-- Lines `re w = b` are null for the standard complex Gaussian. -/
theorem stdGaussian_re_eq (b : ℝ) : stdGaussian ℂ {w | w.re = b} = 0 := by
  have : {w : ℂ | w.re = b} = Complex.re ⁻¹' {b} := rfl
  rw [this, ← Measure.map_apply (by fun_prop) (measurableSet_singleton b), map_re_stdGaussian,
    gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

theorem gaussianPDF_zero_one_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  rw [gaussianPDF, ENNReal.ofReal_le_one, gaussianPDFReal]
  have h1 : 1 ≤ √(2 * π * (1 : NNReal)) := by
    rw [Real.one_le_sqrt]
    push_cast
    nlinarith [Real.two_le_pi]
  have h2 : rexp (-(x - 0) ^ 2 / (2 * (1 : NNReal))) ≤ 1 := by
    rw [exp_le_one_iff]
    push_cast
    nlinarith [sq_nonneg x]
  calc _ ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ h1) h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem lintegral_gaussianReal_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂gaussianReal 0 1 ≤ ∫⁻ x, f x := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hf]
  exact lintegral_mono fun x ↦ mul_le_of_le_one_left (by simp) (gaussianPDF_zero_one_le_one x)

/-- The constant in `lintegral_enorm_log_norm_sub_le`. -/
noncomputable def gaussLogConst : ℝ≥0∞ :=
  ENNReal.ofReal (log 2) + ∫⁻ w, ‖w‖ₑ ∂stdGaussian ℂ + ∫⁻ x in Icc (-1) 1, ‖log x‖ₑ

theorem gaussLogConst_lt_top : gaussLogConst < ∞ := by
  have h1 : ∫⁻ w, ‖w‖ₑ ∂stdGaussian ℂ < ∞ :=
    (IsGaussian.integrable_id (μ := stdGaussian ℂ)).hasFiniteIntegral
  have h2 : ∫⁻ x in Icc (-1 : ℝ) 1, ‖log x‖ₑ < ∞ :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1))).hasFiniteIntegral
  simp [gaussLogConst, h1, h2]

theorem ofReal_posLog_inv_abs_le (x : ℝ) :
    ENNReal.ofReal (log⁺ |x|⁻¹) ≤ (Icc (-1) 1).indicator (fun x ↦ ‖log x‖ₑ) x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs, abs_log_eq_posLog_add_posLog_inv, ← posLog_abs x⁻¹, abs_inv]
    linarith [posLog_nonneg (x := x)]
  · rw [indicator_of_notMem hx, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
    refine (posLog_eq_zero_iff _).2 ?_ |>.le
    rw [abs_inv, abs_abs]
    refine inv_le_one_of_one_le₀ ?_
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx <;> [rw [abs_of_neg (by linarith)]; rw [abs_of_pos (by linarith)]] <;>
      linarith

theorem lintegral_posLog_inv_le (b : ℝ) :
    ∫⁻ x, ENNReal.ofReal (log⁺ |x - b|⁻¹) ∂gaussianReal 0 1 ≤
      ∫⁻ x in Icc (-1) 1, ‖log x‖ₑ := by
  have hm : Measurable fun x : ℝ ↦ ENNReal.ofReal (log⁺ |x|⁻¹) :=
    ENNReal.measurable_ofReal.comp (continuous_posLog.measurable.comp
      (measurable_inv.comp continuous_abs.measurable))
  refine (lintegral_gaussianReal_le (f := fun x ↦ ENNReal.ofReal (log⁺ |x - b|⁻¹))
    (hm.comp (measurable_sub_const b))).trans ?_
  rw [lintegral_sub_right_eq_self (fun x ↦ ENNReal.ofReal (log⁺ |x|⁻¹)) b,
    ← lintegral_indicator measurableSet_Icc]
  exact lintegral_mono ofReal_posLog_inv_abs_le

theorem enorm_log_norm_sub_le {w a : ℂ} (hw : w.re ≠ a.re) :
    ‖log ‖w - a‖‖ₑ ≤ ENNReal.ofReal (log⁺ ‖a‖) + (ENNReal.ofReal (log 2) + ‖w‖ₑ) +
      ENNReal.ofReal (log⁺ |w.re - a.re|⁻¹) := by
  have hre : 0 < |w.re - a.re| := abs_pos.2 (sub_ne_zero.2 hw)
  have hle : |w.re - a.re| ≤ ‖w - a‖ := by
    simpa using Complex.abs_re_le_norm (w - a)
  have h1 : log⁺ ‖w - a‖ ≤ log⁺ ‖a‖ + (log 2 + ‖w‖) := by
    rw [sub_eq_add_neg]
    have := posLog_norm_add_le w (-a)
    rw [norm_neg] at this
    linarith [posLog_le_abs ‖w‖, abs_norm w]
  have h2 : log⁺ ‖w - a‖⁻¹ ≤ log⁺ |w.re - a.re|⁻¹ :=
    Real.posLog_le_posLog (by linarith [inv_nonneg.2 (norm_nonneg (w - a))])
      (inv_anti₀ hre hle)
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs,
    abs_log_eq_posLog_add_posLog_inv, ← ENNReal.ofReal_add (log_nonneg one_le_two) (norm_nonneg _),
    ← ENNReal.ofReal_add (posLog_nonneg) (add_nonneg (log_nonneg one_le_two) (norm_nonneg _)),
    ← ENNReal.ofReal_add (add_nonneg posLog_nonneg
      (add_nonneg (log_nonneg one_le_two) (norm_nonneg _))) posLog_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A bound for `∫ |log ‖w - a‖|` uniform in `a` up to `log⁺ ‖a‖`. -/
theorem lintegral_enorm_log_norm_sub_le (a : ℂ) :
    ∫⁻ w, ‖log ‖w - a‖‖ₑ ∂stdGaussian ℂ ≤ ENNReal.ofReal (log⁺ ‖a‖) + gaussLogConst := by
  have hae : ∀ᵐ w ∂stdGaussian ℂ, w.re ≠ a.re := by
    rw [ae_iff]
    simpa using stdGaussian_re_eq a.re
  refine (lintegral_mono_ae (hae.mono fun w hw ↦ enorm_log_norm_sub_le hw)).trans ?_
  rw [lintegral_add_right _ (by fun_prop), lintegral_add_left (by fun_prop),
    lintegral_add_left (by fun_prop), lintegral_const, lintegral_const, measure_univ, mul_one,
    mul_one]
  have h3 : ∫⁻ w, ENNReal.ofReal (log⁺ |w.re - a.re|⁻¹) ∂stdGaussian ℂ ≤
      ∫⁻ x in Icc (-1) 1, ‖log x‖ₑ := by
    have hm : Measurable fun x : ℝ ↦ ENNReal.ofReal (log⁺ |x - a.re|⁻¹) :=
      ENNReal.measurable_ofReal.comp (continuous_posLog.measurable.comp
        (measurable_inv.comp (continuous_abs.measurable.comp (measurable_sub_const _))))
    rw [← lintegral_map hm (by fun_prop), map_re_stdGaussian]
    exact lintegral_posLog_inv_le a.re
  rw [gaussLogConst, add_assoc]
  gcongr

/-! ### Polynomials in one variable -/

section OneVariable

open Polynomial

theorem enorm_log_norm_mul_prod_le (c w : ℂ) (s : Multiset ℂ) :
    ‖log ‖c * (s.map fun r ↦ w - r).prod‖‖ₑ ≤
      ‖log ‖c‖‖ₑ + (s.map fun r ↦ ‖log ‖w - r‖‖ₑ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      mul_left_comm]
    by_cases h₁ : w - r = 0
    · simp [h₁]
    by_cases h₂ : c * (s.map fun r ↦ w - r).prod = 0
    · simp [h₂]
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 h₁) (norm_ne_zero_iff.2 h₂)]
    calc _ ≤ ‖log ‖w - r‖‖ₑ + ‖log ‖c * (s.map fun r ↦ w - r).prod‖‖ₑ := enorm_add_le _ _
      _ ≤ _ := by
        rw [add_left_comm]
        gcongr

theorem enorm_log_norm_eval_le (p : ℂ[X]) (w : ℂ) :
    ‖log ‖p.eval w‖‖ₑ ≤ ‖log ‖p.leadingCoeff‖‖ₑ + (p.roots.map fun r ↦ ‖log ‖w - r‖‖ₑ).sum := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p)
    IsAlgClosed.card_roots_eq_natDegree]
  rw [eval_mul, eval_C, eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
  exact enorm_log_norm_mul_prod_le _ _ _

theorem lintegral_sum_enorm_log_norm_sub_le (s : Multiset ℂ) :
    ∫⁻ w, (s.map fun r ↦ ‖log ‖w - r‖‖ₑ).sum ∂stdGaussian ℂ ≤
      (s.map fun r ↦ ENNReal.ofReal (log⁺ ‖r‖)).sum + s.card * gaussLogConst := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [lintegral_add_left (by fun_prop)]
    calc _ ≤ (ENNReal.ofReal (log⁺ ‖r‖) + gaussLogConst) +
          ((s.map fun r ↦ ENNReal.ofReal (log⁺ ‖r‖)).sum + s.card * gaussLogConst) :=
          add_le_add (lintegral_enorm_log_norm_sub_le r) ih
      _ = _ := by push_cast; ring

/-- Landau's inequality, logarithmic form: `∑ log⁺ |r| ≤ log ‖p‖₁ - log |lead p|`. -/
theorem sum_posLog_roots_le {p : ℂ[X]} (hp : p ≠ 0) :
    (p.roots.map fun r ↦ log⁺ ‖r‖).sum ≤
      log (p.sum fun _ a ↦ ‖a‖) - log ‖p.leadingCoeff‖ := by
  have hl : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.2 (leadingCoeff_ne_zero.2 hp)
  have hprod : 0 < (p.roots.map fun r ↦ max 1 ‖r‖).prod :=
    Multiset.prod_pos fun x hx ↦ by
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hx
      exact lt_max_of_lt_left one_pos
  have h := (mahlerMeasure_eq_leadingCoeff_mul_prod_roots p).symm.trans_le
    (mahlerMeasure_le_sum_norm_coeff p)
  have hlog : (p.roots.map fun r ↦ log⁺ ‖r‖).sum =
      log (p.roots.map fun r ↦ max 1 ‖r‖).prod := by
    rw [Real.log_multiset_prod, Multiset.map_map]
    · exact congrArg Multiset.sum (Multiset.map_congr rfl fun r _ ↦
        posLog_eq_log_max_one (norm_nonneg r))
    · intro x hx
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hx
      exact (lt_max_of_lt_left one_pos).ne'
  rw [hlog, le_sub_iff_add_le, ← Real.log_mul hprod.ne' hl.ne', mul_comm]
  exact Real.log_le_log (mul_pos hl hprod) h

/-- The **one-variable bound**: `∫ |log |p(w)|| ≤ 2 |log |lead p|| + log⁺ ‖p‖₁ + deg p · C`. -/
theorem lintegral_enorm_log_norm_eval_le {p : ℂ[X]} (hp : p ≠ 0) :
    ∫⁻ w, ‖log ‖p.eval w‖‖ₑ ∂stdGaussian ℂ ≤
      2 * ‖log ‖p.leadingCoeff‖‖ₑ + ENNReal.ofReal (log⁺ (p.sum fun _ a ↦ ‖a‖)) +
        p.natDegree * gaussLogConst := by
  refine (lintegral_mono fun w ↦ enorm_log_norm_eval_le p w).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  refine (add_le_add_right (lintegral_sum_enorm_log_norm_sub_le p.roots) _).trans ?_
  rw [IsAlgClosed.card_roots_eq_natDegree, ← add_assoc]
  gcongr ?_ + _
  have hsum : (p.roots.map fun r ↦ ENNReal.ofReal (log⁺ ‖r‖)).sum =
      ENNReal.ofReal (p.roots.map fun r ↦ log⁺ ‖r‖).sum := by
    induction p.roots using Multiset.induction_on with
    | empty => simp
    | cons r s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.sum_cons,
        ENNReal.ofReal_add posLog_nonneg (Multiset.sum_nonneg fun x hx ↦ by
          obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hx
          exact posLog_nonneg)]
  rw [hsum, two_mul, add_assoc]
  gcongr _ + ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) posLog_nonneg]
  refine ENNReal.ofReal_le_ofReal ((sum_posLog_roots_le hp).trans ?_)
  have h : log (p.sum fun _ a ↦ ‖a‖) ≤ log⁺ (p.sum fun _ a ↦ ‖a‖) := le_max_right _ _
  rw [Real.norm_eq_abs]
  linarith [neg_abs_le (log ‖p.leadingCoeff‖)]

end OneVariable

/-! ### Polynomials in several variables -/

section Several

instance : NullSingletonClass (stdGaussian ℂ) where
  measure_singleton w := measure_mono_null (fun z hz ↦ by simp [Set.mem_singleton_iff.1 hz])
    (stdGaussian_re_eq w.re)

/-- Integration over `Fin (n + 1) → ℂ` splits off the first coordinate. -/
theorem lintegral_complexGaussian_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂complexGaussian (Fin (n + 1)) =
      ∫⁻ z, ∫⁻ w, f (Fin.cons w z) ∂stdGaussian ℂ ∂complexGaussian (Fin n) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ stdGaussian ℂ) 0).symm
  rw [complexGaussian, ← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm (f := fun a ↦ f ((MeasurableEquiv.piFinSuccAbove _ 0).symm a))
      (hf.comp (MeasurableEquiv.measurable _)).aemeasurable]
  refine lintegral_congr fun z ↦ lintegral_congr fun w ↦ ?_
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem complexGaussian_succ_apply {n : ℕ} {S : Set (Fin (n + 1) → ℂ)} (hS : MeasurableSet S) :
    complexGaussian (Fin (n + 1)) S =
      ∫⁻ z, stdGaussian ℂ {w | Fin.cons w z ∈ S} ∂complexGaussian (Fin n) := by
  rw [← lintegral_indicator_one hS, lintegral_complexGaussian_succ (measurable_one.indicator hS)]
  refine lintegral_congr fun z ↦ ?_
  have h : MeasurableSet {w : ℂ | Fin.cons w z ∈ S} :=
    have hc : Measurable fun w : ℂ ↦ (Fin.cons w z : Fin (n + 1) → ℂ) :=
      Measurable.of_eval fun i ↦ by
        induction i using Fin.cases <;> simp [measurable_id', measurable_const]
    hS.preimage hc
  rw [← lintegral_indicator_one h]
  rfl

open MvPolynomial in
theorem eval_cons_eq (n : ℕ) (F : MvPolynomial (Fin (n + 1)) ℂ) (w : ℂ) (z : Fin n → ℂ) :
    eval (Fin.cons w z) F = ((finSuccEquiv ℂ n F).map (eval z)).eval w :=
  eval_eq_eval_mv_eval' z w F

open MvPolynomial in
/-- The zero set of a nonzero polynomial is null for `complexGaussian`. -/
theorem complexGaussian_eval_eq_zero_fin (n : ℕ) :
    ∀ F : MvPolynomial (Fin n) ℂ, F ≠ 0 → complexGaussian (Fin n) {z | eval z F = 0} = 0 := by
  induction n with
  | zero =>
    intro F hF
    convert measure_empty (μ := complexGaussian (Fin 0))
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    rw [Set.mem_ofPred_eq, eq_C_of_isEmpty F, eval_C] at hz
    exact hF (by rw [eq_C_of_isEmpty F, hz, C_0])
  | succ n ih =>
    intro F hF
    set G := finSuccEquiv ℂ n F
    have hG : G ≠ 0 := (finSuccEquiv ℂ n).injective.ne (by simpa using hF)
    have hL := ih _ (Polynomial.leadingCoeff_ne_zero.2 hG)
    rw [complexGaussian_succ_apply (measurableSet_eq_fun (MvPolynomial.continuous_eval F).measurable
      measurable_const)]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hL] with z hz
    have hz : eval z G.leadingCoeff ≠ 0 := hz
    have hq : G.map (eval z) ≠ 0 := fun h ↦ hz (by
      rw [← Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz, h,
        Polynomial.leadingCoeff_zero])
    refine measure_mono_null (fun w hw ↦ ?_) ((G.map (eval z)).roots.toFinset.finite_toSet
      |>.measure_zero _)
    rw [Set.mem_ofPred_eq, eval_cons_eq] at hw
    simpa [Polynomial.mem_roots hq] using hw

theorem measurable_enorm_log_norm_eval {τ : Type*} [Countable τ] (F : MvPolynomial τ ℂ) :
    Measurable fun z : τ → ℂ ↦ ‖log ‖MvPolynomial.eval z F‖‖ₑ :=
  (MvPolynomial.continuous_eval F).measurable.norm.log.enorm

theorem posLog_le_abs_log (x : ℝ) : log⁺ x ≤ |log x| := by
  rw [abs_log_eq_posLog_add_posLog_inv]
  linarith [posLog_nonneg (x := x⁻¹)]

open MvPolynomial in
/-- The pointwise bound behind `lintegral_enorm_log_norm_eval_lt_top_fin`. -/
theorem lintegral_enorm_log_norm_eval_cons_le {n : ℕ} (F : MvPolynomial (Fin (n + 1)) ℂ)
    {z : Fin n → ℂ} (hz : eval z (finSuccEquiv ℂ n F).leadingCoeff ≠ 0) :
    ∫⁻ w, ‖log ‖eval (Fin.cons w z) F‖‖ₑ ∂stdGaussian ℂ ≤
      2 * ‖log ‖eval z (finSuccEquiv ℂ n F).leadingCoeff‖‖ₑ +
        (ENNReal.ofReal (log ((finSuccEquiv ℂ n F).natDegree + 1)) +
          ∑ i ∈ Finset.range ((finSuccEquiv ℂ n F).natDegree + 1),
            ‖log ‖eval z ((finSuccEquiv ℂ n F).coeff i)‖‖ₑ) +
        (finSuccEquiv ℂ n F).natDegree * gaussLogConst := by
  set G := finSuccEquiv ℂ n F
  have hq : G.map (eval z) ≠ 0 := fun h ↦ hz (by
    rw [← Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz, h,
      Polynomial.leadingCoeff_zero])
  simp_rw [eval_cons_eq]
  refine (lintegral_enorm_log_norm_eval_le hq).trans ?_
  rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz,
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz]
  gcongr
  rw [Polynomial.sum_over_range' _ (fun _ ↦ norm_zero) (G.natDegree + 1)
    (by rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz]; omega)]
  simp_rw [Polynomial.coeff_map]
  have h1 : log⁺ (∑ i ∈ Finset.range (G.natDegree + 1), ‖eval z (G.coeff i)‖) ≤
      log (G.natDegree + 1) + ∑ i ∈ Finset.range (G.natDegree + 1),
        |log ‖eval z (G.coeff i)‖| := by
    refine (posLog_sum _ _).trans ?_
    rw [Finset.card_range]
    push_cast
    gcongr with i
    exact posLog_le_abs_log _
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (log_nonneg (by simp)) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _]
  simp_rw [← Real.norm_eq_abs, ofReal_norm]

open MvPolynomial in
/-- `log |F|` has finite `L¹` norm for `complexGaussian` (for `F = 0` it vanishes). -/
theorem lintegral_enorm_log_norm_eval_lt_top_fin (n : ℕ) :
    ∀ F : MvPolynomial (Fin n) ℂ,
      ∫⁻ z, ‖log ‖eval z F‖‖ₑ ∂complexGaussian (Fin n) < ∞ := by
  induction n with
  | zero =>
    intro F
    rw [eq_C_of_isEmpty F]
    simp
  | succ n ih =>
    intro F
    by_cases hF : F = 0
    · simp [hF]
    set G := finSuccEquiv ℂ n F
    have hG : G ≠ 0 := (finSuccEquiv ℂ n).injective.ne (by simpa using hF)
    have hL := complexGaussian_eval_eq_zero_fin n _ (Polynomial.leadingCoeff_ne_zero.2 hG)
    rw [lintegral_complexGaussian_succ (measurable_enorm_log_norm_eval F)]
    refine (lintegral_mono_ae ?_).trans_lt (b := ∫⁻ z, 2 * ‖log ‖eval z G.leadingCoeff‖‖ₑ +
        (ENNReal.ofReal (log (G.natDegree + 1)) +
          ∑ i ∈ Finset.range (G.natDegree + 1), ‖log ‖eval z (G.coeff i)‖‖ₑ) +
        G.natDegree * gaussLogConst ∂complexGaussian (Fin n)) ?_
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hL] with z hz
      exact lintegral_enorm_log_norm_eval_cons_le F hz
    rw [lintegral_add_right _ measurable_const, lintegral_add_left
      ((measurable_enorm_log_norm_eval _).const_mul _), lintegral_const_mul _
      (measurable_enorm_log_norm_eval _), lintegral_add_left measurable_const, lintegral_finsetSum _
      fun i _ ↦ measurable_enorm_log_norm_eval _]
    simp only [lintegral_const, measure_univ, mul_one]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) (ih _),
      ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.sum_lt_top.2 fun i _ ↦ ih _⟩⟩,
      ENNReal.mul_lt_top (by simp) gaussLogConst_lt_top⟩

open MvPolynomial in
theorem eval_piCongrLeft_rename {τ : Type*} {n : ℕ} (e : τ ≃ Fin n) (F : MvPolynomial τ ℂ)
    (z : τ → ℂ) :
    eval (MeasurableEquiv.piCongrLeft (fun _ ↦ ℂ) e z) (rename e F) = eval z F := by
  have : (MeasurableEquiv.piCongrLeft (fun _ ↦ ℂ) e z) ∘ e = z :=
    _root_.funext fun s ↦ MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℂ) e z s
  rw [eval_rename, this]

theorem measurePreserving_piCongrLeft_complexGaussian {n : ℕ} (e : σ ≃ Fin n) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ ↦ ℂ) e) (complexGaussian σ)
      (complexGaussian (Fin n)) :=
  measurePreserving_piCongrLeft (fun _ : Fin n ↦ stdGaussian ℂ) e

open MvPolynomial in
/-- The zero set of a nonzero polynomial is null for `complexGaussian`. -/
theorem complexGaussian_eval_eq_zero {F : MvPolynomial σ ℂ} (hF : F ≠ 0) :
    complexGaussian σ {z | eval z F = 0} = 0 := by
  set e := Fintype.equivFin σ
  have h := complexGaussian_eval_eq_zero_fin _ (rename e F)
    ((rename_injective _ e.injective).ne (by simpa using hF))
  rw [← (measurePreserving_piCongrLeft_complexGaussian e).measure_preimage
    (measurableSet_eq_fun (MvPolynomial.continuous_eval _).measurable
      measurable_const).nullMeasurableSet] at h
  convert h using 2
  ext z
  simp [eval_piCongrLeft_rename]

open MvPolynomial in
theorem ae_eval_ne_zero {F : MvPolynomial σ ℂ} (hF : F ≠ 0) :
    ∀ᵐ z ∂complexGaussian σ, eval z F ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (complexGaussian_eval_eq_zero hF)

open MvPolynomial in
theorem lintegral_enorm_log_norm_eval_lt_top (F : MvPolynomial σ ℂ) :
    ∫⁻ z, ‖log ‖eval z F‖‖ₑ ∂complexGaussian σ < ∞ := by
  set e := Fintype.equivFin σ
  have h := lintegral_enorm_log_norm_eval_lt_top_fin _ (rename e F)
  rw [← (measurePreserving_piCongrLeft_complexGaussian e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)] at h
  simpa [eval_piCongrLeft_rename] using h

open MvPolynomial in
/-- **`log |F|` is integrable** for the product of complex Gaussians (for every `F`; for
`F = 0` it vanishes). -/
theorem integrable_log_norm_eval (F : MvPolynomial σ ℂ) :
    Integrable (fun z ↦ log ‖eval z F‖) (complexGaussian σ) :=
  ⟨(MvPolynomial.continuous_eval F).measurable.norm.log.aestronglyMeasurable,
    lintegral_enorm_log_norm_eval_lt_top F⟩

end Several

end ProbabilityTheory
