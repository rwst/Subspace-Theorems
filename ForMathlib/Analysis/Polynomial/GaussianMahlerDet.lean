/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerSpecialization
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial

-- Used only inside proofs.
import ForMathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The Gaussian Mahler measure of the generic determinant

We show `log M(det (x_{ij})_{N × N}) ≤ N (log (2N) / 2 + 2)`
(`MvPolynomial.gaussLogMahler_det_mvPolynomialX_le`). By Hadamard's inequality
(`Matrix.norm_det_le_prod_sqrt`), `log |det(e^{-c} Z)|` is at most the sum of the `log` of the
norms of the rows. Each row is a vector of `N` independent Gaussians, and Jensen's inequality gives
`∫ log ‖e^{-c} z‖₂ ≤ -c + log (∫ ‖z‖₂²) / 2 = -c + log (2N) / 2`. Finally `c ≥ -2`
(`ProbabilityTheory.neg_two_le_gaussLogMean`), from `log |w| ≥ -log⁺ |re w|⁻¹` and
`∫_{-1}^{1} |log x| dx = 2`.

The true value is `log (N!) / 2 + O(N)`, the same order as Rémond's Stoll numbers.
-/

@[expose] public section

open MeasureTheory Set Real

namespace ProbabilityTheory

/-- The second moment of the standard real Gaussian. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at h
  norm_num at h
  exact h.symm

/-- The second moment of the standard complex Gaussian: `∫ |w|² dγ₁(w) = 2`. -/
theorem integral_norm_sq_stdGaussian : ∫ w : ℂ, ‖w‖ ^ 2 ∂stdGaussian ℂ = 2 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have h : ∀ x : Fin 2 → ℝ, ‖∑ i, x i • Complex.orthonormalBasisOneI i‖ ^ 2 =
      x 0 ^ 2 + x 1 ^ 2 := fun x ↦ by
    simp [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply, ← sq]
  simp_rw [h]
  have hi : ∀ i : Fin 2, Integrable (fun x : Fin 2 → ℝ ↦ x i ^ 2)
      (Measure.pi fun _ ↦ gaussianReal 0 1) := fun i ↦ by
    have h2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
    exact integrable_comp_eval (μ := fun _ : Fin 2 ↦ gaussianReal 0 1) (i := i) h2
  have he : ∀ i : Fin 2, ∫ x, x i ^ 2 ∂(Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 1) = 1 :=
    fun i ↦ (integral_comp_eval (μ := fun _ : Fin 2 ↦ gaussianReal 0 1) (i := i)
      (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)).trans integral_sq_gaussianReal
  rw [integral_add (hi 0) (hi 1), he 0, he 1]
  norm_num

theorem integrable_norm_sq_stdGaussian : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) (stdGaussian ℂ) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian ℂ)).integrable_norm_pow two_ne_zero

/-- `∫_{-1}^{1} |log x| dx = 2`. -/
theorem lintegral_Icc_enorm_log : ∫⁻ x in Icc (-1 : ℝ) 1, ‖log x‖ₑ = ENNReal.ofReal 2 := by
  have hle : ∀ x ∈ Icc (-1 : ℝ) 1, log x ≤ 0 := fun x hx ↦ by
    rw [← log_abs]
    exact log_nonpos (abs_nonneg x) (abs_le.2 hx)
  have hneg : ∀ x ∈ Icc (-1 : ℝ) 1, ‖log x‖ₑ = ENNReal.ofReal (-log x) := fun x hx ↦ by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (hle x hx)]
  rw [setLIntegral_congr_fun measurableSet_Icc hneg, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_neg, integral_log]
    norm_num
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1))).neg
  · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ neg_nonneg.2 (hle x hx)

/-- `c = ∫ log |w| dγ₁(w) ≥ -2`. (In fact `c = (log 2 - γ) / 2`.) -/
theorem neg_two_le_gaussLogMean : -2 ≤ gaussLogMean := by
  set g : ℂ → ℝ := fun w ↦ log⁺ |w.re|⁻¹
  have hgm : Measurable g := continuous_posLog.measurable.comp
    (measurable_inv.comp (continuous_abs.measurable.comp Complex.measurable_re))
  have hlin : ∫⁻ w, ENNReal.ofReal (g w) ∂stdGaussian ℂ ≤ ENNReal.ofReal 2 := by
    have hm : Measurable fun x : ℝ ↦ ENNReal.ofReal (log⁺ |x|⁻¹) :=
      ENNReal.measurable_ofReal.comp (continuous_posLog.measurable.comp
        (measurable_inv.comp continuous_abs.measurable))
    have h := lintegral_posLog_inv_le 0
    simp only [sub_zero] at h
    rw [← map_re_stdGaussian, lintegral_map hm Complex.measurable_re,
      lintegral_Icc_enorm_log] at h
    exact h
  have hg : Integrable g (stdGaussian ℂ) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ ↦ posLog_nonneg)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hint : ∫ w, g w ∂stdGaussian ℂ ≤ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ posLog_nonneg)
      hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_two hlin
  have hae : ∀ᵐ w ∂stdGaussian ℂ, -g w ≤ log ‖w‖ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (stdGaussian_re_eq 0)] with w hw
    have hre : 0 < |w.re| := abs_pos.2 hw
    have hw0 : 0 < ‖w‖ := hre.trans_le (Complex.abs_re_le_norm w)
    rw [← posLog_sub_posLog_inv]
    have h1 : log⁺ ‖w‖⁻¹ ≤ g w := posLog_le_posLog (by linarith [inv_pos.2 hw0])
      (inv_anti₀ hre (Complex.abs_re_le_norm w))
    linarith [posLog_nonneg (x := ‖w‖)]
  have h := integral_mono_ae hg.neg integrable_log_norm_stdGaussian hae
  simp only [Pi.neg_apply, integral_neg] at h
  change -∫ w, g w ∂stdGaussian ℂ ≤ gaussLogMean at h
  linarith

end ProbabilityTheory

namespace MvPolynomial

open ProbabilityTheory

variable {τ : Type*} [Fintype τ]

theorem specRight_sum_X_mul_X (z : τ → ℂ) :
    specRight z (∑ t, X (Sum.inl t) * X (Sum.inr t) : MvPolynomial (τ ⊕ τ) ℂ) =
      ∑ t, C (z t) * X t := by
  simp [specRight, mul_comm]

/-- `log ‖z‖₂ = log M(∑_t z_t Y_t)`, also for `z = 0`. -/
theorem log_sqrt_eq_gaussLogMahler (z : τ → ℂ) :
    log √(∑ t, ‖z t‖ ^ 2) = gaussLogMahler
      (specRight z (∑ t, X (Sum.inl t) * X (Sum.inr t) : MvPolynomial (τ ⊕ τ) ℂ)) := by
  rw [specRight_sum_X_mul_X]
  by_cases hz : z = 0
  · simp [hz]
  · exact (gaussLogMahler_linear hz).symm

/-- **Jensen's inequality for a Gaussian vector**:
`∫ log ‖e^{-c} z‖₂ dγ(z) ≤ log (2 |τ|) / 2 + 2`. -/
theorem integrable_log_sqrt_and_integral_le :
    Integrable (fun z : τ → ℂ ↦ log √(∑ t, ‖gaussScale * z t‖ ^ 2)) (complexGaussian τ) ∧
      ∫ z, log √(∑ t, ‖gaussScale * z t‖ ^ 2) ∂complexGaussian τ ≤
        log (2 * Fintype.card τ) / 2 + 2 := by
  set P : MvPolynomial (τ ⊕ τ) ℂ := ∑ t, X (Sum.inl t) * X (Sum.inr t)
  have hint : Integrable (fun z : τ → ℂ ↦ log √(∑ t, ‖gaussScale * z t‖ ^ 2))
      (complexGaussian τ) := by
    refine (integrable_gaussLogMahler_specRight P).congr
      (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [P, ← log_sqrt_eq_gaussLogMahler, Pi.smul_apply, smul_eq_mul]
  refine ⟨hint, ?_⟩
  rcases isEmpty_or_nonempty τ with hτ | ⟨⟨t₀⟩⟩
  · simp
  set m : ℝ := 2 * Fintype.card τ
  have hm : 0 < m := by
    have := Fintype.card_pos_iff.2 ⟨t₀⟩
    positivity
  set a := ‖gaussScale‖
  have ha : 0 < a := norm_pos_iff.2 gaussScale_ne_zero
  set y : (τ → ℂ) → ℝ := fun z ↦ ∑ t, ‖z t‖ ^ 2
  have hti : ∀ t, Integrable (fun z : τ → ℂ ↦ ‖z t‖ ^ 2) (complexGaussian τ) := fun t ↦
    integrable_comp_eval (μ := fun _ : τ ↦ stdGaussian ℂ) integrable_norm_sq_stdGaussian
  have hyi : Integrable y (complexGaussian τ) := integrable_finsetSum _ fun t _ ↦ hti t
  have hy : ∫ z, y z ∂complexGaussian τ = m := by
    simp only [y]
    rw [integral_finsetSum _ fun t _ ↦ hti t]
    have h1 : ∀ t, ∫ z, ‖z t‖ ^ 2 ∂complexGaussian τ = 2 := fun t ↦
      (integral_comp_eval (μ := fun _ : τ ↦ stdGaussian ℂ) (i := t) (f := fun w : ℂ ↦ ‖w‖ ^ 2)
        (by fun_prop)).trans integral_norm_sq_stdGaussian
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
    ring
  set A := log a + (log m - 1) / 2
  have hae : ∀ᵐ z ∂complexGaussian τ,
      log √(∑ t, ‖gaussScale * z t‖ ^ 2) ≤ A + (2 * m)⁻¹ * y z := by
    filter_upwards [ae_eval_ne_zero (X_ne_zero (R := ℂ) t₀)] with z hz
    rw [eval_X] at hz
    have hy0 : 0 < y z := lt_of_lt_of_le (by positivity : 0 < ‖z t₀‖ ^ 2)
      (Finset.single_le_sum (f := fun t ↦ ‖z t‖ ^ 2) (fun _ _ ↦ by positivity)
        (Finset.mem_univ t₀))
    have he : ∑ t, ‖gaussScale * z t‖ ^ 2 = a ^ 2 * y z := by
      simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
      rfl
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le,
      log_mul ha.ne' (Real.sqrt_pos.2 hy0).ne', log_sqrt hy0.le]
    have h1 := log_le_sub_one_of_pos (div_pos hy0 hm)
    rw [log_div hy0.ne' hm.ne'] at h1
    have h2 : y z / m = 2 * ((2 * m)⁻¹ * y z) := by field_simp
    simp only [A]
    linarith
  refine (integral_mono_ae (g := fun z ↦ A + (2 * m)⁻¹ * y z) hint
    ((integrable_const A).add (hyi.const_mul _)) hae).trans ?_
  rw [integral_add (integrable_const A) (hyi.const_mul _), integral_const, integral_const_mul,
    hy]
  simp only [probReal_univ, smul_eq_mul, one_mul, A]
  have hlog : log a ≤ 2 := by
    change log ‖gaussScale‖ ≤ 2
    rw [gaussScale, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, log_exp]
    linarith [neg_two_le_gaussLogMean]
  have : (2 * m)⁻¹ * m = 1 / 2 := by field_simp
  linarith

/-- **The Gaussian Mahler measure of the generic determinant**:
`log M(det (x_{ij})_{N × N}) ≤ N (log (2N) / 2 + 2)`. -/
theorem gaussLogMahler_det_mvPolynomialX_le (N : ℕ) :
    gaussLogMahler (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det ≤
      N * (log (2 * N) / 2 + 2) := by
  set D := (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det
  have hD : D ≠ 0 := Matrix.det_mvPolynomialX_ne_zero _ _
  set B := log (2 * N) / 2 + 2
  set r : Fin N → (Fin N × Fin N → ℂ) → ℝ :=
    fun i z ↦ log √(∑ j, ‖gaussScale * z (i, j)‖ ^ 2)
  have hrow : ∀ i, Integrable (r i) (complexGaussian (Fin N × Fin N)) ∧
      ∫ z, r i z ∂complexGaussian (Fin N × Fin N) ≤ B := fun i ↦ by
    have hinj : Function.Injective (Prod.mk i : Fin N → Fin N × Fin N) := Prod.mk_right_injective i
    have hmeas : Measurable fun z : Fin N × Fin N → ℂ ↦ z ∘ Prod.mk i :=
      measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
    obtain ⟨h1, h2⟩ := integrable_log_sqrt_and_integral_le (τ := Fin N)
    rw [← map_comp_complexGaussian hinj] at h1 h2
    refine ⟨h1.comp_measurable hmeas, ?_⟩
    rw [integral_map hmeas.aemeasurable h1.aestronglyMeasurable, Fintype.card_fin] at h2
    exact h2
  have hlhs : Integrable (fun z ↦ log ‖eval (gaussScale • z) D‖)
      (complexGaussian (Fin N × Fin N)) := by
    simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale D)
  have hae : ∀ᵐ z ∂complexGaussian (Fin N × Fin N),
      log ‖eval (gaussScale • z) D‖ ≤ ∑ i, r i z := by
    filter_upwards [ae_eval_ne_zero (gaussRescale_ne_zero hD)] with z hz
    rw [eval_gaussRescale] at hz
    have hdet : eval (gaussScale • z) D = (Matrix.of fun i j ↦ gaussScale * z (i, j)).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Matrix.mvPolynomialX]
    rw [hdet] at hz ⊢
    have hH := Matrix.norm_det_le_prod_sqrt (Matrix.of fun i j ↦ gaussScale * z (i, j))
    simp only [Matrix.of_apply] at hH
    have hpos := norm_pos_iff.2 hz
    have hprod : ∏ i, √(∑ j, ‖gaussScale * z (i, j)‖ ^ 2) ≠ 0 := (hpos.trans_le hH).ne'
    rw [← log_prod fun i _ ↦ Finset.prod_ne_zero_iff.1 hprod i (Finset.mem_univ i)]
    exact log_le_log hpos hH
  calc gaussLogMahler D ≤ ∫ z, ∑ i, r i z ∂complexGaussian (Fin N × Fin N) :=
        integral_mono_ae hlhs (integrable_finsetSum _ fun i _ ↦ (hrow i).1) hae
    _ = ∑ i, ∫ z, r i z ∂complexGaussian (Fin N × Fin N) :=
        integral_finsetSum _ fun i _ ↦ (hrow i).1
    _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ ↦ (hrow i).2
    _ = N * B := by simp

end MvPolynomial
