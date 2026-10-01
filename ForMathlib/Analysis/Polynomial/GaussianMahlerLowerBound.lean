/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerMeasure
public import Mathlib.MeasureTheory.Integral.CircleAverage

-- Used only inside proofs.
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A lower bound for the Gaussian Mahler measure

The Gaussian Mahler measure bounds a coefficient from below: `log |F_m| ≤ log M(F)` for a
monomial `m` of the support of `F` that depends only on the support. In one variable this is
`|lead p| ≤ M(p)` (Jensen); the standard complex Gaussian is rotation invariant, so averages
over it are averages of circle averages, and the rescaling makes `∫ log |s w| = 0`. In several
variables, average over the first variable (Lemma 2.1 (1)) and induct.

## Main results

* `ProbabilityTheory.integral_circleAverage_stdGaussian`: polar averaging for `stdGaussian ℂ`.
* `Polynomial.log_norm_leadingCoeff_le_integral`: the one-variable bound.
* `MvPolynomial.exists_mem_log_norm_coeff_le`: `log |F_m| ≤ log M(F)` for some `m` depending only
  on the support of `F`.
-/

@[expose] public section

open MeasureTheory Real

namespace ProbabilityTheory

theorem measurePreserving_mul_circle (a : Circle) :
    MeasurePreserving (fun w : ℂ ↦ (a : ℂ) * w) (stdGaussian ℂ) (stdGaussian ℂ) := by
  have h := stdGaussian_map (E := ℂ) (rotation a)
  refine ⟨(rotation a).continuous.measurable, ?_⟩
  convert h using 2
  funext w
  exact (rotation_apply a w).symm

theorem measurableEmbedding_mul_circle (a : Circle) :
    MeasurableEmbedding fun w : ℂ ↦ (a : ℂ) * w := by
  convert (rotation a).toHomeomorph.measurableEmbedding using 1
  funext w
  exact (rotation_apply a w).symm

/-- **Polar averaging**: for the rotation-invariant `stdGaussian ℂ`, `∫ f` is the average of the
circle averages of `f` over the radii `‖w‖`. -/
theorem integral_circleAverage_stdGaussian {f : ℂ → ℝ} (hfm : Measurable f)
    (hf : Integrable f (stdGaussian ℂ)) :
    Integrable (fun w ↦ circleAverage f 0 ‖w‖) (stdGaussian ℂ) ∧
      ∫ w, circleAverage f 0 ‖w‖ ∂stdGaussian ℂ = ∫ w, f w ∂stdGaussian ℂ := by
  set μ := (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))
  set F : ℂ × ℝ → ℝ := fun p ↦ f (Circle.exp p.2 * p.1)
  have hcont : Continuous fun p : ℂ × ℝ ↦ (Circle.exp p.2 : ℂ) * p.1 :=
    (continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_snd)).mul continuous_fst
  have hFm : Measurable F := hfm.comp hcont.measurable
  have hsec : ∀ θ, Integrable (fun w ↦ F (w, θ)) (stdGaussian ℂ) := fun θ ↦
    (measurePreserving_mul_circle (Circle.exp θ)).integrable_comp_of_integrable hf
  have hint : ∀ θ, ∫ w, F (w, θ) ∂stdGaussian ℂ = ∫ w, f w ∂stdGaussian ℂ := fun θ ↦
    (measurePreserving_mul_circle (Circle.exp θ)).integral_comp
      (measurableEmbedding_mul_circle _) f
  have hnorm : ∀ θ, ∫ w, ‖F (w, θ)‖ ∂stdGaussian ℂ = ∫ w, ‖f w‖ ∂stdGaussian ℂ := fun θ ↦
    (measurePreserving_mul_circle (Circle.exp θ)).integral_comp
      (measurableEmbedding_mul_circle _) fun w ↦ ‖f w‖
  have hF : Integrable F ((stdGaussian ℂ).prod μ) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsec, ?_⟩
    simp_rw [hnorm]
    exact integrable_const _
  have hcirc : ∀ w, circleAverage f 0 ‖w‖ = (2 * π)⁻¹ * ∫ θ, F (w, θ) ∂μ := by
    intro w
    rw [circleAverage_eq_integral_add (Complex.arg w),
      intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ ↦ ?_)
    simp only [F]
    congr 1
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [circleMap_zero, Circle.coe_exp]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [hcirc]
    exact hF.integral_prod_left.const_mul _
  · simp_rw [hcirc]
    rw [integral_const_mul, integral_integral_swap hF]
    simp_rw [hint]
    rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le
      two_pi_pos.le, sub_zero, ← mul_assoc, inv_mul_cancel₀ two_pi_pos.ne', one_mul]

end ProbabilityTheory

namespace Polynomial

open ProbabilityTheory
open MvPolynomial (gaussScale gaussScale_ne_zero)

theorem integrable_log_norm_eval {p : ℂ[X]} (hp : p ≠ 0) :
    Integrable (fun w ↦ log ‖p.eval w‖) (stdGaussian ℂ) :=
  ⟨(continuous_norm.comp p.continuous).measurable.log.aestronglyMeasurable,
    (lintegral_enorm_log_norm_eval_le hp).trans_lt (ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) enorm_lt_top, ENNReal.ofReal_lt_top⟩,
        ENNReal.mul_lt_top (by simp) gaussLogConst_lt_top⟩)⟩

theorem log_norm_gaussScale : log ‖gaussScale‖ = -gaussLogMean := by
  rw [gaussScale, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, log_exp]

/-- `∫ log ‖s w‖ dγ(w) = 0`: the point of the rescaling. -/
theorem integral_log_norm_gaussScale_mul :
    Integrable (fun w : ℂ ↦ log ‖gaussScale * w‖) (stdGaussian ℂ) ∧
      ∫ w, log ‖gaussScale * w‖ ∂stdGaussian ℂ = 0 := by
  have hae : ∀ᵐ w ∂stdGaussian ℂ, w ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := stdGaussian ℂ) 0)
  have h : (fun w : ℂ ↦ log ‖gaussScale * w‖) =ᵐ[stdGaussian ℂ]
      fun w ↦ log ‖gaussScale‖ + log ‖w‖ := by
    filter_upwards [hae] with w hw
    rw [norm_mul, log_mul (norm_ne_zero_iff.2 gaussScale_ne_zero) (norm_ne_zero_iff.2 hw)]
  have hmean : ∫ w, log ‖w‖ ∂stdGaussian ℂ = gaussLogMean := rfl
  refine ⟨((integrable_const _).add integrable_log_norm_stdGaussian).congr h.symm, ?_⟩
  rw [integral_congr_ae h, integral_add (integrable_const _) integrable_log_norm_stdGaussian,
    integral_const, hmean, log_norm_gaussScale]
  simp

theorem leadingCoeff_comp_C_mul_X (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) :
    (p.comp (C c * X)).leadingCoeff = p.leadingCoeff * c ^ p.natDegree := by
  rw [leadingCoeff_comp (by rw [natDegree_C_mul_X c hc]; exact one_ne_zero), leadingCoeff_C_mul_X]

/-- **The one-variable lower bound**: `log |lead p| ≤ ∫ log |p(s w)| dγ(w)`. By polar averaging and
Jensen, the circle average of `log |p(s ·)|` over the radius `‖w‖` is at least
`log |lead p| + deg p · log ‖s w‖`, whose integral is `log |lead p|`. -/
theorem log_norm_leadingCoeff_le_integral {p : ℂ[X]} (hp : p ≠ 0) :
    log ‖p.leadingCoeff‖ ≤ ∫ w, log ‖p.eval (gaussScale * w)‖ ∂stdGaussian ℂ := by
  have hlp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp
  set q := p.comp (C gaussScale * X)
  have hq : ∀ w, p.eval (gaussScale * w) = q.eval w := fun w ↦ by simp [q]
  have hq0 : q ≠ 0 := fun h ↦ by
    have := leadingCoeff_comp_C_mul_X p gaussScale_ne_zero
    rw [← show q = p.comp (C gaussScale * X) from rfl, h, leadingCoeff_zero] at this
    exact mul_ne_zero hlp (pow_ne_zero _ gaussScale_ne_zero) this.symm
  have hfm : Measurable fun w ↦ log ‖p.eval (gaussScale * w)‖ :=
    (continuous_norm.comp (p.continuous.comp (continuous_const.mul continuous_id))).measurable.log
  have hf : Integrable (fun w ↦ log ‖p.eval (gaussScale * w)‖) (stdGaussian ℂ) := by
    simpa [hq] using integrable_log_norm_eval hq0
  obtain ⟨hint, heq⟩ := integral_circleAverage_stdGaussian hfm hf
  rw [← heq]
  have hlow : ∀ w : ℂ, w ≠ 0 → log ‖p.leadingCoeff‖ + p.natDegree * log ‖gaussScale * w‖ ≤
      circleAverage (fun z ↦ log ‖p.eval (gaussScale * z)‖) 0 ‖w‖ := fun w hw ↦ by
    set c : ℂ := gaussScale * ‖w‖
    have hc : c ≠ 0 := mul_ne_zero gaussScale_ne_zero (by simpa using hw)
    have hcw : ‖c‖ = ‖gaussScale * w‖ := by simp [c]
    set r := p.comp (C c * X)
    have hr : circleAverage (fun z ↦ log ‖p.eval (gaussScale * z)‖) 0 ‖w‖ =
        r.logMahlerMeasure := by
      rw [circleAverage_eq_circleAverage_zero_one, logMahlerMeasure_def]
      congr 1
      funext z
      simp [r, c, mul_assoc]
    have hlead := leadingCoeff_comp_C_mul_X p hc
    have hr0 : r.leadingCoeff ≠ 0 := by
      rw [hlead]
      exact mul_ne_zero hlp (pow_ne_zero _ hc)
    rw [hr, logMahlerMeasure_eq_log_MahlerMeasure]
    calc log ‖p.leadingCoeff‖ + p.natDegree * log ‖gaussScale * w‖ = log ‖r.leadingCoeff‖ := by
          rw [hlead, norm_mul p.leadingCoeff, norm_pow, log_mul (norm_ne_zero_iff.2 hlp)
            (pow_ne_zero _ (norm_ne_zero_iff.2 hc)), log_pow, hcw]
      _ ≤ log r.mahlerMeasure := log_le_log (norm_pos_iff.2 hr0) (leadingCoeff_le_mahlerMeasure r)
  have hae : ∀ᵐ w ∂stdGaussian ℂ, w ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := stdGaussian ℂ) 0)
  obtain ⟨hsi, hs0⟩ := integral_log_norm_gaussScale_mul
  have hlin : Integrable (fun w : ℂ ↦ log ‖p.leadingCoeff‖ + p.natDegree * log ‖gaussScale * w‖)
      (stdGaussian ℂ) := (integrable_const _).add (hsi.const_mul _)
  calc log ‖p.leadingCoeff‖
      = ∫ w, (log ‖p.leadingCoeff‖ + p.natDegree * log ‖gaussScale * w‖) ∂stdGaussian ℂ := by
        rw [integral_add (integrable_const _) (hsi.const_mul _), integral_const_mul, hs0]
        simp
    _ ≤ _ := integral_mono_ae hlin hint (hae.mono hlow)

end Polynomial

namespace ProbabilityTheory

/-- Integration over `Fin (n + 1) → ℂ` splits off the first coordinate (Bochner integrals). -/
theorem integral_complexGaussian_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ}
    (hf : Integrable f (complexGaussian (Fin (n + 1)))) :
    Integrable (fun y ↦ ∫ w, f (Fin.cons w y) ∂stdGaussian ℂ) (complexGaussian (Fin n)) ∧
      ∫ z, f z ∂complexGaussian (Fin (n + 1)) =
        ∫ y, ∫ w, f (Fin.cons w y) ∂stdGaussian ℂ ∂complexGaussian (Fin n) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ stdGaussian ℂ) 0).symm
  have he : ∀ p : ℂ × (Fin n → ℂ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm p = Fin.cons p.1 p.2 :=
    fun p ↦ by simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero']
  have hf' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hf
  have h2 := hf'.integral_prod_right
  simp only [Function.comp_apply, he] at h2
  refine ⟨h2, ?_⟩
  calc ∫ z, f z ∂complexGaussian (Fin (n + 1))
      = ∫ p, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm p)
          ∂(stdGaussian ℂ).prod (complexGaussian (Fin n)) :=
        (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) f).symm
    _ = _ := by
        have h3 := integral_prod_symm _ hf'
        simp only [Function.comp_apply, he] at h3
        simp only [he]
        exact h3

end ProbabilityTheory

namespace MvPolynomial

open ProbabilityTheory

/-- The Mahler measure of `F` bounds that of its leading coefficient in the first variable. -/
theorem gaussLogMahler_leadingCoeff_finSuccEquiv_le {n : ℕ} {F : MvPolynomial (Fin (n + 1)) ℂ}
    (hF : F ≠ 0) : gaussLogMahler (finSuccEquiv ℂ n F).leadingCoeff ≤ gaussLogMahler F := by
  set P := finSuccEquiv ℂ n F
  set Q := P.leadingCoeff
  have hP : P ≠ 0 := by simpa [P] using hF
  have hQ : Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  have hFi : Integrable (fun z ↦ log ‖eval (gaussScale • z) F‖) (complexGaussian (Fin (n + 1))) :=
    by simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale F)
  obtain ⟨hint, heq⟩ := integral_complexGaussian_succ hFi
  have hcons : ∀ (w : ℂ) (y : Fin n → ℂ), eval (gaussScale • (Fin.cons w y : Fin (n + 1) → ℂ)) F =
      (P.map (eval (gaussScale • y))).eval (gaussScale * w) := fun w y ↦ by
    have h : gaussScale • (Fin.cons w y : Fin (n + 1) → ℂ) =
        Fin.cons (gaussScale * w) (gaussScale • y) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    rw [h, eval_eq_eval_mv_eval']
  rw [gaussLogMahler, gaussLogMahler, heq]
  refine integral_mono_ae ?_ hint ?_
  · simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale Q)
  filter_upwards [ae_eval_ne_zero (gaussRescale_ne_zero hQ)] with y hy
  rw [eval_gaussRescale] at hy
  simp_rw [hcons]
  have hlead : (P.map (eval (gaussScale • y))).leadingCoeff = eval (gaussScale • y) Q :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy
  have hne : P.map (eval (gaussScale • y)) ≠ 0 := fun h0 ↦ hy (by
    rw [← hlead, h0, Polynomial.leadingCoeff_zero])
  rw [← hlead]
  exact Polynomial.log_norm_leadingCoeff_le_integral hne

theorem exists_mem_log_norm_coeff_le_fin (n : ℕ) :
    ∀ S : Finset (Fin n →₀ ℕ), S.Nonempty → ∃ m ∈ S, ∀ F : MvPolynomial (Fin n) ℂ,
      F.support = S → log ‖F.coeff m‖ ≤ gaussLogMahler F := by
  induction n with
  | zero =>
    intro S hS
    obtain ⟨m, hm⟩ := hS
    refine ⟨m, hm, fun F _ ↦ ?_⟩
    rw [Subsingleton.elim m 0]
    conv_rhs => rw [F.eq_C_of_isEmpty]
    rw [gaussLogMahler_C]
  | succ n ih =>
    intro S hS
    set k := S.sup fun m ↦ m 0
    set T := S.filter fun m ↦ m 0 = k
    have hT : T.Nonempty := by
      obtain ⟨m, hm, hmk⟩ := S.exists_mem_eq_sup hS fun m ↦ m 0
      exact ⟨m, Finset.mem_filter.2 ⟨hm, hmk.symm⟩⟩
    obtain ⟨m', hm', H⟩ := ih (T.image Finsupp.tail) (hT.image _)
    obtain ⟨m₀, hm₀T, rfl⟩ := Finset.mem_image.1 hm'
    have hm₀ := Finset.mem_filter.1 hm₀T
    refine ⟨m₀, hm₀.1, fun F hF ↦ ?_⟩
    have hF0 : F ≠ 0 := by
      rintro rfl
      exact hS.ne_empty (by simpa using hF.symm)
    set P := finSuccEquiv ℂ n F
    have hdeg : P.natDegree = k := by rw [natDegree_finSuccEquiv, degreeOf_eq_sup, hF]
    have hQsupp : P.leadingCoeff.support = T.image Finsupp.tail := by
      rw [Polynomial.leadingCoeff, hdeg]
      have h := image_support_finSuccEquiv (f := F) (i := k)
      rw [hF] at h
      have hT' : T = (P.coeff k).support.image (Finsupp.cons k) := h.symm
      rw [hT', Finset.image_image]
      simp [Function.comp_def, Finsupp.tail_cons]
    have hcoeff : F.coeff m₀ = P.leadingCoeff.coeff (Finsupp.tail m₀) := by
      rw [Polynomial.leadingCoeff, hdeg, finSuccEquiv_coeff_coeff, ← hm₀.2, Finsupp.cons_tail]
    rw [hcoeff]
    exact (H _ hQsupp).trans (gaussLogMahler_leadingCoeff_finSuccEquiv_le hF0)

/-- **The Gaussian Mahler measure bounds a coefficient**: for every nonempty `S` there is `m ∈ S`
with `log |F_m| ≤ log M(F)` for every `F` with support `S`. -/
theorem exists_mem_log_norm_coeff_le {σ : Type*} [Fintype σ] (S : Finset (σ →₀ ℕ))
    (hS : S.Nonempty) : ∃ m ∈ S, ∀ F : MvPolynomial σ ℂ, F.support = S →
      log ‖F.coeff m‖ ≤ gaussLogMahler F := by
  classical
  set e := Fintype.equivFin σ
  obtain ⟨m', hm', H⟩ :=
    exists_mem_log_norm_coeff_le_fin _ (S.image (Finsupp.mapDomain e)) (hS.image _)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
  refine ⟨m, hm, fun F hF ↦ ?_⟩
  have h := H (rename e F) (by rw [support_rename_of_injective e.injective, hF])
  rwa [coeff_rename_mapDomain _ e.injective, gaussLogMahler_rename e.injective] at h

end MvPolynomial
