/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerMeasure
public import ForMathlib.RingTheory.MvPolynomial.WeightedAeval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Specializing a polynomial that splits into linear forms

Rémond's Lemma 2.1 (2) (LNM 1752, Ch. 7) at an archimedean place, in the Gaussian form: let
`P ∈ ℂ[τ ⊕ σ]` be such that every specialization `P(·, z)` is a product `c ∏_j L_j` of `D` linear
forms in the variables `τ`. Then specializing the variables `τ` at `a` gives
`log M(P(a, ·)) ≤ log M(P) + D log ‖a‖₂`. By Lemma 2.1 (1) both sides are averages over `z`,
and pointwise `|P(a, z)| = |c| ∏_j |L_j(a)| ≤ |c| ∏_j ‖L_j‖₂ ‖a‖₂ = M(P(·, z)) ‖a‖₂^D` by
Cauchy–Schwarz.

## Main definitions

* `MvPolynomial.specLeft a`: the specialization `P ↦ P(a, ·)` of `ℂ[τ ⊕ σ]` at `a ∈ ℂ^τ`.

## Main results

* `MvPolynomial.gaussLogMahler_specLeft_le`: Rémond's Lemma 2.1 (2); with the number of linear
  forms from homogeneity, `MvPolynomial.gaussLogMahler_specLeft_le_of_isWeightedHomogeneous`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace MvPolynomial

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] [Fintype τ] in
/-- The specialization `P(a, ·)` of `P ∈ ℂ[τ ⊕ σ]` at `a ∈ ℂ^τ`. -/
noncomputable def specLeft (a : τ → ℂ) : MvPolynomial (τ ⊕ σ) ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval (Sum.elim (fun t ↦ C (a t)) X)

omit [Fintype σ] [Fintype τ] in
theorem eval_specLeft (a : τ → ℂ) (z : σ → ℂ) (P : MvPolynomial (τ ⊕ σ) ℂ) :
    eval z (specLeft a P) = eval (Sum.elim a z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [specLeft]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [specLeft, hp] at *

/-- `z ↦ log M(P(·, z))` is integrable (Fubini). -/
theorem integrable_gaussLogMahler_specRight (P : MvPolynomial (τ ⊕ σ) ℂ) :
    Integrable (fun z ↦ gaussLogMahler (specRight (gaussScale • z) P)) (complexGaussian σ) := by
  have hP : Integrable (fun x ↦ log ‖eval (gaussScale • x) P‖) (complexGaussian (τ ⊕ σ)) := by
    simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale P)
  have hmp := measurePreserving_sumPiEquivProdPi_symm (fun _ : τ ⊕ σ ↦ stdGaussian ℂ)
  have hf' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hP
  refine hf'.integral_prod_right.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  have hs : ∀ w : τ → ℂ, gaussScale • Sum.elim w z =
      Sum.elim (gaussScale • w) (gaussScale • z) := fun w ↦ by
    ext (s | s) <;> rfl
  simp only [Function.comp_apply, gaussLogMahler, eval_specRight]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [← hs]
  rfl

/-- **Cauchy–Schwarz** for a linear form. -/
theorem norm_sum_mul_le (x a : τ → ℂ) :
    ‖∑ t, x t * a t‖ ≤ √(∑ t, ‖x t‖ ^ 2) * √(∑ t, ‖a t‖ ^ 2) :=
  (norm_sum_le _ _).trans <| by
    simp_rw [norm_mul]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The pointwise inequality: `|Q(a)| ≤ M(Q) ‖a‖₂^D` for `Q = c ∏_{j ≤ D} L_j` a product of linear
forms. -/
theorem log_norm_eval_le_gaussLogMahler (a : τ → ℂ) (c : ℂ) (Z : Multiset (τ → ℂ))
    (h : eval a (C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod) ≠ 0) :
    log ‖eval a (C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod)‖ ≤
      gaussLogMahler (C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod) +
        Z.card * log √(∑ t, ‖a t‖ ^ 2) := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons x Z ih =>
    set L : MvPolynomial τ ℂ := ∑ t, C (x t) * X t
    set Q := C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod
    have hQ : C c * ((x ::ₘ Z).map fun x ↦ ∑ t, C (x t) * X t).prod = L * Q := by
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    rw [hQ] at h ⊢
    rw [eval_mul] at h
    have hL : eval a L ≠ 0 := left_ne_zero_of_mul h
    have hQ' : eval a Q ≠ 0 := right_ne_zero_of_mul h
    have hLa : eval a L = ∑ t, x t * a t := by simp [L]
    have hx : x ≠ 0 := fun h0 ↦ hL (by simp [hLa, h0])
    have hQ0 : Q ≠ 0 := fun h0 ↦ hQ' (by rw [h0, map_zero])
    rw [eval_mul, norm_mul, log_mul (norm_ne_zero_iff.2 hL) (norm_ne_zero_iff.2 hQ'),
      gaussLogMahler_mul (linear_ne_zero hx) hQ0, gaussLogMahler_linear hx, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one]
    have hcs := norm_sum_mul_le x a
    rw [← hLa] at hcs
    have hpos := norm_pos_iff.2 hL
    have hxs : 0 < √(∑ t, ‖x t‖ ^ 2) := lt_of_le_of_ne (sqrt_nonneg _) fun h0 ↦ by
      rw [← h0, zero_mul] at hcs
      linarith
    have has : 0 < √(∑ t, ‖a t‖ ^ 2) := lt_of_le_of_ne (sqrt_nonneg _) fun h0 ↦ by
      rw [← h0, mul_zero] at hcs
      linarith
    have h1 : log ‖eval a L‖ ≤ log √(∑ t, ‖x t‖ ^ 2) + log √(∑ t, ‖a t‖ ^ 2) := by
      rw [← log_mul hxs.ne' has.ne']
      exact log_le_log hpos hcs
    linarith [ih hQ']

/-- **Rémond's Lemma 2.1 (2)** at an archimedean place: if every specialization `P(·, z)` is a
product of `D` linear forms, then `log M(P(a, ·)) ≤ log M(P) + D log ‖a‖₂`. -/
theorem gaussLogMahler_specLeft_le {P : MvPolynomial (τ ⊕ σ) ℂ} {D : ℕ} (a : τ → ℂ)
    (hP : ∀ z : σ → ℂ, ∃ (c : ℂ) (Z : Multiset (τ → ℂ)), Z.card = D ∧
      specRight z P = C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod)
    (ha : specLeft a P ≠ 0) :
    gaussLogMahler (specLeft a P) ≤ gaussLogMahler P + D * log √(∑ t, ‖a t‖ ^ 2) := by
  set A := (D : ℝ) * log √(∑ t, ‖a t‖ ^ 2)
  have hint : ∫ z, (gaussLogMahler (specRight (gaussScale • z) P) + A) ∂complexGaussian σ =
      (∫ z, gaussLogMahler (specRight (gaussScale • z) P) ∂complexGaussian σ) + A := by
    rw [integral_add (integrable_gaussLogMahler_specRight P) (integrable_const A),
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [gaussLogMahler_eq_integral_specRight P, ← hint, gaussLogMahler]
  refine integral_mono_ae ?_ ((integrable_gaussLogMahler_specRight P).add (integrable_const A)) ?_
  · simpa [eval_gaussRescale] using integrable_log_norm_eval (gaussRescale (specLeft a P))
  filter_upwards [ae_eval_ne_zero (gaussRescale_ne_zero ha)] with z hz
  rw [eval_gaussRescale] at hz
  obtain ⟨c, Z, hZ, hQ⟩ := hP (gaussScale • z)
  have he : eval (gaussScale • z) (specLeft a P) = eval a (specRight (gaussScale • z) P) := by
    rw [eval_specLeft, eval_specRight]
  rw [he, hQ] at hz ⊢
  have h := log_norm_eval_le_gaussLogMahler a c Z hz
  rwa [hZ] at h

omit [Fintype σ] in
theorem isHomogeneous_prod_linear (Z : Multiset (τ → ℂ)) :
    ((Z.map fun x ↦ ∑ t, C (x t) * X t : Multiset (MvPolynomial τ ℂ)).prod).IsHomogeneous
      Z.card := by
  induction Z using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one τ ℂ
  | cons x Z ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (IsHomogeneous.sum _ _ _ fun t _ ↦ (isHomogeneous_X ℂ t).C_mul _).mul ih

omit [Fintype σ] [Fintype τ] in
/-- `P(·, z)` is homogeneous of degree `D` if `P` has degree `D` in the variables `τ`. -/
theorem isHomogeneous_specRight {P : MvPolynomial (τ ⊕ σ) ℂ} {D : ℕ}
    (hD : IsWeightedHomogeneous (Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)) P D) (z : σ → ℂ) :
    (specRight z P).IsHomogeneous D :=
  hD.aeval_of_algebra _ fun i ↦ by
    rcases i with t | s
    · exact isWeightedHomogeneous_X ℂ _ t
    · exact isWeightedHomogeneous_C _ (z s)

/-- **Rémond's Lemma 2.1 (2)** at an archimedean place, for `P` of degree `D` in the variables
`τ` whose specializations `P(·, z)` are products of linear forms. -/
theorem gaussLogMahler_specLeft_le_of_isWeightedHomogeneous {P : MvPolynomial (τ ⊕ σ) ℂ} {D : ℕ}
    (a : τ → ℂ) (hD : IsWeightedHomogeneous (Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)) P D)
    (hP : ∀ z : σ → ℂ, ∃ (c : ℂ) (Z : Multiset (τ → ℂ)),
      specRight z P = C c * (Z.map fun x ↦ ∑ t, C (x t) * X t).prod)
    (ha : specLeft a P ≠ 0) :
    gaussLogMahler (specLeft a P) ≤ gaussLogMahler P + D * log √(∑ t, ‖a t‖ ^ 2) := by
  refine gaussLogMahler_specLeft_le a (fun z ↦ ?_) ha
  obtain ⟨c, Z, h⟩ := hP z
  by_cases hQ : specRight z P = 0
  · exact ⟨0, Multiset.replicate D 0, by simp, by rw [hQ, C_0, zero_mul]⟩
  refine ⟨c, Z, ?_, h⟩
  have h1 := isHomogeneous_specRight hD z
  rw [h] at hQ h1
  exact ((isHomogeneous_prod_linear Z).C_mul c).inj_right h1 hQ

end MvPolynomial
