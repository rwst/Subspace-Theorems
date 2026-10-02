/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.Analysis.Polynomial.GaussianMahlerDet
public import ForMathlib.NumberTheory.Height.LinearHeight
public import ForMathlib.RingTheory.MvPolynomial.ResultantSpace
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# The heights of the whole space

By Rémond's Lemma 3.7 (`MvPolynomial.associated_resForm_bot`), the resultant forms of
`ℙ = ℙ^{n_1} × ⋯ × ℙ^{n_q}` in generic linear forms are units or the determinants of generic
`(n_j + 1) × (n_j + 1)` matrices. Their coefficients are integers, so the nonarchimedean places
contribute at most `0`, and each archimedean place `log M(det)`. Hence
`h(α res(ℙ)) ≤ [K : ℚ] log M(det_{n_j + 1})` (`MvPolynomial.gaussHeight_resForm_bot_le`), with
the Gaussian Mahler measure `MvPolynomial.detLogMahler` of the generic determinant, and
`h(α res(ℙ)) = 0` in the degenerate cases (`MvPolynomial.gaussHeight_resForm_bot_eq_zero`).
Numerically, `log M(det_N) ≤ N (log (2N) / 2 + 2)` (`MvPolynomial.detLogMahler_le`). (Rémond
computes these heights exactly, LNM 1752, Ch. 7, Cor. 2.4.)
-/

@[expose] public section

open Finset Height Height.AdmissibleAbsValues Real

namespace MvPolynomial

/-- `log M(det (x_{ij}))`: the Gaussian Mahler measure of the generic `N × N` determinant. -/
noncomputable def detLogMahler (N : ℕ) : ℝ :=
  gaussLogMahler (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det

/-- `log M(det_N) ≤ N (log (2N) / 2 + 2)`, by Hadamard's inequality. -/
theorem detLogMahler_le (N : ℕ) : detLogMahler N ≤ N * (log (2 * N) / 2 + 2) :=
  gaussLogMahler_det_mvPolynomialX_le N

theorem scaleVars_one {τ : Type*} (P : MvPolynomial τ ℂ) : scaleVars (fun _ ↦ 1) P = P := by
  change aeval (fun t ↦ C 1 * X t) P = P
  simp only [map_one, one_mul]
  exact aeval_X_left_apply P

theorem map_det_mvPolynomialX {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) :
    map f (Matrix.mvPolynomialX (Fin N) (Fin N) R).det =
      (Matrix.mvPolynomialX (Fin N) (Fin N) S).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

section Det

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [DecidableEq σ] {b : σ → ι}
  {κ : Type*} {d : κ → ι → ℕ} {τ : κ → ι}

/-- The coefficients of the generic linear forms of the block `j`, as the variables of a generic
`N × N` determinant. -/
noncomputable def detVar (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) {N : ℕ} (f : {s // b s = j} ≃ Fin N) :
    Fin N × Fin N → GenericVar b d :=
  fun p ↦ linVar hd (e (f.symm p.1)) (f.symm p.2 : σ)
    ((f.symm p.2).2.trans (e (f.symm p.1)).2.symm)

omit [DecidableEq σ] in
theorem detVar_injective (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) {N : ℕ} (f : {s // b s = j} ≃ Fin N) :
    Function.Injective (detVar hd e f) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [detVar, linVar, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hi : i = i' := f.symm.injective (e.injective (Subtype.ext h1))
  subst hi
  have h3 := Finsupp.single_left_injective one_ne_zero (congrArg Subtype.val (eq_of_heq h2))
  rw [Prod.mk.injEq]
  exact ⟨rfl, f.symm.injective (Subtype.ext h3)⟩

theorem det_linMatrix_eq (K : Type*) [CommRing K] (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) {N : ℕ} (f : {s // b s = j} ≃ Fin N) :
    (linMatrix K hd e).det =
      rename (detVar hd e f) (Matrix.mvPolynomialX (Fin N) (Fin N) K).det := by
  rw [← Matrix.det_submatrix_equiv_self f.symm (linMatrix K hd e), AlgHom.map_det]
  congr 1
  ext i i'
  simp [linMatrix, Matrix.mvPolynomialX, detVar]

end Det

section Height

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [DecidableEq σ] {b : σ → ι}
  {κ : Type*} [Fintype κ] {d : κ → ι → ℕ} {τ : κ → ι}
  {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- **The height of a generic determinant**: `h(α det(u^{(l)}_t)) ≤ [K : ℚ] log M(det_N)`. -/
theorem gaussHeight_det_linMatrix_le (hK : ArchEmbedded K) (hd : ∀ l, d l = Pi.single (τ l) 1)
    {j : ι} (e : {s // b s = j} ≃ {l // τ l = j}) :
    gaussHeight remodelWeight (linMatrix K hd e).det ≤
      totalWeight K * detLogMahler (Fintype.card {s // b s = j}) := by
  set N := Fintype.card {s // b s = j}
  set f := Fintype.equivFin {s // b s = j}
  set g := detVar hd e f
  have hg := detVar_injective hd e f
  rw [det_linMatrix_eq K hd e f]
  set P := (Matrix.mvPolynomialX (Fin N) (Fin N) K).det
  have hP : rename g P ≠ 0 := fun h ↦ Matrix.det_mvPolynomialX_ne_zero (Fin N) K
    (rename_injective g hg (by rw [h, map_zero]))
  have hw : ∀ p, remodelWeight (g p) = 1 := fun p ↦ by
    simp only [g, detVar, linVar, remodelWeight, blockMultinomial]
    rw [Finset.prod_eq_one fun i _ ↦ by
      rw [Finsupp.single_eq_pi_single]
      exact Nat.multinomial_single _ _ _]
    simp
  have harch : ∀ v ∈ archAbsVal (K := K),
      archMahler remodelWeight v (rename g P) = exp (detLogMahler N) := fun v hv ↦ by
    have h := hK v hv
    rw [archMahler_of h, map_rename, scaleVars_rename g (w := fun p ↦ remodelWeight (g p))
      (fun _ ↦ rfl), funext hw, scaleVars_one, gaussLogMahler_rename hg, map_det_mvPolynomialX]
    rfl
  have hnon : ∀ v : nonarchAbsVal (K := K), maxNorm v.val (rename g P) ≤ 1 := fun v ↦ by
    have hPZ : P = map (Int.castRingHom K) (Matrix.mvPolynomialX (Fin N) (Fin N) ℤ).det :=
      (map_det_mvPolynomialX _ N).symm
    rw [maxNorm_rename hg, hPZ]
    refine maxNorm_le zero_le_one fun m ↦ ?_
    rw [coeff_map, eq_intCast]
    exact (isNonarchimedean _ v.2).apply_intCast_le_one (map_zero_le v.val 1) (map_one v.val)
      (map_neg_eq_map v.val)
  have hfin : ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val (rename g P) ≤ 1 := by
    rw [← finprod_one (α := nonarchAbsVal (K := K))]
    exact finprod_le_finprod₀ (hasFiniteMulSupport_maxNorm hP) (fun v ↦ maxNorm_nonneg _)
      (by fun_prop) hnon
  unfold gaussHeight
  split_ifs with h0
  · exact absurd h0 hP
  rw [Multiset.map_congr rfl harch, Multiset.map_const', Multiset.prod_replicate]
  calc log (exp (detLogMahler N) ^ archAbsVal.card *
        ∏ᶠ v : nonarchAbsVal (K := K), maxNorm v.val (rename g P))
      ≤ log (exp (detLogMahler N) ^ archAbsVal.card) :=
        log_le_log (mul_pos (pow_pos (exp_pos _) _) (finprod_maxNorm_pos hP))
          (mul_le_of_le_one_right (pow_pos (exp_pos _) _).le hfin)
    _ = totalWeight K * detLogMahler N := by
        rw [log_pow, log_exp, totalWeight]

theorem gaussHeight_of_isUnit {w : κ → ℂ} {F : MvPolynomial κ K} (hK : ArchEmbedded K)
    (hw : ∀ t, w t ≠ 0) (hF : IsUnit F) : gaussHeight w F = 0 := by
  rw [gaussHeight_of_associated hK hw (associated_one_iff_isUnit.2 hF), gaussHeight_one]

end Height

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] [AdmissibleAbsValues K] {κ : Type u} [Fintype κ]
  {d : κ → ι → ℕ} {τ : κ → ι}

/-- **The height of `ℙ`**: with generic linear forms, `n_i` in the block `i ≠ j` and `n_j + 1`
in the block `j`, `h(α res(ℙ)) ≤ [K : ℚ] log M(det_{n_j + 1})`. -/
theorem gaussHeight_resForm_bot_le (hK : ArchEmbedded K) (hb : Function.Surjective b)
    (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι} (e : {s // b s = j} ≃ {l // τ l = j})
    (hcard : ∀ i ≠ j, #{l | τ l = i} + 1 = #{s | b s = i}) :
    gaussHeight remodelWeight (resForm b K d ⊥) ≤
      totalWeight K * detLogMahler (Fintype.card {s // b s = j}) := by
  classical
  rw [gaussHeight_of_associated hK remodelWeight_ne_zero (associated_resForm_bot hb hd e hcard)]
  exact gaussHeight_det_linMatrix_le hK hd e

/-- In the degenerate distributions of the linear forms, `h(α res(ℙ)) = 0`. -/
theorem gaussHeight_resForm_bot_eq_zero [DecidableEq κ] (hK : ArchEmbedded K)
    (hb : Function.Surjective b) (hd : ∀ l, d l = Pi.single (τ l) 1)
    (hκ : ∑ i, (#{s | b s = i} - 1) + 1 ≤ Fintype.card κ)
    (h : ∀ l₀, ∃ i, #{s | b s = i} ≤ #{l ∈ Finset.univ.erase l₀ | τ l = i}) :
    gaussHeight remodelWeight (resForm b K d ⊥) = 0 :=
  gaussHeight_of_isUnit hK remodelWeight_ne_zero (isUnit_resForm_bot hb hd hκ h)

end Main

end MvPolynomial
