/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedSubspaceHeight
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.LinearAlgebra.Matrix.Transvection

-- Used only inside proofs.
import ArithmeticHeights.GaussLemma
import QuantitativeSubspace.TwistedCalculus

/-!
# Symmetric powers of a twist of the plane

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, §1 and §4. The case `n = 2` of the absolute Minkowski theorem (RT96 Prop. 5.3) runs through
the symmetric powers `S^r A` of a twist `A` of the plane, acting on the binary forms of degree `r`.
This file supplies them and the two facts Prop. 5.3 takes from §4:

* **Lemma 4.5** for `m = 2`: `det S^r M = (det M)^{r(r+1)/2}`, hence
  `|det S^r A|_𝔸 = |det A|_𝔸^{r(r+1)/2}`;
* **Lemma 4.8**, the half Prop. 5.3 uses: `H_A(x₁) ⋯ H_A(x_r) ≤ √2^r · H_{S^r A}(x₁ ⋯ x_r)`.

Binary forms are dehomogenized: `x₀ X + x₁ Y` is the polynomial `x₀ + x₁ T` (`binLinear`), a form
of degree `r` is a polynomial of degree at most `r` read on its first `r + 1` coefficients
(`coeffVec`), and `S^r M` is the matrix whose column `l` holds the coefficients of
`(M e₀)^{r-l} (M e₁)^l` (`Matrix.symPow`). That it acts on products of linear forms by
`S^r M (x₁ ⋯ x_r) = (M x₁) ⋯ (M x_r)` is the homogenization identity `homEval_prod_binLinear`;
functoriality, `S^r 1 = 1` and the action of ring homomorphisms follow, and Lemma 4.5 is proved by
`Matrix.diagonal_transvection_induction`, where `S^r` of a transvection is triangular with unit
diagonal and `S^r` of a diagonal matrix is diagonal.

**The norm on `S^r`.** RT96 give `S^r(Lⁿ)` the ℓ² norm in the monomial basis, and their addendum
corrects a claim that `S^r` of a unitary matrix preserves it. Nothing here needs that claim: the
archimedean components of `S^r A` are just `S^r A_φ`, and Lemma 4.8 at a complex place is proved
directly from the Mahler measure: `‖z‖ ≤ √2 · M(ℓ_z)` for a linear form, `M` is multiplicative,
and Landau's inequality `M(p) ≤ ‖p‖₂` (Mathlib's `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`). At a
finite place it is an equality, Gauss's lemma (`Polynomial.iSup_coeff_mul`).

## Main definitions

* `Polynomial.binLinear`, `Polynomial.coeffVec`: linear forms and binary forms of degree `r`.
* `Matrix.symPow r M`: the `r`-th symmetric power of a `2 × 2` matrix.
* `NumberField.Twist.symPow A r`: the `r`-th symmetric power of a twist of the plane.

## Main results

* `Matrix.symPow_mulVec_coeffVec_prod`, `Matrix.symPow_mul`, `Matrix.symPow_one`,
  `Matrix.symPow_map`: the action on products, functoriality, ring homomorphisms.
* `Matrix.det_symPow`: RT96 Lemma 4.5 for `m = 2`.
* `NumberField.Twist.absDet_symPow`: `|det S^r A|_𝔸 = |det A|_𝔸^{r(r+1)/2}`.
* `NumberField.Twist.prod_absMulHeight_le`: RT96 Lemma 4.8 (lower half).

This is milestone Q2.2c of `QuantitativeSubspace/README.md` (its first part).
-/

@[expose] public section

open Finset Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The binary linear form `x₀ X + x₁ Y` of `x : Fin 2 → R`, dehomogenized at `X = 1`:
`x₀ + x₁ T`. -/
noncomputable def binLinear (x : Fin 2 → R) : R[X] := C (x 0) + C (x 1) * X

/-- The first `r + 1` coefficients of a polynomial: a binary form of degree `r`, dehomogenized,
read in the monomial basis `X^{r-k} Y^k`. -/
def coeffVec (r : ℕ) (p : R[X]) : Fin (r + 1) → R := fun k ↦ p.coeff k

/-- The homogenization in degree `r` of `p`, evaluated at the pair `(u, w)`:
`∑_{l ≤ r} p_l u^{r-l} w^l`. -/
noncomputable def homEval (r : ℕ) (u w p : R[X]) : R[X] :=
  ∑ l ∈ range (r + 1), C (p.coeff l) * u ^ (r - l) * w ^ l

theorem natDegree_binLinear_le (x : Fin 2 → R) : (binLinear x).natDegree ≤ 1 := by
  rw [binLinear, add_comm]
  exact natDegree_linear_le

theorem natDegree_prod_binLinear_le {r : ℕ} (x : Fin r → Fin 2 → R) :
    (∏ j, binLinear (x j)).natDegree ≤ r :=
  (natDegree_prod_le _ _).trans <| (sum_le_sum fun j _ ↦ natDegree_binLinear_le (x j)).trans
    (by simp)

theorem homEval_add (r : ℕ) (u w p q : R[X]) :
    homEval r u w (p + q) = homEval r u w p + homEval r u w q := by
  simp only [homEval, coeff_add, C_add, add_mul, sum_add_distrib]

theorem homEval_C_mul (r : ℕ) (u w : R[X]) (a : R) (p : R[X]) :
    homEval r u w (C a * p) = C a * homEval r u w p := by
  simp only [homEval, coeff_C_mul, C_mul, mul_sum, mul_assoc]

theorem homEval_succ {r : ℕ} (u w : R[X]) {p : R[X]} (hp : p.natDegree ≤ r) :
    homEval (r + 1) u w p = u * homEval r u w p := by
  rw [homEval, sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega), C_0, zero_mul,
    zero_mul, add_zero, homEval, mul_sum]
  refine sum_congr rfl fun l hl ↦ ?_
  rw [mem_range] at hl
  rw [show r + 1 - l = (r - l) + 1 by omega, pow_succ]
  ring

theorem homEval_mul_X (r : ℕ) (u w p : R[X]) :
    homEval (r + 1) u w (p * X) = w * homEval r u w p := by
  rw [homEval, sum_range_succ', coeff_mul_X_zero, C_0, zero_mul, zero_mul, add_zero, homEval,
    mul_sum]
  refine sum_congr rfl fun l hl ↦ ?_
  rw [coeff_mul_X, show r + 1 - (l + 1) = r - l by omega, pow_succ]
  ring

theorem homEval_mul_binLinear {r : ℕ} (u w : R[X]) {p : R[X]} (hp : p.natDegree ≤ r)
    (x : Fin 2 → R) :
    homEval (r + 1) u w (p * binLinear x) = homEval r u w p * (C (x 0) * u + C (x 1) * w) := by
  have : p * binLinear x = C (x 0) * p + C (x 1) * (p * X) := by rw [binLinear]; ring
  rw [this, homEval_add, homEval_C_mul, homEval_C_mul, homEval_succ u w hp, homEval_mul_X]
  ring

/-- **Homogenization is multiplicative on products of linear forms.** -/
theorem homEval_prod_binLinear (u w : R[X]) {r : ℕ} (x : Fin r → Fin 2 → R) :
    homEval r u w (∏ j, binLinear (x j)) = ∏ j, (C (x j 0) * u + C (x j 1) * w) := by
  induction r with
  | zero => simp [homEval]
  | succ r ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc,
      homEval_mul_binLinear u w (natDegree_prod_binLinear_le _), ih]

theorem binLinear_map {S : Type*} [CommRing S] (f : R →+* S) (x : Fin 2 → R) :
    binLinear (f ∘ x) = (binLinear x).map f := by
  simp [binLinear, Polynomial.map_add, Polynomial.map_mul]

theorem coeffVec_map {S : Type*} [CommRing S] (f : R →+* S) (r : ℕ) (p : R[X]) :
    coeffVec r (p.map f) = f ∘ coeffVec r p := by
  ext k
  simp [coeffVec]

/-- The standard point of the `j`-th factor of `X^{r-l} Y^l`: `e₁` for the first `l` factors and
`e₀` after them. -/
def unitPt (l j : ℕ) : Fin 2 → R := if j < l then ![0, 1] else ![1, 0]

theorem prod_binLinear_unitPt (l r : ℕ) :
    ∏ j : Fin r, binLinear (unitPt (R := R) l j) = X ^ min l r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, ih, Fin.val_last]
    by_cases h : r < l
    · rw [show min l (r + 1) = min l r + 1 by omega, pow_succ, unitPt, ite_eq_left h]
      simp [binLinear]
    · rw [show min l (r + 1) = min l r by omega, unitPt, ite_eq_right h]
      simp [binLinear]

theorem coeffVec_X_pow (r : ℕ) (l : Fin (r + 1)) :
    coeffVec r (X ^ (l : ℕ) : R[X]) = Pi.single l 1 := by
  ext k
  simp only [coeffVec, coeff_X_pow, Pi.single_apply, Fin.val_inj]

end Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-- **The `r`-th symmetric power of a `2 × 2` matrix**, in the monomial basis `X^{r-l} Y^l` of
binary forms of degree `r`: its column `l` holds the coefficients of `(M e₀)^{r-l} (M e₁)^l`. -/
noncomputable def symPow (r : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  of fun k l ↦ (binLinear (Mᵀ 0) ^ (r - l) * binLinear (Mᵀ 1) ^ (l : ℕ)).coeff k

theorem symPow_mulVec_coeffVec (r : ℕ) (M : Matrix (Fin 2) (Fin 2) R) (p : R[X]) :
    symPow r M *ᵥ coeffVec r p =
      coeffVec r (homEval r (binLinear (Mᵀ 0)) (binLinear (Mᵀ 1)) p) := by
  ext k
  simp only [mulVec, dotProduct, symPow, of_apply, coeffVec, homEval, finsetSum_coeff,
    mul_assoc, coeff_C_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ (binLinear (Mᵀ 0) ^ (r - l) *
    binLinear (Mᵀ 1) ^ l).coeff k * p.coeff l)]
  exact sum_congr rfl fun _ _ ↦ mul_comm _ _

theorem binLinear_mulVec (M : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    binLinear (M *ᵥ x) = C (x 0) * binLinear (Mᵀ 0) + C (x 1) * binLinear (Mᵀ 1) := by
  simp only [binLinear, mulVec, dotProduct, Fin.sum_univ_two, transpose_apply, C_add, C_mul]
  ring

/-- **The symmetric power on products**: `S^r M (x₁ ⋯ x_r) = (M x₁) ⋯ (M x_r)`. -/
theorem symPow_mulVec_coeffVec_prod (r : ℕ) (M : Matrix (Fin 2) (Fin 2) R)
    (x : Fin r → Fin 2 → R) :
    symPow r M *ᵥ coeffVec r (∏ j, binLinear (x j)) =
      coeffVec r (∏ j, binLinear (M *ᵥ x j)) := by
  rw [symPow_mulVec_coeffVec, homEval_prod_binLinear]
  simp only [binLinear_mulVec]

theorem symPow_mulVec_single (r : ℕ) (M : Matrix (Fin 2) (Fin 2) R) (l : Fin (r + 1)) :
    symPow r M *ᵥ Pi.single l 1 = coeffVec r (∏ j : Fin r, binLinear (M *ᵥ unitPt l j)) := by
  have hl : (X ^ (l : ℕ) : R[X]) = ∏ j : Fin r, binLinear (unitPt l j) := by
    rw [prod_binLinear_unitPt, min_eq_left (by omega)]
  rw [← coeffVec_X_pow, hl, symPow_mulVec_coeffVec_prod]

/-- **Functoriality of the symmetric power.** -/
theorem symPow_mul (r : ℕ) (M N : Matrix (Fin 2) (Fin 2) R) :
    symPow r (M * N) = symPow r M * symPow r N := by
  refine ext_of_mulVec_single fun l ↦ ?_
  rw [← mulVec_mulVec, symPow_mulVec_single, symPow_mulVec_single, symPow_mulVec_coeffVec_prod]
  simp only [mulVec_mulVec]

@[simp] theorem symPow_one (r : ℕ) : symPow r (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  refine ext_of_mulVec_single fun l ↦ ?_
  rw [symPow_mulVec_single, one_mulVec]
  simp only [one_mulVec]
  rw [prod_binLinear_unitPt, show min (l : ℕ) r = l by omega, coeffVec_X_pow]

theorem symPow_map {S : Type*} [CommRing S] (f : R →+* S) (r : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (symPow r M).map f = symPow r (M.map f) := by
  ext k l
  simp only [map_apply, symPow, of_apply, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow,
    ← binLinear_map]
  rfl

theorem symPow_diagonal (r : ℕ) (D : Fin 2 → R) :
    symPow r (diagonal D) = diagonal fun l : Fin (r + 1) ↦ D 0 ^ (r - l) * D 1 ^ (l : ℕ) := by
  ext k l
  have h0 : binLinear ((diagonal D)ᵀ 0) = C (D 0) := by simp [binLinear]
  have h1 : binLinear ((diagonal D)ᵀ 1) = C (D 1) * X := by simp [binLinear]
  rw [symPow, of_apply, h0, h1, mul_pow, ← mul_assoc, ← C_pow, ← C_pow, ← C_mul,
    coeff_C_mul_X_pow, diagonal_apply]
  simp only [Fin.val_inj]
  split_ifs with h
  · subst h; rfl
  · rfl

/-- `∑_{l ≤ r} l = r (r + 1) / 2`. -/
private theorem sum_val_fin (r : ℕ) : ∑ l : Fin (r + 1), (l : ℕ) = r * (r + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ l), Finset.sum_range_id, Nat.add_sub_cancel,
    Nat.mul_comm]

private theorem sum_sub_val_fin (r : ℕ) : ∑ l : Fin (r + 1), (r - l) = r * (r + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ r - l), ← sum_val_fin,
    Fin.sum_univ_eq_sum_range (fun l ↦ l)]
  have := Finset.sum_range_reflect (fun l ↦ l) (r + 1)
  simpa using this

variable {𝕜 : Type*} [Field 𝕜]

private theorem det_symPow_transvection (r : ℕ) (t : TransvectionStruct (Fin 2) 𝕜) :
    (symPow r t.toMatrix).det = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · -- upper triangular: column `l` is `(c + X)^l`
    have h0 : binLinear ((transvection (0 : Fin 2) 1 c)ᵀ 0) = 1 := by
      simp [binLinear, transvection]
    have h1 : binLinear ((transvection (0 : Fin 2) 1 c)ᵀ 1) = X + C c := by
      simp [binLinear, transvection]; ring
    have hM : symPow r (transvection (0 : Fin 2) 1 c) = of fun k l : Fin (r + 1) ↦
        ((X + C c) ^ (l : ℕ)).coeff k := by
      ext k l
      rw [symPow, of_apply, of_apply, h0, h1, one_pow, one_mul]
    simp only [TransvectionStruct.toMatrix, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    rw [hM, det_of_isUpperTriangular]
    · refine prod_eq_one fun l _ ↦ ?_
      rw [of_apply]
      have hd : ((X + C c) ^ (l : ℕ)).natDegree = (l : ℕ) := by
        rw [natDegree_pow, natDegree_X_add_C, mul_one]
      have h := ((monic_X_add_C c).pow (l : ℕ)).coeff_natDegree
      rwa [hd] at h
    · intro k l hlk
      rw [of_apply]
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_pow, natDegree_X_add_C, mul_one]
      exact hlk
  · -- lower triangular: column `l` is `(1 + c X)^{r-l} X^l`
    have h0 : binLinear ((transvection (1 : Fin 2) 0 c)ᵀ 0) = 1 + C c * X := by
      simp [binLinear, transvection]
    have h1 : binLinear ((transvection (1 : Fin 2) 0 c)ᵀ 1) = X := by
      simp [binLinear, transvection]
    have hM : symPow r (transvection (1 : Fin 2) 0 c) = of fun k l : Fin (r + 1) ↦
        ((1 + C c * X) ^ (r - l) * X ^ (l : ℕ)).coeff k := by
      ext k l
      rw [symPow, of_apply, of_apply, h0, h1]
    simp only [TransvectionStruct.toMatrix, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    rw [hM, det_of_isLowerTriangular]
    · refine prod_eq_one fun l _ ↦ ?_
      rw [of_apply, coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
      simp
    · intro k l hkl
      have hkl' : (k : ℕ) < l := Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hkl)
      rw [of_apply, coeff_mul_X_pow']
      exact ite_eq_right (not_le.mpr hkl')
  · exact absurd rfl hij

/-- **The determinant of a symmetric power** (RT96 Lemma 4.5 for `m = 2`):
`det S^r M = (det M)^{r(r+1)/2}`. -/
theorem det_symPow (r : ℕ) (M : Matrix (Fin 2) (Fin 2) 𝕜) :
    (symPow r M).det = M.det ^ (r * (r + 1) / 2) := by
  refine diagonal_transvection_induction (fun M ↦ (symPow r M).det = M.det ^ (r * (r + 1) / 2))
    M (fun D _ ↦ ?_) (fun t ↦ ?_) fun A B hA hB ↦ ?_
  · rw [symPow_diagonal, det_diagonal, det_diagonal, prod_mul_distrib, prod_pow_eq_pow_sum,
      prod_pow_eq_pow_sum, sum_sub_val_fin, sum_val_fin, Fin.prod_univ_two, mul_pow]
  · rw [det_symPow_transvection, TransvectionStruct.det, one_pow]
  · rw [symPow_mul, det_mul, det_mul, hA, hB, mul_pow]

theorem det_symPow_ne_zero (r : ℕ) {M : Matrix (Fin 2) (Fin 2) 𝕜} (hM : M.det ≠ 0) :
    (symPow r M).det ≠ 0 := by
  rw [det_symPow]
  exact pow_ne_zero _ hM

end Matrix

namespace Polynomial

/-! ### Local estimates for products of linear forms -/

/-- The local factor of a polynomial of degree at most `r` only sees its first `r + 1`
coefficients. -/
theorem iSup_coeff_eq_iSup_coeffVec {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {r : ℕ}
    {p : K[X]} (hp : p.natDegree ≤ r) :
    (⨆ n : ℕ, v (p.coeff n)) = ⨆ k : Fin (r + 1), v (coeffVec r p k) := by
  refine le_antisymm (Real.iSup_le (fun n ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    (Real.iSup_le (fun k ↦ le_ciSup (Finsupp.bddAbove_range_apply p.coeff v) (k : ℕ))
      (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  rcases le_or_gt n r with h | h
  · exact Finite.le_ciSup_of_le (⟨n, Nat.lt_succ_of_le h⟩ : Fin (r + 1)) le_rfl
  · rw [p.coeff_eq_zero_of_natDegree_lt (hp.trans_lt h), map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _

theorem iSup_coeff_binLinear {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x : Fin 2 → K) :
    (⨆ n : ℕ, v ((binLinear x).coeff n)) = ⨆ i, v (x i) := by
  rw [iSup_coeff_eq_iSup_coeffVec v (natDegree_binLinear_le x)]
  refine iSup_congr fun i ↦ ?_
  fin_cases i <;> simp [coeffVec, binLinear]

/-- **Gauss's lemma for a product of linear forms.** -/
theorem iSup_coeff_prod_binLinear {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {r : ℕ} (x : Fin r → Fin 2 → K) :
    (⨆ n : ℕ, v ((∏ j, binLinear (x j)).coeff n)) = ∏ j, ⨆ i, v (x j i) := by
  induction r with
  | zero =>
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero,
      iSup_coeff_eq_iSup_coeffVec v (natDegree_one.le : _ ≤ 0)]
    simp [coeffVec]
  | succ r ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, iSup_coeff_mul hv, ih,
      iSup_coeff_binLinear]

theorem mahlerMeasure_binLinear (z : Fin 2 → ℂ) :
    (binLinear z).mahlerMeasure = max ‖z 0‖ ‖z 1‖ := by
  rcases eq_or_ne (z 1) 0 with h | h
  · simp [binLinear, h, mahlerMeasure_const]
  · rw [binLinear, add_comm, mahlerMeasure_C_mul_X_add_C h, max_comm]

theorem norm_le_sqrt_two_mul_mahlerMeasure (z : Fin 2 → ℂ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 2))‖ ≤ √2 * (binLinear z).mahlerMeasure := by
  rw [mahlerMeasure_binLinear, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    ← Real.sqrt_sq (le_max_of_le_left (norm_nonneg _) : 0 ≤ max ‖z 0‖ ‖z 1‖),
    ← Real.sqrt_mul zero_le_two]
  refine Real.sqrt_le_sqrt ?_
  have h0 : ‖z 0‖ ^ 2 ≤ max ‖z 0‖ ‖z 1‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
  have h1 : ‖z 1‖ ^ 2 ≤ max ‖z 0‖ ‖z 1‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
  linarith

/-- Landau's inequality, read on the first `r + 1` coefficients. -/
theorem mahlerMeasure_le_norm_coeffVec {r : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ r) :
    p.mahlerMeasure ≤ ‖(WithLp.toLp 2 (coeffVec r p) : EuclideanSpace ℂ (Fin (r + 1)))‖ := by
  refine (mahlerMeasure_le_sqrt_sum_sq_norm_coeff p).trans ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [coeffVec]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ ‖p.coeff k‖ ^ 2)]
  exact sum_le_sum_of_subset_of_nonneg (supp_subset_range (Nat.lt_succ_of_le hp))
    fun _ _ _ ↦ sq_nonneg _

theorem mahlerMeasure_prod {r : ℕ} (f : Fin r → ℂ[X]) :
    (∏ j, f j).mahlerMeasure = ∏ j, (f j).mahlerMeasure := by
  induction r with
  | zero => simp
  | succ r ih => rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mahlerMeasure_mul, ih]

/-- **Lemma 4.8 at a complex place**: `∏ ‖z_j‖ ≤ √2^r ‖z₁ ⋯ z_r‖`, the product read on the
coefficients of the product of the linear forms. -/
theorem prod_norm_le_sqrt_two_pow_mul {r : ℕ} (z : Fin r → Fin 2 → ℂ) :
    ∏ j, ‖(WithLp.toLp 2 (z j) : EuclideanSpace ℂ (Fin 2))‖ ≤
      √2 ^ r * ‖(WithLp.toLp 2 (coeffVec r (∏ j, binLinear (z j))) :
        EuclideanSpace ℂ (Fin (r + 1)))‖ := by
  calc ∏ j, ‖(WithLp.toLp 2 (z j) : EuclideanSpace ℂ (Fin 2))‖
      ≤ ∏ j, (√2 * (binLinear (z j)).mahlerMeasure) :=
        prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun j _ ↦ norm_le_sqrt_two_mul_mahlerMeasure (z j)
    _ = √2 ^ r * (∏ j, binLinear (z j)).mahlerMeasure := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, mahlerMeasure_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (mahlerMeasure_le_norm_coeffVec (natDegree_prod_binLinear_le z)) (by positivity)

end Polynomial

namespace NumberField.Twist

open Module IntermediateField Matrix

variable {K : Type*} [Field K] [NumberField K] (A : Twist K (Fin 2)) (r : ℕ)

/-- **The `r`-th symmetric power of a twist of the plane** (RT96 §1): `S^r A_v` at every place,
a twist of the space `S^r(K²) ≅ K^{r+1}` of binary forms of degree `r`. -/
noncomputable def symPow : Twist K (Fin (r + 1)) where
  arch φ := (A.arch φ).symPow r
  arch_det_ne_zero φ := det_symPow_ne_zero r (A.arch_det_ne_zero φ)
  arch_conjugate φ := by rw [A.arch_conjugate, symPow_map]
  fin v := (A.fin v).symPow r
  fin_det_ne_zero v := det_symPow_ne_zero r (A.fin_det_ne_zero v)
  finite_setOf_fin_ne_one := A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by
    simp only [h, symPow_one])

@[simp] theorem symPow_arch (φ : K →+* ℂ) : (A.symPow r).arch φ = (A.arch φ).symPow r := rfl

@[simp] theorem symPow_fin (v : FinitePlace K) : (A.symPow r).fin v = (A.fin v).symPow r := rfl

/-- **`|det S^r A|_𝔸 = |det A|_𝔸 ^ {r(r+1)/2}`** (RT96 Lemma 4.5). -/
theorem absDet_symPow : (A.symPow r).absDet = A.absDet ^ (r * (r + 1) / 2) := by
  have hf : (fun v : FinitePlace K ↦ v (A.fin v).det).HasFiniteMulSupport :=
    A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])
  have h0 : 0 ≤ (∏ φ : K →+* ℂ, ‖(A.arch φ).det‖) * ∏ᶠ v : FinitePlace K, v (A.fin v).det :=
    mul_nonneg (prod_nonneg fun _ _ ↦ norm_nonneg _) (finprod_nonneg fun v ↦ apply_nonneg _ _)
  simp only [absDet, symPow_arch, symPow_fin, det_symPow, norm_pow, map_pow]
  rw [prod_pow, ← finprod_pow hf, ← mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul h0, ← Real.rpow_mul h0, mul_comm ((r * (r + 1) / 2 : ℕ) : ℝ)]

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
/-- **Lemma 4.8 at a complex embedding.** -/
theorem prod_archFactor_le (φ : E →+* ℂ) {r : ℕ} (y : Fin r → Fin 2 → E) :
    ∏ j, A.archFactor φ (y j) ≤
      √2 ^ r * (A.symPow r).archFactor φ (coeffVec r (∏ j, binLinear (y j))) := by
  set M := A.arch (φ.comp (algebraMap K E))
  have hφ : φ ∘ coeffVec r (∏ j, binLinear (y j)) =
      coeffVec r (∏ j, binLinear (φ ∘ y j)) := by
    rw [← coeffVec_map, Polynomial.map_prod]
    simp only [binLinear_map]
  have h : (A.symPow r).archFactor φ (coeffVec r (∏ j, binLinear (y j))) =
      ‖(WithLp.toLp 2 (coeffVec r (∏ j, binLinear (M *ᵥ (φ ∘ y j)))) :
        EuclideanSpace ℂ (Fin (r + 1)))‖ := by
    rw [archFactor, symPow_arch, hφ, symPow_mulVec_coeffVec_prod]
  rw [h]
  exact prod_norm_le_sqrt_two_pow_mul fun j ↦ M *ᵥ (φ ∘ y j)

/-- **Lemma 4.8 at a finite place**, with equality: Gauss's lemma. -/
theorem finFactor_symPow (w : FinitePlace E) {r : ℕ} (y : Fin r → Fin 2 → E) :
    (A.symPow r).finFactor w (coeffVec r (∏ j, binLinear (y j))) =
      ∏ j, A.finFactor w (y j) := by
  set N := (A.fin (w.under K)).map (algebraMap K E)
  have hw : IsNonarchimedean w.1 := fun a b ↦ FinitePlace.add_le w a b
  rw [finFactor, symPow_fin, symPow_map, symPow_mulVec_coeffVec_prod]
  have h := iSup_coeff_prod_binLinear hw (fun j ↦ N *ᵥ y j)
  rw [iSup_coeff_eq_iSup_coeffVec _ (natDegree_prod_binLinear_le _)] at h
  exact h

/-- **RT96 Lemma 4.8, relative to a number field**: for nonzero `y₁, …, y_r`,
`∏ H_A(y_j) ≤ (√2^r)^{[E:ℚ]} · H_{S^r A}(y₁ ⋯ y_r)`. -/
theorem prod_mulHeight_le {r : ℕ} {y : Fin r → Fin 2 → E} (hy : ∀ j, y j ≠ 0) :
    ∏ j, A.mulHeight (y j) ≤ (√2 ^ r) ^ finrank ℚ E *
      (A.symPow r).mulHeight (coeffVec r (∏ j, binLinear (y j))) := by
  have hfin := fun j ↦ A.hasFiniteMulSupport_finFactor (hy j)
  simp only [mulHeight]
  rw [prod_mul_distrib, prod_comm, prod_finprod_comm _ _ fun j _ ↦ hfin j]
  simp_rw [← A.finFactor_symPow]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (finprod_nonneg fun w ↦ finFactor_nonneg _ w _)
  calc ∏ φ : E →+* ℂ, ∏ j, A.archFactor φ (y j)
      ≤ ∏ φ : E →+* ℂ, (√2 ^ r *
          (A.symPow r).archFactor φ (coeffVec r (∏ j, binLinear (y j)))) :=
        prod_le_prod₀ (fun φ _ ↦ prod_nonneg fun j _ ↦ A.archFactor_nonneg φ _)
          fun φ _ ↦ A.prod_archFactor_le φ y
    _ = _ := by
        rw [prod_mul_distrib, prod_const, card_univ, NumberField.Embeddings.card]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **RT96 Lemma 4.8** (the half used by Prop. 5.3): for nonzero `x₁, …, x_r ∈ Ω²`,
`∏ H_A(x_j) ≤ √2^r · H_{S^r A}(x₁ ⋯ x_r)`, the product read as the binary form
`∏ (x_{j0} X + x_{j1} Y)`. -/
theorem prod_absMulHeight_le {r : ℕ} {x : Fin r → Fin 2 → Ω} (hx : ∀ j, x j ≠ 0) :
    ∏ j, A.absMulHeight (x j) ≤
      √2 ^ r * (A.symPow r).absMulHeight (coeffVec r (∏ j, binLinear (x j))) := by
  have := numberField_adjoin_range (K := K) (fun p : Fin r × Fin 2 ↦ x p.1 p.2)
  set L := adjoin K (Set.range fun p : Fin r × Fin 2 ↦ x p.1 p.2)
  set y : Fin r → Fin 2 → L := fun j i ↦ ⟨x j i, subset_adjoin K _ ⟨(j, i), rfl⟩⟩
  have hxy : ∀ j, x j = L.val ∘ y j := fun j ↦ rfl
  have hy : ∀ j, y j ≠ 0 := fun j h ↦ hx j (by rw [hxy j, h]; ext; simp)
  have hP : coeffVec r (∏ j, binLinear (x j)) =
      L.val ∘ coeffVec r (∏ j, binLinear (y j)) := by
    rw [show (L.val : L → Ω) = (L.val : L →+* Ω) from rfl, ← coeffVec_map, Polynomial.map_prod]
    simp only [← binLinear_map]
    rfl
  rw [hP, absMulHeight_algHom]
  simp_rw [hxy, absMulHeight_algHom]
  rw [Real.finsetProd_rpow _ _ fun j _ ↦ A.mulHeight_nonneg _]
  calc (∏ j, A.mulHeight (y j)) ^ ((finrank ℚ L : ℝ))⁻¹
      ≤ ((√2 ^ r) ^ finrank ℚ L *
          (A.symPow r).mulHeight (coeffVec r (∏ j, binLinear (y j)))) ^
          ((finrank ℚ L : ℝ))⁻¹ :=
        Real.rpow_le_rpow (prod_nonneg fun j _ ↦ A.mulHeight_nonneg _)
          (A.prod_mulHeight_le hy) (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (mulHeight_nonneg _ _),
          Real.pow_rpow_inv_natCast (by positivity) Module.finrank_pos.ne']

end NumberField.Twist
