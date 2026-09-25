/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- Used only inside proofs.
import ArithmeticHeights.Hadamard
import ArithmeticHeights.Plucker
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Partitioning `ℂⁿ` into classes of small determinant

**Layer 9.3 (infrastructure).** Evertse, "On the Quantitative Subspace Theorem", Lemma 4.3: for
`n ≥ 2` and `M ≥ 1`, `ℂⁿ` can be partitioned into at most `(20 n) ^ n M²` classes such that any
`n` vectors of one class satisfy `|det (y 1, …, y n)| ≤ M⁻¹ ‖y 1‖ ⋯ ‖y n‖`, the norm being the
sup norm (`Matrix.exists_det_partition`). This is the analytic heart of the second gap principle.

Write a nonzero `y` as `λ z` with `|λ| = ‖y‖` and `z` having a coordinate `1` at an index where
`|y|` is largest (`Matrix.detPivot`). The class of `y` is that index together with the cells of
the real and imaginary parts of the other `n - 1` coordinates of `z` in a partition of `[-1, 1]`
into `A` intervals (`Matrix.cellIndex`). Two vectors of a class then have normalized forms within
`1 / K` of each other, and after subtracting the first row from the others Hadamard's inequality
(`Matrix.norm_det_le_card_rpow_mul_prod_norm`) bounds the determinant by
`n ^ (n / 2) K ^ (1 - n)`.

## Main results

* `Matrix.norm_det_le_card_rpow_mul_prod_norm`: **Hadamard's inequality in the sup norm**,
  `|det A| ≤ n ^ (n / 2) ∏ ‖A i‖`, from the complex Hadamard inequality of `ArithmeticHeights`.
* `Matrix.abs_sub_le_of_cellIndex_eq`: two points of `[-1, 1]` in the same cell are within `2 / A`.
* `Matrix.exists_det_partition`: **Evertse's Lemma 4.3**.

## Implementation notes

⚠ **A cell of the pivot coordinate is not recorded.** Recording all `n` coordinates would cost a
factor `A²`, about `9 K²`, which the bound `(20 n) ^ n M²` cannot absorb; the class type is the
sigma type `Σ i, ({j // j ≠ i} → Fin A × Fin A)`, of cardinality `n A ^ (2 (n - 1))`.

⚠ **The grid is `A = ⌈3 K⌉`, not Evertse's `⌊2 √2 K⌋ + 1`.** Two complex numbers whose real and
imaginary parts agree to `2 / A` are within `2 √2 / A < 1 / K`, and `A ≤ 4 K` then gives the count
`n · 16 ^ (n - 1) · n ^ n M²`, below `(20 n) ^ n M²` because `n · 16 ^ (n - 1) ≤ 20 ^ n`.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240; J. Math. Sci. **171** (2010), 824–837 (arXiv:1008.2268), Lemma 4.3.

This is Layer 9.3 (infrastructure) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

universe u

namespace Matrix

open exteriorPower

variable {ι : Type u} [Fintype ι]

/-- **Hadamard's inequality in the sup norm**: a complex determinant is at most `n ^ (n / 2)`
times the product of the sup norms of its rows. -/
theorem norm_det_le_card_rpow_mul_prod_norm [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖A.det‖ ≤ (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * ∏ i, ‖A i‖ := by
  set n := Fintype.card ι with hn
  set e := Fintype.equivFin ι
  set B : Matrix (Fin n) (Fin n) ℂ := A.submatrix e.symm e.symm with hBdef
  have hB : B.det = A.det := det_submatrix_equiv_self e.symm A
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  set s₀ : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  have h1 : ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖B i j‖ ^ 2 := by
    refine le_trans ?_ (sum_sq_norm_plucker_row_le_prod B)
    have hp := plucker_fin_eq_det B.row s₀
    change _ = B.det at hp
    rw [← hB, ← hp]
    exact Finset.single_le_sum (f := fun s ↦ ‖plucker n B.row s‖ ^ 2)
      (fun _ _ ↦ by positivity) (Finset.mem_univ s₀)
  have h2 : ∏ i, ∑ j, ‖B i j‖ ^ 2 ≤ ∏ i, ((n : ℝ) * ‖A (e.symm i)‖ ^ 2) := by
    refine Finset.prod_le_prod₀ (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity)
      fun i _ ↦ ?_
    calc ∑ j, ‖B i j‖ ^ 2 ≤ ∑ _j : Fin n, ‖A (e.symm i)‖ ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _)
            (norm_le_pi_norm (A (e.symm i)) (e.symm j)) 2
      _ = n * ‖A (e.symm i)‖ ^ 2 := by simp
  have h3 : ∏ i, ((n : ℝ) * ‖A (e.symm i)‖ ^ 2) =
      ((n : ℝ) ^ ((n : ℝ) / 2) * ∏ i, ‖A i‖) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow, Equiv.prod_comp e.symm (fun i ↦ ‖A i‖), mul_pow, ← Real.rpow_natCast
      ((n : ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul hn0,
      show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    (h1.trans (h2.trans h3.le))

/-- **The cell of `t` in the partition of `[-1, 1]` into `A` intervals of length `2 / A`**: the
integer part of `(t + 1) A / 2`, with the right end point put into the last cell. -/
noncomputable def cellIndex (A : ℕ) (t : ℝ) : ℕ := min ⌊(t + 1) * A / 2⌋₊ (A - 1)

theorem cellIndex_lt {A : ℕ} (hA : 0 < A) (t : ℝ) : cellIndex A t < A :=
  lt_of_le_of_lt (min_le_right _ _) (by omega)

private theorem cellIndex_le_and_le {A : ℕ} (hA : 0 < A) {u : ℝ} (hu : |u| ≤ 1) :
    (cellIndex A u : ℝ) ≤ (u + 1) * A / 2 ∧ (u + 1) * A / 2 ≤ cellIndex A u + 1 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hu
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hnn : 0 ≤ (u + 1) * A / 2 := div_nonneg (mul_nonneg (by linarith) hA'.le) zero_le_two
  have hle : (u + 1) * A / 2 ≤ A := by nlinarith
  constructor
  · exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hnn)
  · rcases le_total ⌊(u + 1) * A / 2⌋₊ (A - 1) with hm | hm
    · rw [cellIndex, min_eq_left hm]; exact (Nat.lt_floor_add_one _).le
    · rw [cellIndex, min_eq_right hm, Nat.cast_sub (by omega : 1 ≤ A)]; push_cast; linarith

/-- **Two points of `[-1, 1]` in the same cell are within `2 / A` of each other.** -/
theorem abs_sub_le_of_cellIndex_eq {A : ℕ} (hA : 0 < A) {t t' : ℝ} (ht : |t| ≤ 1)
    (ht' : |t'| ≤ 1) (h : cellIndex A t = cellIndex A t') : |t - t'| ≤ 2 / A := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨a1, a2⟩ := cellIndex_le_and_le hA ht
  obtain ⟨b1, b2⟩ := cellIndex_le_and_le hA ht'
  rw [h] at a1 a2
  have : |(t - t') * (A / 2)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (div_pos hA' two_pos)] at this
  rw [le_div_iff₀ hA']
  linarith

omit [Fintype ι] in
private theorem sigma_mk_eq {γ : Type*} {a b : ι} {f : {j // j ≠ a} → γ}
    {g : {j // j ≠ b} → γ} (h : (⟨a, f⟩ : Σ i : ι, ({j // j ≠ i} → γ)) = ⟨b, g⟩) :
    a = b ∧ ∀ l (ha : l ≠ a) (hb : l ≠ b), f ⟨l, ha⟩ = g ⟨l, hb⟩ := by
  obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 h
  exact ⟨rfl, fun l ha hb ↦ by rw [eq_of_heq h']⟩

variable [Nonempty ι]

/-- **The pivot of a vector**: an index at which its coordinates are largest. -/
noncomputable def detPivot (y : ι → ℂ) : ι :=
  (Finset.univ.exists_max_image (fun j ↦ ‖y j‖) Finset.univ_nonempty).choose

theorem norm_le_norm_detPivot (y : ι → ℂ) (j : ι) : ‖y j‖ ≤ ‖y (detPivot y)‖ :=
  (Finset.univ.exists_max_image (fun j ↦ ‖y j‖) Finset.univ_nonempty).choose_spec.2 j
    (Finset.mem_univ j)

theorem norm_detPivot (y : ι → ℂ) : ‖y (detPivot y)‖ = ‖y‖ :=
  le_antisymm (norm_le_pi_norm y _)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (norm_le_norm_detPivot y))

/-- **The class of a vector** in Lemma 4.3: its pivot, and the cells of the real and imaginary
parts of the other coordinates of the vector divided by its pivot coordinate. -/
noncomputable def detCell (A : ℕ) (hA : 0 < A) (y : ι → ℂ) :
    Σ i : ι, ({j // j ≠ i} → Fin A × Fin A) :=
  ⟨detPivot y, fun j ↦ (⟨cellIndex A ((y (detPivot y))⁻¹ * y j).re, cellIndex_lt hA _⟩,
    ⟨cellIndex A ((y (detPivot y))⁻¹ * y j).im, cellIndex_lt hA _⟩)⟩

private theorem detCell_eq {A : ℕ} {hA : 0 < A} {y y' : ι → ℂ}
    (h : detCell A hA y = detCell A hA y') :
    detPivot y = detPivot y' ∧ ∀ l, l ≠ detPivot y →
      cellIndex A ((y (detPivot y))⁻¹ * y l).re = cellIndex A ((y' (detPivot y'))⁻¹ * y' l).re ∧
      cellIndex A ((y (detPivot y))⁻¹ * y l).im = cellIndex A ((y' (detPivot y'))⁻¹ * y' l).im := by
  unfold detCell at h
  obtain ⟨hab, hfg⟩ := sigma_mk_eq h
  refine ⟨hab, fun l hl ↦ ?_⟩
  have := hfg l hl (hab ▸ hl)
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact this

private theorem nat_mul_sixteen_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * 16 ^ (n - 1) ≤ 20 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have hb := one_add_mul_le_pow (a := (1 / 4 : ℝ)) (by norm_num) m
  have h20 : (20 : ℝ) ^ m = 16 ^ m * (1 + 1 / 4) ^ m := by rw [← mul_pow]; norm_num
  have h16 : (0 : ℝ) ≤ 16 ^ m := by positivity
  push_cast
  rw [h20]
  nlinarith

/-- **Evertse's Lemma 4.3.** For `n ≥ 2` and `M ≥ 1` there is a map of `ℂⁿ` to a set of at most
`(20 n) ^ n M²` classes such that any `n` vectors of one class satisfy
`|det (y 1, …, y n)| ≤ M⁻¹ ‖y 1‖ ⋯ ‖y n‖`, in the sup norm. -/
theorem exists_det_partition [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {M : ℝ} (hM : 1 ≤ M) :
    ∃ (α : Type u) (_ : Fintype α) (f : (ι → ℂ) → α),
      (Fintype.card α : ℝ) ≤ (20 * Fintype.card ι) ^ Fintype.card ι * M ^ 2 ∧
      ∀ y : ι → ι → ℂ, (∀ j k, f (y j) = f (y k)) →
        ‖(Matrix.of y).det‖ ≤ M⁻¹ * ∏ j, ‖y j‖ := by
  set n := Fintype.card ι with hndef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set X : ℝ := M * (n : ℝ) ^ ((n : ℝ) / 2) with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM (Real.one_le_rpow hn1 (by positivity))
  have hm0 : n - 1 ≠ 0 := by omega
  set K : ℝ := X ^ (((n - 1 : ℕ) : ℝ)⁻¹) with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow hX1 (by positivity)
  have hK0 : 0 < K := by linarith
  have hKpow : K ^ (n - 1) = X := Real.rpow_inv_natCast_pow (by linarith) hm0
  set A : ℕ := ⌈3 * K⌉₊ with hAdef
  have hA3 : 3 * K ≤ A := Nat.le_ceil _
  have hA4 : (A : ℝ) ≤ 4 * K := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * K by linarith); rw [← hAdef] at this; linarith
  have hA : 0 < A := by exact_mod_cast (show (0 : ℝ) < A by linarith)
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  refine ⟨Σ i : ι, ({j // j ≠ i} → Fin A × Fin A), inferInstance, detCell A hA, ?_, ?_⟩
  · -- The number of classes.
    have hcard : ∀ i : ι, Fintype.card {j // j ≠ i} = n - 1 := fun i ↦ by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have hc : Fintype.card (Σ i : ι, ({j // j ≠ i} → Fin A × Fin A)) = n * (A * A) ^ (n - 1) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hcard]
      simp [← hndef]
    rw [hc]
    push_cast
    calc (n : ℝ) * (A * A) ^ (n - 1) ≤ n * ((4 * K) * (4 * K)) ^ (n - 1) := by
          gcongr
      _ = (n * 16 ^ (n - 1)) * (K ^ (n - 1)) ^ 2 := by ring
      _ = (n * 16 ^ (n - 1)) * (n ^ n * M ^ 2) := by
          rw [hKpow, hX, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((n : ℝ) / 2)) 2,
            ← Real.rpow_mul hn0.le,
            show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
          ring
      _ ≤ 20 ^ n * (n ^ n * M ^ 2) :=
          mul_le_mul_of_nonneg_right (nat_mul_sixteen_pow_le n (by omega)) (by positivity)
      _ = (20 * n) ^ n * M ^ 2 := by ring
  · intro y hy
    by_cases h0 : ∃ j, y j = 0
    · obtain ⟨j, hj⟩ := h0
      rw [Matrix.det_eq_zero_of_row_eq_zero j fun k ↦ by simp [hj], norm_zero]
      exact mul_nonneg (inv_nonneg.2 (by linarith)) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    push Not at h0
    obtain ⟨j₀⟩ := ‹Nonempty ι›
    set lam : ι → ℂ := fun j ↦ y j (detPivot (y j)) with hlam
    have hlam0 : ∀ j, lam j ≠ 0 := fun j h ↦ h0 j (by
      rw [← norm_eq_zero, ← norm_detPivot]; exact norm_eq_zero.2 h)
    have hlamn : ∀ j, ‖lam j‖ = ‖y j‖ := fun j ↦ norm_detPivot (y j)
    set z : ι → ι → ℂ := fun j l ↦ (lam j)⁻¹ * y j l with hz
    have hyz : Matrix.of y = Matrix.diagonal lam * Matrix.of z := by
      ext j l
      simp [hz, Matrix.diagonal_mul, mul_inv_cancel_left₀ (hlam0 j)]
    -- All the vectors have the same pivot.
    set i₀ := detPivot (y j₀) with hi₀
    have hpiv : ∀ j, detPivot (y j) = i₀ := fun j ↦ (detCell_eq (hy j j₀)).1
    have hz1 : ∀ j l, ‖z j l‖ ≤ 1 := fun j l ↦ by
      rw [hz, norm_mul, norm_inv, hlamn, inv_mul_le_iff₀ (norm_pos_iff.2 (fun h ↦ h0 j h))]
      simpa using norm_le_pi_norm (y j) l
    have hzpiv : ∀ j, z j i₀ = 1 := fun j ↦ by
      rw [hz]; simp only; rw [← hpiv j]; exact inv_mul_cancel₀ (hlam0 j)
    have hzl : ∀ j l, z j l = (y j i₀)⁻¹ * y j l := fun j l ↦ by simp only [hz, hlam, hpiv]
    -- The normalized vectors are close.
    have hclose : ∀ j, ‖z j - z j₀‖ ≤ K⁻¹ := fun j ↦ by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l ↦ ?_
      rcases eq_or_ne l i₀ with rfl | hl
      · simp [hzpiv, hK0.le]
      obtain ⟨hre, him⟩ := (detCell_eq (hy j j₀)).2 l (by rw [hpiv]; exact hl)
      simp only [hpiv] at hre him
      rw [← hzl j l, ← hzl j₀ l] at hre him
      have hre' := abs_sub_le_of_cellIndex_eq hA (le_trans (Complex.abs_re_le_norm _) (hz1 j l))
        (le_trans (Complex.abs_re_le_norm _) (hz1 j₀ l)) hre
      have him' := abs_sub_le_of_cellIndex_eq hA (le_trans (Complex.abs_im_le_norm _) (hz1 j l))
        (le_trans (Complex.abs_im_le_norm _) (hz1 j₀ l)) him
      change ‖z j l - z j₀ l‖ ≤ K⁻¹
      have hsq : ‖z j l - z j₀ l‖ ^ 2 ≤ (K⁻¹) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
        have h1 : (z j l).re - (z j₀ l).re ≤ 2 / A ∧ -(2 / A) ≤ (z j l).re - (z j₀ l).re :=
          ⟨(abs_le.1 hre').2, (abs_le.1 hre').1⟩
        have h2 : (z j l).im - (z j₀ l).im ≤ 2 / A ∧ -(2 / A) ≤ (z j l).im - (z j₀ l).im :=
          ⟨(abs_le.1 him').2, (abs_le.1 him').1⟩
        have hAK : 2 / (A : ℝ) ≤ 2 / (3 * K) := div_le_div_of_nonneg_left zero_le_two
          (by positivity) hA3
        have hb : ∀ t : ℝ, t ≤ 2 / A → -(2 / A) ≤ t → t * t ≤ (2 / (3 * K)) ^ 2 := fun t h h' ↦ by
          have : |t| ≤ 2 / (3 * K) := (abs_le.2 ⟨by linarith, h⟩).trans hAK
          nlinarith [abs_mul_abs_self t, abs_nonneg t]
        have e1 := hb _ h1.1 h1.2
        have e2 := hb _ h2.1 h2.2
        have : (2 / (3 * K)) ^ 2 + (2 / (3 * K)) ^ 2 ≤ (K⁻¹) ^ 2 := by
          rw [div_pow, mul_pow, inv_pow]
          field_simp
          norm_num
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    -- Subtract the row `j₀` from the others.
    set z' : ι → ι → ℂ := fun j ↦ if j = j₀ then z j₀ else z j - z j₀ with hz'
    have hdet : (Matrix.of z).det = (Matrix.of z').det := by
      refine (det_eq_of_forall_row_eq_smul_add_const (fun j ↦ if j = j₀ then 0 else -1) j₀
        (by simp) fun j l ↦ ?_).symm
      by_cases hj : j = j₀ <;> simp [hz', hj, sub_eq_add_neg]
    have hz'1 : ‖z' j₀‖ ≤ 1 := by
      simp only [hz', ↓reduceIte]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (hz1 j₀)
    have hprod : ∏ j, ‖z' j‖ ≤ K⁻¹ ^ (n - 1) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
      calc ‖z' j₀‖ * ∏ j ∈ Finset.univ.erase j₀, ‖z' j‖
          ≤ 1 * ∏ _j ∈ Finset.univ.erase j₀, K⁻¹ := by
            refine mul_le_mul hz'1 (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j hj ↦ ?_)
              (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) zero_le_one
            simp only [hz', Finset.ne_of_mem_erase hj, ↓reduceIte]
            exact hclose j
        _ = K⁻¹ ^ (n - 1) := by
            rw [one_mul, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ]
    have hzdet : ‖(Matrix.of z).det‖ ≤ M⁻¹ := by
      rw [hdet]
      calc ‖(Matrix.of z').det‖ ≤ (n : ℝ) ^ ((n : ℝ) / 2) * ∏ j, ‖z' j‖ :=
            norm_det_le_card_rpow_mul_prod_norm _
        _ ≤ (n : ℝ) ^ ((n : ℝ) / 2) * K⁻¹ ^ (n - 1) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = M⁻¹ := by
            have : (n : ℝ) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
            rw [inv_pow, hKpow, hX]
            field_simp
    rw [hyz, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_prod, mul_comm]
    simp only [hlamn]
    exact mul_le_mul_of_nonneg_right hzdet (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

end Matrix
