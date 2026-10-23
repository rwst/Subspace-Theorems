/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.ThreeVariable
public import DiophantineApproximation.LiouvilleInequality

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The plane step (Bugeaud–Evertse 2008, §7, (7.12)–(7.19))

BE.2 (`Real.exists_planes_of_approx`) puts the points `x_n = (b^{t_n}, b^{r_n}, p_n)` into few
planes. This file bounds the number of `x_n` on one plane `U`.

Let `i₁ < i₂` be the two smallest indices with `x_n ∈ U`. Since the `x_n` are pairwise not
proportional (`b ∤ p_n` when `r_n ≥ 1`, and `t_n` increases), `z = x_{i₁} × x_{i₂}` is a nonzero
integer vector with `max |zᵢ| ≤ 2 b^{2 t_{i₂}}`, and every point of `U` satisfies
`z₁ X₁ + z₂ X₂ + z₃ X₃ = 0` ((7.12)). Eliminating `b^r` resp. `p` from the approximation turns it
into a two-variable inequality

* `|ξ(z₁ + z₂) b^t + (ξ z₃ - z₂) p| ≤ |z₂| (b^t)^{-ε}` ((7.13)), and
* `|(ξ z₃ + z₁) b^t + (z₂ - ξ z₃) b^r| ≤ |z₃| (b^t)^{-ε}`,

to which BE.0 applies at `n = 2` (`Real.exists_lines_of_approx`). The determinant `ξ z₃ - z₂` is
bounded below by Liouville's inequality (`Real.exists_inv_le_abs_add_mul`), so the threshold is
`O(ε⁻¹ (1 + log max |zᵢ|)) = O(ε⁻¹ t_{i₂})`. Since `t_n` at least doubles with `n`, only
`O(1 + log ε⁻¹)` of the points lie below it ((7.14)–(7.15)); the others lie on
`K ε⁻³ (1 + log ε⁻¹)²` lines, at most one point per line (`Real.card_mem_plane_le`). BE08 use
Corollary 5.2 here, whose threshold `(3 d t_{i₂})^{2/ε}` costs nothing either, and get
`(ε⁻¹)^{3+η}`.

## Main results

* `Submodule.det_eq_zero_of_forall_mem`: `n` vectors of a proper subspace of `ℚⁿ` have
  determinant `0`.
* `Real.exists_inv_le_abs_add_mul`: Liouville's inequality `|c₀ + c₁ ξ| ≥ (A Z^d)⁻¹`.
* `Real.exists_lines_of_approx`: the two-variable step.
* `Real.exists_plane_eq`: the plane through two points, `z = x₁ × x₂` ((7.12)).
* `Real.card_mem_plane_le`: **the plane step**.

`Additions/PlaneLiouville.lean` replaces the two-variable count by Liouville's inequality for the
planes with `z₃ ≠ 0` (`Real.card_mem_plane_le_log`).

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Finset

/-- **`n` vectors of a proper subspace of `ℚⁿ` have determinant `0`.** -/
theorem Submodule.det_eq_zero_of_forall_mem {n : ℕ} {U : Submodule ℚ (Fin n → ℚ)} (hU : U ≠ ⊤)
    (v : Fin n → Fin n → ℚ) (hv : ∀ i, v i ∈ U) : (Matrix.of v).det = 0 := by
  by_contra h
  have hspan := (Matrix.linearIndependent_rows_of_det_ne_zero h).span_eq_top_of_card_eq_finrank'
    (by simp)
  refine hU (eq_top_iff.mpr (hspan.symm.le.trans (Submodule.span_le.mpr ?_)))
  rintro _ ⟨i, rfl⟩
  exact hv i

namespace Real

variable {b : ℕ}

/-- **Liouville's inequality for `c₀ + c₁ ξ`**: for `ξ` real algebraic irrational of degree `d`
there is `A ≥ 1` with `|c₀ + c₁ ξ| ≥ (A Z^d)⁻¹` for integers `(c₀, c₁) ≠ 0` with `|cᵢ| ≤ Z`. -/
theorem exists_inv_le_abs_add_mul {ξ : ℝ} (hirr : Irrational ξ) (halg : IsAlgebraic ℚ ξ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (c₀ c₁ : ℤ) (Z : ℝ), |(c₀ : ℝ)| ≤ Z → |(c₁ : ℝ)| ≤ Z →
      (c₀ ≠ 0 ∨ c₁ ≠ 0) → (A * Z ^ (minpoly ℚ ξ).natDegree)⁻¹ ≤ |c₀ + c₁ * ξ| := by
  obtain ⟨A, hA, h⟩ := exists_pos_one_le_pow_natDegree_mul_abs_sub_div hirr halg
  set d := (minpoly ℚ ξ).natDegree
  refine ⟨max A 1, le_max_right _ _, fun c₀ c₁ Z h₀ h₁ hc ↦ ?_⟩
  by_cases hc₁ : c₁ = 0
  · have hc₀ : c₀ ≠ 0 := by tauto
    have h1 : (1 : ℝ) ≤ |(c₀ : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc₀
    have hZ : 1 ≤ Z := h1.trans h₀
    have : 1 ≤ max A 1 * Z ^ d := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ hZ)
    simp only [hc₁, Int.cast_zero, zero_mul, add_zero]
    exact (inv_le_one_of_one_le₀ this).trans h1
  -- `m = |c₁| ≥ 1`, and `c₀ + c₁ ξ = ± m (ξ - a / m)`
  set m : ℕ := c₁.natAbs with hm
  have hm1 : 1 ≤ m := Int.natAbs_pos.mpr hc₁
  have hmR : (m : ℝ) = |(c₁ : ℝ)| := by rw [hm, Nat.cast_natAbs, Int.cast_abs]
  have hm' : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    rw [Nat.cast_sub hm1]; ring
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨a, ha⟩ : ∃ a : ℤ, |(c₀ : ℝ) + c₁ * ξ| = m * |ξ - a / m| := by
    rcases lt_or_gt_of_ne hc₁ with hneg | hpos
    · refine ⟨c₀, ?_⟩
      have : (c₁ : ℝ) = -m := by
        rw [hmR, abs_of_neg (by exact_mod_cast hneg)]; ring
      rw [this, ← abs_of_pos hm0, ← abs_mul, abs_of_pos hm0, ← abs_neg]
      congr 1
      field_simp
      ring
    · refine ⟨-c₀, ?_⟩
      have : (c₁ : ℝ) = m := by rw [hmR, abs_of_pos (by exact_mod_cast hpos)]
      rw [this, ← abs_of_pos hm0, ← abs_mul, abs_of_pos hm0]
      congr 1
      field_simp
      push_cast
      ring
  have hL := h a (m - 1)
  rw [hm'] at hL
  have hmZ : (m : ℝ) ≤ Z := hmR ▸ h₁
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  rw [ha]
  calc (max A 1 * Z ^ d)⁻¹ ≤ (A * (m : ℝ) ^ d)⁻¹ := by
        gcongr
        exact le_max_left _ _
    _ ≤ |ξ - a / m| := by
        rw [inv_le_iff_one_le_mul₀ (by positivity)]
        linarith
    _ ≤ m * |ξ - a / m| := le_mul_of_one_le_left (abs_nonneg _) hm1R

/-- **The two-variable step**: BE.0 at `n = 2` with the forms `X₁` and
`(a₀ + a₁ ξ) X₁ + (c₀ + c₁ ξ) X₂` at `∞` and the coordinates at the primes dividing `b`. For `ξ`
real algebraic irrational and `b ≥ 2` there is `K > 0` such that for `0 < ε ≤ 1` and integers
`|aᵢ|, |cᵢ| ≤ Z`, `(c₀, c₁) ≠ 0`, the points `(b^t, w)` with `|w| ≤ b^t`,
`|(a₀ + a₁ ξ) b^t + (c₀ + c₁ ξ) w| ≤ Z (b^t)^{-ε}` and `K ε⁻¹ (1 + log Z) ≤ t log b` lie on at most
`K ε⁻³ (1 + log ε⁻¹)²` lines. -/
theorem exists_lines_of_approx (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (hirr : Irrational ξ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ Z : ℝ, 1 ≤ Z → ∀ a₀ a₁ c₀ c₁ : ℤ,
      |(a₀ : ℝ)| ≤ Z → |(a₁ : ℝ)| ≤ Z → |(c₀ : ℝ)| ≤ Z → |(c₁ : ℝ)| ≤ Z → (c₀ ≠ 0 ∨ c₁ ≠ 0) →
      ∃ T : Finset (Submodule ℚ (Fin 2 → ℚ)),
        (#T : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ (t : ℕ) (w : ℤ), |(w : ℝ)| ≤ (b : ℝ) ^ t →
          |(a₀ + a₁ * ξ) * b ^ t + (c₀ + c₁ * ξ) * w| ≤ Z * ((b : ℝ) ^ t) ^ (-ε) →
          K * ε⁻¹ * (1 + log Z) ≤ t * log b → ∃ U ∈ T, ![(b : ℚ) ^ t, (w : ℚ)] ∈ U := by
  classical
  set S : Finset Nat.Primes := b.primeFactors.subtype Nat.Prime with hS
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceBoundAt_three hξ S 2 le_rfl (by norm_num)
  obtain ⟨A, hA, hLiou⟩ := exists_inv_le_abs_add_mul hirr hξ
  set d := (minpoly ℚ ξ).natDegree
  have hlogA : 0 ≤ log A := log_nonneg hA
  refine ⟨K₀ * (d + 3) * (1 + log A), by positivity, fun ε hε hε1 Z hZ a₀ a₁ c₀ c₁ ha₀ ha₁ hc₀ hc₁
    hc ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogZ : 0 ≤ log Z := log_nonneg hZ
  set g : Nat.Primes → ℝ := fun l ↦ -(b.factorization l : ℝ) * log l / log b with hg
  have hg0 : ∀ l, g l ≤ 0 := fun l ↦ by
    have : 0 ≤ log (l : ℝ) := log_natCast_nonneg _
    have : 0 < log (b : ℝ) := log_pos hbR
    simp only [hg, neg_mul, neg_div]
    exact neg_nonpos.mpr (div_nonneg (by positivity) this.le)
  have hgsum : ∑ l ∈ S, g l = -1 := sum_factorization_log_div hb
  set P : Fin 2 → Fin 2 → Fin 3 → ℤ := ![![![1, 0, 0], 0], ![![a₀, a₁, 0], ![c₀, c₁, 0]]] with hP
  have hPB : ∀ i j m, |(P i j m : ℝ)| ≤ Z := by
    intro i j m
    fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [P] <;> linarith
  set γ : ℝ := (A * Z ^ d)⁻¹ with hγ
  have hAZ : 1 ≤ A * Z ^ d := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hZ)
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := inv_le_one_of_one_le₀ hAZ
  have hdet : γ ≤ |(Matrix.of fun i j ↦ quadVal ξ (P i j)).det| := by
    refine (hLiou c₀ c₁ Z hc₀ hc₁ hc).trans_eq ?_
    simp [Matrix.det_fin_two, quadVal, P]
  set e : Fin 2 → ℝ := ![1, -ε] with he
  set f : Nat.Primes → Fin 2 → ℝ := fun l ↦ ![g l, 0] with hf
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hBE P Z hZ hPB γ hγ0 hγ1 hdet Z hZ e f ε hε hε1
    (fun i ↦ by fin_cases i <;> simp [e]; linarith) ⟨0, by simp [e]⟩
    (exists_le_one_sub_div_of_exists_nonpos le_rfl hε1 ⟨1, by simp [e]; linarith⟩)
    (fun l _ i ↦ by fin_cases i <;> simp [f, hg0 l]) (fun l _ ↦ ⟨1, by simp [f]⟩)
    (by simp [e, f, Fin.sum_univ_two, hgsum])
  have hK₀ : K₀ ≤ K₀ * (d + 3) * (1 + log A) := by
    have : (1 : ℝ) ≤ (d + 3) * (1 + log A) := by nlinarith
    nlinarith
  refine ⟨T, ?_, hTtop, ?_⟩
  · refine hTcard.trans ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀ (by positivity))
      (by positivity)
  · intro t w hw happ hthr
    set x : Fin 2 → ℤ := ![(b : ℤ) ^ t, w] with hx
    have hbt : (1 : ℝ) ≤ (b : ℝ) ^ t := one_le_pow₀ hbR.le
    have hX : (⨆ i, |(x i : ℝ)|) = (b : ℝ) ^ t := by
      refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
      · fin_cases i <;> simp [x, abs_of_pos hb0, hw]
      · refine le_ciSup_of_le (Set.finite_range _).bddAbove 0 ?_
        simp [x, abs_of_pos hb0]
    have hx0 : x ≠ 0 := fun h ↦ by
      have := congrFun h 0
      simp [x] at this
      omega
    have hinf : ∀ i, |∑ j, quadVal ξ (P i j) * x j| ≤ Z * (⨆ k, |(x k : ℝ)|) ^ e i := by
      rw [hX]
      intro i
      fin_cases i
      · simp only [x, P, e, quadVal, Fin.sum_univ_two]
        simp [abs_of_pos hb0]
        nlinarith
      · simp only [x, P, e, quadVal, Fin.sum_univ_two]
        convert happ using 2 <;> simp
    have hpad : ∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤
        (⨆ k, |(x k : ℝ)|) ^ f l i := by
      rw [hX]
      have hcast : ∀ n : ℕ, (((b : ℤ) ^ n : ℤ) : ℚ) = (b : ℚ) ^ n := fun n ↦ by push_cast; rfl
      intro l _ i
      fin_cases i
      · change ((padicNorm (l : ℕ) (((b : ℤ) ^ t : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((b : ℝ) ^ t) ^ g l
        rw [hcast t, padicNorm_pow_eq_rpow hb l t]
      · change ((padicNorm (l : ℕ) ((w : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((b : ℝ) ^ t) ^ (0 : ℝ)
        rw [rpow_zero]
        exact_mod_cast padicNorm.of_int w
    have hthr' : K₀ * ε⁻¹ * (1 + log Z + log Z + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) := by
      rw [hX, log_pow, hγ, inv_inv, log_mul (by positivity) (by positivity), log_pow]
      have hε0 : 0 ≤ K₀ * ε⁻¹ := by positivity
      have hd : (0 : ℝ) ≤ d := by positivity
      calc K₀ * ε⁻¹ * (1 + log Z + log Z + (log A + d * log Z))
          ≤ K₀ * ε⁻¹ * ((d + 3) * (1 + log A) * (1 + log Z)) := by
            gcongr
            nlinarith [mul_nonneg hd hlogA, mul_nonneg hlogA hlogZ,
              mul_nonneg (mul_nonneg hd hlogA) hlogZ]
        _ = K₀ * (d + 3) * (1 + log A) * ε⁻¹ * (1 + log Z) := by ring
        _ ≤ t * log b := hthr
    obtain ⟨U, hU, hmem⟩ := hTmem x hx0 hinf hpad hthr'
    refine ⟨U, hU, ?_⟩
    convert hmem using 1
    ext i
    fin_cases i <;> simp [x]

/-- `|a b - c d| ≤ 2 M²` when `|a|, |b|, |c|, |d| ≤ M`. -/
private theorem abs_mul_sub_mul_le {a b c d M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M)
    (hd : |d| ≤ M) : |a * b - c * d| ≤ 2 * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  calc |a * b - c * d| ≤ |a| * |b| + |c| * |d| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ M * M + M * M := by gcongr
    _ = 2 * M ^ 2 := by ring

/-- If `b^{t₁} p₂ = p₁ b^{t₂}` with `t₁ < t₂`, then `b ∣ p₂`. -/
private theorem dvd_of_pow_mul_eq {t₁ t₂ : ℕ} {p₁ p₂ : ℤ} (hb : 2 ≤ b) (ht : t₁ < t₂)
    (h : (b : ℤ) ^ t₁ * p₂ = p₁ * b ^ t₂) : (b : ℤ) ∣ p₂ := by
  obtain ⟨k, rfl⟩ : ∃ k, t₂ = t₁ + (k + 1) := ⟨t₂ - t₁ - 1, by omega⟩
  have hb0 : (b : ℤ) ^ t₁ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))
  have : p₂ = p₁ * b ^ k * b := mul_left_cancel₀ hb0 (by rw [h]; ring)
  exact ⟨p₁ * b ^ k, by rw [this]; ring⟩

/-- **The points on a given plane, above the threshold.** For `ξ` real algebraic irrational and
`b ≥ 2` there is `K > 0` such that for `0 < ε ≤ 1`: if the points `(b^{t_n}, b^{r_n}, p_n)`,
`n ∈ J`, with `t` strictly increasing and `b ∤ p_n` when `r_n ≥ 1`, satisfy the approximation
`|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}` and lie on the plane `z₁ X₁ + z₂ X₂ + z₃ X₃ = 0` with
`|zᵢ| ≤ Z`, `(z₂, z₃) ≠ 0`, and `K ε⁻¹ (1 + log Z) ≤ t_n log b`, then there are at most
`K ε⁻³ (1 + log ε⁻¹)²` of them. -/
theorem card_le_of_plane (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (hirr : Irrational ξ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (r t : ℕ → ℕ) (p : ℕ → ℤ), StrictMono t →
      ∀ (z : Fin 3 → ℤ) (Z : ℝ), 1 ≤ Z → (∀ i, |(z i : ℝ)| ≤ Z) → (z 1 ≠ 0 ∨ z 2 ≠ 0) →
      ∀ J : Finset ℕ, (∀ n ∈ J, r n < t n) → (∀ n ∈ J, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) →
      (∀ n ∈ J, |(p n : ℝ)| ≤ (b : ℝ) ^ t n) →
      (∀ n ∈ J, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε)) →
      (∀ n ∈ J, z 0 * (b : ℤ) ^ t n + z 1 * (b : ℤ) ^ r n + z 2 * p n = 0) →
      (∀ n ∈ J, K * ε⁻¹ * (1 + log Z) ≤ t n * log b) →
      (#J : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K₁, hK₁, hL⟩ := exists_lines_of_approx hb hξ hirr
  refine ⟨2 * K₁, by positivity, fun ε hε hε1 r t p ht z Z hZ hzZ hz J hrt hdvd hp happ hpl hthr ↦
    ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hZ2 : 1 ≤ 2 * Z := by linarith
  have hlogZ : 0 ≤ log Z := log_nonneg hZ
  have hz0 := hzZ 0
  have hz1 := hzZ 1
  have hz2 := hzZ 2
  have hthr' : ∀ n ∈ J, K₁ * ε⁻¹ * (1 + log (2 * Z)) ≤ t n * log b := fun n hn ↦ by
    refine le_trans ?_ (hthr n hn)
    rw [log_mul (by norm_num) (by positivity)]
    have : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have : 0 ≤ K₁ * ε⁻¹ := by positivity
    nlinarith
  have hplR : ∀ n ∈ J, (z 0 : ℝ) * (b : ℝ) ^ t n + z 1 * (b : ℝ) ^ r n + z 2 * p n = 0 :=
    fun n hn ↦ by exact_mod_cast hpl n hn
  have hrpow : ∀ n, 0 ≤ ((b : ℝ) ^ t n) ^ (-ε) := fun n ↦ rpow_nonneg (by positivity) _
  -- eliminating `b^r`: the pairs `(b^t, p)`
  obtain ⟨T₁, hT₁card, hT₁top, hT₁mem⟩ := hL ε hε hε1 (2 * Z) hZ2 0 (z 0 + z 1) (-z 1) (z 2)
    (by simp; linarith) (by push_cast; exact (abs_add_le _ _).trans (by linarith))
    (by push_cast; rw [abs_neg]; linarith) (by linarith)
    (by rcases hz with h | h; exacts [Or.inl (neg_ne_zero.mpr h), Or.inr h])
  -- eliminating `p`: the pairs `(b^t, b^r)`
  obtain ⟨T₂, hT₂card, hT₂top, hT₂mem⟩ := hL ε hε hε1 (2 * Z) hZ2 (z 0) (z 2) (z 1) (-z 2)
    (by linarith) (by linarith) (by linarith) (by push_cast; rw [abs_neg]; linarith)
    (by rcases hz with h | h; exacts [Or.inl h, Or.inr (neg_ne_zero.mpr h)])
  have hφ₁ : ∀ n ∈ J.filter (fun n ↦ 1 ≤ r n), ∃ U ∈ T₁, ![(b : ℚ) ^ t n, (p n : ℚ)] ∈ U := by
    intro n hn
    obtain ⟨hn, -⟩ := mem_filter.mp hn
    refine hT₁mem (t n) (p n) (hp n hn) ?_ (hthr' n hn)
    calc _ = |(z 1 : ℝ)| * |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| := by
          rw [← abs_mul]; congr 1; push_cast; linear_combination ξ * hplR n hn
      _ ≤ Z * ((b : ℝ) ^ t n) ^ (-ε) := mul_le_mul hz1 (happ n hn) (abs_nonneg _) (by linarith)
      _ ≤ 2 * Z * ((b : ℝ) ^ t n) ^ (-ε) := by have := hrpow n; nlinarith
  have hφ₂ : ∀ n ∈ J.filter (fun n ↦ ¬ 1 ≤ r n), ∃ U ∈ T₂,
      ![(b : ℚ) ^ t n, (((b : ℤ) ^ r n : ℤ) : ℚ)] ∈ U := by
    intro n hn
    obtain ⟨hn, -⟩ := mem_filter.mp hn
    refine hT₂mem (t n) ((b : ℤ) ^ r n) ?_ ?_ (hthr' n hn)
    · push_cast
      rw [abs_of_pos (by positivity)]
      exact pow_le_pow_right₀ hbR.le (hrt n hn).le
    calc _ = |(z 2 : ℝ)| * |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| := by
          rw [← abs_mul]; congr 1; push_cast; linear_combination hplR n hn
      _ ≤ Z * ((b : ℝ) ^ t n) ^ (-ε) := mul_le_mul hz2 (happ n hn) (abs_nonneg _) (by linarith)
      _ ≤ 2 * Z * ((b : ℝ) ^ t n) ^ (-ε) := by have := hrpow n; nlinarith
  choose! φ₁ hφ₁T hφ₁U using hφ₁
  choose! φ₂ hφ₂T hφ₂U using hφ₂
  -- at most one point per line
  have hJ₁ : #(J.filter (fun n ↦ 1 ≤ r n)) ≤ #T₁ := by
    refine card_le_card_of_injOn φ₁ (fun n hn ↦ hφ₁T n hn) fun n hn m hm hnm ↦ ?_
    have hu := hφ₁U n hn
    have hv := hφ₁U m hm
    rw [hnm] at hu
    have h := Submodule.det_eq_zero_of_forall_mem (hT₁top _ (hφ₁T m hm))
      ![![(b : ℚ) ^ t n, (p n : ℚ)], ![(b : ℚ) ^ t m, (p m : ℚ)]]
      (fun i ↦ by fin_cases i; exacts [hu, hv])
    rw [Matrix.det_fin_two] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    have h' : (b : ℤ) ^ t n * p m = p n * b ^ t m := by
      have : (b : ℚ) ^ t n * p m = p n * b ^ t m := by linear_combination h
      exact_mod_cast this
    obtain ⟨hn, hrn⟩ := mem_filter.mp (mem_coe.mp hn)
    obtain ⟨hm, hrm⟩ := mem_filter.mp (mem_coe.mp hm)
    by_contra hne
    rcases lt_or_gt_of_ne (ht.injective.ne hne) with hlt | hlt
    · exact hdvd m hm hrm (dvd_of_pow_mul_eq hb hlt h')
    · exact hdvd n hn hrn (dvd_of_pow_mul_eq (p₁ := p m) hb hlt (by linear_combination -h'))
  have hJ₂ : #(J.filter (fun n ↦ ¬ 1 ≤ r n)) ≤ #T₂ := by
    refine card_le_card_of_injOn φ₂ (fun n hn ↦ hφ₂T n hn) fun n hn m hm hnm ↦ ?_
    have hu := hφ₂U n hn
    have hv := hφ₂U m hm
    rw [hnm] at hu
    have h := Submodule.det_eq_zero_of_forall_mem (hT₂top _ (hφ₂T m hm))
      ![![(b : ℚ) ^ t n, (((b : ℤ) ^ r n : ℤ) : ℚ)], ![(b : ℚ) ^ t m, (((b : ℤ) ^ r m : ℤ) : ℚ)]]
      (fun i ↦ by fin_cases i; exacts [hu, hv])
    rw [Matrix.det_fin_two] at h
    obtain ⟨-, hrn⟩ := mem_filter.mp (mem_coe.mp hn)
    obtain ⟨-, hrm⟩ := mem_filter.mp (mem_coe.mp hm)
    have hrn0 : r n = 0 := by omega
    have hrm0 : r m = 0 := by omega
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hrn0, hrm0, pow_zero, Int.cast_one, mul_one,
      one_mul] at h
    have : b ^ t n = b ^ t m := by exact_mod_cast sub_eq_zero.mp h
    exact ht.injective (Nat.pow_right_injective hb this)
  have hcard := card_filter_add_card_filter_not (s := J) (fun n ↦ 1 ≤ r n)
  have : (#J : ℝ) ≤ #T₁ + #T₂ := by rw [← hcard]; push_cast; exact_mod_cast add_le_add hJ₁ hJ₂
  linarith

/-- **The plane through two points** (Bugeaud–Evertse 2008, (7.12)). If `x₁ = (b^{t₁}, b^{r₁}, p₁)`
and `x₂ = (b^{t₂}, b^{r₂}, p₂)`, `t₁ < t₂`, lie in a proper subspace `U` of `ℚ³`, then
`z = x₁ × x₂` has `|zᵢ| ≤ 2 b^{2 t₂}` and `(z₂, z₃) ≠ 0`, and every `(b^t, b^r, p) ∈ U` satisfies
`z₁ b^t + z₂ b^r + z₃ p = 0`. -/
theorem exists_plane_eq (hb : 2 ≤ b) {U : Submodule ℚ (Fin 3 → ℚ)} (hU : U ≠ ⊤)
    {r₁ t₁ r₂ t₂ : ℕ} {p₁ p₂ : ℤ} (ht : t₁ < t₂) (hr₁ : r₁ < t₁) (hr₂ : r₂ < t₂)
    (hp₁ : |(p₁ : ℝ)| ≤ (b : ℝ) ^ t₁) (hp₂ : |(p₂ : ℝ)| ≤ (b : ℝ) ^ t₂)
    (hdvd : 1 ≤ r₂ → ¬ (b : ℤ) ∣ p₂) (h₁ : ![(b : ℚ) ^ t₁, (b : ℚ) ^ r₁, (p₁ : ℚ)] ∈ U)
    (h₂ : ![(b : ℚ) ^ t₂, (b : ℚ) ^ r₂, (p₂ : ℚ)] ∈ U) :
    ∃ z : Fin 3 → ℤ, (∀ i, |(z i : ℝ)| ≤ 2 * ((b : ℝ) ^ t₂) ^ 2) ∧ (z 1 ≠ 0 ∨ z 2 ≠ 0) ∧
      ∀ (r t : ℕ) (p : ℤ), ![(b : ℚ) ^ t, (b : ℚ) ^ r, (p : ℚ)] ∈ U →
        z 0 * (b : ℤ) ^ t + z 1 * (b : ℤ) ^ r + z 2 * p = 0 := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set z : Fin 3 → ℤ := ![(b : ℤ) ^ r₁ * p₂ - p₁ * (b : ℤ) ^ r₂,
    p₁ * (b : ℤ) ^ t₂ - (b : ℤ) ^ t₁ * p₂,
    (b : ℤ) ^ t₁ * (b : ℤ) ^ r₂ - (b : ℤ) ^ r₁ * (b : ℤ) ^ t₂] with hz
  refine ⟨z, ?_, ?_, fun r t p hn ↦ ?_⟩
  · -- `|zᵢ| ≤ 2 b^{2 t₂}`
    set M : ℝ := (b : ℝ) ^ t₂ with hM
    have hB₁ : |(b : ℝ) ^ t₁| ≤ M := by
      rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ hbR.le ht.le
    have hB₂ : |(b : ℝ) ^ t₂| ≤ M := by rw [abs_of_pos (by positivity)]
    have hR₁ : |(b : ℝ) ^ r₁| ≤ M := by
      rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ hbR.le (by omega)
    have hR₂ : |(b : ℝ) ^ r₂| ≤ M := by
      rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ hbR.le hr₂.le
    have hp₁' : |(p₁ : ℝ)| ≤ M := hp₁.trans (pow_le_pow_right₀ hbR.le ht.le)
    intro i
    fin_cases i <;> simp only [z, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> push_cast
    · exact abs_mul_sub_mul_le hR₁ hp₂ hp₁' hR₂
    · exact abs_mul_sub_mul_le hp₁' hB₂ hB₁ hp₂
    · exact abs_mul_sub_mul_le hB₁ hR₂ hR₁ hB₂
  · -- `(z₂, z₃) ≠ 0`, since `x₁` and `x₂` are not proportional
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hz] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h1 h2
    have h2' : b ^ (t₁ + r₂) = b ^ (r₁ + t₂) := by
      rw [pow_add, pow_add]
      exact_mod_cast sub_eq_zero.mp h2
    have hr2 : 1 ≤ r₂ := by have := Nat.pow_right_injective hb h2'; omega
    exact hdvd hr2 (dvd_of_pow_mul_eq (p₁ := p₁) hb ht (by linear_combination -h1))
  · -- `det (x₁, x₂, x) = 0`
    have h := Submodule.det_eq_zero_of_forall_mem hU
      ![![(b : ℚ) ^ t₁, (b : ℚ) ^ r₁, (p₁ : ℚ)],
        ![(b : ℚ) ^ t₂, (b : ℚ) ^ r₂, (p₂ : ℚ)], ![(b : ℚ) ^ t, (b : ℚ) ^ r, (p : ℚ)]]
      (fun i ↦ by fin_cases i; exacts [h₁, h₂, hn])
    rw [Matrix.det_fin_three] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const] at h
    have : ((z 0 * (b : ℤ) ^ t + z 1 * (b : ℤ) ^ r + z 2 * p : ℤ) : ℚ) = 0 := by
      rw [hz]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      push_cast
      linear_combination h
    exact_mod_cast this

/-- **The plane step** (Bugeaud–Evertse 2008, (7.12)–(7.19)). For `ξ` real algebraic irrational
and `b ≥ 2` there is `K > 0` such that for `0 < ε ≤ 1`: if `t` at least doubles
(`2 t_n < t_{n+1}`) and the points `x_n = (b^{t_n}, b^{r_n}, p_n)`, `n ∈ I`, with `r_n < t_n`,
`|p_n| ≤ b^{t_n}`, `b ∤ p_n` when `r_n ≥ 1` and `|b^{t_n} ξ - b^{r_n} ξ - p_n| ≤ (b^{t_n})^{-ε}`
lie in a proper subspace `U` of `ℚ³`, then there are at most `K ε⁻³ (1 + log ε⁻¹)²` of them. No
threshold: the points below it are `O(1 + log ε⁻¹)` by the doubling. -/
theorem card_mem_plane_le (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (hirr : Irrational ξ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (r t : ℕ → ℕ) (p : ℕ → ℤ),
      (∀ n, 2 * t n < t (n + 1)) → ∀ U : Submodule ℚ (Fin 3 → ℚ), U ≠ ⊤ → ∀ I : Finset ℕ,
      (∀ n ∈ I, r n < t n) → (∀ n ∈ I, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) →
      (∀ n ∈ I, |(p n : ℝ)| ≤ (b : ℝ) ^ t n) →
      (∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε)) →
      (∀ n ∈ I, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U) →
      (#I : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K₂, hK₂, hP⟩ := card_le_of_plane hb hξ hirr
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < log b := log_pos hbR
  set K₃ : ℝ := max 1 (K₂ * (2 + 2 * log b) / log b) with hK₃
  have hK₃1 : 1 ≤ K₃ := le_max_left _ _
  have hlogK₃ : 0 ≤ log K₃ := log_nonneg hK₃1
  refine ⟨K₂ + 3 + 2 * log K₃, by positivity,
    fun ε hε hε1 r t p ht U hU I hrt hdvd hp happ hmem ↦ ?_⟩
  have htm : StrictMono t := strictMono_nat_of_lt_succ fun n ↦ by have := ht n; omega
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
  set X := ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 with hX
  rw [mul_assoc]
  have hX1 : 1 + log ε⁻¹ ≤ X := by
    have h1 : 1 ≤ ε⁻¹ ^ 3 := one_le_pow₀ hεinv
    have h2 : 1 + log ε⁻¹ ≤ (1 + log ε⁻¹) ^ 2 := by nlinarith
    nlinarith
  by_cases hI : #I ≤ 1
  · have : (#I : ℝ) ≤ 1 := by exact_mod_cast hI
    nlinarith
  -- the two smallest indices `i₁ < i₂`
  have hI0 : I.Nonempty := card_pos.mp (by omega)
  set i₁ := I.min' hI0 with hi₁def
  have hi₁ : i₁ ∈ I := min'_mem _ _
  have hI1 : (I.erase i₁).Nonempty := by
    rw [← card_pos, card_erase_of_mem hi₁]; omega
  set i₂ := (I.erase i₁).min' hI1 with hi₂def
  have hi₂' : i₂ ∈ I.erase i₁ := min'_mem _ _
  have hi₂ : i₂ ∈ I := mem_of_mem_erase hi₂'
  have h12 : i₁ < i₂ := lt_of_le_of_ne (min'_le _ _ hi₂) (ne_of_mem_erase hi₂').symm
  have hge : ∀ n ∈ I, n ≠ i₁ → i₂ ≤ n := fun n hn hne ↦ min'_le _ _ (mem_erase.mpr ⟨hne, hn⟩)
  have ht12 : t i₁ < t i₂ := htm h12
  have ht2 : 1 ≤ t i₂ := by
    have := ht (i₂ - 1)
    rw [Nat.sub_add_cancel (by omega)] at this
    omega
  -- the plane through `x_{i₁}` and `x_{i₂}`, with `|zᵢ| ≤ Z = 2 b^{2 t_{i₂}}`
  set M : ℝ := (b : ℝ) ^ t i₂ with hM
  set Z : ℝ := 2 * M ^ 2 with hZdef
  obtain ⟨z, hzZ, hz12, hpl⟩ := exists_plane_eq hb hU ht12 (hrt i₁ hi₁) (hrt i₂ hi₂) (hp i₁ hi₁)
    (hp i₂ hi₂) (hdvd i₂ hi₂) (hmem i₁ hi₁) (hmem i₂ hi₂)
  have hplane : ∀ n ∈ I, z 0 * (b : ℤ) ^ t n + z 1 * (b : ℤ) ^ r n + z 2 * p n = 0 :=
    fun n hn ↦ hpl (r n) (t n) (p n) (hmem n hn)
  have hM1 : 1 ≤ M := one_le_pow₀ hbR.le
  have hZ1 : 1 ≤ Z := by nlinarith
  -- the points above the threshold
  set θ : ℝ := K₂ * ε⁻¹ * (1 + log Z) with hθ
  have hJ := hP ε hε hε1 r t p htm z Z hZ1 hzZ hz12 (I.filter fun n ↦ θ ≤ t n * log b)
    (fun n hn ↦ hrt n (mem_filter.mp hn).1) (fun n hn ↦ hdvd n (mem_filter.mp hn).1)
    (fun n hn ↦ hp n (mem_filter.mp hn).1) (fun n hn ↦ happ n (mem_filter.mp hn).1)
    (fun n hn ↦ hplane n (mem_filter.mp hn).1) (fun n hn ↦ (mem_filter.mp hn).2)
  -- the points below it: `i₁` and `i₂ ≤ n ≤ i₂ + m`
  have hKε : 1 ≤ K₃ * ε⁻¹ := one_le_mul_of_one_le_of_one_le hK₃1 hεinv
  set m : ℕ := ⌈logb 2 (K₃ * ε⁻¹)⌉₊ with hm
  have h2m : K₃ * ε⁻¹ ≤ 2 ^ m := by
    calc K₃ * ε⁻¹ = (2 : ℝ) ^ logb 2 (K₃ * ε⁻¹) := (rpow_logb (by norm_num) (by norm_num)
          (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (m : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ m := rpow_natCast _ _
  have hlog2 : 1 / 2 ≤ log 2 := by have := log_two_gt_d9; linarith
  have hmle : (m : ℝ) ≤ 2 * (log K₃ + log ε⁻¹) + 1 := by
    have hl : 0 ≤ logb 2 (K₃ * ε⁻¹) := logb_nonneg (by norm_num) hKε
    have := Nat.ceil_lt_add_one hl
    have hlb : logb 2 (K₃ * ε⁻¹) ≤ 2 * (log K₃ + log ε⁻¹) := by
      rw [logb, div_le_iff₀ (by positivity), ← log_mul (by positivity) (by positivity)]
      have : 0 ≤ log (K₃ * ε⁻¹) := log_nonneg hKε
      nlinarith
    linarith
  have hL : I.filter (fun n ↦ ¬ θ ≤ t n * log b) ⊆ insert i₁ (Icc i₂ (i₂ + m)) := by
    intro n hn
    obtain ⟨hn, hnθ⟩ := mem_filter.mp hn
    rw [mem_insert, mem_Icc]
    by_cases hn1 : n = i₁
    · exact Or.inl hn1
    refine Or.inr ⟨hge n hn hn1, ?_⟩
    by_contra hnm
    apply hnθ
    -- `t_n ≥ 2^{m+1} t_{i₂}` is above the threshold
    have hdbl := Nat.two_pow_mul_le_of_doubling ht i₂ (n - i₂)
    rw [Nat.add_sub_cancel' (hge n hn hn1)] at hdbl
    have hpow : 2 ^ m ≤ 2 ^ (n - i₂) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htn : (2 : ℝ) ^ m * t i₂ ≤ t n := by
      have : 2 ^ m * t i₂ ≤ t n := (Nat.mul_le_mul_right _ hpow).trans hdbl
      exact_mod_cast this
    have ht2R : (1 : ℝ) ≤ t i₂ := by exact_mod_cast ht2
    have hlogZ : log Z = log 2 + 2 * (t i₂ * log b) := by
      rw [hZdef, hM, log_mul (by norm_num) (by positivity), log_pow, log_pow]; ring
    have hlog2' : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hK₃' : K₂ * (2 + 2 * log b) ≤ K₃ * log b := by
      rw [← div_le_iff₀ hlogb]; exact le_max_right _ _
    calc θ = K₂ * ε⁻¹ * (1 + log 2 + 2 * (t i₂ * log b)) := by rw [hθ, hlogZ]; ring
      _ ≤ K₂ * ε⁻¹ * (t i₂ * (2 + 2 * log b)) := by
          gcongr
          nlinarith
      _ = ε⁻¹ * t i₂ * (K₂ * (2 + 2 * log b)) := by ring
      _ ≤ ε⁻¹ * t i₂ * (K₃ * log b) := by gcongr
      _ = K₃ * ε⁻¹ * t i₂ * log b := by ring
      _ ≤ 2 ^ m * t i₂ * log b := by gcongr
      _ ≤ t n * log b := by gcongr
  have hLcard : (#(I.filter fun n ↦ ¬ θ ≤ t n * log b) : ℝ) ≤ m + 2 := by
    have := (card_le_card hL).trans (card_insert_le _ _)
    rw [Nat.card_Icc] at this
    have : #(I.filter fun n ↦ ¬ θ ≤ t n * log b) ≤ m + 2 := by omega
    exact_mod_cast this
  have hcard := card_filter_add_card_filter_not (s := I) (fun n ↦ θ ≤ t n * log b)
  have hI' : (#I : ℝ) ≤ K₂ * X + (m + 2) := by
    rw [← hcard]; push_cast
    have := hJ
    rw [mul_assoc] at this
    linarith
  nlinarith

end Real
