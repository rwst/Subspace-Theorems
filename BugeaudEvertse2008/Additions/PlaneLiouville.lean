/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.PlaneStep

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences

/-!
# The plane step without a second Subspace application

A proper subspace `U` of `ℚ³` holds `O(1 + log ε⁻¹)` of the points `x_n = (b^{t_n}, b^{r_n}, p_n)`
of a doubling sequence whose gap `s_n = t_n - r_n` is large, `ε t_n < 4 s_n`
(`Real.card_mem_plane_le_log`). Bugeaud–Evertse's plane step (`Real.card_mem_plane_le`) gives
`ε⁻³ (1 + log ε⁻¹)²`. Let `z₁ X₁ + z₂ X₂ + z₃ X₃ = 0` be the plane
(`Real.exists_plane_eq`), `|zᵢ| ≤ Z = 2 b^{2 t_{i₂}}`.

* If `z₃ ≠ 0`, Liouville's inequality, applied twice, bounds the point: `t log b ≤ D (1 + log Z)`
  (`Real.exists_mul_log_le_of_plane`). Eliminating `p` gives
  `b^r Γ = z₃ (b^t ξ - b^r ξ - p)` with `Γ = (z₃ ξ + z₁) b^s + (z₂ - z₃ ξ)`, so `|Γ| ≤ Z`.
  Liouville at `z₁ + z₃ ξ` bounds `b^s ≤ A (2 + |ξ|) Z^{d+1}`. Then Liouville at
  `Γ = (z₁ b^s + z₂) + z₃ (b^s - 1) ξ ≠ 0` bounds `b^r ≤ A Z (2 Z b^s)^d`. So the points lie in a
  window `t ≤ R t_{i₂}` of the doubling sequence: `O(1)` of them.
* If `z₃ = 0`, then `z₁ b^t = -z₂ b^r`, so the gap `s = s₀` is the same at all points of the plane.
  A large gap gives `ε t < 4 s₀ ≤ 4 t_{i₁}`: a window of ratio `4 / ε`, `O(log ε⁻¹)` points.

No approximation property beyond `|b^t ξ - b^r ξ - p| ≤ 1` is used, and no Subspace Theorem.

## Main results

* `Real.exists_mul_log_le_of_plane`: a point on a plane with `z₃ ≠ 0` has `t log b ≤ D (1 + log Z)`.
* `Real.card_mem_plane_le_log`: **at most `K (1 + log ε⁻¹)` points with a large gap on a plane**.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7;
R. Stephan, *The exponent `1/4` in three complexity bounds: integer bases, continued fractions, and
the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), Lemmas 3.4–3.5.
-/

@[expose] public section

open Finset

namespace Real

variable {b : ℕ}

/-- Liouville at `z₁ + z₃ ξ` bounds `β = b^s`: from `|(z₃ ξ + z₁) β + (z₂ - z₃ ξ)| ≤ Z`. -/
private theorem le_of_liouville_one {A Z β ξ z₀ z₁ z₂ : ℝ} {d : ℕ} (hA : 0 < A) (hZ : 0 < Z)
    (hβ : 0 < β) (hΓ : |(z₂ * ξ + z₀) * β + (z₁ - z₂ * ξ)| ≤ Z) (hz₁ : |z₁| ≤ Z) (hz₂ : |z₂| ≤ Z)
    (hL : (A * Z ^ d)⁻¹ ≤ |z₀ + z₂ * ξ|) : β ≤ A * (2 + |ξ|) * Z ^ (d + 1) := by
  have hAZ : 0 < A * Z ^ d := by positivity
  have h1 : |z₀ + z₂ * ξ| * β ≤ Z * (2 + |ξ|) := by
    have : |z₀ + z₂ * ξ| * β =
        |((z₂ * ξ + z₀) * β + (z₁ - z₂ * ξ)) - (z₁ - z₂ * ξ)| := by
      rw [← abs_of_pos hβ, ← abs_mul, abs_of_pos hβ]
      congr 1; ring
    rw [this]
    calc _ ≤ |(z₂ * ξ + z₀) * β + (z₁ - z₂ * ξ)| + (|z₁| + |z₂| * |ξ|) := by
          refine (abs_sub _ _).trans ?_
          gcongr
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ Z + (Z + Z * |ξ|) := by gcongr
      _ = Z * (2 + |ξ|) := by ring
  rw [inv_le_iff_one_le_mul₀ hAZ] at hL
  calc β = 1 * β := (one_mul _).symm
    _ ≤ (|z₀ + z₂ * ξ| * (A * Z ^ d)) * β := mul_le_mul_of_nonneg_right hL hβ.le
    _ = (|z₀ + z₂ * ξ| * β) * (A * Z ^ d) := by ring
    _ ≤ (Z * (2 + |ξ|)) * (A * Z ^ d) := mul_le_mul_of_nonneg_right h1 hAZ.le
    _ = A * (2 + |ξ|) * Z ^ (d + 1) := by ring

/-- Liouville at `Γ` bounds `ρ = b^r`: from `ρ |Γ| ≤ Z` and `|Γ| ≥ c⁻¹`. -/
private theorem le_of_liouville_two {ρ Γ Z c : ℝ} (hρ : 0 < ρ) (h : ρ * |Γ| ≤ Z) (hc : 0 < c)
    (hL : c⁻¹ ≤ |Γ|) : ρ ≤ c * Z := by
  rw [inv_le_iff_one_le_mul₀ hc] at hL
  calc ρ = ρ * 1 := (mul_one _).symm
    _ ≤ ρ * (|Γ| * c) := mul_le_mul_of_nonneg_left hL hρ.le
    _ = (ρ * |Γ|) * c := by ring
    _ ≤ Z * c := mul_le_mul_of_nonneg_right h hc.le
    _ = c * Z := by ring

/-- The logarithmic bookkeeping of `Real.exists_mul_log_le_of_plane`. -/
private theorem log_bound_arith {d la lx lz lβ lW l2 L : ℝ} (hd : 0 ≤ d) (hla : 0 ≤ la)
    (hlx : 0 ≤ lx) (hlz : 0 ≤ lz) (hl2 : l2 ≤ 1) (hβ : lβ ≤ la + lx + (d + 1) * lz)
    (hW : lW = l2 + lz + lβ) (hL : L ≤ la + lx + (d + 1) * lz + (la + d * lW + lz)) :
    L ≤ (d + 2) ^ 2 * (1 + la + lx) * (1 + lz) := by
  subst hW
  have h1 : d * l2 ≤ d := mul_le_of_le_one_right hd hl2
  have h2 := mul_le_mul_of_nonneg_left hβ hd
  have := mul_nonneg hd hlz
  have := mul_nonneg hd hla
  have := mul_nonneg hd hlx
  have := mul_nonneg (mul_nonneg hd hd) hlz
  have := mul_nonneg (mul_nonneg hd hd) hla
  have := mul_nonneg (mul_nonneg hd hd) hlx
  have := mul_nonneg (mul_nonneg hd hd) (mul_nonneg hla hlz)
  have := mul_nonneg (mul_nonneg hd hd) (mul_nonneg hlx hlz)
  have := mul_nonneg hd (mul_nonneg hla hlz)
  have := mul_nonneg hd (mul_nonneg hlx hlz)
  have := mul_nonneg hla hlz
  have := mul_nonneg hlx hlz
  have := mul_nonneg hd hd
  nlinarith

/-- **A point on a plane with `z₃ ≠ 0` is small.** For `ξ` real algebraic irrational and `b ≥ 2`
there is `D ≥ 1` such that if `z₁ b^t + z₂ b^r + z₃ p = 0` with `|zᵢ| ≤ Z`, `z₃ ≠ 0`, `r < t` and
`|b^t ξ - b^r ξ - p| ≤ 1`, then `t log b ≤ D (1 + log Z)`.
First proved as Lemma 3.4 of Stephan's *The exponent `1/4` in three complexity bounds* (2026,
arXiv:2610.30937). -/
theorem exists_mul_log_le_of_plane (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (z : Fin 3 → ℤ) (Z : ℝ), 1 ≤ Z → (∀ i, |(z i : ℝ)| ≤ Z) → z 2 ≠ 0 →
      ∀ (r t : ℕ) (p : ℤ), r < t → z 0 * (b : ℤ) ^ t + z 1 * (b : ℤ) ^ r + z 2 * p = 0 →
      |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ 1 → (t : ℝ) * log b ≤ D * (1 + log Z) := by
  obtain ⟨A, hA, hL⟩ := exists_inv_le_abs_add_mul hirr hξ
  obtain ⟨d, hd⟩ : ∃ d, d = (minpoly ℚ ξ).natDegree := ⟨_, rfl⟩
  rw [← hd] at hL
  have hlogA : 0 ≤ log A := log_nonneg hA
  have hlogξ : 0 ≤ log (2 + |ξ|) := log_nonneg (by linarith [abs_nonneg ξ])
  refine ⟨((d : ℝ) + 2) ^ 2 * (1 + log A + log (2 + |ξ|)), ?_,
    fun z Z hZ hzZ hz2 r t p hrt hpl happ ↦ ?_⟩
  · have : (1 : ℝ) ≤ ((d : ℝ) + 2) ^ 2 := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hA0 : 0 < A := by linarith
  have hξ2 : 0 < 2 + |ξ| := by linarith [abs_nonneg ξ]
  obtain ⟨s, rfl⟩ : ∃ s, t = r + s := ⟨t - r, by omega⟩
  have hs : 1 ≤ s := by omega
  rw [pow_add] at happ hpl
  -- `β = b^s`, `ρ = b^r`
  obtain ⟨β, hβ⟩ : ∃ β, β = (b : ℝ) ^ s := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (b : ℝ) ^ r := ⟨_, rfl⟩
  have hβ1 : (b : ℝ) ≤ β := by
    rw [hβ]; calc (b : ℝ) = b ^ 1 := (pow_one _).symm
      _ ≤ b ^ s := pow_le_pow_right₀ hbR.le hs
  have hρ1 : 1 ≤ ρ := hρ ▸ one_le_pow₀ hbR.le
  have hβ0 : 0 < β := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hgoal : ((r + s : ℕ) : ℝ) * log b = log (ρ * β) := by
    rw [hρ, hβ, ← pow_add, log_pow]
  rw [← hρ, ← hβ] at happ
  have hplR : (z 0 : ℝ) * (ρ * β) + z 1 * ρ + z 2 * p = 0 := by
    rw [hρ, hβ]; exact_mod_cast hpl
  have hz0 := hzZ 0
  have hz1 := hzZ 1
  have hz2' := hzZ 2
  -- `ρ Γ = z₃ (b^t ξ - b^r ξ - p)`, so `ρ |Γ| ≤ Z`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = (z 2 * ξ + z 0) * β + (z 1 - z 2 * ξ) := ⟨_, rfl⟩
  have hρΓ : ρ * Γ = z 2 * (ρ * β * ξ - ρ * ξ - p) := by
    rw [hΓ]; linear_combination hplR
  have hρΓle : ρ * |Γ| ≤ Z := by
    rw [← abs_of_pos hρ0, ← abs_mul, hρΓ, abs_mul]
    calc |(z 2 : ℝ)| * |ρ * β * ξ - ρ * ξ - p| ≤ Z * 1 :=
          mul_le_mul hz2' happ (abs_nonneg _) hZ0.le
      _ = Z := mul_one _
  have hΓle : |Γ| ≤ Z := le_trans (le_mul_of_one_le_left (abs_nonneg _) hρ1) hρΓle
  -- Liouville at `z₁ + z₃ ξ`: `β ≤ A (2 + |ξ|) Z^{d+1}`
  have hβle : β ≤ A * (2 + |ξ|) * Z ^ (d + 1) :=
    le_of_liouville_one hA0 hZ0 hβ0 (hΓ ▸ hΓle) hz1 hz2' (hL (z 0) (z 2) Z hz0 hz2' (Or.inr hz2))
  -- Liouville at `Γ = (z₁ b^s + z₂) + z₃ (b^s - 1) ξ`: `ρ ≤ A W^d Z`, `W = 2 Z β`
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * Z * β := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; positivity
  have hc₀ : |((z 0 * (b : ℤ) ^ s + z 1 : ℤ) : ℝ)| ≤ W := by
    push_cast
    rw [← hβ]
    calc |(z 0 : ℝ) * β + z 1| ≤ |(z 0 : ℝ)| * β + |(z 1 : ℝ)| := by
          rw [← abs_of_pos hβ0, ← abs_mul, abs_of_pos hβ0]; exact abs_add_le _ _
      _ ≤ Z * β + Z := by gcongr
      _ ≤ W := by rw [hW]; nlinarith
  have hc₁ : |((z 2 * ((b : ℤ) ^ s - 1) : ℤ) : ℝ)| ≤ W := by
    push_cast
    rw [← hβ, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ β - 1), hW]
    nlinarith [abs_nonneg (z 2 : ℝ)]
  have hc₁0 : z 2 * ((b : ℤ) ^ s - 1) ≠ 0 := by
    refine mul_ne_zero hz2 (sub_ne_zero.mpr ?_)
    have : (1 : ℤ) < (b : ℤ) ^ s := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < b)) (by omega)
    omega
  have hL2 := hL _ _ W hc₀ hc₁ (Or.inr hc₁0)
  have hΓeq : ((z 0 * (b : ℤ) ^ s + z 1 : ℤ) : ℝ) + ((z 2 * ((b : ℤ) ^ s - 1) : ℤ) : ℝ) * ξ =
      Γ := by
    rw [hΓ, hβ]; push_cast; ring
  rw [hΓeq] at hL2
  have hWd : 0 < W ^ d := pow_pos hW0 d
  have hAW : 0 < A * W ^ d := mul_pos hA0 hWd
  have hρle : ρ ≤ A * W ^ d * Z := le_of_liouville_two hρ0 hρΓle hAW hL2
  -- `b^t = b^r b^s`, and the logarithms
  have hZd : 0 < Z ^ (d + 1) := pow_pos hZ0 _
  have hbt : ρ * β ≤ (A * (2 + |ξ|) * Z ^ (d + 1)) * (A * W ^ d * Z) := by
    rw [mul_comm ρ β]
    exact mul_le_mul hβle hρle hρ0.le (by positivity)
  have hlog := log_le_log (mul_pos hρ0 hβ0) hbt
  have hR : log (A * (2 + |ξ|) * Z ^ (d + 1) * (A * W ^ d * Z)) =
      log A + log (2 + |ξ|) + (d + 1) * log Z + (log A + d * log W + log Z) := by
    rw [log_mul (mul_pos (mul_pos hA0 hξ2) hZd).ne' (mul_pos hAW hZ0).ne',
      log_mul (mul_pos hA0 hξ2).ne' hZd.ne', log_mul hA0.ne' hξ2.ne', log_mul hAW.ne' hZ0.ne',
      log_mul hA0.ne' hWd.ne', log_pow, log_pow]
    push_cast; ring
  rw [hR] at hlog
  have hlogβ : log β ≤ log A + log (2 + |ξ|) + (d + 1) * log Z := by
    have := log_le_log hβ0 hβle
    rw [log_mul (mul_pos hA0 hξ2).ne' hZd.ne', log_mul hA0.ne' hξ2.ne', log_pow] at this
    push_cast at this
    exact this
  have hlogW : log W = log 2 + log Z + log β := by
    rw [hW, log_mul (by positivity) hβ0.ne', log_mul (by norm_num) hZ0.ne']
  have hlog2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [hgoal]
  exact log_bound_arith (Nat.cast_nonneg d) hlogA hlogξ (log_nonneg hZ) hlog2 hlogβ hlogW hlog

/-- **The plane step for large gaps.** For `ξ` real algebraic irrational and `b ≥ 2` there is
`K ≥ 1` such that for `0 < ε ≤ 1`: if `t` at least doubles and the points
`x_n = (b^{t_n}, b^{r_n}, p_n)`, `n ∈ I`, with `r_n < t_n`, `b ∤ p_n` when `r_n ≥ 1`,
`|p_n| ≤ b^{t_n}`, `|b^{t_n} ξ - b^{r_n} ξ - p_n| ≤ 1` and a large gap `ε t_n < 4 (t_n - r_n)` lie
in a proper subspace `U` of `ℚ³`, then there are at most `K (1 + log ε⁻¹)` of them.
First proved as Lemma 3.5 of Stephan's *The exponent `1/4` in three complexity bounds* (2026,
arXiv:2610.30937). -/
theorem card_mem_plane_le_log (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (hirr : Irrational ξ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (r t : ℕ → ℕ) (p : ℕ → ℤ),
      (∀ n, 2 * t n < t (n + 1)) → ∀ U : Submodule ℚ (Fin 3 → ℚ), U ≠ ⊤ → ∀ I : Finset ℕ,
      (∀ n ∈ I, r n < t n) → (∀ n ∈ I, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) →
      (∀ n ∈ I, |(p n : ℝ)| ≤ (b : ℝ) ^ t n) →
      (∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ 1) →
      (∀ n ∈ I, ε * t n < 4 * ((t n : ℝ) - r n)) →
      (∀ n ∈ I, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U) →
      (#I : ℝ) ≤ K * (1 + log ε⁻¹) := by
  classical
  obtain ⟨D, hD, hP⟩ := exists_mul_log_le_of_plane hb hξ hirr
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < log b := log_pos hbR
  have hlog2 : 1 / 2 ≤ log 2 := by have := log_two_gt_d9; linarith
  have hlog2' : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  -- the window of the case `z₃ ≠ 0`
  set R : ℝ := D * (2 + 2 * log b) / log b with hR
  have hR1 : 1 ≤ R := by
    rw [hR, le_div_iff₀ hlogb]; nlinarith
  have hK0 : 0 ≤ log R / log 2 := div_nonneg (log_nonneg hR1) (by linarith)
  refine ⟨log R / log 2 + 6, by linarith, fun ε hε hε1 r t p ht U hU I hrt hdvd hp happ hgap
    hmem ↦ ?_⟩
  have htm : StrictMono t := strictMono_nat_of_lt_succ fun n ↦ by have := ht n; omega
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg (one_le_inv₀ hε |>.mpr hε1)
  have hK : log R / log 2 + 6 ≤ (log R / log 2 + 6) * (1 + log ε⁻¹) := by nlinarith
  by_cases hI : #I ≤ 1
  · have : (#I : ℝ) ≤ 1 := by exact_mod_cast hI
    linarith
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
  obtain ⟨z, hzZ, hz12, hpl⟩ := exists_plane_eq hb hU ht12 (hrt i₁ hi₁) (hrt i₂ hi₂) (hp i₁ hi₁)
    (hp i₂ hi₂) (hdvd i₂ hi₂) (hmem i₁ hi₁) (hmem i₂ hi₂)
  have hplane : ∀ n ∈ I, z 0 * (b : ℤ) ^ t n + z 1 * (b : ℤ) ^ r n + z 2 * p n = 0 :=
    fun n hn ↦ hpl (r n) (t n) (p n) (hmem n hn)
  by_cases hz2 : z 2 = 0
  · -- `z₃ = 0`: the gap is the same at all points, so they lie in a window of ratio `4 / ε`
    have hz1 : z 1 ≠ 0 := hz12.resolve_right (not_not.mpr hz2)
    have hgapeq : ∀ n ∈ I, (t n : ℝ) - r n = t i₁ - r i₁ := by
      intro n hn
      have e1 := hplane n hn
      have e2 := hplane i₁ hi₁
      rw [hz2, zero_mul, add_zero] at e1 e2
      have hz0 : z 0 ≠ 0 := by
        intro h0
        rw [h0, zero_mul, zero_add] at e1
        exact hz1 ((mul_eq_zero.mp e1).resolve_right
          (pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))))
      have h : (b : ℤ) ^ (t n + r i₁) = (b : ℤ) ^ (t i₁ + r n) := by
        apply mul_left_cancel₀ hz0
        rw [pow_add, pow_add]
        linear_combination (b : ℤ) ^ r i₁ * e1 - (b : ℤ) ^ r n * e2
      have h' : b ^ (t n + r i₁) = b ^ (t i₁ + r n) := by exact_mod_cast h
      have h'' := Nat.pow_right_injective hb h'
      have : (t n : ℝ) + r i₁ = t i₁ + r n := by exact_mod_cast h''
      linarith
    have hwin : ∀ n ∈ I, i₁ ≤ n ∧ (t n : ℝ) ≤ 4 * ε⁻¹ * t i₁ := by
      intro n hn
      refine ⟨min'_le _ _ hn, ?_⟩
      have h1 := hgap n hn
      rw [hgapeq n hn] at h1
      have hr : (0 : ℝ) ≤ r i₁ := Nat.cast_nonneg _
      calc (t n : ℝ) = ε⁻¹ * (ε * t n) := by field_simp
        _ ≤ ε⁻¹ * (4 * t i₁) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hε.le)
        _ = 4 * ε⁻¹ * t i₁ := by ring
    have ht1 : 0 < t i₁ := by have := hrt i₁ hi₁; omega
    have hJ := Nat.card_le_of_doubling_window ht ht1
      (by have := one_le_inv₀ hε |>.mpr hε1; linarith) hwin
    have h4 : log (4 * ε⁻¹) = 2 * log 2 + log ε⁻¹ := by
      rw [log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      push_cast; ring
    rw [h4, add_div, mul_div_assoc, div_self (by linarith : log 2 ≠ 0)] at hJ
    have h5 : log ε⁻¹ / log 2 ≤ 2 * log ε⁻¹ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  · -- `z₃ ≠ 0`: the points lie in the window `t ≤ R t_{i₂}` of `i₂`
    set Z : ℝ := 2 * ((b : ℝ) ^ t i₂) ^ 2 with hZ
    have hM1 : (1 : ℝ) ≤ (b : ℝ) ^ t i₂ := one_le_pow₀ hbR.le
    have hZ1 : 1 ≤ Z := by nlinarith
    have hlogZ : log Z = log 2 + 2 * (t i₂ * log b) := by
      rw [hZ, log_mul (by norm_num) (by positivity), log_pow, log_pow]; ring
    have ht2 : (1 : ℝ) ≤ t i₂ := by exact_mod_cast (show 1 ≤ t i₂ by omega)
    have hwin : ∀ n ∈ I.erase i₁, i₂ ≤ n ∧ (t n : ℝ) ≤ R * t i₂ := by
      intro n hn
      have hnI := mem_of_mem_erase hn
      refine ⟨hge n hnI (ne_of_mem_erase hn), ?_⟩
      have h := hP z Z hZ1 hzZ hz2 (r n) (t n) (p n) (hrt n hnI) (hplane n hnI) (happ n hnI)
      rw [hlogZ] at h
      rw [hR, div_mul_eq_mul_div, le_div_iff₀ hlogb]
      have : D * (1 + (log 2 + 2 * (t i₂ * log b))) ≤ D * (2 + 2 * log b) * t i₂ := by
        rw [mul_assoc]
        gcongr
        nlinarith
      linarith
    have hJ := Nat.card_le_of_doubling_window ht (by omega) hR1 hwin
    have hc : (#I : ℝ) = #(I.erase i₁) + 1 := by
      rw [card_erase_of_mem hi₁]
      have : 1 ≤ #I := by omega
      push_cast [Nat.cast_sub this]
      ring
    linarith

end Real
