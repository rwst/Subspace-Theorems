/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.Additions.PlaneLiouville
public import BugeaudEvertse2008.Additions.SmallGap
public import BugeaudEvertse2008.Repetitions

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import QuantitativeSubspace.RealFormInterval

/-!
# Bugeaud–Evertse 2008, Theorem 2.1, with `1/3`

The count of `BugeaudEvertse2008/Additions/Theorem21Quarter.lean` with the interval form of the
quantitative Subspace Theorem (`Real.SubspaceIntervalWith`). In each of the `k ≈ 2/ε` classes of
`r/t` the points `(b^t, b^r, p)` lie in one plane, or have `t log b` in one of
`K ε⁻² (1 + log ε⁻¹)` intervals `[s, K ε⁻¹ s)` (`Real.exists_plane_intervals_of_approx`); the
points `(b^t - b^r, p)` of the small gaps lie on one line or in `K ε⁻² (1 + log ε⁻¹)` such
intervals (`Real.exists_line_intervals_of_small_gap`). The exponents `t_n` double, so an interval
holds `O(log (K ε⁻¹))` of them (`Real.card_le_of_forall_mem_window`); a plane holds
`O(1 + log ε⁻¹)` points with a large gap (`Real.card_mem_plane_le_log`), and the line at most one
point with a small gap (`Int.dvd_of_pow_sub_pow_mul_eq`). Hence
`N ≤ A ε⁻³ (1 + log ε⁻¹)²` (`Real.card_le_of_approx_third`), which contradicts `3 v < 1`.

## Main results

* `Real.exists_plane_intervals_of_approx`: the three-variable step, interval form.
* `Real.exists_line_intervals_of_small_gap`: the two-variable step, interval form.
* `Real.card_le_of_approx_third`: the count of the points.
* `Real.frequently_lt_complexity_of_lt_third`: **Theorem 2.1** with `η < 1/3`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Theorem 2.1 and §7; J.-H. Evertse, R. G. Ferretti, *A further
improvement of the quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590,
Theorem 3.3.
-/

@[expose] public section

open Filter Finset

namespace Real

variable {b : ℕ}

/-- **The three-variable step, interval form.** For `ξ` real algebraic and `b ≥ 2` there is
`K ≥ 1` such that for `0 < ε ≤ 1` there are at most `3 ε⁻¹` proper subspaces of `ℚ³` and at
most `K ε⁻³ (1 + log ε⁻¹)` reals `s` such that every point `(b^t, b^r, p)` with `r < t`,
`|p| ≤ b^t`, `|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}` and `K ε⁻¹ ≤ t log b` lies in one of the subspaces
or has `s ≤ t log b < K ε⁻¹ s` for one of the reals. -/
theorem exists_plane_intervals_of_approx (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)), (#T : ℝ) ≤ 3 * ε⁻¹ ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ∧
      ∀ (r t : ℕ) (p : ℤ), r < t → |(p : ℝ)| ≤ (b : ℝ) ^ t →
        |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε) → K * ε⁻¹ ≤ t * log b →
        (∃ U ∈ T, ![(b : ℚ) ^ t, (b : ℚ) ^ r, (p : ℚ)] ∈ U) ∨
          ∃ s ∈ 𝒯, s ≤ t * log b ∧ t * log b < K * ε⁻¹ * s := by
  classical
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceIntervalAt_of_isAlgebraic hξ (basePrimes b) 3 (by norm_num)
    (by norm_num)
  refine ⟨24 * K₀, by linarith, fun ε hε hε1 ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  -- the classes and the weight `δ = ε - 1/k`
  set k : ℕ := ⌊2 / ε⌋₊ + 1 with hk
  have hk2 : 2 / ε < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hk3 : (k : ℝ) ≤ 3 * ε⁻¹ := by
    have : (⌊2 / ε⌋₊ : ℝ) ≤ 2 / ε := Nat.floor_le (by positivity)
    rw [hk]; push_cast; rw [div_eq_mul_inv] at *; linarith
  have hkpos : (0 : ℝ) < k := by positivity
  set δ := ε - 1 / k with hδ
  have hkε : 1 / k < ε / 2 := by
    rw [div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hε] at hk2
    linarith
  have hδ0 : ε / 2 ≤ δ := by rw [hδ]; linarith
  have hδpos : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; have : 0 < 1 / (k : ℝ) := by positivity
                         linarith
  have hδinv : δ⁻¹ ≤ 2 * ε⁻¹ := by
    calc δ⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hδ0
      _ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
  have hclass := fun ℓ (hℓ : ℓ < k) ↦ by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := approx_class_hyps hb hε hk2 hℓ
    exact hBE approxForms 1 le_rfl abs_approxForms_le 1 one_pos le_rfl
      (one_le_abs_det_approxForms ξ) 1 le_rfl (approxExp ε k ℓ) (approxPadic b k ℓ) δ hδpos hδ1
      h1 h2 h3 h4 h5 h6
  choose! U hUtop 𝒯 h𝒯card hmem using hclass
  refine ⟨(range k).image U, ?_, ?_, (range k).biUnion 𝒯, ?_, ?_⟩
  · calc (#((range k).image U) : ℝ) ≤ k := by exact_mod_cast card_image_le.trans (card_range k).le
      _ ≤ 3 * ε⁻¹ := hk3
  · intro W hW
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hW
    exact hUtop ℓ (mem_range.mp hℓ)
  · -- the count
    have hlogδ : 1 + log δ⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      have : log δ⁻¹ ≤ log (2 * ε⁻¹) := log_le_log (by positivity) hδinv
      rw [log_mul (by norm_num) (by positivity)] at this
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have := log_nonneg hεinv
      linarith
    have hlogδ0 : 0 ≤ 1 + log δ⁻¹ := by have := log_nonneg hδinv1; linarith
    calc (#((range k).biUnion 𝒯) : ℝ) ≤ ∑ ℓ ∈ range k, (#(𝒯 ℓ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _ℓ ∈ range k, K₀ * δ⁻¹ ^ 2 * (1 + log δ⁻¹) :=
          sum_le_sum fun ℓ hℓ ↦ h𝒯card ℓ (mem_range.mp hℓ)
      _ = k * (K₀ * δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ (3 * ε⁻¹) * (K₀ * (2 * ε⁻¹) ^ 2 * (2 * (1 + log ε⁻¹))) := by gcongr
      _ = 24 * K₀ * ε⁻¹ ^ 3 * (1 + log ε⁻¹) := by ring
  · intro r t p hrt hp happ hthr
    obtain ⟨hℓk, hx0, hinf, hpad, hX⟩ := approx_class_mem hb (by exact_mod_cast hkpos) hrt hp happ
    have hlog : log (⨆ k, |(approxPoint b r t p k : ℝ)|) = t * log b := by rw [hX, log_pow]
    have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log (1 : ℝ)⁻¹) ≤
        log (⨆ k, |(approxPoint b r t p k : ℝ)|) := by
      rw [hlog]
      simp only [log_one, inv_one, add_zero, mul_one]
      calc K₀ * δ⁻¹ ≤ K₀ * (2 * ε⁻¹) := by gcongr
        _ ≤ 24 * K₀ * ε⁻¹ := by
            have : 0 ≤ K₀ * ε⁻¹ := by positivity
            linarith
        _ ≤ t * log b := hthr
    rcases hmem _ hℓk _ hx0 hinf hpad hthr' with hU | ⟨s, hs, h1, h2⟩
    · exact .inl ⟨_, mem_image_of_mem _ (mem_range.mpr hℓk), cast_approxPoint b r t p ▸ hU⟩
    refine .inr ⟨s, mem_biUnion.mpr ⟨_, mem_range.mpr hℓk, hs⟩, hlog ▸ h1, ?_⟩
    rw [hlog] at h2
    have hc0 : 0 ≤ (t : ℝ) * log b := by have := log_pos hbR; positivity
    have hs0 : 0 ≤ s := by
      by_contra hs0
      push Not at hs0
      nlinarith [mul_pos (by positivity : (0 : ℝ) < K₀) (inv_pos.2 hδpos)]
    calc (t : ℝ) * log b < K₀ * δ⁻¹ * s := h2
      _ ≤ K₀ * (2 * ε⁻¹) * s := by gcongr
      _ ≤ 24 * K₀ * ε⁻¹ * s := by
          have : 0 ≤ K₀ * ε⁻¹ * s := by positivity
          linarith

/-- **The two-variable step for small gaps, interval form.** For `ξ` real algebraic and `b ≥ 2`
there is `K ≥ 1` such that for `0 < ε ≤ 1` there are a proper subspace `U` of `ℚ²` and at most
`K ε⁻² (1 + log ε⁻¹)` reals `s` such that every point `(b^t - b^r, p)` with `r < t`,
`|p| ≤ b^t`, `|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}`, a small gap `4 (t - r) ≤ ε t` and
`K ε⁻¹ ≤ t log b` lies in `U` or has `s ≤ t log b < K ε⁻¹ s` for one of the reals. -/
theorem exists_line_intervals_of_small_gap (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ U : Submodule ℚ (Fin 2 → ℚ), U ≠ ⊤ ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) ∧
      ∀ (r t : ℕ) (p : ℤ), r < t → |(p : ℝ)| ≤ (b : ℝ) ^ t →
        |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε) → 4 * ((t : ℝ) - r) ≤ ε * t →
        K * ε⁻¹ ≤ t * log b →
        ![(b : ℚ) ^ t - (b : ℚ) ^ r, (p : ℚ)] ∈ U ∨
          ∃ s ∈ 𝒯, s ≤ t * log b ∧ t * log b < K * ε⁻¹ * s := by
  classical
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceIntervalAt_of_isAlgebraic hξ (basePrimes b) 2 le_rfl
    (by norm_num)
  refine ⟨8 * K₀, by linarith, fun ε hε hε1 ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < log b := log_pos hbR
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
  have hlog2 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hδinv : δ⁻¹ = 2 * ε⁻¹ := by rw [hδ, inv_div, div_eq_mul_inv]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gap_hyps hb hε hε1
  obtain ⟨U, hU, 𝒯, h𝒯card, hmem⟩ := hBE gapForms 1 le_rfl abs_gapForms_le 1 one_pos le_rfl
    (one_le_abs_det_gapForms ξ) 1 le_rfl (gapExp ε) (gapPadic b ε) δ hδ0 hδ1 h1 h2 h3 h4 h5 h6
  refine ⟨U, hU, 𝒯, ?_, fun r t p hrt hp happ hgap hthr ↦ ?_⟩
  · -- `K₀ (2 ε⁻¹)² (1 + log 2 + log ε⁻¹) ≤ 8 K₀ ε⁻² (1 + log ε⁻¹)`
    refine h𝒯card.trans ?_
    rw [hδinv, log_mul (by norm_num) (by positivity)]
    calc K₀ * (2 * ε⁻¹) ^ 2 * (1 + (log 2 + log ε⁻¹))
        ≤ K₀ * (2 * ε⁻¹) ^ 2 * (2 * (1 + log ε⁻¹)) := by gcongr; linarith
      _ = 8 * K₀ * ε⁻¹ ^ 2 * (1 + log ε⁻¹) := by ring
  obtain ⟨hx0, hinf, hpad, hX', hX, hbr⟩ := gap_mem hb hε hε1 hrt hp happ hgap
  set X := ⨆ i, |(gapPoint b r t p i : ℝ)| with hXdef
  have hbr0 : 0 < (b : ℝ) ^ r := by positivity
  have hX0 : 0 < X := by linarith
  have hlogX : t * log b - log 2 ≤ log X := by
    have h := log_le_log (by positivity) (show (b : ℝ) ^ t / 2 ≤ X by linarith)
    rwa [log_div (by positivity) (by norm_num), log_pow] at h
  have hlogX' : log X ≤ t * log b := by
    have h := log_le_log hX0 hX
    rwa [log_pow] at h
  have hKε : 1 ≤ K₀ * ε⁻¹ := one_le_mul_of_one_le_of_one_le hK₀ hεinv
  have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log 1⁻¹) ≤ log X := by
    simp only [log_one, inv_one, add_zero, mul_one]
    rw [hδinv]
    linarith
  rcases hmem _ hx0 hinf hpad hthr' with hxU | ⟨s, hs, hs1, hs2⟩
  · exact .inl (cast_gapPoint b r t p ▸ hxU)
  refine .inr ⟨s, hs, hs1.trans hlogX', ?_⟩
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    nlinarith [mul_pos (by positivity : (0 : ℝ) < K₀) (inv_pos.2 hδ0)]
  -- `t log b ≤ log X + log 2 < 2 K₀ δ⁻¹ s`
  have hbig : log 2 ≤ K₀ * δ⁻¹ * s := by linarith
  calc (t : ℝ) * log b ≤ log X + log 2 := by linarith
    _ < 2 * (K₀ * δ⁻¹ * s) := by linarith
    _ = 4 * K₀ * ε⁻¹ * s := by rw [hδinv]; ring
    _ ≤ 8 * K₀ * ε⁻¹ * s := by
        have : 0 ≤ K₀ * ε⁻¹ * s := by positivity
        linarith

/-- **The count of the points** (Bugeaud–Evertse 2008, §7, interval form). For `ξ` real algebraic
irrational and `b ≥ 2` there is `A > 0` such that for `0 < ε ≤ 1`, every doubling sequence
`2 t_n < t_{n+1}` and every finite set `I` of indices whose points `(b^{t_n}, b^{r_n}, p_n)` have
`r_n < t_n`, `b ∤ p_n` when `r_n ≥ 1`, `|p_n| ≤ b^{t_n}`,
`|b^{t_n} ξ - b^{r_n} ξ - p_n| ≤ (b^{t_n})^{-ε}` and `A ε⁻¹ ≤ t_n log b`,
`#I ≤ A ε⁻³ (1 + log ε⁻¹)²`. -/
theorem card_le_of_approx_third (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (r t : ℕ → ℕ) (p : ℕ → ℤ),
      (∀ n, r n < t n) → (∀ n, 2 * t n < t (n + 1)) → ∀ I : Finset ℕ,
      (∀ n ∈ I, r n < t n ∧ (1 ≤ r n → ¬ (b : ℤ) ∣ p n) ∧ |(p n : ℝ)| ≤ (b : ℝ) ^ t n ∧
        |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε) ∧
        A * ε⁻¹ ≤ t n * log b) →
      (#I : ℝ) ≤ A * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K₂, hK₂, hT⟩ := exists_plane_intervals_of_approx hb hξ
  obtain ⟨K₃, hK₃, hPl⟩ := card_mem_plane_le_log hb hξ hirr
  obtain ⟨K₄, hK₄, hL⟩ := exists_line_intervals_of_small_gap hb hξ
  have hlK₂ := log_nonneg hK₂
  have hlK₄ := log_nonneg hK₄
  set A : ℝ := 3 * K₃ + 1 + K₂ * (2 * log K₂ + 3) + K₄ * (2 * log K₄ + 3) with hAdef
  have hA2 : 0 ≤ K₂ * (2 * log K₂ + 3) ∧ 0 ≤ K₄ * (2 * log K₄ + 3) :=
    ⟨by positivity, by positivity⟩
  have hAK : K₂ ≤ A ∧ K₄ ≤ A := by
    have h2 : 3 * K₂ ≤ K₂ * (2 * log K₂ + 3) := by nlinarith
    have h4 : 3 * K₄ ≤ K₄ * (2 * log K₄ + 3) := by nlinarith
    constructor <;> linarith
  refine ⟨A, by linarith, fun ε hε hε1 r t p hrt hgap I hI ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < log b := log_pos hbR
  have hεi1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have htm : StrictMono t := strictMono_nat_of_lt_succ fun n ↦ by have := hgap n; omega
  obtain ⟨T, hTcard, hTtop, 𝒯, h𝒯card, hTmem⟩ := hT ε hε hε1
  obtain ⟨U', hU', 𝒯', h𝒯'card, hLmem⟩ := hL ε hε hε1
  have hthr : ∀ n ∈ I, ∀ K : ℝ, K ≤ A → K * ε⁻¹ ≤ t n * log b :=
    fun n hn K hK ↦ (mul_le_mul_of_nonneg_right hK (by positivity)).trans (hI n hn).2.2.2.2
  have happ1 : ∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ 1 := fun n hn ↦
    (hI n hn).2.2.2.1.trans
      (rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hbR.le) (by linarith))
  -- the heights `t_n log b` double
  set g : ℕ → ℝ := fun n ↦ (t n : ℝ) * log b with hg
  have hg0 : ∀ n, 0 < g n := fun n ↦ by
    have : 0 < t n := by have := hrt n; omega
    have : (0 : ℝ) < t n := by exact_mod_cast this
    positivity
  have hgq : ∀ n, 2 * g n ≤ g (n + 1) := fun n ↦ by
    have h : (2 * t n : ℝ) ≤ t (n + 1) := by exact_mod_cast (hgap n).le
    calc 2 * g n = (2 * t n : ℝ) * log b := by rw [hg]; ring
      _ ≤ (t (n + 1) : ℝ) * log b := mul_le_mul_of_nonneg_right h hlogb.le
  have hKX : ∀ K : ℝ, 1 ≤ K → 1 ≤ K * ε⁻¹ := fun K hK ↦ one_le_mul_of_one_le_of_one_le hK hεi1
  -- split by the size of the gap
  set big := I.filter fun n ↦ ε * t n < 4 * ((t n : ℝ) - r n) with hbig
  set small := I.filter fun n ↦ ¬ ε * t n < 4 * ((t n : ℝ) - r n) with hsmall
  have hsplit : (#I : ℝ) = #big + #small := by
    have h := card_filter_add_card_filter_not (s := I) fun n ↦ ε * t n < 4 * ((t n : ℝ) - r n)
    rw [hbig, hsmall]
    exact_mod_cast h.symm
  -- the large gaps: few planes with few points each, and few windows
  have hcases : ∀ n ∈ big,
      (∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U) ∨
        ∃ s ∈ 𝒯, s ≤ g n ∧ g n < K₂ * ε⁻¹ * s := by
    intro n hn
    have hnI := (mem_filter.mp hn).1
    obtain ⟨h1, -, h3, h4, -⟩ := hI n hnI
    exact hTmem _ _ _ h1 h3 h4 (hthr n hnI K₂ hAK.1)
  set big₁ := big.filter fun n ↦ ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U
    with hbig₁
  set big₂ := big.filter fun n ↦ ¬ ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U
    with hbig₂
  have hbigs : (#big : ℝ) = #big₁ + #big₂ := by
    have h := card_filter_add_card_filter_not (s := big)
      fun n ↦ ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  have hφ : ∀ n ∈ big₁, ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U :=
    fun n hn ↦ (mem_filter.mp hn).2
  choose! φ hφT hφU using hφ
  have hbig₁c : (#big₁ : ℝ) ≤ #T * (K₃ * (1 + log ε⁻¹)) := by
    have hsum := card_eq_sum_card_fiberwise (s := big₁) (t := T) (f := φ) hφT
    have hfib : ∀ U ∈ T, (#(big₁.filter fun n ↦ φ n = U) : ℝ) ≤ K₃ * (1 + log ε⁻¹) := by
      intro U hU
      have hmemI : ∀ n ∈ big₁.filter fun n ↦ φ n = U, n ∈ I := fun n hn ↦
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
      refine hPl ε hε hε1 r t p hgap U (hTtop U hU) _
        (fun n hn ↦ (hI n (hmemI n hn)).1) (fun n hn ↦ (hI n (hmemI n hn)).2.1)
        (fun n hn ↦ (hI n (hmemI n hn)).2.2.1) (fun n hn ↦ happ1 n (hmemI n hn))
        (fun n hn ↦ (mem_filter.mp (mem_filter.mp (mem_filter.mp hn).1).1).2) fun n hn ↦ ?_
      obtain ⟨hn, hφn⟩ := mem_filter.mp hn
      rw [← hφn]; exact hφU n hn
    calc (#big₁ : ℝ) = ∑ U ∈ T, (#(big₁.filter fun n ↦ φ n = U) : ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T, K₃ * (1 + log ε⁻¹) := sum_le_sum hfib
      _ = #T * (K₃ * (1 + log ε⁻¹)) := by rw [sum_const, nsmul_eq_mul]
  have hbig₂c : (#big₂ : ℝ) ≤ #𝒯 * (log (K₂ * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K₂ hK₂) 𝒯 fun n hn ↦ by
      obtain ⟨hnb, hn⟩ := mem_filter.mp hn
      exact (hcases n hnb).resolve_left hn
  -- the small gaps: one line with at most one point, and few windows
  have hcases' : ∀ n ∈ small,
      ![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)] ∈ U' ∨
        ∃ s ∈ 𝒯', s ≤ g n ∧ g n < K₄ * ε⁻¹ * s := by
    intro n hn
    obtain ⟨hnI, hns⟩ := mem_filter.mp hn
    obtain ⟨h1, -, h3, h4, -⟩ := hI n hnI
    exact hLmem _ _ _ h1 h3 h4 (not_lt.mp hns) (hthr n hnI K₄ hAK.2)
  set small₁ := small.filter fun n ↦ ![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)] ∈ U'
    with hsmall₁
  set small₂ := small.filter fun n ↦ ![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)] ∉ U'
    with hsmall₂
  have hsmalls : (#small : ℝ) = #small₁ + #small₂ := by
    have h := card_filter_add_card_filter_not (s := small)
      fun n ↦ ![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)] ∈ U'
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  have hsm : ∀ n ∈ small, 3 * t n ≤ 4 * r n := by
    intro n hn
    have h := not_lt.mp (mem_filter.mp hn).2
    have ht0 : (0 : ℝ) ≤ t n := Nat.cast_nonneg _
    have : (3 : ℝ) * t n ≤ 4 * r n := by nlinarith
    exact_mod_cast this
  have hsmall₁c : (#small₁ : ℝ) ≤ 1 := by
    have : #small₁ ≤ 1 := by
      refine card_le_one.2 fun n hn m hm ↦ ?_
      by_contra hne
      wlog hnm : n < m generalizing n m
      · exact this m hm n hn (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hnm) (Ne.symm hne))
      obtain ⟨hns, hnU⟩ := mem_filter.mp hn
      obtain ⟨hms, hmU⟩ := mem_filter.mp hm
      have hnI := (mem_filter.mp hns).1
      have hmI := (mem_filter.mp hms).1
      have h := Submodule.det_eq_zero_of_forall_mem hU'
        ![![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)], ![(b : ℚ) ^ t m - (b : ℚ) ^ r m, (p m : ℚ)]]
        (fun i ↦ by fin_cases i; exacts [hnU, hmU])
      rw [Matrix.det_fin_two] at h
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at h
      have h' : ((b : ℤ) ^ t n - (b : ℤ) ^ r n) * p m = ((b : ℤ) ^ t m - (b : ℤ) ^ r m) * p n := by
        have : ((b : ℚ) ^ t n - (b : ℚ) ^ r n) * p m = ((b : ℚ) ^ t m - (b : ℚ) ^ r m) * p n := by
          linear_combination h
        exact_mod_cast this
      have h1 : 2 * t n < t m := (hgap n).trans_le (htm.monotone hnm)
      have := hsm m hms
      have hrn := (hI n hnI).1
      have hrm := (hI m hmI).1
      have hr : r n < r m := by omega
      exact (hI m hmI).2.1 (by omega) (Int.dvd_of_pow_sub_pow_mul_eq
        (by exact_mod_cast (by omega : b ≠ 0)) hrn hr hrm.le h')
    exact_mod_cast this
  have hsmall₂c : (#small₂ : ℝ) ≤ #𝒯' * (log (K₄ * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K₄ hK₄) 𝒯' fun n hn ↦ by
      obtain ⟨hns, hn⟩ := mem_filter.mp hn
      exact (hcases' n hns).resolve_left hn
  -- the sum
  have hW₂ := log_div_log_two_le hK₂ hεi1
  have hW₄ := log_div_log_two_le hK₄ hεi1
  have hb₁ := hbig₁c
  have hb₂ := hbig₂c
  have hs₂ := hsmall₂c
  clear_value big₁ big₂ small₁ small₂ big small g
  clear hcases hcases' hφT hφU hbig₁c hbig₂c hsmall₂c hTmem hLmem
  set X := ε⁻¹ with hX
  set Λ := 1 + log ε⁻¹ with hΛ
  have hΛ1 : 1 ≤ Λ := by have := log_nonneg hεi1; rw [hΛ]; linarith
  set W₂ := log (K₂ * X) / log 2 + 1 with hW₂def
  set W₄ := log (K₄ * X) / log 2 + 1 with hW₄def
  have hW₂0 : 0 ≤ W₂ := by
    rw [hW₂def]
    have := log_nonneg (hKX K₂ hK₂)
    have : 0 < log (2 : ℝ) := log_pos (by norm_num)
    positivity
  have hW₄0 : 0 ≤ W₄ := by
    rw [hW₄def]
    have := log_nonneg (hKX K₄ hK₄)
    have : 0 < log (2 : ℝ) := log_pos (by norm_num)
    positivity
  clear_value X Λ W₂ W₄
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hεi1 (by norm_num)
  have hX3 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := pow_le_pow_right₀ hεi1 (by norm_num)
  have hΛ2 : Λ ≤ Λ ^ 2 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 2 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have h1 : 1 ≤ X ^ 3 * Λ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hεi1)
    (one_le_pow₀ hΛ1)
  have hc₁ : (#big₁ : ℝ) ≤ 3 * K₃ * (X ^ 3 * Λ ^ 2) := by
    calc (#big₁ : ℝ) ≤ #T * (K₃ * Λ) := hb₁
      _ ≤ 3 * X * (K₃ * Λ) := by gcongr
      _ = 3 * K₃ * (X * Λ) := by ring
      _ ≤ 3 * K₃ * (X ^ 3 * Λ ^ 2) := by gcongr
  have hc₂ : (#big₂ : ℝ) ≤ K₂ * (2 * log K₂ + 3) * (X ^ 3 * Λ ^ 2) := by
    calc (#big₂ : ℝ) ≤ #𝒯 * W₂ := hb₂
      _ ≤ K₂ * X ^ 3 * Λ * ((2 * log K₂ + 3) * Λ) := by gcongr
      _ = K₂ * (2 * log K₂ + 3) * (X ^ 3 * Λ ^ 2) := by ring
  have hc₄ : (#small₂ : ℝ) ≤ K₄ * (2 * log K₄ + 3) * (X ^ 3 * Λ ^ 2) := by
    have hK : 0 ≤ K₄ * Λ * ((2 * log K₄ + 3) * Λ) := by positivity
    calc (#small₂ : ℝ) ≤ #𝒯' * W₄ := hs₂
      _ ≤ K₄ * X ^ 2 * Λ * ((2 * log K₄ + 3) * Λ) := by gcongr
      _ = X ^ 2 * (K₄ * Λ * ((2 * log K₄ + 3) * Λ)) := by ring
      _ ≤ X ^ 3 * (K₄ * Λ * ((2 * log K₄ + 3) * Λ)) := mul_le_mul_of_nonneg_right hX23 hK
      _ = K₄ * (2 * log K₄ + 3) * (X ^ 3 * Λ ^ 2) := by ring
  have e : A * X ^ 3 * Λ ^ 2 = (3 * K₃ + 1 + K₂ * (2 * log K₂ + 3) + K₄ * (2 * log K₄ + 3)) *
      (X ^ 3 * Λ ^ 2) := by rw [hAdef]; ring
  rw [hsplit, hbigs, hsmalls, e]
  have hP : 0 ≤ X ^ 3 * Λ ^ 2 := by linarith
  nlinarith

/-- **Bugeaud–Evertse 2008, Theorem 2.1, with `1/3` in place of `1/11`.** If the base-`b` digits
`a` of a real algebraic irrational number are given, then for every `η < 1/3` and every `C` the
complexity exceeds `C n (log n)^η` for infinitely many `n`. -/
theorem frequently_lt_complexity_of_lt_third (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (ofDigits a)) (halg : IsAlgebraic ℚ (ofDigits a)) {η : ℝ} (hη : η < 1 / 3)
    (C : ℝ) : ∃ᶠ n : ℕ in atTop, C * n * log n ^ η < Function.complexity a n := by
  classical
  by_contra h
  rw [not_frequently] at h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  -- `p(n) ≤ c n (log n)^u` with `c = max C 1`, `u = max η 0`
  set u := max η 0 with hudef
  set c := max C 1 with hcdef
  have hu : 0 ≤ u := le_max_right _ _
  have hu3 : u < 1 / 3 := max_lt hη (by norm_num)
  have hp : ∀ n ≥ max n₀ 3, (Function.complexity a n : ℝ) ≤ c * n * log n ^ u := by
    intro n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hlog : 1 ≤ log n := by
      rw [le_log_iff_exp_le (by linarith)]
      have := exp_one_lt_d9
      linarith
    have h1 := not_lt.mp (hn₀ n ((le_max_left _ _).trans hn))
    have h2 : 0 ≤ (n : ℝ) * log n ^ η := by positivity
    calc (Function.complexity a n : ℝ) ≤ C * n * log n ^ η := h1
      _ = C * ((n : ℝ) * log n ^ η) := by ring
      _ ≤ c * ((n : ℝ) * log n ^ η) := by gcongr; exact le_max_left _ _
      _ ≤ c * ((n : ℝ) * log n ^ u) := by
          gcongr
          exact le_max_left _ _
      _ = c * n * log n ^ u := by ring
  -- `u < v < 1/3`
  set v := (u + 1 / 3) / 2 with hvdef
  have huv : u < v := by rw [hvdef]; linarith
  have hv : 0 < v := by linarith
  have hv3 : (3 : ℕ) * v < 1 := by push_cast; rw [hvdef]; linarith
  set ξ := ofDigits a with hξ
  obtain ⟨Cg, r, t, p, hrt, hgap, hbd, hdvd, hpb, happ⟩ :=
    exists_approx_of_complexity_le hb hu huv (max n₀ 3) hp
  obtain ⟨A, hA, hcnt⟩ := card_le_of_approx_third hb halg hirr
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  obtain ⟨N, hN⟩ := (eventually_doubling_thresholds 3 2 (by norm_num) (by norm_num) (C := Cg) hv
    hv3 hA (log_pos hbR)).exists
  obtain ⟨hε0, hε1, hεle, hthr, hcount⟩ := hN t hgap hbd
  set ε := log (t (2 * N)) ^ (-v) with hε
  -- the points `x_n`, `N ≤ n < 2N`
  have hI : ∀ n ∈ Ico N (2 * N), r n < t n ∧ (1 ≤ r n → ¬ (b : ℤ) ∣ p n) ∧
      |(p n : ℝ)| ≤ (b : ℝ) ^ t n ∧
      |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε) ∧
      A * ε⁻¹ ≤ t n * log b := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    refine ⟨hrt n, hdvd n, hpb n, ?_, hthr n hn1⟩
    refine (happ n).trans (rpow_le_rpow_of_exponent_le (one_le_pow₀ hbR.le) ?_)
    exact neg_le_neg (hεle n hn1 hn2.le)
  have hfin := hcnt ε hε0 hε1 r t p hrt hgap _ hI
  rw [Nat.card_Ico, show 2 * N - N = N by omega] at hfin
  linarith

end Real
