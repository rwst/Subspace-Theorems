/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.Problems
public import Stephan2026a.QuantitativeLines

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import Mathlib.Analysis.Complex.ExponentialBounds
import QuantitativeSubspace.RealFormInterval
import Stephan2026a.QuantitativePlaneStep
import Stephan2026a.QuantitativeViolators

/-!
# Problem 5.2 for every `η < 1/3`

The count of `Stephan2026a/QuantitativeTheorem.lean` with the interval form of the quantitative
Subspace Theorem (`Real.SubspaceIntervalWith`) in place of the count of subspaces. In each of the
`k ≈ 2/ε` classes of the gap the kernel points lie in one plane, or have `c log 3` in one of
`K ε⁻² (1 + log ε⁻¹)` intervals `[s, K ε⁻¹ s)`
(`SteeringWord.exists_plane_intervals_of_violators`); the line points of the small gaps lie on
one line or in `K ε⁻² (1 + log ε⁻¹)` such intervals
(`SteeringWord.exists_line_intervals_of_violators`). The positions `c = τ_n + 2` of a doubling
sequence grow by a factor `3/2`, so an interval holds `O(log (K ε⁻¹))` of them
(`Real.card_le_of_forall_mem_window`), and

```text
N ≤ 3 ε⁻¹ · 12 (1 + log ε⁻¹) + K ε⁻³ (1 + log ε⁻¹) · O(1 + log ε⁻¹) + 3 + O(ε⁻² (1 + log ε⁻¹)²),
```

which is `N^{3 v + o(1)}` and contradicts `3 v < 1`. The exponent drops from `1/(1 + 3)` to
`1/(1 + 2)`: Evertse–Ferretti's `δ⁻³` is `δ⁻²` intervals times `δ⁻¹` windows of the gap
principle in each, and points of geometrically growing height need no gap principle.

## Main results

* `SteeringWord.exists_plane_intervals_of_violators`: the three-variable step, interval form.
* `SteeringWord.exists_line_intervals_of_violators`: the two-variable step, interval form.
* `SteeringWord.frequently_lt_complexity_third`: for every `η < 1/3` and `C`,
  `p_T(k) > C k (log k)^η` for infinitely many `k`.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, Problem 5.2;
Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7; J.-H. Evertse, R. G. Ferretti, *A further improvement of the
quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590, Theorem 3.3.

R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the exponent `1/2` in
three complexity bounds* (2026), Remark 8.1.
-/

@[expose] public section

open Filter Finset Real Function

namespace SteeringWord

/-- `log` of a positive integer power of `3`. -/
theorem log_iSup_abs_kernelPoint {a c : ℕ} (ha : 2 ≤ a) (hac : a < c) :
    log (⨆ k, |(kernelPoint a c k : ℝ)|) = c * log 3 := by
  rw [iSup_abs_kernelPoint ha hac, log_pow]

/-- **The three-variable step, interval form.** There is `K ≥ 1` such that for `0 < ε ≤ 1`
there are at most `3 ε⁻¹` proper subspaces of `ℚ³` (one per class of the gap) and at most
`K ε⁻³ (1 + log ε⁻¹)` reals `s` such that the kernel point of every pair `2 ≤ a < c` with
`|ε_c - ε_a| ≤ (3^c)^{-ε}` and `K ε⁻¹ ≤ c log 3` lies in one of the subspaces or has
`s ≤ c log 3 < K ε⁻¹ s` for one of the reals. -/
theorem exists_plane_intervals_of_violators :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)), (#T : ℝ) ≤ 3 * ε⁻¹ ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ∧
      ∀ a c : ℕ, 2 ≤ a → a < c → |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) →
        K * ε⁻¹ ≤ c * log 3 →
        (∃ U ∈ T, (fun i ↦ (kernelPoint a c i : ℚ)) ∈ U) ∨
          ∃ s ∈ 𝒯, s ≤ c * log 3 ∧ c * log 3 < K * ε⁻¹ * s := by
  classical
  set S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} with hS
  set K₀ := intervalConst 3 1 #S 0 (log 2 + ∑ l ∈ S, log (l : ℕ)) with hK₀def
  have hBE : SubspaceIntervalWith 0 S 3 K₀ :=
    subspaceIntervalWith_zero S (by norm_num) (by norm_num)
  have hK₀ : 1 ≤ K₀ := one_le_intervalConst ..
  refine ⟨24 * K₀, by linarith, fun ε hε hε1 ↦ ?_⟩
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
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  have hδinv : δ⁻¹ ≤ 2 * ε⁻¹ := by
    calc δ⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hδ0
      _ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
  have hclass := fun ℓ (hℓ : ℓ < k) ↦ by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kernel_class_hyps hε hk2 hℓ
    exact hBE kernelForms 1 le_rfl abs_kernelForms_le 1 one_pos le_rfl one_le_abs_det_kernelForms
      1 le_rfl (kernelExp ε k ℓ) (kernelPadic k ℓ) δ hδpos hδ1 h1 h2 h3 h4 h5 h6
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
  · intro a c ha hac happ hthr
    obtain ⟨hℓk, hx0, hinf, hpad⟩ := kernel_class_mem (by exact_mod_cast hkpos) ha hac happ
    have hlog := log_iSup_abs_kernelPoint ha hac
    have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log (1 : ℝ)⁻¹) ≤
        log (⨆ k, |(kernelPoint a c k : ℝ)|) := by
      rw [hlog]
      simp only [log_one, inv_one, add_zero, mul_one]
      calc K₀ * δ⁻¹ ≤ K₀ * (2 * ε⁻¹) := by gcongr
        _ ≤ 24 * K₀ * ε⁻¹ := by
            have : 0 ≤ K₀ * ε⁻¹ := by positivity
            linarith
        _ ≤ c * log 3 := hthr
    rcases hmem _ hℓk _ hx0 hinf hpad hthr' with hU | ⟨s, hs, h1, h2⟩
    · exact .inl ⟨_, mem_image_of_mem _ (mem_range.mpr hℓk), hU⟩
    refine .inr ⟨s, mem_biUnion.mpr ⟨_, mem_range.mpr hℓk, hs⟩, hlog ▸ h1, ?_⟩
    rw [hlog] at h2
    have hc0 : 0 ≤ (c : ℝ) * log 3 := by positivity
    have hs0 : 0 ≤ s := by
      by_contra hs0
      push Not at hs0
      nlinarith [mul_pos (by positivity : (0 : ℝ) < K₀) (inv_pos.2 hδpos)]
    calc (c : ℝ) * log 3 < K₀ * δ⁻¹ * s := h2
      _ ≤ K₀ * (2 * ε⁻¹) * s := by gcongr
      _ ≤ 24 * K₀ * ε⁻¹ * s := by
          have : 0 ≤ K₀ * ε⁻¹ * s := by positivity
          linarith

/-- **The two-variable step, interval form.** There is `K ≥ 1` such that for `0 < ε ≤ 1`
there are a proper subspace `U` of `ℚ²` and at most `K ε⁻² (1 + log ε⁻¹)` reals `s` such that
the line point of every pair `2 ≤ a < c` with `|ε_c - ε_a| ≤ (3^c)^{-ε}`, a small gap
`c - a ≤ ε c / 4` and `K ε⁻¹ ≤ c log 3` lies in `U` or has `s ≤ c log 3 < K ε⁻¹ s` for one of
the reals. -/
theorem exists_line_intervals_of_violators :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ U : Submodule ℚ (Fin 2 → ℚ), U ≠ ⊤ ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) ∧
      ∀ a c : ℕ, 2 ≤ a → a < c → |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) →
        ((c - a : ℕ) : ℝ) ≤ ε / 4 * c → K * ε⁻¹ ≤ c * log 3 →
        (fun i ↦ (linePoint a c i : ℚ)) ∈ U ∨
          ∃ s ∈ 𝒯, s ≤ c * log 3 ∧ c * log 3 < K * ε⁻¹ * s := by
  classical
  set S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} with hS
  set K₀ := intervalConst 2 1 #S 0 (log 2 + ∑ l ∈ S, log (l : ℕ)) with hK₀def
  have hBE : SubspaceIntervalWith 0 S 2 K₀ := subspaceIntervalWith_zero S le_rfl (by norm_num)
  have hK₀ : 1 ≤ K₀ := one_le_intervalConst ..
  refine ⟨8 * K₀, by linarith, fun ε hε hε1 ↦ ?_⟩
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  set δ := 3 * ε / 4 with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hδ' : δ⁻¹ = 4 / 3 * ε⁻¹ := by rw [hδ]; field_simp
  have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := line_hyps hε hε1
  obtain ⟨U, hU, 𝒯, h𝒯card, hmem⟩ := hBE lineForms 1 le_rfl abs_lineForms_le 1 one_pos le_rfl
    one_le_abs_det_lineForms 3 (by norm_num) (lineExp ε) (linePadic ε) δ hδpos hδ1 h1 h2 h3 h4
    h5 h6
  have hl3 : log 3 ≤ 2 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  refine ⟨U, hU, 𝒯, ?_, fun a c ha hac happ hgap hthr ↦ ?_⟩
  · -- the count
    have hlogδ : 1 + log δ⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      rw [hδ', log_mul (by norm_num) (by positivity)]
      have : log (4 / 3 : ℝ) ≤ 1 := by
        have := log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
        linarith
      have := log_nonneg hεinv
      linarith
    refine h𝒯card.trans ?_
    calc K₀ * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ≤ K₀ * (4 / 3 * ε⁻¹) ^ 2 * (2 * (1 + log ε⁻¹)) := by
          rw [← hδ']; gcongr
      _ ≤ 8 * K₀ * ε⁻¹ ^ 2 * (1 + log ε⁻¹) := by
          have : 0 ≤ K₀ * ε⁻¹ ^ 2 * (1 + log ε⁻¹) := by
            have := log_nonneg hεinv
            positivity
          nlinarith
  obtain ⟨hy0, hinf, hpad, hlogY, hlogY'⟩ := line_mem hε hε1 ha hac happ hgap
  have hl30 : 0 < log 3 := log_pos (by norm_num)
  have hKε : 1 ≤ K₀ * ε⁻¹ := one_le_mul_of_one_le_of_one_le hK₀ hεinv
  have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 3 + log (1 : ℝ)⁻¹) ≤
      log (⨆ k, |(linePoint a c k : ℝ)|) := by
    simp only [log_one, inv_one, add_zero]
    rw [hδ']
    nlinarith
  rcases hmem _ hy0 hinf hpad hthr' with hU | ⟨s, hs, hs1, hs2⟩
  · exact .inl hU
  refine .inr ⟨s, hs, hs1.trans hlogY', ?_⟩
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    nlinarith [mul_pos (by positivity : (0 : ℝ) < K₀) (inv_pos.2 hδpos)]
  -- `c log 3 ≤ log Y + log 3 < 2 K₀ δ⁻¹ s`
  have hbig : 2 * log 3 ≤ K₀ * δ⁻¹ * s := by nlinarith
  calc (c : ℝ) * log 3 ≤ log (⨆ k, |(linePoint a c k : ℝ)|) + log 3 := by linarith
    _ < 2 * (K₀ * δ⁻¹ * s) := by linarith
    _ = 8 / 3 * K₀ * ε⁻¹ * s := by rw [hδ']; ring
    _ ≤ 8 * K₀ * ε⁻¹ * s := by
        have : 0 ≤ K₀ * ε⁻¹ * s := by positivity
        linarith

/-- `log (3/2) ≥ 1/3`, since `e < (3/2)^3`. -/
theorem third_le_log_three_halves : 1 / 3 ≤ log (3 / 2 : ℝ) := by
  rw [le_log_iff_exp_le (by norm_num)]
  by_contra hc
  push Not at hc
  have h3 : (3 / 2 : ℝ) ^ 3 < exp (1 / 3) ^ 3 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
  rw [← exp_nat_mul] at h3
  norm_num at h3
  linarith [exp_one_lt_d9]

/-- **The window factor**: `log (K X) / log (3/2) + 1 ≤ (3 log K + 4) (1 + log X)` for
`K, X ≥ 1`. -/
theorem log_div_log_three_halves_le {K X : ℝ} (hK : 1 ≤ K) (hX : 1 ≤ X) :
    log (K * X) / log (3 / 2) + 1 ≤ (3 * log K + 4) * (1 + log X) := by
  have hlK := log_nonneg hK
  have hlX := log_nonneg hX
  have hq := third_le_log_three_halves
  have hq0 : 0 < log (3 / 2 : ℝ) := by linarith
  rw [log_mul (by linarith) (by linarith)]
  have : (log K + log X) / log (3 / 2) ≤ 3 * (log K + log X) := by
    rw [div_le_iff₀ hq0]
    nlinarith
  nlinarith [mul_nonneg hlK hlX]

/-- **The count of the violators** (Problem 5.2, steps 2–4, interval form). There is `A > 0` such
that for `0 < ε ≤ 1`, every doubling sequence `2 τ_n < τ_{n+1}` with `r_n < τ_n`, and every
finite set `I` of indices whose pairs `(r_n + 2, τ_n + 2)` are kernel violators
`|ε_c - ε_a| ≤ (3^c)^{-ε}` with `A ε⁻¹ ≤ c log 3`, `#I ≤ A ε⁻³ (1 + log ε⁻¹)²`. -/
theorem card_le_of_violators_third :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ r τ : ℕ → ℕ, (∀ n, r n < τ n) →
      (∀ n, 2 * τ n < τ (n + 1)) → ∀ I : Finset ℕ,
      (∀ n ∈ I, |(eps (τ n + 2) : ℝ) - eps (r n + 2)| ≤ ((3 : ℝ) ^ (τ n + 2)) ^ (-ε) ∧
        A * ε⁻¹ ≤ ((τ n + 2 : ℕ) : ℝ) * log 3) →
      (#I : ℝ) ≤ A * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K₂, hK₂, hT⟩ := exists_plane_intervals_of_violators
  obtain ⟨K₄, hK₄, hL⟩ := exists_line_intervals_of_violators
  have hlK₂ := log_nonneg hK₂
  have hlK₄ := log_nonneg hK₄
  set A : ℝ := 39 + K₂ * (3 * log K₂ + 4) + K₄ * (3 * log K₄ + 4) with hAdef
  have hA2 : 0 ≤ K₂ * (3 * log K₂ + 4) ∧ 0 ≤ K₄ * (3 * log K₄ + 4) :=
    ⟨by positivity, by positivity⟩
  have hAK : K₂ ≤ A ∧ K₄ ≤ A := by
    have h2 : 4 * K₂ ≤ K₂ * (3 * log K₂ + 4) := by nlinarith
    have h4 : 4 * K₄ ≤ K₄ * (3 * log K₄ + 4) := by nlinarith
    constructor <;> linarith
  refine ⟨A, by linarith, fun ε hε hε1 r τ hrτ hgap I hI ↦ ?_⟩
  have hεi1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  obtain ⟨T, hTcard, hTtop, 𝒯, h𝒯card, hTmem⟩ := hT ε hε hε1
  obtain ⟨U', hU', 𝒯', h𝒯'card, hLmem⟩ := hL ε hε hε1
  have hthr : ∀ n ∈ I, ∀ K : ℝ, K ≤ A → K * ε⁻¹ ≤ ((τ n + 2 : ℕ) : ℝ) * log 3 :=
    fun n hn K hK ↦ (mul_le_mul_of_nonneg_right hK (by positivity)).trans (hI n hn).2
  -- the heights `c_n log 3`, `c_n = τ_n + 2`, grow by a factor `3/2`
  set g : ℕ → ℝ := fun n ↦ ((τ n + 2 : ℕ) : ℝ) * log 3 with hg
  have hg0 : ∀ n, 0 < g n := fun n ↦ by
    have := log_pos (by norm_num : (1 : ℝ) < 3)
    positivity
  have hgq : ∀ n, 3 / 2 * g n ≤ g (n + 1) := fun n ↦ by
    have h : 2 * τ n + 1 ≤ τ (n + 1) := hgap n
    have h' : (2 * τ n + 1 : ℝ) ≤ τ (n + 1) := by exact_mod_cast h
    have hτ0 : (0 : ℝ) ≤ τ n := Nat.cast_nonneg _
    have hc : 3 / 2 * (((τ n + 2 : ℕ) : ℝ)) ≤ ((τ (n + 1) + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    calc 3 / 2 * g n = 3 / 2 * (((τ n + 2 : ℕ) : ℝ)) * log 3 := by rw [hg, mul_assoc]
      _ ≤ ((τ (n + 1) + 2 : ℕ) : ℝ) * log 3 :=
          mul_le_mul_of_nonneg_right hc (log_pos (by norm_num : (1 : ℝ) < 3)).le
  have hKX : ∀ K : ℝ, 1 ≤ K → 1 ≤ K * ε⁻¹ := fun K hK ↦ one_le_mul_of_one_le_of_one_le hK hεi1
  -- split by the size of the gap
  set big := I.filter fun n ↦ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n with hbig
  set small := I.filter fun n ↦ ¬ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n with hsmall
  have hsplit : (#I : ℝ) = #big + #small := by
    have h := card_filter_add_card_filter_not (s := I)
      fun n ↦ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n
    rw [hbig, hsmall]
    exact_mod_cast h.symm
  -- the large gaps: few planes with few points each, and few windows
  have hcases : ∀ n ∈ big,
      (∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U) ∨
        ∃ s ∈ 𝒯, s ≤ g n ∧ g n < K₂ * ε⁻¹ * s := by
    intro n hn
    have hnI := (mem_filter.mp hn).1
    have := hrτ n
    exact hTmem _ _ (by omega) (by omega) (hI n hnI).1 (hthr n hnI K₂ hAK.1)
  set big₁ := big.filter fun n ↦ ∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U
    with hbig₁
  set big₂ := big.filter fun n ↦
    ¬ ∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U with hbig₂
  have hbigs : (#big : ℝ) = #big₁ + #big₂ := by
    have h := card_filter_add_card_filter_not (s := big)
      fun n ↦ ∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U
    exact_mod_cast h.symm
  have hφ : ∀ n ∈ big₁, ∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U :=
    fun n hn ↦ (mem_filter.mp hn).2
  choose! φ hφT hφU using hφ
  have hbig₁c : (#big₁ : ℝ) ≤ #T * (12 * (1 + log ε⁻¹)) := by
    have hsum := card_eq_sum_card_fiberwise (s := big₁) (t := T) (f := φ) hφT
    have hfib : ∀ U ∈ T, (#(big₁.filter fun n ↦ φ n = U) : ℝ) ≤ 12 * (1 + log ε⁻¹) :=
      fun U hU ↦ card_mem_plane_le (hTtop U hU) hgap hrτ hε hε1 _ fun n hn ↦ by
        obtain ⟨hnb, hφn⟩ := mem_filter.mp hn
        exact ⟨hφn ▸ hφU n hnb, (mem_filter.mp (mem_filter.mp hnb).1).2⟩
    calc (#big₁ : ℝ) = ∑ U ∈ T, (#(big₁.filter fun n ↦ φ n = U) : ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T, 12 * (1 + log ε⁻¹) := sum_le_sum hfib
      _ = #T * (12 * (1 + log ε⁻¹)) := by rw [sum_const, nsmul_eq_mul]
  have hbig₂c : (#big₂ : ℝ) ≤ #𝒯 * (log (K₂ * ε⁻¹) / log (3 / 2) + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K₂ hK₂) 𝒯 fun n hn ↦ by
      obtain ⟨hnb, hn⟩ := mem_filter.mp hn
      exact (hcases n hnb).resolve_left hn
  -- the small gaps: one line with at most three points, and few windows
  have hcases' : ∀ n ∈ small,
      (fun i ↦ (linePoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U' ∨
        ∃ s ∈ 𝒯', s ≤ g n ∧ g n < K₄ * ε⁻¹ * s := by
    intro n hn
    obtain ⟨hnI, hns⟩ := mem_filter.mp hn
    have := hrτ n
    refine hLmem _ _ (by omega) (by omega) (hI n hnI).1 ?_ (hthr n hnI K₄ hAK.2)
    have hs : ((τ n + 2 - (r n + 2) : ℕ) : ℝ) = (τ n : ℝ) - r n := by
      rw [show τ n + 2 - (r n + 2) = τ n - r n by omega, Nat.cast_sub (hrτ n).le]
    rw [hs]
    push_cast
    linarith [not_lt.mp hns]
  set small₁ := small.filter fun n ↦ (fun i ↦ (linePoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U'
    with hsmall₁
  set small₂ := small.filter fun n ↦ (fun i ↦ (linePoint (r n + 2) (τ n + 2) i : ℚ)) ∉ U'
    with hsmall₂
  have hsmalls : (#small : ℝ) = #small₁ + #small₂ := by
    have h := card_filter_add_card_filter_not (s := small)
      fun n ↦ (fun i ↦ (linePoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U'
    exact_mod_cast h.symm
  have hsmall₁c : (#small₁ : ℝ) ≤ 3 :=
    card_mem_line_le hU' hgap hrτ _ fun n hn ↦ (mem_filter.mp hn).2
  have hsmall₂c : (#small₂ : ℝ) ≤ #𝒯' * (log (K₄ * ε⁻¹) / log (3 / 2) + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K₄ hK₄) 𝒯' fun n hn ↦ by
      obtain ⟨hns, hn⟩ := mem_filter.mp hn
      exact (hcases' n hns).resolve_left hn
  -- the sum
  have hW₂ := log_div_log_three_halves_le hK₂ hεi1
  have hW₄ := log_div_log_three_halves_le hK₄ hεi1
  have hb₁ := hbig₁c
  have hb₂ := hbig₂c
  have hs₂ := hsmall₂c
  clear_value big₁ big₂ small₁ small₂ big small g
  clear hcases hcases' hφT hφU hbig₁c hbig₂c hsmall₂c hTmem hLmem
  set X := ε⁻¹ with hX
  set Λ := 1 + log ε⁻¹ with hΛ
  have hΛ1 : 1 ≤ Λ := by have := log_nonneg hεi1; rw [hΛ]; linarith
  set W₂ := log (K₂ * X) / log (3 / 2) + 1 with hW₂def
  set W₄ := log (K₄ * X) / log (3 / 2) + 1 with hW₄def
  have hW₂0 : 0 ≤ W₂ := by
    rw [hW₂def]
    have := log_nonneg (hKX K₂ hK₂)
    have : 0 < log (3 / 2 : ℝ) := log_pos (by norm_num)
    positivity
  have hW₄0 : 0 ≤ W₄ := by
    rw [hW₄def]
    have := log_nonneg (hKX K₄ hK₄)
    have : 0 < log (3 / 2 : ℝ) := log_pos (by norm_num)
    positivity
  clear_value X Λ W₂ W₄
  have hX3 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := pow_le_pow_right₀ hεi1 (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hεi1 (by norm_num)
  have hΛ2 : Λ ≤ Λ ^ 2 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 2 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have h1 : 1 ≤ X ^ 3 * Λ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hεi1)
    (one_le_pow₀ hΛ1)
  have hc₁ : (#big₁ : ℝ) ≤ 36 * (X ^ 3 * Λ ^ 2) := by
    calc (#big₁ : ℝ) ≤ #T * (12 * Λ) := hb₁
      _ ≤ 3 * X * (12 * Λ) := by gcongr
      _ = 36 * (X * Λ) := by ring
      _ ≤ 36 * (X ^ 3 * Λ ^ 2) := by gcongr
  have hc₂ : (#big₂ : ℝ) ≤ K₂ * (3 * log K₂ + 4) * (X ^ 3 * Λ ^ 2) := by
    calc (#big₂ : ℝ) ≤ #𝒯 * W₂ := hb₂
      _ ≤ K₂ * X ^ 3 * Λ * ((3 * log K₂ + 4) * Λ) := by gcongr
      _ = K₂ * (3 * log K₂ + 4) * (X ^ 3 * Λ ^ 2) := by ring
  have hc₄ : (#small₂ : ℝ) ≤ K₄ * (3 * log K₄ + 4) * (X ^ 3 * Λ ^ 2) := by
    have hK : 0 ≤ K₄ * Λ * ((3 * log K₄ + 4) * Λ) := by positivity
    calc (#small₂ : ℝ) ≤ #𝒯' * W₄ := hs₂
      _ ≤ K₄ * X ^ 2 * Λ * ((3 * log K₄ + 4) * Λ) := by gcongr
      _ = X ^ 2 * (K₄ * Λ * ((3 * log K₄ + 4) * Λ)) := by ring
      _ ≤ X ^ 3 * (K₄ * Λ * ((3 * log K₄ + 4) * Λ)) := mul_le_mul_of_nonneg_right hX23 hK
      _ = K₄ * (3 * log K₄ + 4) * (X ^ 3 * Λ ^ 2) := by ring
  have e : A * X ^ 3 * Λ ^ 2 = (36 + K₂ * (3 * log K₂ + 4) + 3 + K₄ * (3 * log K₄ + 4)) *
      (X ^ 3 * Λ ^ 2) := by rw [hAdef]; ring
  rw [hsplit, hbigs, hsmalls, e]
  have hP : 0 ≤ X ^ 3 * Λ ^ 2 := by linarith
  nlinarith

/-- **Problem 5.2, for every `η < 1/3`.** For every `η < 1/3` and every `C`, the complexity of
the steering word exceeds `C k (log k)^η` for infinitely many `k`. -/
theorem frequently_lt_complexity_third {η : ℝ} (hη : η < 1 / 3) (C : ℝ) :
    ∃ᶠ k : ℕ in atTop, C * k * log k ^ η < complexity t k := by
  classical
  by_contra h
  rw [not_frequently] at h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  -- `p(k) ≤ c k (log k)^u` with `c = max C 1`, `u = max η 0`
  set u := max η 0 with hudef
  set c := max C 1 with hcdef
  have hu : 0 ≤ u := le_max_right _ _
  have hu3 : u < 1 / 3 := max_lt hη (by norm_num)
  have hp : ∀ k ≥ max n₀ 3, (complexity t k : ℝ) ≤ c * k * log k ^ u := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
    have hlog : 1 ≤ log k := by
      rw [le_log_iff_exp_le (by linarith)]
      have := exp_one_lt_d9
      linarith
    have h1 := not_lt.mp (hn₀ k ((le_max_left _ _).trans hk))
    have h2 : 0 ≤ (k : ℝ) * log k ^ η := by positivity
    calc (complexity t k : ℝ) ≤ C * k * log k ^ η := h1
      _ = C * ((k : ℝ) * log k ^ η) := by ring
      _ ≤ c * ((k : ℝ) * log k ^ η) := by gcongr; exact le_max_left _ _
      _ ≤ c * ((k : ℝ) * log k ^ u) := by
          gcongr
          exact le_max_left _ _
      _ = c * k * log k ^ u := by ring
  -- `u < v < 1/3`
  set v := (u + 1 / 3) / 2 with hvdef
  have huv : u < v := by rw [hvdef]; linarith
  have hv : 0 < v := by linarith
  have hv3 : ((3 : ℕ) : ℝ) * v < 1 := by rw [hvdef]; push_cast; linarith
  obtain ⟨Cg, r, τ, hrτ, hgap, hbd, hrep⟩ := exists_violators_of_complexity_le hu huv (max n₀ 3) hp
  obtain ⟨A, hA, hcnt⟩ := card_le_of_violators_third
  set Kt : ℝ := A * 7776 with hKtdef
  have hKt0 : 0 < Kt := by positivity
  -- opaque from here on: unfolding it makes defeq checks on real arithmetic explode
  clear_value Kt
  obtain ⟨N, hN⟩ := (eventually_doubling_thresholds 3 2 (by norm_num) (by norm_num) (C := Cg) hv
    hv3 hKt0 (log_pos (by norm_num : (1 : ℝ) < 3))).exists
  obtain ⟨hε0, hε1, hεle, hthr, hcount⟩ := hN τ hgap hbd
  set ε₀ := log (τ (2 * N)) ^ (-v) with hε₀
  set ε := ε₀ / 6 with hεdef
  have hε : 0 < ε := by positivity
  have hε1' : ε ≤ 1 := by rw [hεdef]; linarith
  have hεinv : ε⁻¹ = 6 * ε₀⁻¹ := by rw [hεdef, inv_div, div_eq_mul_inv]
  have hε₀inv : 1 ≤ ε₀⁻¹ := one_le_inv₀ hε0 |>.mpr hε1
  have hlogε₀ : 0 ≤ log ε₀⁻¹ := log_nonneg hε₀inv
  -- `N ≥ 1`, so the indices `n ≥ N` have `τ_n ≥ 3`
  have hN1 : 1 ≤ N := by
    by_contra h0
    have h0' : N = 0 := by omega
    rw [h0'] at hcount
    have : 0 ≤ Kt * ε₀⁻¹ ^ 3 * (1 + log ε₀⁻¹) ^ 2 := by positivity
    push_cast at hcount
    linarith
  have hτ3 : ∀ n, 1 ≤ n → 3 ≤ τ n := fun n hn ↦ by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := hgap k
    have := hrτ k
    omega
  -- the pairs `(r_n + 2, τ_n + 2)`, `N ≤ n < 2N`, are kernel violators with exponent `ε`
  have hI : ∀ n ∈ Ico N (2 * N),
      |(eps (τ n + 2) : ℝ) - eps (r n + 2)| ≤ ((3 : ℝ) ^ (τ n + 2)) ^ (-ε) ∧
        A * ε⁻¹ ≤ ((τ n + 2 : ℕ) : ℝ) * log 3 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    refine ⟨abs_eps_sub_le_rpow (hrep n) ?_, ?_⟩
    · have h3 : (3 : ℝ) ≤ τ n := by exact_mod_cast hτ3 n (by omega)
      have hle : ε₀ * τ n ≤ τ n * log (τ n) ^ (-v) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hεle n hn1 hn2.le) (by positivity)
      have hceil := Nat.le_ceil ((τ n : ℝ) * log (τ n) ^ (-v))
      push_cast
      rw [hεdef]
      nlinarith
    · have h := hthr n hn1
      have hl3 : 0 < log 3 := log_pos (by norm_num)
      rw [hεinv]
      push_cast
      have : 0 ≤ ε₀⁻¹ := by positivity
      nlinarith
  have hfin := hcnt ε hε hε1' r τ hrτ hgap _ hI
  rw [Nat.card_Ico, show 2 * N - N = N by omega] at hfin
  -- `N ≤ Kt ε₀⁻³ (1 + log ε₀⁻¹)² < N`
  have hLε : 1 + log ε⁻¹ ≤ 6 * (1 + log ε₀⁻¹) := by
    rw [hεinv, log_mul (by norm_num) (by positivity)]
    have : log 6 ≤ 5 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
      linarith
    linarith
  have hL0 : 0 ≤ 1 + log ε⁻¹ := by
    have := log_nonneg (one_le_inv₀ hε |>.mpr hε1')
    linarith
  have hfin' : (N : ℝ) ≤ Kt * ε₀⁻¹ ^ 3 * (1 + log ε₀⁻¹) ^ 2 := by
    calc (N : ℝ) ≤ A * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := hfin
      _ ≤ A * (6 * ε₀⁻¹) ^ 3 * (6 * (1 + log ε₀⁻¹)) ^ 2 := by
          rw [hεinv] at hLε hL0 ⊢; gcongr
      _ = A * 7776 * ε₀⁻¹ ^ 3 * (1 + log ε₀⁻¹) ^ 2 := by ring
      _ = Kt * ε₀⁻¹ ^ 3 * (1 + log ε₀⁻¹) ^ 2 := by rw [hKtdef]
  linarith

end SteeringWord
