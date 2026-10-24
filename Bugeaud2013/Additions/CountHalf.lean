/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.Delta
public import Bugeaud2013.Additions.SubspaceInterval

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences

/-!
# The number of points, with one interval result for all cells

The count of `Bugeaud2013/Additions/CountThird.lean` with the interval form of the quantitative
Subspace Theorem for a set of exponents (`Real.SubspaceIntervalFamily α`) in the first
application: the `⌈8/ε⌉ + 1` cells of `ρ = log Q / log H` have the same forms and differ only in
their exponents, so one application to the set of all of them puts the points into `K` proper
subspaces of `ℚ⁴`, `K` independent of `ε`, or `log H` into `K ε⁻² (1 + log ε⁻¹)` intervals
`[s, K ε⁻¹ s)` (`Real.exists_cover_four_intervals_family`). The application on `T₀` is as before
(`Real.exists_planes_t0_intervals`). Hence `K ε⁻² (1 + log ε⁻¹)²` points
(`Real.card_le_of_cfPoints_half`), so `Real.CFCount α 1` (`Real.cfCount_one`) and the exponent
`δ < 1/2` in (6.1) (`Nat.frequently_lt_encard_factors_of_lt_half`).

## Main results

* `Real.exists_cover_four_intervals_family`: the first application, one interval result for all
  cells.
* `Real.card_le_of_cfPoints_half`: the count.
* `Real.cfCount_one`: the count in the shape `Real.CFCount α 1`.
* `Nat.frequently_lt_encard_factors_of_lt_half`: (6.1) with `δ < 1/2`.

## References

J.-H. Evertse, R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*, Ann.
of Math. **177** (2013), 513–590, Theorems 2.3 and 3.3.

R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the exponent `1/2` in
three complexity bounds* (2026), Theorem B and §6.
-/

@[expose] public section

open Finset Module

namespace Real

variable {α A ε c : ℝ} {D : ℕ}

/-- **The first application, one interval result for all cells**: the points with
`log H ≥ K ε^{-K}` lie in one of at most `K` proper subspaces of `ℚ⁴`, or have `log H` in one of
at most `K ε⁻² (1 + log ε⁻¹)` intervals `[s, K ε⁻¹ s)`. -/
theorem exists_cover_four_intervals_family (hSI : SubspaceIntervalFamily α) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)), (#T : ℝ) ≤ K ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) ∧
        ∀ (v : Fin 4 → ℤ) (H Q : ℝ), CFPoint α A ε v H Q → 1 ≤ log H →
          K * ε⁻¹ ^ K ≤ log H →
          (∃ U ∈ T, ptQ v ∈ U) ∨ ∃ s ∈ 𝒯, s ≤ log H ∧ log H < K * ε⁻¹ * s := by
  classical
  obtain ⟨K₄, hK₄, h4⟩ := hSI 4 (by norm_num) le_rfl
  have hA4 : (1 : ℝ) ≤ (A + 1) ^ 4 := one_le_pow₀ (by linarith)
  set C : ℝ := 24 * (A + 1) ^ 4 with hCdef
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hlC : 0 ≤ log C := Real.log_nonneg hC1
  have hlA : 0 ≤ log (A + 1) := Real.log_nonneg (by linarith)
  have hlCA : 4 * log (A + 1) ≤ log C := by
    have := Real.log_le_log (by positivity) (show (A + 1) ^ 4 ≤ C by simp only [C]; linarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  set κ := K₄ * 2 ^ K₄ * (1 + log C) + 4 * log (A + 1)
  set K := max (max K₄ κ) (8 * K₄)
  have hKK : K₄ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hκK : κ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have h8 : 8 * K₄ ≤ K := le_max_right _ _
  refine ⟨K, hK₄.trans hKK, fun ε hε hε1 ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hL0 : 0 ≤ log ε⁻¹ := Real.log_nonneg hεi
  have hdet : (1 : ℝ) ≤ |(Matrix.of fun i k ↦ quadVal α (formCoef i k)).det| := by
    rw [det_formCoef, abs_neg, abs_one]
  -- all cells at once
  obtain ⟨T, hT, hTtop, 𝒯, h𝒯, hmem⟩ := h4 formCoef 1 le_rfl
    (fun i k m ↦ by exact_mod_cast abs_formCoef_le i k m) 1 one_pos le_rfl hdet C hC1 (ε / 2)
    (by positivity) (by linarith) (cellExp ε '' {j | j < cells ε})
    (by rintro _ ⟨j, hj, rfl⟩; exact ⟨cellExp_le_one hε hj, ⟨3, rfl⟩, sum_cellExp_le hε j⟩)
  have hδi : (ε / 2)⁻¹ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  refine ⟨T, hT.trans hKK, hTtop, 𝒯, ?_, ?_⟩
  · have hl : 1 + log (ε / 2)⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      rw [hδi, Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hl0 : 0 ≤ 1 + log (ε / 2)⁻¹ := by rw [hδi, Real.log_mul (by norm_num) (by positivity)]
                                           have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
                                           linarith
    calc (#𝒯 : ℝ) ≤ K₄ * (ε / 2)⁻¹ ^ 2 * (1 + log (ε / 2)⁻¹) := h𝒯
      _ ≤ K₄ * (2 * ε⁻¹) ^ 2 * (2 * (1 + log ε⁻¹)) := by
          rw [hδi] at hl0 hl ⊢
          gcongr
      _ = 8 * K₄ * ε⁻¹ ^ 2 * (1 + log ε⁻¹) := by ring
      _ ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) := by gcongr
  intro v H Q hp hH hlate
  have hlogH : 0 < log H := by linarith
  have hQ1 := hp.one_le_Q
  have hρ0 : 0 ≤ log Q / log H := div_nonneg (Real.log_nonneg hQ1) hlogH.le
  have hρ1 : log Q / log H ≤ 1 / 2 := by
    have := Real.log_le_log (by positivity) hp.sq_le
    rw [Real.log_pow] at this
    rw [div_le_iff₀ hlogH]
    push_cast at this; linarith
  obtain ⟨j, hj, h0, h1, -, -⟩ := exists_cell hε hρ0 hρ1
  have hv0 : v ≠ 0 := fun h ↦ hp.v0_ne_zero (by simp [h])
  set X := ⨆ k, |(v k : ℝ)| with hXdef
  have hX1 : 1 ≤ X := one_le_iSup_abs_of_cfPoint hp
  have hX0 : 0 < X := by linarith
  have hHX : H ≤ (A + 1) ^ 4 * X := hp.head.trans (by gcongr; exact abs_le_iSup_abs v 0)
  have hXH : X ≤ H := ciSup_le fun k ↦ hp.abs_le k
  have hYlog : log H - 4 * log (A + 1) ≤ log X := by
    have := Real.log_le_log hp.H_pos hHX
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hthr : K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log 1 + log C + log 1⁻¹) ≤ log X := by
    rw [inv_one, Real.log_one, add_zero, add_zero]
    have he2 : (ε / 2)⁻¹ ^ K₄ = 2 ^ K₄ * ε⁻¹ ^ K₄ := by
      rw [inv_div, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity)]
    have hp1 : 1 ≤ ε⁻¹ ^ K₄ := Real.one_le_rpow hεi (by linarith)
    have hp2 : ε⁻¹ ^ K₄ ≤ ε⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hεi hKK
    have h3 : κ * ε⁻¹ ^ K₄ ≤ K * ε⁻¹ ^ K :=
      mul_le_mul hκK hp2 (by positivity) ((zero_le_one.trans hK₄).trans hKK)
    have h5 : 4 * log (A + 1) ≤ 4 * log (A + 1) * ε⁻¹ ^ K₄ :=
      le_mul_of_one_le_right (by positivity) hp1
    rw [he2]
    have : K₄ * (2 ^ K₄ * ε⁻¹ ^ K₄) * (1 + log C) + 4 * log (A + 1) * ε⁻¹ ^ K₄ =
        κ * ε⁻¹ ^ K₄ := by simp only [κ]; ring
    linarith
  rcases hmem _ ⟨j, hj, rfl⟩ v hv0 (fun i ↦ cell_ineq hA hε.le hp hlogH (by positivity) h0 h1 i)
    hthr with hvU | ⟨s, hs, hs1, hs2⟩
  · exact .inl hvU
  refine .inr ⟨s, hs, hs1.trans (Real.log_le_log hX0 hXH), ?_⟩
  -- `log H ≤ log X + 4 log (A + 1) < 2 K₄ (ε/2)⁻¹ s`
  have hthr0 : log C ≤ K₄ * (ε / 2)⁻¹ ^ K₄ * (1 + log C) := by
    have h1 : 1 ≤ (ε / 2)⁻¹ ^ K₄ := Real.one_le_rpow (by rw [hδi]; linarith) (by linarith)
    have : 1 ≤ K₄ * (ε / 2)⁻¹ ^ K₄ := one_le_mul_of_one_le_of_one_le hK₄ h1
    nlinarith
  have hbig : 4 * log (A + 1) ≤ K₄ * (ε / 2)⁻¹ * s := by
    rw [inv_one, Real.log_one, add_zero, add_zero] at hthr
    linarith
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    have : 0 < K₄ * (ε / 2)⁻¹ := by positivity
    nlinarith [Real.log_nonneg hX1]
  calc log H ≤ log X + 4 * log (A + 1) := by linarith
    _ < 2 * (K₄ * (ε / 2)⁻¹ * s) := by linarith
    _ = 4 * K₄ * ε⁻¹ * s := by rw [hδi]; ring
    _ ≤ K * ε⁻¹ * s := by
        have : 0 ≤ ε⁻¹ * s := by positivity
        nlinarith

variable {Hs Qs : ℕ → ℝ} {vs : ℕ → Fin 4 → ℤ}

/-- **The count of the points, with one interval result for all cells.** If the interval forms
`Real.SubspaceIntervalFamily α` and `Real.SubspaceInterval α` and some `Real.SubspaceBound α a`
hold, then a family of points of §3 with exponent `ε`, doubling heights and `log H ≥ K ε^{-K}`
has at most `K ε⁻² (1 + log ε⁻¹)²` members. -/
theorem card_le_of_cfPoints_half {a : ℝ} (hSIF : SubspaceIntervalFamily α)
    (hSI : SubspaceInterval α) (hSB : SubspaceBound α a) (hA : 1 ≤ A) (hc : 0 < c)
    (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (Hs Qs : ℕ → ℝ) (vs : ℕ → Fin 4 → ℤ)
      (I : Finset ℕ), Doubling Hs → (∀ k ∈ I, CFPoint α A ε (vs k) (Hs k) (Qs k)) →
      (∀ k ∈ I, K * ε⁻¹ ^ K ≤ log (Hs k)) →
      (#I : ℝ) ≤ K * ε⁻¹ ^ 2 * (1 + log ε⁻¹) ^ 2 := by
  classical
  obtain ⟨K4, hK4, hcov4⟩ := exists_cover_four_intervals_family hSIF hA
  obtain ⟨Kt, hKt, hcovt⟩ := exists_planes_t0_intervals hSI hA
  obtain ⟨KE, NT, hNT, hcovE⟩ := exists_planeCover hSB hA hc hL
  set cP := 4 * log (log (twoConst c D) + 4 * D + 4) + 6
  have hcP : 0 ≤ cP := by
    have : 0 ≤ log (log (twoConst c D) + 4 * D + 4) := by
      have := Real.log_nonneg (one_le_twoConst hc D)
      have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      exact Real.log_nonneg (by linarith)
    simp only [cP]; linarith
  set ME := max 1 (9 * KE)
  have hlME : 0 ≤ logb 2 ME := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  set cH := (NT + 1) * cP + logb 2 ME + 1
  have hcH : 0 ≤ cH := by positivity
  have hlK4 := Real.log_nonneg hK4
  have hlKt := Real.log_nonneg hKt
  set Kc := cP + K4 * cH + K4 * (2 * log K4 + 3) + Kt * (2 * log Kt + 3)
  have hKc0 : 0 ≤ Kc := by positivity
  set K := max 1 (max (max K4 Kt) Kc)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK4K : K4 ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKtK : Kt ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hKcK : Kc ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, by linarith, fun ε hε hε1 Hs Qs vs I hdbl hpt hthr ↦ ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  set L := log ε⁻¹ with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hεi
  -- the thresholds
  have hthr' (K' : ℝ) (hK' : K' ≤ K) (hK'0 : 0 ≤ K') (k : ℕ) (hk : k ∈ I) :
      K' * ε⁻¹ ^ K' ≤ log (Hs k) :=
    (mul_le_mul hK' (Real.rpow_le_rpow_of_exponent_le hεi hK') (by positivity)
      (by linarith)).trans (hthr k hk)
  -- the covers
  obtain ⟨T4, hT4, hT4top, 𝒯4, h𝒯4, hT4mem⟩ := hcov4 ε hε hε1
  obtain ⟨P0, hP0, 𝒯0, h𝒯0, hP0mem⟩ := hcovt ε hε hε1
  -- the heights double
  set g : ℕ → ℝ := fun k ↦ log (Hs k) with hg
  have hg0 : ∀ k, 0 < g k := fun k ↦ by have := hdbl.one_le_log k; simp only [hg]; linarith
  have hgq : ∀ k, 2 * g k ≤ g (k + 1) := hdbl.two_mul_log_le
  have hKX : ∀ K' : ℝ, 1 ≤ K' → 1 ≤ K' * ε⁻¹ := fun K' hK' ↦
    one_le_mul_of_one_le_of_one_le hK' hεi
  -- the points of `T₀` and the others
  set J0 := I.filter fun k ↦ vs k 1 = vs k 2 with hJ0
  set J1 := I.filter fun k ↦ vs k 1 ≠ vs k 2 with hJ1
  have hIJ : (#I : ℝ) = #J0 + #J1 := by
    have h := card_filter_add_card_filter_not (s := I) fun k ↦ vs k 1 = vs k 2
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  -- `T₀`: one plane, and windows
  set J0a := J0.filter fun k ↦ ptQ (vs k) ∈ P0 with hJ0a
  set J0b := J0.filter fun k ↦ ptQ (vs k) ∉ P0 with hJ0b
  have hJ0s : (#J0 : ℝ) = #J0a + #J0b := by
    have h := card_filter_add_card_filter_not (s := J0) fun k ↦ ptQ (vs k) ∈ P0
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  have hJ0a : (#J0a : ℝ) ≤ planeBound c D ε := by
    refine le_trans ?_ (card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt P0 hP0)
    refine Nat.cast_le.2 (card_le_card fun k hk ↦ ?_)
    obtain ⟨hk0, hkP⟩ := mem_filter.1 hk
    exact mem_filter.2 ⟨(mem_filter.1 hk0).1, hkP⟩
  have hJ0b : (#J0b : ℝ) ≤ #𝒯0 * (log (Kt * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX Kt hKt) 𝒯0 fun k hk ↦ by
      obtain ⟨hk0, hkP⟩ := mem_filter.1 hk
      obtain ⟨hkI, hk12⟩ := mem_filter.1 hk0
      exact (hP0mem (vs k) (Hs k) (Qs k) (hpt k hkI) hk12
        (hthr' Kt hKtK (by linarith) k hkI)).resolve_left hkP
  -- the others: the subspaces of the cells, and windows
  set J1a := J1.filter fun k ↦ ∃ S ∈ T4, ptQ (vs k) ∈ S with hJ1a
  set J1b := J1.filter fun k ↦ ¬ ∃ S ∈ T4, ptQ (vs k) ∈ S with hJ1b
  have hJ1s : (#J1 : ℝ) = #J1a + #J1b := by
    have h := card_filter_add_card_filter_not (s := J1) fun k ↦ ∃ S ∈ T4, ptQ (vs k) ∈ S
    rw [← Nat.cast_add]
    exact congrArg Nat.cast h.symm
  set HB := (NT + 1) * planeBound c D ε + logb 2 ME + 1 with hHBdef
  have hJ1a : (#J1a : ℝ) ≤ #T4 * HB := by
    have hsub : J1a ⊆ T4.biUnion fun S ↦ {k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} := by
      intro k hk
      obtain ⟨hk1, S, hS, hkS⟩ := mem_filter.1 hk
      obtain ⟨hkI, hk12⟩ := mem_filter.1 hk1
      exact mem_biUnion.2 ⟨S, hS, mem_filter.2 ⟨hkI, hkS, hk12⟩⟩
    refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
    push_cast
    calc ∑ S ∈ T4, (#{k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} : ℝ) ≤ ∑ _S ∈ T4, HB :=
          Finset.sum_le_sum fun S hS ↦
            card_mem_le_of_ne_top hc hL hα hε hε1 hdbl I hpt hNT hcovE S (hT4top S hS)
      _ = #T4 * HB := by rw [Finset.sum_const, nsmul_eq_mul]
  have hJ1b : (#J1b : ℝ) ≤ #𝒯4 * (log (K4 * ε⁻¹) / log 2 + 1) :=
    card_le_of_forall_mem_window (by norm_num) hg0 hgq (hKX K4 hK4) 𝒯4 fun k hk ↦ by
      obtain ⟨hk1, hkS⟩ := mem_filter.1 hk
      have hkI := (mem_filter.1 hk1).1
      exact (hT4mem (vs k) (Hs k) (Qs k) (hpt k hkI) (hdbl.one_le_log k)
        (hthr' K4 hK4K (by linarith) k hkI)).resolve_left hkS
  -- the sizes
  have hB := planeBound_le hc D hε hε1
  have hHB : HB ≤ cH * (1 + L) := by
    have h1 : (NT + 1) * planeBound c D ε ≤ (NT + 1) * (cP * (1 + L)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h2 : logb 2 ME + 1 ≤ (logb 2 ME + 1) * (1 + L) := le_mul_of_one_le_right
      (by positivity) (by linarith)
    simp only [HB, cH]
    nlinarith
  have hHB0 : 0 ≤ HB := by
    have := planeBound_nonneg hc D hε hε1
    simp only [HB]
    positivity
  have hW4 := log_div_log_two_le hK4 hεi
  have hWt := log_div_log_two_le hKt hεi
  have hT4c := hT4
  clear_value J0a J0b J1a J1b J0 J1 g
  clear hT4mem hP0mem
  set X := ε⁻¹ with hX
  set Λ := 1 + L with hΛ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  set W4 := log (K4 * X) / log 2 + 1 with hW4def
  set Wt := log (Kt * X) / log 2 + 1 with hWtdef
  have hW40 : 0 ≤ W4 := by
    rw [hW4def]
    have := Real.log_nonneg (hKX K4 hK4)
    have : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hWt0 : 0 ≤ Wt := by
    rw [hWtdef]
    have := Real.log_nonneg (hKX Kt hKt)
    have : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hB' : planeBound c D ε ≤ cP * Λ := hB
  have hHB' : HB ≤ cH * Λ := hHB
  clear_value X Λ W4 Wt HB
  have h1X : 1 ≤ X ^ 2 := one_le_pow₀ hεi
  have hΛ2 : Λ ≤ Λ ^ 2 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 2 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have h1 : 1 ≤ X ^ 2 * Λ ^ 2 := one_le_mul_of_one_le_of_one_le h1X (one_le_pow₀ hΛ1)
  have hΛX : Λ ≤ X ^ 2 * Λ ^ 2 := by
    calc Λ = 1 * Λ := (one_mul Λ).symm
      _ ≤ X ^ 2 * Λ ^ 2 := mul_le_mul h1X hΛ2 (by linarith) (by linarith)
  have hc0a : (#J0a : ℝ) ≤ cP * (X ^ 2 * Λ ^ 2) := by
    calc (#J0a : ℝ) ≤ cP * Λ := hJ0a.trans hB'
      _ ≤ cP * (X ^ 2 * Λ ^ 2) := by gcongr
  have hc0b : (#J0b : ℝ) ≤ Kt * (2 * log Kt + 3) * (X ^ 2 * Λ ^ 2) := by
    calc (#J0b : ℝ) ≤ #𝒯0 * Wt := hJ0b
      _ ≤ Kt * X ^ 2 * Λ * ((2 * log Kt + 3) * Λ) := by gcongr
      _ = Kt * (2 * log Kt + 3) * (X ^ 2 * Λ ^ 2) := by ring
  have hc1a : (#J1a : ℝ) ≤ K4 * cH * (X ^ 2 * Λ ^ 2) := by
    calc (#J1a : ℝ) ≤ #T4 * HB := hJ1a
      _ ≤ K4 * (cH * Λ) := by gcongr
      _ = K4 * cH * Λ := by ring
      _ ≤ K4 * cH * (X ^ 2 * Λ ^ 2) := by gcongr
  have hc1b : (#J1b : ℝ) ≤ K4 * (2 * log K4 + 3) * (X ^ 2 * Λ ^ 2) := by
    calc (#J1b : ℝ) ≤ #𝒯4 * W4 := hJ1b
      _ ≤ K4 * X ^ 2 * Λ * ((2 * log K4 + 3) * Λ) := by gcongr
      _ = K4 * (2 * log K4 + 3) * (X ^ 2 * Λ ^ 2) := by ring
  have hP : 0 ≤ X ^ 2 * Λ ^ 2 := by linarith
  have hsum : (#I : ℝ) ≤ Kc * (X ^ 2 * Λ ^ 2) := by
    rw [hIJ, hJ0s, hJ1s]
    have e : Kc * (X ^ 2 * Λ ^ 2) = cP * (X ^ 2 * Λ ^ 2) +
        Kt * (2 * log Kt + 3) * (X ^ 2 * Λ ^ 2) + K4 * cH * (X ^ 2 * Λ ^ 2) +
        K4 * (2 * log K4 + 3) * (X ^ 2 * Λ ^ 2) := by simp only [Kc]; ring
    rw [e]
    linarith
  calc (#I : ℝ) ≤ Kc * (X ^ 2 * Λ ^ 2) := hsum
    _ ≤ K * (X ^ 2 * Λ ^ 2) := mul_le_mul_of_nonneg_right hKcK hP
    _ = K * X ^ 2 * Λ ^ 2 := by ring

/-- **The count with one interval result for all cells, in the shape of (6.1)**:
`Real.CFCount α 1`, since `ε⁻² (1 + log ε⁻¹)² ≤ ε^{-(1+1)} (1 + log ε⁻¹)³`. -/
theorem cfCount_one {a : ℝ} (hSIF : SubspaceIntervalFamily α) (hSI : SubspaceInterval α)
    (hSB : SubspaceBound α a) (hc : 0 < c) (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1) :
    CFCount α 1 := by
  intro A hA
  obtain ⟨K, hK, hcnt⟩ := card_le_of_cfPoints_half hSIF hSI hSB hA hc hL hα
  refine ⟨K, hK, fun ε hε hε1 Hs Qs vs I hdbl hpt hthr ↦ (hcnt ε hε hε1 Hs Qs vs I hdbl hpt
    hthr).trans ?_⟩
  have hεi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hΛ : 1 ≤ 1 + log ε⁻¹ := by have := Real.log_nonneg hεi; linarith
  rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : (1 + log ε⁻¹) ^ 2 ≤ (1 + log ε⁻¹) ^ 3 := pow_le_pow_right₀ hΛ (by norm_num)
  have : 0 ≤ K * ε⁻¹ ^ 2 := by positivity
  gcongr

end Real

namespace Nat

variable {a : ℕ → ℕ}

/-- **(6.1) with `δ < 1/2`** (Evertse–Ferretti 2013, Theorem 2.3 for a set of exponents). The
cells of the first application have the same forms, so one interval result serves all of them,
and the count is `ε⁻²` instead of `ε⁻³` (`Real.cfCount_one`). -/
theorem frequently_lt_encard_factors_of_lt_half (ha : ∀ n, 1 ≤ a (n + 1))
    (hdeg : 3 ≤ (minpoly ℚ (contFrac a)).natDegree) {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ < 1 / 2)
    (C : ℝ) :
    ∃ᶠ n in Filter.atTop, ∀ k : ℕ, (Function.factors (fun i ↦ a (i + 1)) n).encard = k →
      C * n * Real.log n ^ δ < k := by
  have halg := isAlgebraic_of_three_le_natDegree hdeg
  obtain ⟨c, hc, D, hLq⟩ := Real.exists_pos_le_abs_quadVal halg hdeg
  exact frequently_lt_encard_factors_of_cfCount ha
    (Real.cfCount_one (Real.subspaceIntervalFamily_of_isAlgebraic halg)
      (Real.subspaceInterval_of_isAlgebraic halg) (Real.subspaceBound_three halg) hc hLq
      (abs_contFrac_le_one ha)) (by norm_num) hδ (by linarith) C

end Nat
