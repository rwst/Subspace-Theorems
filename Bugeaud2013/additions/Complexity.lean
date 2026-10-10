/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FactorComplexity
public import Mathlib.Data.Set.Card

/-!
# Repetitions from a complexity bound

If a sequence has at most `p` factors of length `ℓ ≥ 12`, two of the positions `0, …, p` carry
the same factor of length `ℓ` (pigeonhole). This gives a repetition of length `u₀ ≥ ℓ / 3` at a
distance `r ≥ u₀`, which is then slid as far to the left as it goes
(`Function.exists_rep_min`). In the indexing of the continued fraction `[0; a₁, a₂, …]` this is
`Nat.exists_config`: a repetition `a_{m + r} = a_m` for `j + 1 < m ≤ j + 1 + u` with
`a_{j+1} ≠ a_{j+1+r}` when `j ≥ 1`, the hypotheses of `Nat.cfPoint_spadeVec`.
-/

@[expose] public section

namespace Function

variable {β : Type*} {x : ℕ → β}

/-- Two positions `i < i' ≤ p` with the same factor of length `ℓ ≥ 12` give a repetition of
length `u₀ ≥ ℓ / 3` at a distance `r ≥ u₀`. -/
theorem exists_rep_of_lt {ℓ p i i' : ℕ} (hℓ : 12 ≤ ℓ) (hlt : i < i') (hi' : i' ≤ p)
    (h : ∀ k < ℓ, x (i + k) = x (i' + k)) :
    ∃ w₀ r u₀, u₀ ≤ r ∧ ℓ ≤ 3 * u₀ ∧ w₀ ≤ p ∧ r ≤ p + ℓ ∧
      ∀ k, w₀ ≤ k → k < w₀ + u₀ → x (k + r) = x k := by
  set s := i' - i with hs
  have hbase : ∀ k, i ≤ k → k + s < i + ℓ + s → x (k + s) = x k := by
    intro k hk hks
    have := h (k - i) (by omega)
    rw [show i + (k - i) = k by omega, show i' + (k - i) = k + s by omega] at this
    exact this.symm
  by_cases hsl : ℓ ≤ s
  · exact ⟨i, s, ℓ, hsl, by omega, by omega, by omega, fun k hk hkl ↦ hbase k hk (by omega)⟩
  · have hdm := Nat.div_add_mod (ℓ + s) (2 * s)
    have hmod := Nat.mod_lt (ℓ + s) (show 0 < 2 * s by omega)
    set q := (ℓ + s) / (2 * s)
    set m := (ℓ + s) % (2 * s)
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0] at hdm; omega
      · exact h0
    have hPs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    have h2 : 2 * (q * s) + m = ℓ + s := by rw [← hdm]; ring
    have hmul := forall_add_mul_eq_of_forall_add_eq hbase q
    refine ⟨i, q * s, q * s, le_rfl, by omega, by omega, by omega, fun k hk hkl ↦ ?_⟩
    exact hmul k hk (by omega)

/-- **Sliding a repetition to the left.** A repetition of length `u₀ ≤ r` at distance `r` after
`w₀` gives one of length `u ≥ u₀ - 1`, `u ≤ r`, after `j + 1 ≤ w₀ + 1` that cannot be slid
further when `j ≥ 1`. -/
theorem exists_rep_min {w₀ r u₀ : ℕ} (hu₀ : u₀ ≤ r)
    (hrep : ∀ k, w₀ ≤ k → k < w₀ + u₀ → x (k + r) = x k) :
    ∃ j u, u₀ ≤ u + 1 ∧ u ≤ r ∧ j ≤ w₀ ∧
      (∀ k, j + 1 ≤ k → k < j + 1 + u → x (k + r) = x k) ∧ (1 ≤ j → x j ≠ x (j + r)) := by
  classical
  have hex : ∃ w, ∀ k, w ≤ k → k < w₀ + u₀ → x (k + r) = x k := ⟨w₀, hrep⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ w₀ := Nat.find_min' hex hrep
  by_cases hw : Nat.find hex ≤ 1
  · refine ⟨0, min (w₀ + u₀ - 1) r, by omega, min_le_right _ _, by omega,
      fun k hk hku ↦ hspec k (by omega) (by omega), by omega⟩
  · refine ⟨Nat.find hex - 1, min (w₀ + u₀ - Nat.find hex) r, by omega, min_le_right _ _,
      by omega, fun k hk hku ↦ hspec k (by omega) (by omega), fun _ heq ↦ ?_⟩
    refine Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) fun k hk hkE ↦ ?_
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact heq.symm
    · exact hspec k (by omega) hkE

/-- **Repetitions from a complexity bound.** At most `p` factors of length `ℓ ≥ 12` give a
repetition of length `u` with `ℓ ≤ 4 u`, `u ≤ r`, after `j + 1` with `j + 1 + r ≤ 2 p + ℓ + 1`,
that cannot be slid to the left when `j ≥ 1`. -/
theorem exists_rep_of_encard_le {ℓ p : ℕ} (hℓ : 12 ≤ ℓ) (hp : (factors x ℓ).encard ≤ p) :
    ∃ j r u, 1 ≤ u ∧ u ≤ r ∧ 2 ≤ r ∧ ℓ ≤ 4 * u ∧ j + 1 + r ≤ 2 * p + ℓ + 1 ∧
      (∀ k, j + 1 ≤ k → k < j + 1 + u → x (k + r) = x k) ∧ (1 ≤ j → x j ≠ x (j + r)) := by
  have hfin : (factors x ℓ).Finite := Set.finite_of_encard_le_coe hp
  have hcard : hfin.toFinset.card ≤ p := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast hfin.cast_ncard_eq ▸ hp
  obtain ⟨i, hi, i', hi', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (p + 1)) (t := hfin.toFinset) (f := fun i ↦ factor x i ℓ)
    (by simpa using Nat.lt_succ_of_le hcard)
    (fun i _ ↦ hfin.mem_toFinset.mpr ⟨i, rfl⟩)
  rw [Finset.mem_range] at hi hi'
  have heq' := factor_eq_factor_iff.mp heq
  obtain ⟨w₀, r, u₀, hu₀r, hℓu, hw₀, hrp, hrep⟩ : ∃ w₀ r u₀, u₀ ≤ r ∧ ℓ ≤ 3 * u₀ ∧ w₀ ≤ p ∧
      r ≤ p + ℓ ∧ ∀ k, w₀ ≤ k → k < w₀ + u₀ → x (k + r) = x k := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact exists_rep_of_lt hℓ hlt (by omega) heq'
    · exact exists_rep_of_lt hℓ hlt (by omega) fun k hk ↦ (heq' k hk).symm
  obtain ⟨j, u, hu, hur, hj, hrep', hne'⟩ := exists_rep_min hu₀r hrep
  exact ⟨j, r, u, by omega, hur, by omega, by omega, by omega, hrep', hne'⟩

end Function

namespace Nat

/-- **The configurations of `Nat.cfPoint_spadeVec` from a complexity bound.** If
`a₁ a₂ …` has at most `p` factors of length `ℓ ≥ 12`, there is a repetition
`a_{m + r} = a_m` for `j + 1 < m ≤ j + 1 + u`, with `1 ≤ u ≤ r`, `2 ≤ r`, `ℓ ≤ 4 u`,
`j + 1 + r ≤ 2 p + ℓ + 1` and `a_{j+1} ≠ a_{j+1+r}` when `j ≥ 1`. -/
theorem exists_config {a : ℕ → ℕ} {ℓ p : ℕ} (hℓ : 12 ≤ ℓ)
    (hp : (Function.factors (fun k ↦ a (k + 1)) ℓ).encard ≤ p) :
    ∃ j r u, 1 ≤ u ∧ u ≤ r ∧ 2 ≤ r ∧ ℓ ≤ 4 * u ∧ j + 1 + r ≤ 2 * p + ℓ + 1 ∧
      (∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) ∧
      (1 ≤ j → a (j + 1) ≠ a (j + 1 + r)) := by
  obtain ⟨j, r, u, hu, hur, hr, hℓu, hm, hrep, hne⟩ := Function.exists_rep_of_encard_le hℓ hp
  refine ⟨j, r, u, hu, hur, hr, hℓu, hm, fun m hm1 hm2 ↦ ?_, fun hj ↦ ?_⟩
  · have := hrep (m - 1) (by omega) (by omega)
    rwa [show m - 1 + r + 1 = m + r by omega, show m - 1 + 1 = m by omega] at this
  · have := hne hj
    rwa [show j + r + 1 = j + 1 + r by omega] at this

end Nat
