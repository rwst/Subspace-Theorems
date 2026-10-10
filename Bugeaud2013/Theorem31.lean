/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.FirstCase
public import Bugeaud2013.Lagrange

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
# Bugeaud 2013, Theorem 3.1: stammering continued fractions are transcendental

**Theorem 3.1.** Let `a = (a_ℓ)_{ℓ ≥ 1}` be a sequence of positive integers with
`(q_ℓ^{1/ℓ})_{ℓ ≥ 1}` bounded. If `a` satisfies Condition `(♠)`, then `α = [0; a₁, a₂, …]` is
transcendental.

The analytic core is `Nat.false_of_spadeData`: algebraic `α` with the normalized lengths of
`(♠)` satisfies a non-trivial rational quadratic equation. It assembles the first Subspace
application (`Nat.exists_spade_relation`), the first case (`Nat.false_of_first_case`) and the
second case (the Claim `Nat.claim` twice around `Nat.exists_spade_relation_three`). Since
`(♠)` excludes eventually periodic sequences, Lagrange's theorem
(`Nat.isEventuallyPeriodic_of_quadratic`) turns "quadratic" into a contradiction.

## Main results

* `Nat.exists_contDen_le_two_pow`: bounded `q_ℓ^{1/ℓ}` gives `q_ℓ ≤ 2^{K ℓ}`.
* `Nat.false_of_spadeData`: the core of the proof.
* `Nat.transcendental_contFrac_of_isSpade`: **Theorem 3.1**.

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, Theorem 3.1.
-/

@[expose] public section

open Filter

namespace Nat

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

omit ha in
/-- **The growth hypothesis of Theorem 3.1** in the form used by the proof: if `(q_ℓ^{1/ℓ})` is
bounded, then `q_ℓ ≤ 2^{K ℓ}` for some `K`. -/
theorem exists_contDen_le_two_pow
    (hq : BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ)))) :
    ∃ K : ℕ, ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ) := by
  obtain ⟨B, hB⟩ := hq
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, fun ℓ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  have hq0 : (0 : ℝ) ≤ contDen a ℓ := Nat.cast_nonneg _
  have hb : (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ)) ≤ B := hB ⟨ℓ, rfl⟩
  have hroot : ((contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))) ^ ℓ = contDen a ℓ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  calc (contDen a ℓ : ℝ) = ((contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))) ^ ℓ := hroot.symm
    _ ≤ ((2 : ℝ) ^ K) ^ ℓ :=
        pow_le_pow_left₀ (Real.rpow_nonneg hq0 _) (hb.trans hK.le) ℓ
    _ = 2 ^ (K * ℓ) := by rw [← pow_mul]

/-- **The core of the proof of Theorem 3.1.** If `α = [0; a₁, a₂, …]` is algebraic, satisfies no
non-trivial rational equation of degree at most `2`, and `q_ℓ ≤ 2^{K ℓ}`, then the normalized
lengths of Condition `(♠)` cannot exist. -/
theorem false_of_spadeData (halg : IsAlgebraic ℚ (contFrac a))
    (hq : ∀ A B C : ℚ, (A : ℝ) * contFrac a ^ 2 + B * contFrac a + C = 0 →
      A = 0 ∧ B = 0 ∧ C = 0)
    {K : ℕ} (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) {w u v : ℕ → ℕ} {C : ℕ}
    (hd : SpadeData a w u v C) : False := by
  obtain ⟨x, hx0, hrel⟩ := exists_spade_relation ha halg hK hd
  by_cases hcase : ∃ ℓ, ∃ᶠ n in atTop,
      (∑ i, (x i : ℝ) * (spadeVec a (w n - 1) (u n + v n) i : ℝ) = 0) ∧ w n = ℓ
  · -- **first case**: `w_n = ℓ` infinitely often
    obtain ⟨ℓ, hℓ⟩ := hcase
    obtain ⟨g, hg, hgP⟩ := extraction_of_frequently_atTop hℓ
    have hℓ1 : 1 ≤ ℓ := (hgP 0).2 ▸ hd.one_le (g 0)
    set j := ℓ - 1 with hj
    set M : ℕ → ℕ := fun n ↦ j + (u (g n) + v (g n))
    have hM : Tendsto M atTop atTop :=
      tendsto_atTop_mono (fun n ↦ Nat.le_add_left _ _) (hd.tendsto_add.comp hg.tendsto_atTop)
    set Y : Fin 4 → ℚ := ![x 0 * contDen a j + x 2 * contNum a j,
      -(x 0 * contDen a (j + 1) + x 2 * contNum a (j + 1)),
      x 1 * contDen a j + x 3 * contNum a j,
      -(x 1 * contDen a (j + 1) + x 3 * contNum a (j + 1))] with hYdef
    refine false_of_first_case ha halg hq hM (Y := Y) ?_ fun n ↦ ?_
    · -- `Y ≠ 0`, as `(p_j q_{j+1} - p_{j+1} q_j)² = 1`
      intro hY
      have hdet : (contNum a (j + 1) : ℚ) * contDen a j - contNum a j * contDen a (j + 1) =
          (-1) ^ j := by exact_mod_cast contNum_mul_contDen_sub a j
      have hd0 : ((-1 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      have y0 : Y 0 = 0 := by rw [hY]; rfl
      have y1 : Y 1 = 0 := by rw [hY]; rfl
      have y2 : Y 2 = 0 := by rw [hY]; rfl
      have y3 : Y 3 = 0 := by rw [hY]; rfl
      simp only [hYdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at y0 y1 y2 y3
      have e0 : x 0 * (-1) ^ j = 0 := by
        rw [← hdet]; linear_combination (contNum a (j + 1) : ℚ) * y0 + contNum a j * y1
      have e2 : x 2 * (-1) ^ j = 0 := by
        rw [← hdet]; linear_combination -(contDen a (j + 1) : ℚ) * y0 - contDen a j * y1
      have e1 : x 1 * (-1) ^ j = 0 := by
        rw [← hdet]; linear_combination (contNum a (j + 1) : ℚ) * y2 + contNum a j * y3
      have e3 : x 3 * (-1) ^ j = 0 := by
        rw [← hdet]; linear_combination -(contDen a (j + 1) : ℚ) * y2 - contDen a j * y3
      refine hx0 (funext fun i ↦ ?_)
      fin_cases i
      · exact (_root_.mul_eq_zero.mp e0).resolve_right hd0
      · exact (_root_.mul_eq_zero.mp e1).resolve_right hd0
      · exact (_root_.mul_eq_zero.mp e2).resolve_right hd0
      · exact (_root_.mul_eq_zero.mp e3).resolve_right hd0
    · -- the relation at `(q_{M+1}, q_M, p_{M+1}, p_M)`
      obtain ⟨h, hw⟩ := hgP n
      rw [hw, Fin.sum_univ_four, spadeVec_zero, spadeVec_one, spadeVec_two, spadeVec_three,
        show ℓ - 1 + 1 + (u (g n) + v (g n)) = M n + 1 by simp only [M, j]; omega,
        show ℓ - 1 + (u (g n) + v (g n)) = M n by simp only [M, j],
        show ℓ - 1 + 1 = j + 1 by simp only [j]] at h
      simp only [hYdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      push_cast at h ⊢
      linear_combination h
  · -- **second case**: `w_n → ∞` along the relation
    have hc' (ℓ : ℕ) : ∀ᶠ n in atTop,
        ¬((∑ i, (x i : ℝ) * (spadeVec a (w n - 1) (u n + v n) i : ℝ) = 0) ∧ w n = ℓ) :=
      not_frequently.mp fun h ↦ hcase ⟨ℓ, h⟩
    obtain ⟨g, hg, hgP⟩ := extraction_of_frequently_atTop hrel
    have hd' := hd.comp hg
    have hw : Tendsto (w ∘ g) atTop atTop := by
      refine tendsto_atTop.2 fun L ↦ ?_
      have hall := (eventually_all_finset (Finset.range L)).2 fun ℓ _ ↦
        hg.tendsto_atTop.eventually (hc' ℓ)
      filter_upwards [hall] with n hn
      by_contra hlt
      push Not at hlt
      exact hn (w (g n)) (Finset.mem_range.2 hlt) ⟨hgP n, rfl⟩
    -- the Claim: `x₁ + (x₂ + x₃) α + x₄ α² = 0`, so `x₁ = x₄ = 0` and `x₂ = -x₃`
    have hS := claim ha hd' hw (x := fun i ↦ (x i : ℝ))
      (Eventually.frequently (Eventually.of_forall hgP))
    obtain ⟨h3, h12, h0⟩ := hq (x 3) (x 1 + x 2) (x 0) (by push_cast; linear_combination hS)
    have hx1 : x 1 ≠ 0 := by
      intro h1
      have h2 : x 2 = 0 := by rw [h1, zero_add] at h12; exact h12
      exact hx0 (funext fun i ↦ by fin_cases i <;> assumption)
    -- hence `B₂ = B₃` along the subsequence
    have hB (n : ℕ) : spadeVec a ((w ∘ g) n - 1) ((u ∘ g) n + (v ∘ g) n) 1 =
        spadeVec a ((w ∘ g) n - 1) ((u ∘ g) n + (v ∘ g) n) 2 := by
      have h := hgP n
      rw [Fin.sum_univ_four, h0, h3, show x 2 = -x 1 by linarith [h12]] at h
      push_cast at h
      have hx1' : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx1
      have : (x 1 : ℝ) * ((spadeVec a (w (g n) - 1) (u (g n) + v (g n)) 1 : ℝ) -
          spadeVec a (w (g n) - 1) (u (g n) + v (g n)) 2) = 0 := by linear_combination h
      have := (_root_.mul_eq_zero.mp this).resolve_left hx1'
      exact_mod_cast sub_eq_zero.mp this
    -- the last Subspace application and the Claim again
    obtain ⟨t, ht0, htrel⟩ := exists_spade_relation_three ha halg hK hd' hB
    have hT := claim ha hd' hw (x := ![(t 0 : ℝ), t 1, 0, t 2]) (htrel.mono fun n hn ↦ by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination hn)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, add_zero] at hT
    obtain ⟨g2, g1, g0⟩ := hq (t 2) (t 1) (t 0) (by linear_combination hT)
    exact ht0 (funext fun i ↦ by fin_cases i <;> assumption)

/-- **Bugeaud 2013, Theorem 3.1.** Let `a₁, a₂, …` be positive integers with `(q_ℓ^{1/ℓ})`
bounded. If `(a_ℓ)_{ℓ ≥ 1}` satisfies Condition `(♠)`, then `[0; a₁, a₂, …]` is transcendental. -/
theorem transcendental_contFrac_of_isSpade
    (hq : BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))))
    (hs : Function.IsSpade fun k ↦ a (k + 1)) : Transcendental ℚ (contFrac a) := by
  intro halg
  obtain ⟨hnp, hrep⟩ := hs
  obtain ⟨w, u, v, C, hd⟩ := exists_spadeData hrep
  obtain ⟨K, hK⟩ := exists_contDen_le_two_pow hq
  refine false_of_spadeData ha halg (fun A B C h ↦ ?_) hK hd
  by_contra hne
  exact hnp (isEventuallyPeriodic_of_quadratic ha hne h)

end Positive

end Nat
