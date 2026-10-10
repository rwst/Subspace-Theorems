/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Theorem11

-- Used only inside proofs.
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Theorem 1.4 (Bugeaud 2013, §4): quasi-periodic continued fractions

A **quasi-periodic** continued fraction is

`α = [0; a₁, …, a_{n₀-1}, (a_{n₀}, …, a_{n₀+r₀-1})^{λ₀}, (a_{n₁}, …, a_{n₁+r₁-1})^{λ₁}, …]`

with `n_{k+1} = n_k + λ_k r_k`: from position `n_k` on, a block of length `r_k` is repeated
`λ_k` times. **Theorem 1.4**: if `(q_ℓ^{1/ℓ})` is bounded, `a` is not eventually periodic and
`liminf λ_{k+1} / λ_k > 1`, then `α` is transcendental.

The proof (§4): with `W_k = a₁ … a_{n_k - 1}` and `U_k` the block repeated `⌊λ_k / 2⌋` times,
`W_k U_k U_k` is a prefix of `a`, and the geometric growth of `λ_k` bounds `|W_k| / |U_k|` along
the `k` at which `r_k` is a record; Theorem 3.1 applies.

## Main definitions

* `Nat.IsQuasiPeriodic a n r l`: the data `n_k`, `r_k`, `λ_k = l k` of a quasi-periodic `a`.

## Main results

* `Nat.IsQuasiPeriodic.hasSpadeRepetitions`: `liminf λ_{k+1} / λ_k > 1` gives the repetitions
  of Condition `(♠)`.
* `Nat.transcendental_contFrac_of_isQuasiPeriodic`: **Theorem 1.4**.

## Implementation notes

⚠ **Bounded `r_k` is not a separate case.** The paper refers to Corollary 3.3 of
Adamczewski–Bugeaud (2007) when `(r_k)` is bounded. The argument for unbounded `(r_k)` only needs
some `R` with `r_h ≤ R r_k` for all `h < k`, for infinitely many `k`: records (`R = 1`) when
`(r_k)` is unbounded, every `k` (`R` = the bound) when it is bounded. So Theorem 3.1 covers both.

⚠ **`liminf λ_{k+1} / λ_k > 1` is stated as `∃ ε > 0, ∀ᶠ k, (1 + ε) λ_k < λ_{k+1}`**, which is
equivalent. `Filter.liminf` on `ℝ` is not used: when the ratios tend to `∞` it returns a junk
value.

⚠ **The block is `U_k = (a_{n_k} … a_{n_k+r_k-1})^{⌊λ_k/2⌋}`**, of length `P = ⌊λ_k/2⌋ r_k`, so
`a` has period `P` on a segment of length `2P` after position `n_k - 1` (indexing from `0`),
which is what `Function.hasSpadeRepetitions_of_periodic` consumes (with `w = 2`).
-/

@[expose] public section

open Filter

namespace Nat

variable {a : ℕ → ℕ}

/-- **A quasi-periodic sequence** `a₁ a₂ …`: from position `n k` on, a block of length `r k ≥ 1`
is repeated `l k` times (`l k` is the paper's `λ_k`), and `n (k + 1) = n k + l k * r k`. The
repetition is stated as the period `r k` on `[n k, n (k + 1))`. -/
structure IsQuasiPeriodic (a : ℕ → ℕ) (n r l : ℕ → ℕ) : Prop where
  one_le_n : 1 ≤ n 0
  one_le_r : ∀ k, 1 ≤ r k
  succ : ∀ k, n (k + 1) = n k + l k * r k
  per : ∀ k m, n k ≤ m → m + r k < n (k + 1) → a (m + r k) = a m

variable {n r l : ℕ → ℕ}

/-- The positions `n k` are at least `1`. -/
theorem IsQuasiPeriodic.one_le (h : IsQuasiPeriodic a n r l) (k : ℕ) : 1 ≤ n k := by
  induction k with
  | zero => exact h.one_le_n
  | succ k ih => rw [h.succ]; omega

/-- Infinitely many `k` at which `r` dominates its past: `r h ≤ R r k` for all `h < k`. -/
theorem exists_frequently_le_mul (hr : ∀ k, 1 ≤ r k) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ᶠ k in atTop, ∀ h < k, (r h : ℝ) ≤ R * r k := by
  by_cases hb : BddAbove (Set.range r)
  · obtain ⟨R, hR⟩ := hb
    refine ⟨R, Nat.cast_nonneg R, (Eventually.of_forall fun k h _ ↦ ?_).frequently⟩
    have h1 : (1 : ℝ) ≤ r k := by exact_mod_cast hr k
    have h2 : (r h : ℝ) ≤ R := by exact_mod_cast hR ⟨h, rfl⟩
    nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  · refine ⟨1, zero_le_one, frequently_atTop.mpr fun N ↦ ?_⟩
    classical
    set M := (Finset.range N).sup r
    have hex : ∃ j, M < r j := by
      by_contra hne
      push Not at hne
      exact hb ⟨M, by rintro _ ⟨j, rfl⟩; exact hne j⟩
    refine ⟨Nat.find hex, ?_, fun h hh ↦ ?_⟩
    · by_contra hlt
      exact (Nat.find_spec hex).not_ge
        (Finset.le_sup (f := r) (Finset.mem_range.mpr (by omega)))
    · have := Nat.find_min hex hh
      push Not at this
      have := Nat.find_spec hex
      rw [one_mul]
      exact_mod_cast (show r h ≤ r (Nat.find hex) by omega)

/-- **The repetitions of `(♠)` in a quasi-periodic sequence** (§4, proof of Theorem 1.4): if
`λ_{k+1} > (1 + ε) λ_k` for all large `k`, then `a₁ a₂ …` has the repetitions of `(♠)`. -/
theorem IsQuasiPeriodic.hasSpadeRepetitions (h : IsQuasiPeriodic a n r l) {ε : ℝ}
    (hε : 0 < ε) (hl : ∀ᶠ k in atTop, (1 + ε) * l k < l (k + 1)) :
    Function.HasSpadeRepetitions fun k ↦ a (k + 1) := by
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hl
  -- `λ` grows
  have hlinc : ∀ k, k0 ≤ k → l k < l (k + 1) := fun k hk ↦ by
    have := hk0 k hk
    have : (l k : ℝ) < l (k + 1) := by nlinarith [(Nat.cast_nonneg (l k) : (0 : ℝ) ≤ l k)]
    exact_mod_cast this
  have hlgrow : ∀ j, j ≤ l (k0 + j) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => have := hlinc (k0 + j) (by omega); rw [← add_assoc]; omega
  -- the prefix before `n_k` is short: `ε (n_k - n_{k₀}) ≤ B λ_k` if `r_h ≤ B` on `[k₀, k)`
  have hkey : ∀ B : ℝ, 0 ≤ B → ∀ j, (∀ i, k0 ≤ i → i < k0 + j → (r i : ℝ) ≤ B) →
      ε * ((n (k0 + j) : ℝ) - n k0) ≤ B * l (k0 + j) := by
    intro B hB j
    induction j with
    | zero => intro _; simp only [add_zero, sub_self, mul_zero]; positivity
    | succ j ih =>
      intro hrB
      have h1 := ih fun i hi hij ↦ hrB i hi (by omega)
      have h2 := hrB (k0 + j) (by omega) (by omega)
      have h3 := hk0 (k0 + j) (by omega)
      have hs : (n (k0 + (j + 1)) : ℝ) = n (k0 + j) + l (k0 + j) * r (k0 + j) := by
        rw [← add_assoc]; exact_mod_cast h.succ (k0 + j)
      rw [hs, ← add_assoc]
      have hl0 : (0 : ℝ) ≤ l (k0 + j) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hε.le hl0)]
  -- the good indices
  obtain ⟨R, hR, hfr⟩ := exists_frequently_le_mul h.one_le_r
  obtain ⟨g, hg, hgd⟩ :=
    extraction_of_frequently_atTop (hfr.and_eventually (eventually_ge_atTop (k0 + 2)))
  set P : ℕ → ℕ := fun m ↦ l (g m) / 2 * r (g m) with hP
  have hl2 : ∀ m, 2 ≤ l (g m) := fun m ↦ by
    have := hlgrow (g m - k0); have := (hgd m).2
    rw [show k0 + (g m - k0) = g m by omega] at *; omega
  have hP1 : ∀ m, 1 ≤ P m := fun m ↦ by
    have := hl2 m; have := h.one_le_r (g m)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- `λ_k r_k ≤ 4 P`
  have hlr : ∀ m, l (g m) * r (g m) ≤ 4 * P m := fun m ↦ by
    have h1 := Nat.div_add_mod (l (g m)) 2
    have h2 := Nat.mod_lt (l (g m)) (show 0 < 2 by omega)
    have h3 : l (g m) ≤ 4 * (l (g m) / 2) := by have := hl2 m; omega
    calc l (g m) * r (g m) ≤ 4 * (l (g m) / 2) * r (g m) := Nat.mul_le_mul_right _ h3
      _ = 4 * P m := by rw [hP, mul_assoc]
  refine Function.hasSpadeRepetitions_of_periodic (w := 2) (C' := n k0 + 4 * R / ε)
    (r := fun m ↦ n (g m) - 1) (s := P) one_lt_two ?_ hP1 (fun m ↦ ?_) (fun m i hi hiL ↦ ?_)
  · refine tendsto_atTop_atTop.mpr fun b ↦ ⟨k0 + 2 * b, fun m hm ↦ ?_⟩
    have h1 := hlgrow (g m - k0)
    have h2 := (hgd m).2
    have h3 : m ≤ g m := hg.id_le m
    rw [show k0 + (g m - k0) = g m by omega] at h1
    have h4 : b ≤ l (g m) / 2 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact h4.trans (Nat.le_mul_of_pos_right _ (h.one_le_r _))
  · -- `n_k - 1 ≤ C' P`
    have hk := (hgd m).2
    have hb := hkey (R * r (g m)) (by positivity) (g m - k0) fun i _ hi ↦ (hgd m).1 i (by omega)
    rw [show k0 + (g m - k0) = g m by omega] at hb
    have hP1' : (1 : ℝ) ≤ P m := by exact_mod_cast hP1 m
    have hlr' : (l (g m) : ℝ) * r (g m) ≤ 4 * P m := by exact_mod_cast hlr m
    have hsub : ((n (g m) - 1 : ℕ) : ℝ) ≤ n (g m) := by exact_mod_cast Nat.sub_le _ _
    have hn0 : (0 : ℝ) ≤ n k0 := Nat.cast_nonneg _
    have hdiv : (n (g m) : ℝ) - n k0 ≤ R * (l (g m) * r (g m)) / ε := by
      rw [le_div_iff₀ hε]; linarith
    have hRl : R * (l (g m) * r (g m)) / ε ≤ 4 * R / ε * P m := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; nlinarith
    calc ((n (g m) - 1 : ℕ) : ℝ) ≤ n k0 + 4 * R / ε * P m := by linarith
      _ ≤ (n k0 + 4 * R / ε) * P m := by nlinarith
  · -- the period `P` on `[n_k - 1, n_k - 1 + 2 P)`
    have hceil : ⌈(2 : ℝ) * (P m : ℝ)⌉₊ = 2 * P m := by
      rw [show (2 : ℝ) * (P m : ℝ) = ((2 * P m : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
    rw [hceil] at hiL
    have hn1 := h.one_le (g m)
    have hc : 2 * (l (g m) / 2) * r (g m) ≤ l (g m) * r (g m) :=
      Nat.mul_le_mul_right _ (Nat.mul_div_le _ _)
    have hsucc := h.succ (g m)
    have hPm : P m = l (g m) / 2 * r (g m) := rfl
    have e := Function.forall_add_mul_eq_of_forall_add_eq (h.per (g m)) (l (g m) / 2) (i + 1)
      (by omega) (by rw [mul_assoc] at hc; omega)
    rw [show i + P m + 1 = i + 1 + l (g m) / 2 * r (g m) by omega]
    exact e

/-- **Theorem 1.4 (Bugeaud 2013).** A quasi-periodic continued fraction
`[0; a₁, …, a_{n₀-1}, (a_{n₀} … a_{n₀+r₀-1})^{λ₀}, …]` with `(q_ℓ^{1/ℓ})` bounded, `a` not
eventually periodic and `liminf λ_{k+1} / λ_k > 1` (that is, `λ_{k+1} > (1 + ε) λ_k` for some
`ε > 0` and all large `k`) is transcendental. -/
theorem transcendental_contFrac_of_isQuasiPeriodic (ha : ∀ n, 1 ≤ a (n + 1))
    (hq : BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))))
    (hp : ¬ Function.IsEventuallyPeriodic fun k ↦ a (k + 1)) (h : IsQuasiPeriodic a n r l)
    {ε : ℝ} (hε : 0 < ε) (hl : ∀ᶠ k in atTop, (1 + ε) * l k < l (k + 1)) :
    Transcendental ℚ (contFrac a) :=
  transcendental_contFrac_of_isSpade ha hq ⟨hp, h.hasSpadeRepetitions hε hl⟩

end Nat
