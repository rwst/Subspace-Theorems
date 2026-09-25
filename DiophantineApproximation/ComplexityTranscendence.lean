/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FactorComplexity
public import DiophantineApproximation.TranscendenceCriterion

/-!
# The complexity of an algebraic irrational

**Layer 7.5** (Adamczewski–Bugeaud 2007, Theorem 1). For `b ≥ 2` and `a : ℕ → Fin b`, if
`ξ = ∑ k, a k / b ^ (k + 1)` is an algebraic irrational, then the number `p n` of distinct words
of length `n` in `a` satisfies `p n / n → ∞`.

The proof is Layer 7.4 and the combinatorial lemma of `DiophantineApproximation/FactorComplexity`:
if `p n / n` does not tend to `∞`, then `p n ≤ C n` for infinitely many `n`, so `a` is stammering
(`Function.exists_periodic_of_frequently_complexity_le`), and a stammering expansion of an
irrational number is transcendental (`Real.transcendental_ofDigits_of_forall_periodic`).

## Main results

* `Real.tendsto_complexity_div_atTop`: **the theorem**.
* `Real.transcendental_ofDigits_of_frequently_complexity_le`: the same, read as a transcendence
  criterion: `p n ≤ C n` for infinitely many `n` and `a` not eventually periodic.
* `Real.irrational_ofDigits_iff`: for `b ≥ 2`, `ξ` is irrational if and only if `a` is not
  eventually periodic, so the two readings have the same hypotheses.

## Implementation notes

⚠ **Irrationality and non-periodicity are the same hypothesis, but only one direction was
needed before.** Layer 7.4 proved `Real.irrational_ofDigits` (not eventually periodic ⟹
irrational), which is all the criterion consumes. The converse is cheap once the tails are in
hand: a period `p` from `N` on makes the tail at `N` a fixed point of `T ↦ (P + T) / b ^ p`
(`Real.pow_mul_ofDigits`), hence rational, and it is recorded so that the theorem may be stated
with either hypothesis.

⚠ **The theorem says nothing about any particular `n`.** `p n / n → ∞` is compatible with
`p n ≤ n + 1` at every `n` below any given bound; what is excluded is a linear bound along an
infinite set. The combinatorial lemma consumes exactly that, and the Morse–Hedlund lower bound
`p n ≥ n + 1` (`Function.lt_complexity`) is the elementary floor any irrational meets.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565.

This is part of Layer 7.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Filter

namespace Real

variable {b : ℕ}

/-- **An eventually periodic expansion has a rational value**: with period `p` from `N` on, the
tail at `N` is `P / (b ^ p - 1)`. -/
theorem not_irrational_ofDigits (hb : 2 ≤ b) {a : ℕ → Fin b}
    (ha : Function.IsEventuallyPeriodic a) : ¬ Irrational (ofDigits a) := by
  obtain ⟨N, p, hp, hper⟩ := ha
  set c : ℕ → Fin b := fun i ↦ a (i + N) with hc
  have hcp : (fun i ↦ c (i + p)) = c := by
    funext i; simp only [hc]; rw [show i + p + N = i + N + p by omega, hper _ (by omega)]
  have hB : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < b)) hp.ne'
  have htail : ofDigits c = (digitsPrefix c p : ℝ) / ((b : ℝ) ^ p - 1) := by
    have := pow_mul_ofDigits c p
    rw [hcp] at this
    rw [eq_div_iff (by linarith)]; linarith
  have hb0 : (b : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))
  have hval : ofDigits a = (((digitsPrefix a N : ℚ) + (digitsPrefix c p : ℚ) /
      ((b : ℚ) ^ p - 1)) / (b : ℚ) ^ N : ℚ) := by
    push_cast
    rw [eq_div_iff hb0, mul_comm, pow_mul_ofDigits a N]
    change _ + ofDigits c = _
    rw [htail]
  rw [hval]
  exact Rat.not_irrational _

/-- For `b ≥ 2`, **the value of an expansion is irrational if and only if the expansion is not
eventually periodic.** -/
theorem irrational_ofDigits_iff (hb : 2 ≤ b) {a : ℕ → Fin b} :
    Irrational (ofDigits a) ↔ ¬ Function.IsEventuallyPeriodic a :=
  ⟨fun h ha ↦ not_irrational_ofDigits hb ha h, irrational_ofDigits⟩

/-- **A transcendence criterion by complexity.** If `a` is not eventually periodic and has at most
`C n` factors of length `n` for infinitely many `n`, its value is transcendental. -/
theorem transcendental_ofDigits_of_frequently_complexity_le (hb : 2 ≤ b) {a : ℕ → Fin b}
    (ha : ¬ Function.IsEventuallyPeriodic a) {C : ℝ}
    (h : ∃ᶠ n in atTop, (Function.complexity a n : ℝ) ≤ C * n) :
    Transcendental ℚ (ofDigits a) := by
  obtain ⟨w, C', hw, hC', r, s, hs, -, hrs, hper⟩ :=
    Function.exists_periodic_of_frequently_complexity_le h
  exact transcendental_ofDigits_of_forall_periodic hb (irrational_ofDigits ha) hw hC' hs hrs hper

/-- **The complexity of an algebraic irrational** (Adamczewski–Bugeaud 2007, Theorem 1). For
`b ≥ 2`, if `∑ k, a k / b ^ (k + 1)` is algebraic and irrational, then the number `p n` of
distinct words of length `n` in its digits satisfies `p n / n → ∞`. -/
theorem tendsto_complexity_div_atTop (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (ofDigits a)) (halg : IsAlgebraic ℚ (ofDigits a)) :
    Tendsto (fun n ↦ (Function.complexity a n : ℝ) / n) atTop atTop := by
  rw [tendsto_atTop]
  by_contra! hC
  obtain ⟨C, hC⟩ := hC
  refine transcendental_ofDigits_of_frequently_complexity_le hb
    ((irrational_ofDigits_iff hb).mp hirr) (C := C) ?_ halg
  refine (hC.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  have : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ((div_lt_iff₀ this).mp hn).le

end Real

/-! ### Acceptance criteria -/

section Examples

open Classical in
/-- The digits of `∑ k, 2 ^ (-2 ^ k)` in base `2`: `1` at the positions `2 ^ k - 1`. -/
private noncomputable def powTwoDigits (x : ℕ) : Fin 2 := if ∃ u, x + 1 = 2 ^ u then 1 else 0

private theorem powTwoDigits_eq_zero {x : ℕ} (h : ¬ ∃ u, x + 1 = 2 ^ u) : powTwoDigits x = 0 := by
  classical
  exact ite_eq_right h

private theorem exists_of_powTwoDigits_eq_one {x : ℕ} (h : powTwoDigits x = 1) :
    ∃ u, x + 1 = 2 ^ u := by
  by_contra h'
  rw [powTwoDigits_eq_zero h'] at h
  exact absurd h (by decide)

/-- Beyond position `2 n` a window of length `n` contains at most one `1`. -/
private theorem eq_of_powTwoDigits_eq_one {n i j t : ℕ} (hi : 2 * n ≤ i) (hj : j < n) (ht : t < n)
    (h1 : powTwoDigits (i + j) = 1) (h2 : powTwoDigits (i + t) = 1) : j = t := by
  obtain ⟨u, hu⟩ := exists_of_powTwoDigits_eq_one h1
  obtain ⟨v, hv⟩ := exists_of_powTwoDigits_eq_one h2
  rcases lt_trichotomy u v with huv | rfl | huv
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt huv)
    rw [pow_succ] at this; omega
  · omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt huv)
    rw [pow_succ] at this; omega

/-- **Conformance: the complexity of the powers of `2` is at most `3 n + 1`** — `2 n` factors
start before position `2 n`, and every later one has at most one `1`, in one of `n` places. -/
private theorem complexity_powTwoDigits_le (n : ℕ) :
    Function.complexity powTwoDigits n ≤ 3 * n + 1 := by
  set g : ℕ → List (Fin 2) := fun j ↦ List.ofFn fun t : Fin n ↦ if (t : ℕ) = j then 1 else 0
  have hsub : Function.factors powTwoDigits n ⊆
      (fun i ↦ Function.factor powTwoDigits i n) '' ↑(Finset.range (2 * n)) ∪
        g '' ↑(Finset.range (n + 1)) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i < 2 * n
    · exact Or.inl ⟨i, by simpa using hi, rfl⟩
    right
    by_cases h : ∃ j < n, powTwoDigits (i + j) = 1
    · obtain ⟨j, hj, hj1⟩ := h
      refine ⟨j, by simp; omega, ?_⟩
      simp only [g, Function.factor]
      congr 1; funext t
      split_ifs with htj
      · rw [← htj] at hj1; exact hj1.symm
      · by_contra hne
        have : powTwoDigits (i + t) = 1 := by
          revert hne; generalize powTwoDigits (i + t) = y; revert y; decide
        exact htj (eq_of_powTwoDigits_eq_one (by omega) t.2 hj this hj1)
    · push Not at h
      refine ⟨n, by simp, ?_⟩
      simp only [g, Function.factor]
      congr 1; funext t
      rw [ite_eq_right (show ¬ (t : ℕ) = n by omega)]
      have := h t t.2
      revert this; generalize powTwoDigits (i + t) = y; revert y; decide
  calc Function.complexity powTwoDigits n
      ≤ ((fun i ↦ Function.factor powTwoDigits i n) '' ↑(Finset.range (2 * n)) ∪
          g '' ↑(Finset.range (n + 1))).ncard :=
        Set.ncard_le_ncard hsub (((Finset.finite_toSet _).image _).union
          ((Finset.finite_toSet _).image _))
    _ ≤ ((fun i ↦ Function.factor powTwoDigits i n) '' ↑(Finset.range (2 * n))).ncard +
          (g '' ↑(Finset.range (n + 1))).ncard := Set.ncard_union_le _ _
    _ ≤ (↑(Finset.range (2 * n)) : Set ℕ).ncard + (↑(Finset.range (n + 1)) : Set ℕ).ncard :=
        add_le_add (Set.ncard_image_le (Finset.finite_toSet _))
          (Set.ncard_image_le (Finset.finite_toSet _))
    _ = 3 * n + 1 := by rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range,
          Finset.card_range]; ring

private theorem not_isEventuallyPeriodic_powTwoDigits :
    ¬ Function.IsEventuallyPeriodic powTwoDigits := by
  rintro ⟨N, p, hp, h⟩
  obtain ⟨j, hj⟩ : ∃ j, N + p < 2 ^ j := ⟨N + p, Nat.lt_two_pow_self⟩
  have e := h (2 ^ j - 1) (by omega)
  have h1 : powTwoDigits (2 ^ j - 1) = 1 := by
    classical
    exact ite_eq_left ⟨j, by omega⟩
  rw [h1, powTwoDigits_eq_zero] at e
  · exact absurd e (by decide)
  rintro ⟨u, hu⟩
  have hlt : 2 ^ j < 2 ^ u := by omega
  have hgt : 2 ^ u < 2 ^ (j + 1) := by rw [pow_succ]; omega
  rw [Nat.pow_lt_pow_iff_right (by norm_num)] at hlt hgt
  omega

/-- **The roadmap's test: `∑ k, 2 ^ (-2 ^ k)` is transcendental by 7.5.** Its binary digits have
complexity at most `3 n + 1 ≤ 4 n` and are not eventually periodic. -/
example : Transcendental ℚ (Real.ofDigits powTwoDigits) :=
  Real.transcendental_ofDigits_of_frequently_complexity_le le_rfl
    not_isEventuallyPeriodic_powTwoDigits (C := 4) <| frequently_atTop.mpr fun N ↦
      ⟨N + 1, Nat.le_succ N, by
        have := complexity_powTwoDigits_le (N + 1)
        have : (Function.complexity powTwoDigits (N + 1) : ℝ) ≤ 3 * (N + 1 : ℕ) + 1 := by
          exact_mod_cast this
        push_cast at this ⊢; linarith⟩

/-- The same number is not an algebraic irrational, read off the theorem itself: `p n / n` stays
below `4`. -/
example : ¬ (Irrational (Real.ofDigits powTwoDigits) ∧ IsAlgebraic ℚ (Real.ofDigits powTwoDigits))
    := by
  rintro ⟨hirr, halg⟩
  obtain ⟨n, hn, hn1⟩ := (((Real.tendsto_complexity_div_atTop le_rfl hirr halg).eventually_gt_atTop
    4).and (eventually_ge_atTop 1)).exists
  have h := complexity_powTwoDigits_le n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h' : (Function.complexity powTwoDigits n : ℝ) ≤ 3 * n + 1 := by exact_mod_cast h
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [lt_div_iff₀ hn0] at hn
  linarith

end Examples

/-- An algebraic irrational has, in base `10`, more than `1000 n` distinct blocks of `n` digits for
every large `n`. -/
example {a : ℕ → Fin 10} (hirr : Irrational (Real.ofDigits a))
    (halg : IsAlgebraic ℚ (Real.ofDigits a)) :
    ∀ᶠ n in atTop, 1000 * n < Function.complexity a n := by
  filter_upwards [(Real.tendsto_complexity_div_atTop (by norm_num) hirr halg).eventually_gt_atTop
    1000, eventually_ge_atTop 1] with n hn hn1
  have : (0 : ℝ) < n := by exact_mod_cast hn1
  exact_mod_cast (lt_div_iff₀ this).mp hn

/-- Rejection: irrationality is load-bearing. The constant sequence `0` has one factor of each
length and an algebraic value, so `p n / n → 0`. -/
example : ¬ Tendsto (fun n ↦ (Function.complexity (fun _ ↦ (0 : Fin 10)) n : ℝ) / n) atTop
    atTop := by
  intro h
  obtain ⟨n, hn, hn2⟩ := ((h.eventually_gt_atTop 1).and (eventually_ge_atTop 2)).exists
  rw [Function.complexity_const, Nat.cast_one] at hn
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  rw [lt_div_iff₀ (by linarith)] at hn
  linarith
