/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MahlerExponent

-- Used only inside proofs.
import Mathlib.Data.Fintype.Pi

/-!
# The box principle: `n ≤ w_n`

Every real number that is not algebraic of degree at most `n` satisfies `mahlerExponent n ξ ≥ n`.
This is Dirichlet's argument on the `n + 1` numbers `1, ξ, …, ξ ^ n`: among the `(H+1) ^ (n+1)`
values `∑ a k * ξ ^ k` with `0 ≤ a k ≤ H`, two lie in the same one of `(H+1) ^ (n+1) - 1`
subintervals of the interval of length `2 H ∑ |ξ| ^ k` that contains them all, and their
difference is an integer polynomial of degree at most `n`, of naive height at most `H`, with
`|P ξ| ≤ 4 (∑ |ξ| ^ k) H ^ (-n)`.

Together with `Real.koksmaExponent_le_mahlerExponent` this is the elementary half of Layer 1.3;
Wirsing's converse inequalities, which bound `w_n` above by `w_n^*`, are not here.

## Main results

* `Real.le_mahlerExponent_of_aeval_ne_zero`: **`n ≤ mahlerExponent n ξ`** whenever no nonzero
  integer polynomial of degree at most `n` vanishes at `ξ`.
* `Real.le_mahlerExponent_of_transcendental`: the same for a transcendental `ξ`, at every `n`.

## Implementation notes

⚠ **The roadmap's name `le_mahlerExponent` was already taken.** In Layer 1.2 it is the order
lemma `(w : ℝ≥0∞) ≤ mahlerExponent n ξ` from an infinite `mahlerSet`, which every proof of this
layer uses; the box principle is `Real.le_mahlerExponent_of_aeval_ne_zero`.

⚠ **The box principle produces one polynomial per `H`, and infinitude is again the height gap.**
Nothing says the polynomials obtained from different `H` are distinct — they need not be — and
nothing bounds their heights from below. What does the work is
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt` once more: `|P ξ|` is at most `4 S / H`, so it
can be made smaller than any threshold, and below the threshold the height exceeds any prescribed
bound. This is the same device Layer 1.2 used for the primitive part and for the Möbius
transforms, and it is why the hypothesis `aeval ξ P ≠ 0` is needed rather than merely convenient.

⚠ **The pigeonhole is run on `(H+1) ^ (n+1) - 1` boxes, not `(H+1) ^ (n+1)`.** With as many boxes
as tuples the argument proves nothing, and the endpoint `|L a| = T` is attained, so the box index
has to be clamped: `min ⌊u a⌋₊ (N - 1)`. `Real.abs_sub_le_one_of_min_floor_eq` is that clamp's
only consequence, and it is what replaces the usual "half-open interval" bookkeeping.

⚠ **The loss from `(H+1) ^ (n+1) - 1` to `H ^ (n+1)` is a factor of two and nothing more.**
`H ^ (n+1) ≤ (H+1) ^ (n+1) = N + 1 ≤ 2 N` is the only arithmetic needed, and it is why the
constant is `4 ∑ |ξ| ^ k` rather than the `2 ∑ |ξ| ^ k` a sharper count would give. The constant
is absorbed by `Real.le_mahlerExponent_of_infinite` and never appears in the conclusion.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.1
and Theorem 3.1.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Polynomial
open scoped ENNReal NNReal

namespace Real

/-! ### The clamped box index -/

/-- **The pigeonhole step.** Two points of `[0, N]` whose clamped box indices agree are at
distance at most `1`. The clamp `min ⌊x⌋₊ (N - 1)` is what allows `N` boxes to cover the closed
interval `[0, N]`, whose right endpoint is attained. -/
theorem abs_sub_le_one_of_min_floor_eq {N : ℕ} (hN : 1 ≤ N) {s t : ℝ}
    (hs0 : 0 ≤ s) (hsN : s ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (h : min ⌊s⌋₊ (N - 1) = min ⌊t⌋₊ (N - 1)) : |s - t| ≤ 1 := by
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN, Nat.cast_one]
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ N →
      ((min ⌊x⌋₊ (N - 1) : ℕ) : ℝ) ≤ x ∧ x ≤ ((min ⌊x⌋₊ (N - 1) : ℕ) : ℝ) + 1 := by
    intro x hx0 hxN
    refine ⟨le_trans (Nat.cast_le.2 (min_le_left _ _)) (Nat.floor_le hx0), ?_⟩
    rcases le_or_gt ⌊x⌋₊ (N - 1) with h1 | h1
    · rw [min_eq_left h1]
      exact (Nat.lt_floor_add_one x).le
    · rw [min_eq_right (by omega : N - 1 ≤ ⌊x⌋₊), hcast]
      linarith
  obtain ⟨h1, h2⟩ := key s hs0 hsN
  obtain ⟨h3, h4⟩ := key t ht0 htN
  rw [h] at h1 h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### One small value per height bound -/

/-- **Dirichlet's box principle for `1, ξ, …, ξ ^ n`.** For every height bound `H ≥ 1` there is a
nonzero integer polynomial of degree at most `n` and naive height at most `H` with
`|P ξ| * H ^ n ≤ 4 ∑ |ξ| ^ k`. Nothing is assumed about `ξ`: the value may well be zero, and it is
the caller who excludes that. -/
theorem exists_abs_aeval_mul_pow_le (ξ : ℝ) (n H : ℕ) (hH : 1 ≤ H) :
    ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ P.supNorm ≤ (H : ℝ) ∧
      |aeval ξ P| * (H : ℝ) ^ n ≤ 4 * ∑ k ∈ Finset.range (n + 1), |ξ| ^ k := by
  classical
  set S : ℝ := ∑ k ∈ Finset.range (n + 1), |ξ| ^ k with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    have h1 : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have h2 := Finset.single_le_sum (f := fun k ↦ |ξ| ^ k) (fun i _ ↦ by positivity) h1
    rw [hSdef]
    simpa using h2
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  set T : ℝ := (H : ℝ) * S with hTdef
  have hT0 : 0 < T := by rw [hTdef]; nlinarith
  -- the number of boxes
  have hpow : 2 ≤ (H + 1) ^ (n + 1) := by
    have h2 : (H + 1) ^ 1 ≤ (H + 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h2
    exact le_trans (by omega) h2
  set N : ℕ := (H + 1) ^ (n + 1) - 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNsucc : N + 1 = (H + 1) ^ (n + 1) := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- the tuples, their extensions to coefficient functions, and the linear forms
  set D : Finset (Fin (n + 1) → ℕ) :=
    Fintype.piFinset fun _ : Fin (n + 1) ↦ Finset.range (H + 1) with hDdef
  set e : (Fin (n + 1) → ℕ) → ℕ → ℤ :=
    fun a i ↦ if h : i < n + 1 then (a ⟨i, h⟩ : ℤ) else 0 with hedef
  set L : (Fin (n + 1) → ℕ) → ℝ :=
    fun a ↦ ∑ k ∈ Finset.range (n + 1), (e a k : ℝ) * ξ ^ k with hLdef
  set u : (Fin (n + 1) → ℕ) → ℝ := fun a ↦ (L a + T) / (2 * T) * N with hudef
  have hcard : D.card = N + 1 := by
    rw [hDdef, Fintype.card_piFinset]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    omega
  have hzero : ∀ (a : Fin (n + 1) → ℕ) (i : ℕ), ¬ i < n + 1 → e a i = 0 := by
    intro a i h
    simp only [hedef]
    exact dite_eq_right_of_eq_false (eq_false h)
  have hcoeff : ∀ a ∈ D, ∀ i, 0 ≤ e a i ∧ e a i ≤ (H : ℤ) := by
    intro a ha i
    by_cases h : i < n + 1
    · have hmem : a ⟨i, h⟩ ∈ Finset.range (H + 1) := Fintype.mem_piFinset.1 ha ⟨i, h⟩
      have h2 : a ⟨i, h⟩ ≤ H := by have := Finset.mem_range.1 hmem; omega
      have he : e a i = (a ⟨i, h⟩ : ℤ) := by
        simp only [hedef]
        exact dite_eq_left_of_eq_true (eq_true h)
      rw [he]
      exact ⟨by positivity, by exact_mod_cast h2⟩
    · rw [hzero a i h]
      exact ⟨le_rfl, by positivity⟩
  have hL : ∀ a ∈ D, |L a| ≤ T := by
    intro a ha
    have hstep : |L a| ≤ ∑ k ∈ Finset.range (n + 1), (H : ℝ) * |ξ| ^ k := by
      refine le_trans (by simpa only [hLdef] using
        Finset.abs_sum_le_sum_abs (fun k ↦ (e a k : ℝ) * ξ ^ k) (Finset.range (n + 1))) ?_
      refine Finset.sum_le_sum fun k _ ↦ ?_
      obtain ⟨h1, h2⟩ := hcoeff a ha k
      rw [abs_mul, abs_pow]
      have hb : |(e a k : ℝ)| ≤ (H : ℝ) := by
        rw [abs_of_nonneg (by exact_mod_cast h1)]
        exact_mod_cast h2
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    rw [hTdef, hSdef, Finset.mul_sum]
    exact hstep
  have hubd : ∀ a ∈ D, 0 ≤ u a ∧ u a ≤ (N : ℝ) := by
    intro a ha
    have h := abs_le.1 (hL a ha)
    have hdiv0 : (0 : ℝ) ≤ (L a + T) / (2 * T) := div_nonneg (by linarith) (by linarith)
    have hdiv : (L a + T) / (2 * T) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    simp only [hudef]
    exact ⟨mul_nonneg hdiv0 (by positivity),
      le_of_le_of_eq (mul_le_mul_of_nonneg_right hdiv (by positivity)) (one_mul _)⟩
  -- the pigeonhole
  have hlt : (Finset.range N).card < D.card := by
    rw [hcard, Finset.card_range]
    omega
  obtain ⟨a, ha, b, hb, hab, hg⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun a ↦ min ⌊u a⌋₊ (N - 1)) hlt
      (fun a _ ↦ Finset.mem_coe.2 (Finset.mem_range.2 (by omega : min ⌊u a⌋₊ (N - 1) < N)))
  obtain ⟨hua0, huaN⟩ := hubd a ha
  obtain ⟨hub0, hubN⟩ := hubd b hb
  have hu1 : |u a - u b| ≤ 1 := abs_sub_le_one_of_min_floor_eq hN1 hua0 huaN hub0 hubN hg
  have huab : u a - u b = (L a - L b) / (2 * T) * N := by
    simp only [hudef, div_mul_eq_mul_div, ← sub_div]
    congr 1
    ring
  have hLab : |L a - L b| * (N : ℝ) ≤ 2 * T := by
    have h1 : |L a - L b| * (N : ℝ) / (2 * T) ≤ 1 := by
      calc |L a - L b| * (N : ℝ) / (2 * T) = |(L a - L b) / (2 * T) * (N : ℝ)| := by
            rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * T),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
            ring
        _ = |u a - u b| := by rw [huab]
        _ ≤ 1 := hu1
    rwa [div_le_one (by linarith)] at h1
  -- the polynomial
  set P₀ : ℤ[X] := ∑ k ∈ Finset.range (n + 1), monomial k (e a k - e b k) with hP₀def
  have hPc : ∀ i, P₀.coeff i = e a i - e b i := by
    intro i
    rw [hP₀def, finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i fun k ↦ e a k - e b k]
    by_cases hi : i ∈ Finset.range (n + 1)
    · exact ite_eq_left_of_eq_true _ _ (eq_true hi)
    · have hni : ¬ i < n + 1 := fun h ↦ hi (Finset.mem_range.2 h)
      rw [hzero a i hni, hzero b i hni, sub_zero, ite_self]
  refine ⟨P₀, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hab
    refine fun h0 ↦ hk ?_
    have hik : ((k : ℕ)) < n + 1 := k.isLt
    have hc := hPc (k : ℕ)
    rw [h0, coeff_zero] at hc
    have he : e a (k : ℕ) = (a k : ℤ) := by
      simp only [hedef]
      exact dite_eq_left_of_eq_true (eq_true hik)
    have he' : e b (k : ℕ) = (b k : ℤ) := by
      simp only [hedef]
      exact dite_eq_left_of_eq_true (eq_true hik)
    rw [he, he'] at hc
    omega
  · refine natDegree_le_iff_coeff_eq_zero.2 fun m hm ↦ ?_
    have hni : ¬ m < n + 1 := by omega
    rw [hPc m, hzero a m hni, hzero b m hni, sub_zero]
  · refine supNorm_le_of_forall fun i ↦ ?_
    obtain ⟨h1, h2⟩ := hcoeff a ha i
    obtain ⟨h3, h4⟩ := hcoeff b hb i
    rw [hPc i, Int.norm_eq_abs]
    push_cast
    rw [abs_le]
    have c1 : (0 : ℝ) ≤ (e a i : ℝ) := by exact_mod_cast h1
    have c2 : (e a i : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2
    have c3 : (0 : ℝ) ≤ (e b i : ℝ) := by exact_mod_cast h3
    have c4 : (e b i : ℝ) ≤ (H : ℝ) := by exact_mod_cast h4
    constructor <;> linarith
  · have hval : aeval ξ P₀ = L a - L b := by
      rw [hP₀def, map_sum, hLdef]
      simp only [aeval_monomial, eq_intCast, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      ring
    rw [hval]
    have hHn : (H : ℝ) ^ (n + 1) ≤ 2 * (N : ℝ) := by
      have h1 : H ^ (n + 1) ≤ (H + 1) ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
      have h2 : H ^ (n + 1) ≤ 2 * N := by omega
      exact_mod_cast h2
    have hkey : |L a - L b| * (H : ℝ) ^ n * (N : ℝ) ≤ 4 * S * (N : ℝ) := by
      calc |L a - L b| * (H : ℝ) ^ n * (N : ℝ) = |L a - L b| * (N : ℝ) * (H : ℝ) ^ n := by ring
        _ ≤ 2 * T * (H : ℝ) ^ n := mul_le_mul_of_nonneg_right hLab (by positivity)
        _ = 2 * S * (H : ℝ) ^ (n + 1) := by rw [hTdef]; ring
        _ ≤ 2 * S * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hHn (by linarith)
        _ = 4 * S * (N : ℝ) := by ring
    exact le_of_mul_le_mul_right hkey hNR

/-! ### The box principle -/

/-- **The box principle: `n ≤ w_n`.** If no nonzero integer polynomial of degree at most `n`
vanishes at `ξ` — that is, if `ξ` is not algebraic of degree at most `n` — then Mahler's exponent
is at least `n`. -/
theorem le_mahlerExponent_of_aeval_ne_zero {n : ℕ} {ξ : ℝ}
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    (n : ℝ≥0∞) ≤ mahlerExponent n ξ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set S : ℝ := ∑ k ∈ Finset.range (n + 1), |ξ| ^ k with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    have h1 : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have h2 := Finset.single_le_sum (f := fun k ↦ |ξ| ^ k) (fun i _ ↦ by positivity) h1
    rw [hSdef]
    simpa using h2
  have hA0 : (0 : ℝ) < 4 * S := by linarith
  have hmain := le_mahlerExponent_of_infinite (n := n) (ξ := ξ) (w := (n : ℝ)) hA0 ?_
  · rwa [ENNReal.ofReal_natCast] at hmain
  refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
  obtain ⟨δ, hδ0, hδ⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ n B
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt (4 * S / δ)
  refine ?_
  set H : ℕ := max H₀ 1 with hHdef
  have hH1 : 1 ≤ H := le_max_right _ _
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hHδ : 4 * S / δ < (H : ℝ) := by
    refine lt_of_lt_of_le hH₀ ?_
    exact_mod_cast le_max_left H₀ 1
  obtain ⟨P, hP0, hdeg, hsup, hbound⟩ := exists_abs_aeval_mul_pow_le ξ n H hH1
  have hne : aeval ξ P ≠ 0 := hξ P hP0 hdeg
  have habs : 0 < |aeval ξ P| := abs_pos.2 hne
  have hsn : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  have hpowmono : (H : ℝ) ≤ (H : ℝ) ^ n := by
    calc (H : ℝ) = (H : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (H : ℝ) ^ n := pow_le_pow_right₀ hHR hn
  have hlt : |aeval ξ P| < δ := by
    have h1 : |aeval ξ P| * (H : ℝ) ≤ 4 * S :=
      le_trans (mul_le_mul_of_nonneg_left hpowmono (le_of_lt habs)) hbound
    have h2 : 4 * S < δ * (H : ℝ) := by
      rw [div_lt_iff₀ hδ0] at hHδ
      linarith
    nlinarith
  refine ⟨P, ⟨hdeg, habs, ?_⟩, hδ P hdeg habs hlt⟩
  have hsnpos : (0 : ℝ) < P.supNorm ^ n := by positivity
  have h1 : P.supNorm ^ (-(n : ℝ)) = (P.supNorm ^ n)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  have h2 : P.supNorm ^ n ≤ (H : ℝ) ^ n := pow_le_pow_left₀ (by linarith) hsup n
  calc |aeval ξ P| = |aeval ξ P| * (H : ℝ) ^ n / (H : ℝ) ^ n := by
        field_simp
    _ ≤ 4 * S / (H : ℝ) ^ n := by gcongr
    _ ≤ 4 * S / P.supNorm ^ n := by gcongr
    _ = 4 * S * P.supNorm ^ (-(n : ℝ)) := by rw [h1]; ring

/-- **The box principle for a transcendental number**, at every degree bound. -/
theorem le_mahlerExponent_of_transcendental {ξ : ℝ} (hξ : Transcendental ℚ ξ) (n : ℕ) :
    (n : ℝ≥0∞) ≤ mahlerExponent n ξ := by
  refine le_mahlerExponent_of_aeval_ne_zero fun P hP0 _ h ↦ hξ ⟨P.map (Int.castRingHom ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff ((algebraMap ℤ ℚ).injective_int)).2 hP0
  · rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
    exact h

/-! ### Acceptance criteria -/

/-- **Acceptance test: the box principle.** -/
example {n : ℕ} {ξ : ℝ} (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    (n : ℝ≥0∞) ≤ mahlerExponent n ξ :=
  le_mahlerExponent_of_aeval_ne_zero hξ

/-- **Acceptance test: at degree one it is Dirichlet's theorem**, `1 ≤ w_1` for an irrational,
which Layer 1.2 proved from `Real.irrationalityExponent` and which the box principle now proves
again, from the hypothesis that `ξ` is not rational. -/
example {ξ : ℝ} (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ 1 → aeval ξ P ≠ 0) :
    (1 : ℝ≥0∞) ≤ mahlerExponent 1 ξ := by
  simpa using le_mahlerExponent_of_aeval_ne_zero hξ

/-- **Rejection test: the hypothesis on `ξ` is load-bearing.** At a rational `ξ` the conclusion
`1 ≤ mahlerExponent 1 ξ` is false — Layer 1.2 computed the value `0` — so the box principle
cannot hold without excluding the algebraic numbers of degree at most `n`. -/
example (q : ℚ) : ¬ (1 : ℝ≥0∞) ≤ mahlerExponent 1 (q : ℝ) := by
  rw [mahlerExponent_one_ratCast]
  norm_num

end Real
