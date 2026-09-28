/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.AutomaticComplexity
public import AdamczewskiBugeaud2007.HenselExpansion
public import AdamczewskiBugeaud2007.PadicSubspace

-- Used only inside proofs.
import Mathlib.Tactic.LinearCombination

/-!
# Transcendence of `p`-adic numbers

**Section 6 of Adamczewski–Bugeaud 2007.** For a prime `p` and digits `a : ℕ → Fin p`, let
`α = ∑ n, a n p ^ n ∈ ℚ_p` (`Padic.ofDigits`).

* **Theorem 6** (the `p`-adic criterion): if `a` is stammering and not eventually periodic, `α`
  is transcendental.
* **Theorem 1B**: if `α` is an algebraic irrational, the number `p n` of distinct words of length
  `n` in `a` satisfies `p n / n → ∞`.
* **Theorem 2B**: if `a` is automatic and `α` is irrational, `α` is transcendental.

## Main results

* `Padic.transcendental_ofDigits_of_forall_periodic`: Theorem 6 in its working form, on periodic
  segments of the digits.
* `Padic.transcendental_ofDigits_of_isStammering`: **Theorem 6**.
* `Padic.transcendental_ofDigits_of_frequently_complexity_le`: the criterion by complexity.
* `Padic.tendsto_complexity_div_atTop`: **Theorem 1B**.
* `Padic.transcendental_ofDigits_of_isAutomatic`: **Theorem 2B**.

## Implementation notes

The proof follows the real one (`Real.transcendental_ofDigits_of_forall_periodic`, Layer 7.4 of
`DiophantineApproximation`), with the Subspace Theorem at `p` instead of at `∞`
(`Padic.exists_finset_submodule_of_repetition`). A repetition of `⌈w s⌉ - s` digits after
position `r` puts `(p ^ s - 1) α` within `p ^ (-(r + ⌈w s⌉))` of the integer
`P = p ^ s P_r - P_(r+s)` (`Padic.norm_mul_ofDigits_sub_le`). At the points `(p ^ s, 1, P)` the
coordinates at `∞` contribute at most `p ^ (r + 2 s)` and the forms at `p` at most
`p ^ (-s) p ^ (-(r + ⌈w s⌉))`, so the product is at most `p ^ (-(w - 1) s)`, a negative power of
the sup norm `p ^ (r + s)` as long as `r / s` is bounded.

⚠ **The endgame is shorter than over `ℝ`.** One proper subspace `z 0 X + z 1 Y + z 2 Z = 0`
contains infinitely many of the points. If `z 2 = 0` it fixes `p ^ s`. Otherwise
`P = -(z 0 p ^ s + z 1) / z 2`, and the approximation reads `‖p ^ s θ + η‖ ≤ p ^ (-s)` with
`θ = α + z 0 / z 2` and `η = z 1 / z 2 - α`. Now `p ^ s θ → 0` in `ℚ_p` whatever `θ` is, so
`η = 0` and `α` is rational. Over `ℝ` the term `b ^ s θ` grows instead, and `θ = 0` has to be
excluded first.

⚠ **Only the integral part of the paper's expansion appears.** The paper's Theorem 6 is about
`∑_{k ≥ -m} a k p ^ k` with Condition `(∗)_w` on `(a k)_{k ≥ 1}`. That number is a rational
multiple of `Padic.ofDigits` of the digits from `k = 1` on plus a rational, so the statements
here are equivalent to the paper's.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §6 (Theorems 1B, 2B and 6).
-/

@[expose] public section

open Filter

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- **Theorem 6 in its working form** (Adamczewski–Bugeaud 2007, §6). Let `α = ∑ n, a n p ^ n`
be irrational, and suppose that for `w > 1` there are positions `r k` and strictly increasing
periods `s k` with `r k ≤ C s k` such that the segment of the digits of length `⌈w s k⌉` after
position `r k` has period `s k`. Then `α` is transcendental. -/
theorem transcendental_ofDigits_of_forall_periodic {a : ℕ → Fin p}
    (hirr : ofDigits a ∉ Set.range ((↑) : ℚ → ℚ_[p])) {w C : ℝ} (hw : 1 < w) (hC : 0 ≤ C)
    {r s : ℕ → ℕ} (hs : StrictMono s) (hrs : ∀ k, (r k : ℝ) ≤ C * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → a (i + s k) = a i) :
    Transcendental ℚ (ofDigits a) := by
  intro halg
  set α := ofDigits a with hα
  set B : ℝ := (p : ℝ) with hBdef
  have hB1 : (1 : ℝ) < B := by rw [hBdef]; exact_mod_cast (Fact.out : p.Prime).one_lt
  have hB0 : (0 : ℝ) < B := by linarith
  set ε : ℝ := (w - 1) / (C + 1) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨T, hTproper, hTmem⟩ := exists_finset_submodule_of_repetition halg hε
  -- the length of the repetition beyond one period
  set t : ℕ → ℕ := fun k ↦ ⌈w * s k⌉₊ - s k with htdef
  have hsw : ∀ k, s k ≤ ⌈w * s k⌉₊ := fun k ↦ by
    have h1 : (s k : ℝ) ≤ w * s k := le_mul_of_one_le_left (Nat.cast_nonneg _) hw.le
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have ht : ∀ k, (w - 1) * s k ≤ (t k : ℝ) := fun k ↦ by
    rw [htdef, Nat.cast_sub (hsw k)]
    linarith [Nat.le_ceil (w * s k)]
  have hrep : ∀ k, ∀ i < t k, a (i + (r k + s k)) = a (i + r k) := by
    intro k i hi
    have h := hper k (i + r k) (Nat.le_add_left _ _)
      (by simp only [htdef] at hi; have := hsw k; omega)
    rwa [show i + r k + s k = i + (r k + s k) by ring] at h
  -- the points
  set P : ℕ → ℕ := fun n ↦ ∑ i ∈ Finset.range n, (a i : ℕ) * p ^ i with hPdef
  set X : ℕ → ℤ := fun k ↦ (p : ℤ) ^ s k * (P (r k) : ℤ) - (P (r k + s k) : ℤ) with hXdef
  set x : ℕ → Fin 3 → ℤ := fun k ↦ ![(p : ℤ) ^ s k, 1, X k] with hxdef
  have hx0 : ∀ k, x k 0 = (p : ℤ) ^ s k := fun k ↦ rfl
  have hx1 : ∀ k, x k 1 = 1 := fun k ↦ rfl
  have hx2 : ∀ k, x k 2 = X k := fun k ↦ rfl
  have hL3 : ∀ k, ‖α * ((x k 0 : ℤ) : ℚ_[p]) - α * ((x k 1 : ℤ) : ℚ_[p]) - ((x k 2 : ℤ) : ℚ_[p])‖
      ≤ (B ^ (r k + s k + t k))⁻¹ := by
    intro k
    have h := norm_mul_ofDigits_sub_le a (hrep k)
    rw [hx0, hx1, hx2, hXdef, hPdef]
    convert h using 2
    push_cast
    ring
  have hxne : ∀ k, (fun i ↦ ((x k i : ℤ) : ℚ)) ≠ 0 := fun k h ↦ by
    have h1 : ((x k 1 : ℤ) : ℚ) = 0 := by simpa using congrFun h 1
    rw [hx1, Int.cast_one] at h1
    exact one_ne_zero h1
  -- the size of the point at `∞`
  have hX : ∀ k, |((X k : ℤ) : ℝ)| ≤ B ^ (r k + s k) := by
    intro k
    have h1 := sum_digits_lt a (r k)
    have h2 := sum_digits_lt a (r k + s k)
    have h1' : ((P (r k) : ℕ) : ℝ) < B ^ r k := by rw [hBdef]; exact_mod_cast h1
    have h2' : ((P (r k + s k) : ℕ) : ℝ) < B ^ (r k + s k) := by rw [hBdef]; exact_mod_cast h2
    have hXr : ((X k : ℤ) : ℝ) = B ^ s k * (P (r k) : ℝ) - (P (r k + s k) : ℝ) := by
      rw [hXdef, hBdef]; push_cast; ring
    have hP0 : (0 : ℝ) ≤ (P (r k) : ℝ) := Nat.cast_nonneg _
    have hP0' : (0 : ℝ) ≤ (P (r k + s k) : ℝ) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) < B ^ s k := pow_pos hB0 _
    have h3 : B ^ s k * (P (r k) : ℝ) < B ^ s k * B ^ r k := mul_lt_mul_of_pos_left h1' hs0
    have h4 : 0 ≤ B ^ s k * (P (r k) : ℝ) := mul_nonneg hs0.le hP0
    rw [pow_add] at h2' ⊢
    rw [hXr, abs_le]
    constructor <;> nlinarith
  have hsup : ∀ k, (⨆ i, |((x k i : ℤ) : ℝ)|) ≤ B ^ (r k + s k) := by
    intro k
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · change |((x k 0 : ℤ) : ℝ)| ≤ _
      rw [hx0]
      push_cast
      rw [abs_of_pos (pow_pos hB0 _)]
      exact pow_le_pow_right₀ hB1.le (Nat.le_add_left _ _)
    · change |((x k 1 : ℤ) : ℝ)| ≤ _
      rw [hx1, Int.cast_one, abs_one]
      exact one_le_pow₀ hB1.le
    · exact hX k
  have hsuppos : ∀ k, 0 < ⨆ i, |((x k i : ℤ) : ℝ)| := fun k ↦
    lt_of_lt_of_le (by rw [hx1]; norm_num) (Finite.le_ciSup_of_le (1 : Fin 3) le_rfl)
  have hsmall : ∀ k, (∏ i, |((x k i : ℤ) : ℝ)|) * (‖((x k 0 : ℤ) : ℚ_[p])‖
        * ‖((x k 1 : ℤ) : ℚ_[p])‖
        * ‖α * ((x k 0 : ℤ) : ℚ_[p]) - α * ((x k 1 : ℤ) : ℚ_[p]) - ((x k 2 : ℤ) : ℚ_[p])‖)
      ≤ (⨆ i, |((x k i : ℤ) : ℝ)|) ^ (-ε) := by
    intro k
    have hE := hL3 k
    have hn0 : ‖((x k 0 : ℤ) : ℚ_[p])‖ = (B ^ s k)⁻¹ := by
      rw [hx0]; push_cast; rw [norm_p_pow, zpow_neg, zpow_natCast]
    have hn1 : ‖((x k 1 : ℤ) : ℚ_[p])‖ = 1 := by rw [hx1]; simp
    have ha0 : |((x k 0 : ℤ) : ℝ)| = B ^ s k := by
      rw [hx0]; push_cast; exact abs_of_pos (pow_pos hB0 _)
    have ha1 : |((x k 1 : ℤ) : ℝ)| = 1 := by rw [hx1]; simp
    have hrs' : (0 : ℝ) < B ^ (r k + s k + t k) := pow_pos hB0 _
    rw [Fin.prod_univ_three, hn0, hn1, ha0, ha1]
    calc B ^ s k * 1 * |((x k 2 : ℤ) : ℝ)| * ((B ^ s k)⁻¹ * 1
            * ‖α * ((x k 0 : ℤ) : ℚ_[p]) - α * ((x k 1 : ℤ) : ℚ_[p]) - ((x k 2 : ℤ) : ℚ_[p])‖)
        ≤ B ^ s k * 1 * B ^ (r k + s k) * ((B ^ s k)⁻¹ * 1 * (B ^ (r k + s k + t k))⁻¹) := by
          rw [hx2]
          gcongr
          all_goals first | exact hX k | exact hE
      _ = (B ^ t k)⁻¹ := by
          rw [pow_add _ (r k + s k) (t k)]
          field_simp
      _ = B ^ (-(t k : ℝ)) := by rw [Real.rpow_neg hB0.le, Real.rpow_natCast]
      _ ≤ B ^ (-(ε * ((r k + s k : ℕ) : ℝ))) := by
          refine Real.rpow_le_rpow_of_exponent_le hB1.le (neg_le_neg ?_)
          refine le_trans ?_ (ht k)
          rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          push_cast
          nlinarith [hrs k, (Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
      _ = (B ^ (r k + s k)) ^ (-ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
          ring_nf
      _ ≤ (⨆ i, |((x k i : ℤ) : ℝ)|) ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos (hsuppos k) (hsup k) (by linarith)
  -- one subspace contains infinitely many of the points
  have hmem : ∀ k, ∃ V ∈ T, (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ V := fun k ↦
    hTmem (x k) (hxne k) (hsmall k)
  choose V hVT hxV using hmem
  obtain ⟨⟨V₀, hV₀⟩, hinf⟩ := Finite.exists_infinite_fiber (fun k ↦ (⟨V k, hVT k⟩ : T))
  set K : Set ℕ := (fun k ↦ (⟨V k, hVT k⟩ : T)) ⁻¹' {⟨V₀, hV₀⟩} with hKdef
  have hK : K.Infinite := Set.infinite_coe_iff.mp hinf
  have hKV : ∀ k ∈ K, (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ V₀ := fun k hk ↦ by
    have h : V k = V₀ := congrArg Subtype.val (Set.mem_singleton_iff.mp hk)
    rw [← h]
    exact hxV k
  obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr (hTproper V₀ hV₀)) inferInstance
  set z : Fin 3 → ℚ := fun i ↦ f (fun t ↦ if i = t then 1 else 0) with hzdef
  have hfx : ∀ y : Fin 3 → ℚ, f y = ∑ i, y i * z i := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]
  have hz : ¬ (z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, Fin.sum_univ_three, h0, h1, h2])
  have hrel : ∀ k ∈ K, (p : ℚ) ^ s k * z 0 + z 1 + (X k : ℚ) * z 2 = 0 := by
    intro k hk
    have hmap : f (fun i ↦ ((x k i : ℤ) : ℚ)) ∈ Submodule.map f V₀ :=
      Submodule.mem_map_of_mem (hKV k hk)
    rw [hfV, Submodule.mem_bot, hfx, Fin.sum_univ_three, hx0, hx1, hx2] at hmap
    push_cast at hmap
    linear_combination hmap
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hz2 : z 2 = 0
  · -- the relation does not involve the third coordinate: it pins down `p ^ s`
    obtain ⟨k₁, hk₁⟩ := hK.nonempty
    obtain ⟨k₂, hk₂, hlt⟩ := hK.exists_gt k₁
    have hlin : ∀ k ∈ K, (p : ℚ) ^ s k * z 0 + z 1 = 0 := fun k hk ↦ by
      simpa [hz2] using hrel k hk
    have hne : (p : ℚ) ^ s k₁ - (p : ℚ) ^ s k₂ ≠ 0 :=
      sub_ne_zero.mpr (pow_lt_pow_right₀ hp1 (hs hlt)).ne
    have hz0 : z 0 = 0 := by
      have : ((p : ℚ) ^ s k₁ - (p : ℚ) ^ s k₂) * z 0 = 0 := by
        linear_combination hlin k₁ hk₁ - hlin k₂ hk₂
      exact (mul_eq_zero.mp this).resolve_left hne
    have hz1 : z 1 = 0 := by linear_combination hlin k₁ hk₁ - (p : ℚ) ^ s k₁ * hz0
    exact hz ⟨hz0, hz1, hz2⟩
  · -- the relation determines the third coordinate, and the approximation makes `α` rational
    have hz2' : ((z 2 : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hz2
    set θ : ℚ_[p] := α + (z 0 : ℚ_[p]) / (z 2 : ℚ_[p]) with hθ
    set η : ℚ_[p] := (z 1 : ℚ_[p]) / (z 2 : ℚ_[p]) - α with hη
    have hbound : ∀ k ∈ K, ‖(p : ℚ_[p]) ^ s k * θ + η‖ ≤ (B ^ s k)⁻¹ := by
      intro k hk
      have hrel' : (p : ℚ_[p]) ^ s k * (z 0 : ℚ_[p]) + (z 1 : ℚ_[p])
          + ((X k : ℤ) : ℚ_[p]) * (z 2 : ℚ_[p]) = 0 := by
        have h := congrArg (fun q : ℚ ↦ (q : ℚ_[p])) (hrel k hk)
        push_cast at h
        exact h
      have hXk : ((X k : ℤ) : ℚ_[p])
          = -((p : ℚ_[p]) ^ s k * (z 0 : ℚ_[p]) + (z 1 : ℚ_[p])) / (z 2 : ℚ_[p]) := by
        rw [eq_div_iff hz2']
        linear_combination hrel'
      have hid : α * ((x k 0 : ℤ) : ℚ_[p]) - α * ((x k 1 : ℤ) : ℚ_[p]) - ((x k 2 : ℤ) : ℚ_[p])
          = (p : ℚ_[p]) ^ s k * θ + η := by
        rw [hx0, hx1, hx2, hXk, hθ, hη]
        push_cast
        ring
      rw [← hid]
      refine (hL3 k).trans (inv_anti₀ (pow_pos hB0 _) (pow_le_pow_right₀ hB1.le ?_))
      omega
    by_cases hη0 : η = 0
    · refine hirr ⟨z 1 / z 2, ?_⟩
      push_cast
      linear_combination hη0
    · have hηpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((1 + ‖θ‖) / ‖η‖) hB1
      obtain ⟨k, hk, hNk⟩ := hK.exists_gt N
      have hsk : N ≤ s k := hNk.le.trans (hs.id_le k)
      have h1 := hbound k hk
      have h2 : (1 + ‖θ‖) / ‖η‖ < B ^ s k := hN.trans_le (pow_le_pow_right₀ hB1.le hsk)
      rw [div_lt_iff₀ hηpos] at h2
      have hps : ‖(p : ℚ_[p]) ^ s k * θ‖ = (B ^ s k)⁻¹ * ‖θ‖ := by
        rw [norm_mul, norm_p_pow, zpow_neg, zpow_natCast]
      have h3 : ‖η‖ ≤ ‖(p : ℚ_[p]) ^ s k * θ + η‖ + ‖(p : ℚ_[p]) ^ s k * θ‖ := by
        have := norm_sub_le ((p : ℚ_[p]) ^ s k * θ + η) ((p : ℚ_[p]) ^ s k * θ)
        rwa [add_sub_cancel_left] at this
      rw [hps] at h3
      have hBs : 0 < B ^ s k := pow_pos hB0 _
      have h5 : ‖η‖ ≤ (B ^ s k)⁻¹ * (1 + ‖θ‖) := by rw [mul_add, mul_one]; linarith
      have h4 : ‖η‖ * B ^ s k ≤ 1 + ‖θ‖ :=
        (le_div_iff₀ hBs).mp (by rw [div_eq_inv_mul]; exact h5)
      linarith

/-- **Theorem 6 (Adamczewski–Bugeaud 2007, §6): the `p`-adic stammering criterion.** If the
digits `a` are stammering and not eventually periodic, `∑ n, a n p ^ n` is transcendental. -/
theorem transcendental_ofDigits_of_isStammering {a : ℕ → Fin p}
    (hst : Function.IsStammering a) (hper : ¬ Function.IsEventuallyPeriodic a) :
    Transcendental ℚ (ofDigits a) := by
  obtain ⟨w, hw, h⟩ := hst
  obtain ⟨C, hC, r, s, hs, -, hrs, hp⟩ := h.exists_periodic (by linarith)
  exact transcendental_ofDigits_of_forall_periodic (ofDigits_notMem_range_ratCast hper) hw hC hs
    hrs hp

/-- **A `p`-adic transcendence criterion by complexity.** If `a` is not eventually periodic and
has at most `C n` factors of length `n` for infinitely many `n`, then `∑ n, a n p ^ n` is
transcendental. -/
theorem transcendental_ofDigits_of_frequently_complexity_le {a : ℕ → Fin p}
    (ha : ¬ Function.IsEventuallyPeriodic a) {C : ℝ}
    (h : ∃ᶠ n in atTop, (Function.complexity a n : ℝ) ≤ C * n) :
    Transcendental ℚ (ofDigits a) := by
  obtain ⟨w, C', hw, hC', r, s, hs, -, hrs, hper⟩ :=
    Function.exists_periodic_of_frequently_complexity_le h
  exact transcendental_ofDigits_of_forall_periodic (ofDigits_notMem_range_ratCast ha) hw hC' hs
    hrs hper

/-- **Theorem 1B (Adamczewski–Bugeaud 2007, §6).** If `∑ n, a n p ^ n ∈ ℚ_p` is algebraic and
irrational, the number `p n` of distinct words of length `n` in its digits satisfies
`p n / n → ∞`. -/
theorem tendsto_complexity_div_atTop {a : ℕ → Fin p}
    (hirr : ofDigits a ∉ Set.range ((↑) : ℚ → ℚ_[p])) (halg : IsAlgebraic ℚ (ofDigits a)) :
    Tendsto (fun n ↦ (Function.complexity a n : ℝ) / n) atTop atTop := by
  rw [tendsto_atTop]
  by_contra! hC
  obtain ⟨C, hC⟩ := hC
  refine transcendental_ofDigits_of_frequently_complexity_le
    (fun h ↦ hirr (ofDigits_mem_range_ratCast h)) (C := C) ?_ halg
  refine (hC.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  have : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ((div_lt_iff₀ this).mp hn).le

/-- **Theorem 2B (Adamczewski–Bugeaud 2007, §6): irrational automatic `p`-adic numbers are
transcendental.** If the digits `a` are automatic and `∑ n, a n p ^ n ∈ ℚ_p` is irrational, it is
transcendental. -/
theorem transcendental_ofDigits_of_isAutomatic {a : ℕ → Fin p}
    (hauto : Function.IsAutomatic a) (hirr : ofDigits a ∉ Set.range ((↑) : ℚ → ℚ_[p])) :
    Transcendental ℚ (ofDigits a) :=
  let ⟨_, hC⟩ := hauto.frequently_complexity_le
  transcendental_ofDigits_of_frequently_complexity_le
    (fun h ↦ hirr (ofDigits_mem_range_ratCast h)) hC

end Padic

/-! ### Acceptance criteria -/

/-- **Rejection: irrationality is load-bearing in Theorem 2B.** A constant digit sequence is
automatic, and its value is rational. -/
example {p : ℕ} [Fact p.Prime] (d : Fin p) : Function.IsAutomatic (fun _ : ℕ ↦ d) ∧
    Padic.ofDigits (fun _ : ℕ ↦ d) ∈ Set.range ((↑) : ℚ → ℚ_[p]) :=
  ⟨Function.isAutomatic_const d, Padic.ofDigits_mem_range_ratCast ⟨0, 1, one_pos, fun _ _ ↦ rfl⟩⟩

/-- **Theorem 2B at work:** a non-eventually-periodic automatic sequence of `p`-adic digits has a
transcendental value, the irrationality coming from the digits alone. -/
example {p : ℕ} [Fact p.Prime] {a : ℕ → Fin p} (hauto : Function.IsAutomatic a)
    (hper : ¬ Function.IsEventuallyPeriodic a) : Transcendental ℚ (Padic.ofDigits a) :=
  Padic.transcendental_ofDigits_of_isAutomatic hauto (Padic.ofDigits_notMem_range_ratCast hper)
