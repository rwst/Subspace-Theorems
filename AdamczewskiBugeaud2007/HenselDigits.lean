/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.PadicTranscendence
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The Hensel expansion of a `p`-adic number, and Theorems 1B and 6 as printed

Every `α ∈ ℚ_p` has a unique **Hensel expansion** `α = ∑_{k ≥ -m} a_k p ^ k` with digits
`a_k ∈ {0, …, p - 1}`, where `m = max 0 (-v(α))`. Adamczewski–Bugeaud 2007 state Theorems 1B and 6
for this expansion. `HenselExpansion.lean` works with the value `Padic.ofDigits a` of a digit
sequence given in advance; this file computes the digits of a given `α` and restates the two
theorems in the paper's form.

## Main definitions

* `PadicInt.henselDigits x`: the digits of `x ∈ ℤ_p`, from Mathlib's approximations
  `PadicInt.appr`: the `k`-th is `⌊appr x (k + 1) / p ^ k⌋`.
* `Padic.henselShift α`: `m = max 0 (-v(α))`, the least `m ≥ 0` with `p ^ m α ∈ ℤ_p`.
* `Padic.henselDigits α`: the digits `a_{-m}, a_{-m+1}, …` of `α`, indexed from `0`.

## Main results

* `PadicInt.ofDigits_henselDigits`: `x = ∑ a_k p ^ k` for `x ∈ ℤ_p`.
* `Padic.ofDigits_henselDigits`: `p ^ m α = ∑ a_{k - m} p ^ k`, i.e. `α = ∑_{k ≥ -m} a_k p ^ k`.
* `Padic.tendsto_complexity_henselDigits_div_atTop`: **Theorem 1B** as printed.
* `Padic.transcendental_of_isStammering_henselDigits`: **Theorem 6** as printed.

## Implementation notes

⚠ **The paper's index `k ≥ -m` is shifted to `k + m ≥ 0`.** `henselDigits α k` is the paper's
`a_{k - m}`. Theorem 6 asks Condition `(∗)_w` of `(a_k)_{k ≥ 1}`, which is
`k ↦ henselDigits α (k + (m + 1))`.

⚠ **For `v(α) ≥ 0` the expansion starts at `k = 0`**, with `m = 0`, and may begin with zeros.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §6, Theorems 1B and 6.
-/

@[expose] public section

open Filter

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt

/-- The **Hensel digits** of `x ∈ ℤ_p`: the `k`-th is `⌊appr x (k + 1) / p ^ k⌋`, where
`appr x n < p ^ n` is Mathlib's approximation of `x` modulo `p ^ n`. -/
noncomputable def henselDigits (x : ℤ_[p]) (k : ℕ) : Fin p :=
  ⟨x.appr (k + 1) / p ^ k, Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact x.appr_lt _)⟩

/-- **The first `n` digits give the approximation modulo `p ^ n`**: `∑_{i < n} a_i p ^ i =
appr x n`. The step: `appr x (n + 1) = appr x n + p ^ n c` with `appr x n < p ^ n`, so the new
digit is `c`. -/
theorem sum_henselDigits (x : ℤ_[p]) (n : ℕ) :
    ∑ i ∈ Finset.range n, (henselDigits x i : ℕ) * p ^ i = x.appr n := by
  induction n with
  | zero => simp [appr]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    obtain ⟨c, hc⟩ := dvd_appr_sub_appr x n (n + 1) (Nat.le_succ n)
    have hle := appr_mono x (show n ≤ n + 1 by omega)
    have hlt := appr_lt x n
    have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
    have e : x.appr (n + 1) = x.appr n + p ^ n * c := by rw [← hc]; omega
    simp only [henselDigits, e]
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, zero_add, mul_comm]

/-- **A `p`-adic integer is the value of its Hensel expansion.** -/
theorem ofDigits_henselDigits (x : ℤ_[p]) : Padic.ofDigits (henselDigits x) = x := by
  -- `‖x - ofDigits‖ ≤ p ^ (-n)` for every `n`
  have hbound : ∀ n : ℕ, ‖(x : ℚ_[p]) - Padic.ofDigits (henselDigits x)‖ ≤ ((p : ℝ) ^ n)⁻¹ := by
    intro n
    rw [Padic.ofDigits_eq_sum_add _ n, sum_henselDigits, ← sub_sub]
    have h1 : ‖(x : ℚ_[p]) - (x.appr n : ℚ_[p])‖ ≤ ((p : ℝ) ^ n)⁻¹ := by
      have := (norm_le_pow_iff_mem_span_pow (x - (x.appr n : ℤ_[p])) n).mpr (appr_spec n x)
      rwa [zpow_neg, zpow_natCast, norm_def] at this
    have h2 : ‖(p : ℚ_[p]) ^ n * Padic.ofDigits fun i ↦ henselDigits x (i + n)‖ ≤
        ((p : ℝ) ^ n)⁻¹ := by
      rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
      exact mul_le_of_le_one_right (by positivity) (Padic.norm_ofDigits_le_one _)
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
    simpa using h1
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hlim : Tendsto (fun n : ℕ ↦ ((p : ℝ) ^ n)⁻¹) atTop (nhds 0) := by
    simpa [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hp)
  have h0 := ge_of_tendsto' hlim hbound
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

end PadicInt

namespace Padic

/-- The shift `m = max 0 (-v(α))`: the least `m ≥ 0` with `p ^ m α ∈ ℤ_p`, so that the Hensel
expansion of `α` starts at `p ^ (-m)`. -/
noncomputable def henselShift (α : ℚ_[p]) : ℕ := (-α.valuation).toNat

theorem norm_pow_henselShift_mul_le_one (α : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ henselShift α * α‖ ≤ 1 := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  have hp : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
  rw [norm_mul, norm_p_pow, norm_eq_zpow_neg_valuation hα, ← zpow_add₀ (by positivity)]
  -- not `omega`: it mints a private auxiliary proof, which `henselDigits` would carry into the
  -- compared closure (see `COMPARATOR.md`)
  refine zpow_le_one_of_nonpos₀ hp ?_
  simp only [henselShift]
  linarith [Int.self_le_toNat (-α.valuation)]

/-- The **Hensel digits** of `α ∈ ℚ_p`: `henselDigits α k` is the paper's `a_{k - m}`, with
`m = henselShift α`, so that `α = ∑_{k ≥ -m} a_k p ^ k`. -/
noncomputable def henselDigits (α : ℚ_[p]) : ℕ → Fin p :=
  PadicInt.henselDigits ⟨(p : ℚ_[p]) ^ henselShift α * α, norm_pow_henselShift_mul_le_one α⟩

/-- **The Hensel expansion of `α`**: `∑_k a_{k - m} p ^ k = p ^ m α`, i.e.
`α = ∑_{k ≥ -m} a_k p ^ k`. -/
theorem ofDigits_henselDigits (α : ℚ_[p]) :
    ofDigits (henselDigits α) = (p : ℚ_[p]) ^ henselShift α * α :=
  PadicInt.ofDigits_henselDigits _

/-- An algebraic number stays algebraic, and an irrational one irrational, under `x ↦ q + r x` for
rationals `q` and `r ≠ 0`. -/
theorem isAlgebraic_ratCast_add_mul_iff {x : ℚ_[p]} (q : ℚ) {r : ℚ} (hr : r ≠ 0) :
    IsAlgebraic ℚ ((q : ℚ_[p]) + r * x) ↔ IsAlgebraic ℚ x := by
  have e : x = ((q : ℚ_[p]) + r * x) * (r⁻¹ : ℚ) + (-(q * r⁻¹) : ℚ) := by
    push_cast
    field_simp
    ring
  constructor
  · intro h
    rw [e]
    exact ((h.isIntegral.mul (isIntegral_algebraMap (x := r⁻¹))).add
      (isIntegral_algebraMap (x := -(q * r⁻¹)))).isAlgebraic
  · intro h
    exact ((isIntegral_algebraMap (x := q)).add
      ((isIntegral_algebraMap (x := r)).mul h.isIntegral)).isAlgebraic

theorem mem_range_ratCast_add_mul_iff {x : ℚ_[p]} (q : ℚ) {r : ℚ} (hr : r ≠ 0) :
    (q : ℚ_[p]) + r * x ∈ Set.range ((↑) : ℚ → ℚ_[p]) ↔ x ∈ Set.range ((↑) : ℚ → ℚ_[p]) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(s - q) / r, ?_⟩
    rw [Rat.cast_div, Rat.cast_sub, hs]
    field_simp
    ring
  · rintro ⟨s, rfl⟩
    exact ⟨q + r * s, by push_cast; ring⟩

/-- **Theorem 1B (Adamczewski–Bugeaud 2007), as printed.** The complexity `p (n)` of the Hensel
expansion `(a_k)_{k ≥ -m}` of an irrational algebraic `α ∈ ℚ_p` satisfies `p (n) / n → ∞`. -/
theorem tendsto_complexity_henselDigits_div_atTop {α : ℚ_[p]}
    (hirr : α ∉ Set.range ((↑) : ℚ → ℚ_[p])) (halg : IsAlgebraic ℚ α) :
    Tendsto (fun n ↦ (Function.complexity (henselDigits α) n : ℝ) / n) atTop atTop := by
  have hr : ((p : ℚ) ^ henselShift α) ≠ 0 := pow_ne_zero _ (by exact_mod_cast
    (Fact.out : p.Prime).ne_zero)
  have e : ofDigits (henselDigits α) = ((0 : ℚ) : ℚ_[p]) + ((p : ℚ) ^ henselShift α : ℚ) * α := by
    rw [ofDigits_henselDigits]
    push_cast
    ring
  refine tendsto_complexity_div_atTop ?_ ?_
  · rw [e, mem_range_ratCast_add_mul_iff 0 hr]
    exact hirr
  · rw [e, isAlgebraic_ratCast_add_mul_iff 0 hr]
    exact halg

/-- **Theorem 6 (Adamczewski–Bugeaud 2007), as printed.** If the Hensel digits `(a_k)_{k ≥ 1}` of
`α ∈ ℚ_p` satisfy Condition `(∗)_w` for some `w > 1` — they are stammering and not eventually
periodic — then `α` is transcendental. -/
theorem transcendental_of_isStammering_henselDigits {α : ℚ_[p]}
    (hst : Function.IsStammering fun k ↦ henselDigits α (k + (henselShift α + 1)))
    (hper : ¬ Function.IsEventuallyPeriodic fun k ↦ henselDigits α (k + (henselShift α + 1))) :
    Transcendental ℚ α := by
  have ht := transcendental_ofDigits_of_isStammering hst hper
  set n := henselShift α + 1
  set S : ℕ := ∑ i ∈ Finset.range n, (henselDigits α i : ℕ) * p ^ i
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- `p ^ m α = S + p ^ n T`, so `T = -S / p ^ n + p ^ (m - n) α`, with `p ^ (m - n) = p⁻¹`
  have e : ofDigits (fun i ↦ henselDigits α (i + n)) =
      ((-(S : ℚ) / p ^ n : ℚ) : ℚ_[p]) + ((p⁻¹ : ℚ) : ℚ_[p]) * α := by
    have h := ofDigits_eq_sum_add (henselDigits α) n
    rw [ofDigits_henselDigits] at h
    have hpn : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0)
    push_cast
    field_simp
    have hpinv : (p : ℚ_[p]) * (p : ℚ_[p])⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hp0)
    rw [show n = henselShift α + 1 from rfl, pow_succ] at h ⊢
    linear_combination -h - ((p : ℚ_[p]) ^ henselShift α * α) * hpinv
  rw [e, Transcendental, isAlgebraic_ratCast_add_mul_iff _ (inv_ne_zero hp0)] at ht
  exact ht

end Padic
