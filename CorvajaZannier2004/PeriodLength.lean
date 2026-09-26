/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PartialQuotients

-- Used only inside proofs.
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Cofinite

/-!
# Theorem 2 of Corvaja–Zannier: the periods of the continued fractions of `αⁿ`

**Theorem 2** (Corvaja–Zannier 2004, p. 1; the problem of Mendès France). Let `α > 0` be a real
quadratic irrational. If `α` is neither the square root of a rational number nor a unit, the
period of the continued fraction of `αⁿ` tends to infinity with `n`. If `α` is the square root of
a rational number, the period of `α²ⁿ⁺¹` tends to infinity. (If `α` is a unit, the period is
bounded: `Real.bddAbove_cfPeriod_pow`.)

## Main results

* `Real.abs_sub_quadConj_le`: for `z > 1` with `cfTail z r = z`, `|z - z'| ≤ 4 ∏_{i<r} (aᵢ + 1)`.
* `Real.isPisot_of_cfPeriod_le`: bounded periods of `βⁿ` along `n ∈ S`, with `βⁿ - β'ⁿ ≥ c βⁿ`,
  make `β` a Pisot number.
* `Real.tendsto_cfPeriod_pow`, `Real.tendsto_cfPeriod_pow_odd`: Theorem 2 (a), (b).

## Implementation notes

⚠ **The reduction (4.6) and the square-root case, uniformly.** The proof makes
`αⁿ - kₙ` reduced, `kₙ = ⌊α'ⁿ⌋ + 1`, which works as soon as `αⁿ - α'ⁿ > 2`; the paper's
condition `α > |α'|` guarantees that, and so does `α' = -α` for odd `n` (then `αⁿ - kₙ` is
`αⁿ + ⌊αⁿ⌋`, the paper's `1 / (αⁿ - ⌊αⁿ⌋)` up to one step of the algorithm). The contradiction is
`|αⁿ - α'ⁿ| ≥ c αⁿ` against `|z - z'| = e^{o(n)}` in both cases.

⚠ **Why `α` is a unit.** As in the paper: the Proposition makes `β` Pisot, then `±1/β'` Pisot,
where `β` is whichever of `α, α'` has the larger absolute value (inverted if both lie in the unit
disc, where the second step already fails).

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Theorem 2 and pp. 10–11.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {x z β : ℝ}

/-- **The numerators and denominators of the convergents** of `x > 1` are at most
`∏_{i<j} (aᵢ + 1)`. -/
theorem cfNum_cfDen_le_prod (hx : Irrational x) (h1 : 1 < x) (j : ℕ) :
    cfNum x (j + 1) ≤ ∏ i ∈ Finset.range j, (cfQuot x i + 1) ∧
      cfNum x j ≤ ∏ i ∈ Finset.range j, (cfQuot x i + 1) ∧
      cfDen x (j + 1) ≤ ∏ i ∈ Finset.range j, (cfQuot x i + 1) ∧
      cfDen x j ≤ ∏ i ∈ Finset.range j, (cfQuot x i + 1) := by
  have ha : ∀ i, 1 ≤ cfQuot x i := fun i ↦ by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [cfQuot, cfTail_zero]
      exact Int.le_floor.mpr (by exact_mod_cast h1.le)
    · exact one_le_cfQuot hx hi
  have hnum0 : ∀ j, 0 ≤ cfNum x j := fun j ↦ by
    rcases j with _ | j
    · simp [cfNum]
    · exact zero_le_one.trans (one_le_cfNum hx h1 (by omega))
  induction j with
  | zero => simp [cfNum, cfDen]
  | succ j ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih
    have hP : 1 ≤ ∏ i ∈ Finset.range j, (cfQuot x i + 1) := by
      have := Finset.prod_pos (s := Finset.range j) (f := fun i ↦ cfQuot x i + 1) fun i _ ↦ by
        have := ha i
        omega
      omega
    have haj := ha j
    rw [Finset.prod_range_succ]
    have hd1 := cfDen_nonneg hx (j + 1)
    have hd0 := cfDen_nonneg hx j
    have hn1 := hnum0 (j + 1)
    have hn0 := hnum0 j
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show j + 1 + 1 = j + 2 by ring, cfNum_succ_succ]
      nlinarith
    · nlinarith
    · rw [show j + 1 + 1 = j + 2 by ring, cfDen_succ_succ]
      nlinarith
    · nlinarith

/-- **A purely periodic quadratic irrational has small conjugate distance.** For `z > 1` with
`cfTail z r = z`, the fixed-point equation `q z² + (q' - p) z - p' = 0` of the period gives
`(z - z')² = ((p - q')² + 4 p' q) / q²`, so `|z - z'| ≤ p + p' + q + q' ≤ 4 ∏_{i<r} (aᵢ + 1)`. -/
theorem abs_sub_quadConj_le (hz : IsQuadraticIrrational z) (h1 : 1 < z) {r : ℕ} (hr : 0 < r)
    (hper : cfTail z r = z) :
    |z - quadConj z| ≤ 4 * ∏ i ∈ Finset.range r, ((cfQuot z i + 1 : ℤ) : ℝ) := by
  have hfix := eq_cfNum_div_cfDen hz.1 r
  rw [hper] at hfix
  have hD := cfDen_mul_cfTail_add_pos hz.1 r
  rw [hper] at hD
  obtain ⟨b₁, b₂, b₃, b₄⟩ := cfNum_cfDen_le_prod hz.1 h1 r
  set P := cfNum z (r + 1)
  set P' := cfNum z r
  set Q := cfDen z (r + 1)
  set Q' := cfDen z r
  set Pm := ∏ i ∈ Finset.range r, (cfQuot z i + 1)
  -- positivity of the entries
  have hP0 : 0 ≤ P := zero_le_one.trans (one_le_cfNum hz.1 h1 (by omega))
  have hP'0 : 0 ≤ P' := zero_le_one.trans (one_le_cfNum hz.1 h1 hr)
  have hQ0 : 0 ≤ Q := cfDen_nonneg hz.1 _
  have hQ'0 : 0 ≤ Q' := cfDen_nonneg hz.1 _
  have hQ1 : (1 : ℤ) ≤ Q := one_le_cfDen hz.1 (by omega)
  have hQ' : ((Q : ℚ)) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hQ1).ne'
  have hroot : ((Q : ℚ) : ℝ) * z ^ 2 + ((Q' - P : ℚ) : ℝ) * z + ((-P' : ℚ) : ℝ) = 0 := by
    have := (eq_div_iff hD.ne').mp hfix
    push_cast
    linear_combination this
  have hsum := hz.add_quadConj hQ' hroot
  have hprod := hz.mul_quadConj hQ' hroot
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hsq : (z - quadConj z) ^ 2 * (Q : ℝ) ^ 2 = ((P : ℝ) - Q') ^ 2 + 4 * P' * Q := by
    have e : (z - quadConj z) ^ 2 = (z + quadConj z) ^ 2 - 4 * (z * quadConj z) := by ring
    rw [e, hsum, hprod]
    push_cast
    field_simp
    ring
  have hle : (z - quadConj z) ^ 2 ≤ ((P : ℝ) + P' + Q + Q') ^ 2 := by
    have hP0' : (0 : ℝ) ≤ P := by exact_mod_cast hP0
    have hP'0' : (0 : ℝ) ≤ P' := by exact_mod_cast hP'0
    have hQ'0' : (0 : ℝ) ≤ Q' := by exact_mod_cast hQ'0
    have h2 : (z - quadConj z) ^ 2 ≤ (z - quadConj z) ^ 2 * (Q : ℝ) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
    rw [hsq] at h2
    nlinarith [sq_nonneg ((P' : ℝ) - Q)]
  have habs : |z - quadConj z| ≤ (P : ℝ) + P' + Q + Q' := by
    have hnn : (0 : ℝ) ≤ (P : ℝ) + P' + Q + Q' := by
      have : (0 : ℤ) ≤ P + P' + Q + Q' := by omega
      exact_mod_cast this
    exact abs_le_of_sq_le_sq' hle hnn |> fun h ↦ abs_le.mpr h
  calc |z - quadConj z| ≤ (P : ℝ) + P' + Q + Q' := habs
    _ ≤ 4 * (Pm : ℝ) := by
      have : P + P' + Q + Q' ≤ 4 * Pm := by omega
      exact_mod_cast this
    _ = 4 * ∏ i ∈ Finset.range r, ((cfQuot z i + 1 : ℤ) : ℝ) := by
      rw [Int.cast_prod]

/-- **The Proposition in the proof of Theorem 2** (pp. 10–11). Let `β > 1` be a quadratic
irrational and `S` an infinite set of exponents with `βⁿ` irrational, `βⁿ - β'ⁿ ≥ c βⁿ` and the
period of `βⁿ` at most `B`. Then `β` is a Pisot number. Otherwise Lemma 5 makes every partial
quotient `aᵢ(βⁿ)`, `1 ≤ i ≤ r`, of size `e^{o(n)}`; the reduced `z = βⁿ - kₙ`, `kₙ = ⌊β'ⁿ⌋ + 1`,
is purely periodic with period `r` and partial quotients among these, so
`c βⁿ ≤ |z - z'| ≤ 4 ∏ (aᵢ + 1) = e^{o(n)}`. -/
theorem isPisot_of_cfPeriod_le (hβ : IsQuadraticIrrational β) (h1 : 1 < β) {S : Set ℕ}
    (hS : S.Infinite) (hirr : ∀ n ∈ S, Irrational (β ^ n)) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ n ∈ S, c * β ^ n ≤ β ^ n - quadConj β ^ n) {B : ℕ}
    (hB : ∀ n ∈ S, cfPeriod (β ^ n) ≤ B) : IsPisot β := by
  classical
  by_contra hPis
  have hL5 := (isPisot_or_tendsto_log_cfQuot_of_mem hβ h1 hirr).resolve_left hPis
  -- a common period `r`
  obtain ⟨r, -, hr⟩ : ∃ r ∈ Finset.range (B + 1), {n ∈ S | cfPeriod (β ^ n) = r}.Infinite := by
    by_contra hne
    push Not at hne
    exact hS ((Set.Finite.biUnion (Finset.finite_toSet _) fun r hr ↦ hne r hr).subset
      fun n hn ↦ Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hB n hn)))) ⟨hn, rfl⟩)
  obtain ⟨n₁, hn₁⟩ := hr.nonempty
  have hr0 : 0 < r := hn₁.2 ▸ (hβ.quadConj_pow (hirr n₁ hn₁.1)).1.cfPeriod_pos
  -- `aᵢ(βⁿ) < e^{ηn}` for `1 ≤ i ≤ r`, eventually along `S`
  set L := Real.log β with hL
  have hL0 : 0 < L := Real.log_pos h1
  set η := L / (4 * r) with hηdef
  have hη : 0 < η := by positivity
  have hev : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 S, ∀ i ∈ Finset.Icc 1 r,
      Real.log (cfQuot (β ^ n) i) / n < η := by
    rw [eventually_all_finset]
    intro i hi
    exact (hL5 i (Finset.mem_Icc.mp hi).1).eventually (gt_mem_nhds hη)
  rw [eventually_inf_principal, eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  -- `c βⁿ` beats `2` and `4 (2 e^{ηn})^r` for large `n`
  set K := 4 * 2 ^ r / c + 2 / c + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * Real.log K / (3 * L))
  obtain ⟨n, hn, hnlarge⟩ := hr.exists_gt (max N (max N₁ 1))
  obtain ⟨hnS, hnr⟩ := hn
  have hnN : N ≤ n := (le_max_left _ _).trans hnlarge.le
  have hnN₁ : (N₁ : ℝ) ≤ n := by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hnlarge.le
  have hn1 : 1 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hnlarge.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hβn : β ^ n = Real.exp (n * L) := by
    rw [hL, ← Real.exp_log (pow_pos (zero_lt_one.trans h1) n), Real.log_pow]
  have hexpK : K < Real.exp (3 * n * L / 4) := by
    rw [← Real.exp_log hK0]
    refine Real.exp_lt_exp.mpr ?_
    rw [div_lt_iff₀ (by positivity)] at hN₁
    nlinarith
  have hbig : 4 * (2 * Real.exp (η * n)) ^ r < c * β ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, hβn]
    have e : (r : ℝ) * (η * n) = n * L / 4 := by
      rw [hηdef]
      field_simp
    rw [e]
    have hsplit : Real.exp (n * L) = Real.exp (n * L / 4) * Real.exp (3 * n * L / 4) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit]
    have h4 : 4 * 2 ^ r / c < Real.exp (3 * n * L / 4) := by
      refine lt_of_le_of_lt ?_ hexpK
      rw [hK]
      have : 0 ≤ 2 / c := by positivity
      linarith
    rw [div_lt_iff₀ hc] at h4
    have hpos := Real.exp_pos (n * L / 4)
    nlinarith
  have htwo : 2 < c * β ^ n := by
    have h2 : 2 / c < Real.exp (3 * n * L / 4) := by
      refine lt_of_le_of_lt ?_ hexpK
      rw [hK]
      have : 0 ≤ 4 * 2 ^ r / c := by positivity
      linarith
    rw [div_lt_iff₀ hc] at h2
    have : Real.exp (3 * n * L / 4) ≤ β ^ n := by
      rw [hβn]
      exact Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  -- the reduced number `z = βⁿ - kₙ`
  set x := β ^ n with hx
  have hxq := hβ.quadConj_pow (hirr n hnS)
  set x' := quadConj x with hx'
  have hx'irr : Irrational x' := hxq.1.irrational_quadConj
  set k : ℤ := ⌊x'⌋ + 1 with hk
  have hzq := hxq.1.sub_intCast k
  set z := x - k with hz
  have hfr0 : 0 < Int.fract x' := (Int.fract_nonneg _).lt_of_ne' hx'irr.fract_ne_zero
  have hfr1 : Int.fract x' < 1 := Int.fract_lt_one _
  have hz' : quadConj z = Int.fract x' - 1 := by
    rw [hzq.2, hk, Int.fract]
    push_cast
    ring
  have hgapn := hgap n hnS
  rw [← hxq.2] at hgapn
  have hz1 : 1 < z := by
    have := Int.floor_le x'
    rw [hz, hk]
    push_cast
    linarith
  have hred : IsReduced z := ⟨hzq.1, hz1, by rw [hz']; linarith, by rw [hz']; linarith⟩
  -- its period is `r`, and it is purely periodic
  have hzx : TailEquiv z x := by
    have := tailEquiv_add_intCast x (-k)
    rwa [Int.cast_neg, ← sub_eq_add_neg] at this
  have hzr : cfPeriod z = r := by
    rw [cfPeriod_eq_of_tailEquiv hzq.1.1 hxq.1.1 hzx, ← hnr]
  have hpure : cfTail z r = z :=
    hred.cfTail_eq_self (hzr ▸ hzq.1.isCFPeriod_cfPeriod)
  -- the partial quotients of `z` are those of `βⁿ` at indices `1, …, r`
  have htail1 : cfTail z 1 = cfTail x 1 := by
    rw [cfTail_one, cfTail_one, hz, Int.fract_sub_intCast]
  have hquot : ∀ i ∈ Finset.range r, ((cfQuot z i + 1 : ℤ) : ℝ) ≤ 2 * Real.exp (η * n) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    -- the index in `βⁿ`
    obtain ⟨j, hj1, hjr, hj⟩ : ∃ j, 1 ≤ j ∧ j ≤ r ∧ cfQuot z i = cfQuot x j := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨r, hr0, le_rfl, ?_⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hr0
        rw [show 0 + m + 1 = 1 + m by ring] at hpure ⊢
        calc cfQuot z 0 = cfQuot z (1 + m) := by rw [cfQuot, cfQuot, cfTail_zero, hpure]
          _ = cfQuot x (1 + m) := by rw [cfQuot_add, htail1, ← cfQuot_add]
      · refine ⟨i, hi0, hi'.le, ?_⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi0
        rw [zero_add, show m + 1 = 1 + m by ring, cfQuot_add, htail1, ← cfQuot_add]
    have hbound := hN n hnN hnS j (Finset.mem_Icc.mpr ⟨hj1, hjr⟩)
    have haj : (1 : ℝ) ≤ cfQuot x j := by exact_mod_cast one_le_cfQuot hxq.1.1 hj1
    rw [div_lt_iff₀ hn0] at hbound
    have : (cfQuot x j : ℝ) < Real.exp (η * n) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < cfQuot x j)]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [hj]
    push_cast
    linarith
  have hprod : ∏ i ∈ Finset.range r, ((cfQuot z i + 1 : ℤ) : ℝ) ≤
      (2 * Real.exp (η * n)) ^ r := by
    calc ∏ i ∈ Finset.range r, ((cfQuot z i + 1 : ℤ) : ℝ)
        ≤ ∏ i ∈ Finset.range r, (2 * Real.exp (η * n)) :=
          Finset.prod_le_prod₀ (fun i _ ↦ by
            have : (1 : ℤ) ≤ cfQuot z i := by
              rcases Nat.eq_zero_or_pos i with rfl | hi0
              · rw [cfQuot, cfTail_zero]
                exact Int.le_floor.mpr (by exact_mod_cast hz1.le)
              · exact one_le_cfQuot hzq.1.1 hi0
            have : (0 : ℤ) ≤ cfQuot z i + 1 := by omega
            exact_mod_cast this) hquot
      _ = (2 * Real.exp (η * n)) ^ r := by rw [Finset.prod_const, Finset.card_range]
  have habs := abs_sub_quadConj_le hzq.1 hz1 hr0 hpure
  have hdiff : z - quadConj z = x - x' := by rw [hzq.2, hz]; ring
  rw [hdiff] at habs
  have : c * x ≤ |x - x'| := hgapn.trans (le_abs_self _)
  linarith

/-- The conjugate of an integral quadratic irrational is integral: `x + x'` is a rational
integer. -/
theorem IsQuadraticIrrational.isIntegral_quadConj (hx : IsQuadraticIrrational x)
    (hint : IsIntegral ℤ x) : IsIntegral ℤ (quadConj x) := by
  obtain ⟨b, c, h⟩ := hx.exists_monic_of_isIntegral hint
  have hs := hx.add_quadConj (a := 1) (b := b) (c := c) one_ne_zero
    (by push_cast; linear_combination h)
  have hb : IsIntegral ℤ ((-b : ℤ) : ℝ) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := -b)
  have : quadConj x = ((-b : ℤ) : ℝ) - x := by
    push_cast at hs ⊢
    linarith
  rw [this]
  exact hb.sub hint

/-- The conjugate of a quadratic Pisot number lies in the open unit interval. -/
theorem IsQuadraticIrrational.abs_quadConj_lt_one (hx : IsQuadraticIrrational x)
    (h : IsPisot x) : |quadConj x| < 1 := by
  have hmem : (quadConj x : ℂ) ∈ (minpoly ℚ x).aroots ℂ := by
    rw [hx.aroots_minpoly]
    simp
  have hne : (quadConj x : ℂ) ≠ x := by exact_mod_cast hx.quadConj_ne
  simpa [Complex.norm_real] using h.2.2 _ hmem hne

/-- The Proposition with the gap condition replaced by `|β'| < β`: then
`βⁿ - β'ⁿ ≥ (1 - |β'|/β) βⁿ` for `n ≥ 1`. -/
theorem isPisot_of_cfPeriod_le_of_abs_lt (hβ : IsQuadraticIrrational β) (h1 : 1 < β)
    (hlt : |quadConj β| < β) {S : Set ℕ} (hS : S.Infinite) (hpos : ∀ n ∈ S, 0 < n)
    (hirr : ∀ n ∈ S, Irrational (β ^ n)) {B : ℕ} (hB : ∀ n ∈ S, cfPeriod (β ^ n) ≤ B) :
    IsPisot β := by
  have hβ0 : 0 < β := zero_lt_one.trans h1
  set ρ := |quadConj β| / β with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hβ0).mpr hlt
  refine isPisot_of_cfPeriod_le hβ h1 hS hirr (c := 1 - ρ) (by linarith) (fun n hn ↦ ?_) hB
  have hpow : |quadConj β| ^ n = ρ ^ n * β ^ n := by
    rw [← mul_pow, hρ, div_mul_cancel₀ _ hβ0.ne']
  have hρn : ρ ^ n ≤ ρ := pow_le_of_le_one hρ0 hρ1.le (hpos n hn).ne'
  have hle : quadConj β ^ n ≤ |quadConj β| ^ n := by
    rw [← abs_pow]
    exact le_abs_self _
  have hβn : 0 < β ^ n := pow_pos hβ0 n
  nlinarith

/-- The Proposition for `|γ| > |γ'|`, `|γ| > 1`, of either sign: `γ` is an algebraic integer and
`|γ'| < 1`. -/
theorem isIntegral_of_cfPeriod_le {γ : ℝ} (hγ : IsQuadraticIrrational γ) (h1 : 1 < |γ|)
    (hlt : |quadConj γ| < |γ|) {S : Set ℕ} (hS : S.Infinite) (hpos : ∀ n ∈ S, 0 < n)
    (hirr : ∀ n ∈ S, Irrational (γ ^ n)) {B : ℕ} (hB : ∀ n ∈ S, cfPeriod (γ ^ n) ≤ B) :
    IsIntegral ℤ γ ∧ |quadConj γ| < 1 := by
  rcases le_or_gt 0 γ with h0 | h0
  · rw [abs_of_nonneg h0] at h1 hlt
    have h := isPisot_of_cfPeriod_le_of_abs_lt hγ h1 hlt hS hpos hirr hB
    exact ⟨h.2.1, hγ.abs_quadConj_lt_one h⟩
  · rw [abs_of_neg h0] at h1 hlt
    have hng := hγ.neg
    have hpow : ∀ n, (-γ) ^ n = γ ^ n ∨ (-γ) ^ n = -γ ^ n := fun n ↦ by
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inl (he.neg_pow γ)
      · exact Or.inr (ho.neg_pow γ)
    have hirr' : ∀ n ∈ S, Irrational ((-γ) ^ n) := fun n hn ↦ by
      rcases hpow n with h | h <;> rw [h]
      exacts [hirr n hn, (hirr n hn).neg]
    have hB' : ∀ n ∈ S, cfPeriod ((-γ) ^ n) ≤ B := fun n hn ↦ by
      rcases hpow n with h | h <;> rw [h]
      · exact hB n hn
      · rw [cfPeriod_eq_of_tailEquiv (hirr n hn).neg (hirr n hn) (tailEquiv_neg (hirr n hn))]
        exact hB n hn
    have h := isPisot_of_cfPeriod_le_of_abs_lt hng.1 h1 (by rw [hng.2, abs_neg]; exact hlt) hS
      hpos hirr' hB'
    refine ⟨by simpa using h.2.1.neg, ?_⟩
    have := hng.1.abs_quadConj_lt_one h
    rwa [hng.2, abs_neg] at this

/-- **Theorem 2 (a) of Corvaja–Zannier** (p. 1): if the real quadratic irrational `α` is neither
the square root of a rational number nor a unit, the period of the continued fraction of `αⁿ`
tends to infinity. (The paper assumes `α > 0`; the sign plays no role.) -/
theorem tendsto_cfPeriod_pow {α : ℝ} (hα : IsQuadraticIrrational α) (hsq : ∀ r : ℚ, α ^ 2 ≠ r)
    (hunit : ¬ (IsIntegral ℤ α ∧ IsIntegral ℤ α⁻¹)) :
    Tendsto (fun n ↦ cfPeriod (α ^ n)) atTop atTop := by
  set α' := quadConj α with hα'
  have hα'q := hα.isQuadraticIrrational_quadConj
  have hirr : ∀ n, 0 < n → Irrational (α ^ n) := fun n hn ⟨r, hr⟩ ↦ by
    obtain ⟨s, hs⟩ := hα.exists_sq_eq_of_pow_eq hn hr.symm
    exact hsq s hs
  have hirr' : ∀ n, 0 < n → Irrational (α' ^ n) := fun n hn ↦ by
    rw [← (hα.quadConj_pow (hirr n hn)).2]
    exact (hα.quadConj_pow (hirr n hn)).1.irrational_quadConj
  have hper' : ∀ n, 0 < n → cfPeriod (α' ^ n) = cfPeriod (α ^ n) := fun n hn ↦ by
    rw [← (hα.quadConj_pow (hirr n hn)).2]
    exact (hα.quadConj_pow (hirr n hn)).1.cfPeriod_quadConj
  -- `|α| ≠ |α'|`, since `α'  = -α` would make `α² = -α α'` rational
  have habs : |α'| ≠ |α| := by
    intro h
    rcases abs_eq_abs.mp h with h | h
    · exact hα.quadConj_ne h
    · obtain ⟨a, b, c, ha, hq⟩ := hα.2
      have hm := hα.mul_quadConj ha hq
      rw [← hα', h] at hm
      exact hsq (-(c / a)) (by push_cast; linear_combination -hm)
  -- a set of exponents with bounded period
  rw [tendsto_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  set S := {n | cfPeriod (α ^ n) < B ∧ 0 < n} with hSdef
  have hS : S.Infinite :=
    Nat.frequently_atTop_iff_infinite.mp (hB.and_eventually (eventually_gt_atTop 0))
  -- `γ₁` is the one of `α, α'` of larger absolute value, `γ₂ = γ₁'` the other
  obtain ⟨γ₁, hq1, hlt, hirr1, hirr2, hper1, hper2, hunitγ⟩ : ∃ γ₁ : ℝ,
      IsQuadraticIrrational γ₁ ∧ |quadConj γ₁| < |γ₁| ∧
      (∀ n ∈ S, Irrational (γ₁ ^ n)) ∧ (∀ n ∈ S, Irrational (quadConj γ₁ ^ n)) ∧
      (∀ n ∈ S, cfPeriod (γ₁ ^ n) ≤ B) ∧ (∀ n ∈ S, cfPeriod (quadConj γ₁ ^ n) ≤ B) ∧
      (IsIntegral ℤ γ₁ → IsIntegral ℤ (quadConj γ₁)⁻¹ → IsIntegral ℤ α ∧ IsIntegral ℤ α⁻¹) := by
    rcases lt_or_gt_of_ne habs with h | h
    · refine ⟨α, hα, h, fun n hn ↦ hirr n hn.2, fun n hn ↦ hirr' n hn.2,
        fun n hn ↦ hn.1.le, fun n hn ↦ (hper' n hn.2).le.trans hn.1.le, fun h1 h2 ↦ ⟨h1, ?_⟩⟩
      have := hα'q.inv
      rw [hα.quadConj_quadConj] at this
      rw [← this.2]
      exact this.1.isIntegral_quadConj h2
    · refine ⟨α', hα'q, by rwa [hα.quadConj_quadConj], fun n hn ↦ hirr' n hn.2, ?_, ?_, ?_, ?_⟩
      · rw [hα.quadConj_quadConj]
        exact fun n hn ↦ hirr n hn.2
      · exact fun n hn ↦ (hper' n hn.2).le.trans hn.1.le
      · rw [hα.quadConj_quadConj]
        exact fun n hn ↦ hn.1.le
      · rw [hα.quadConj_quadConj]
        refine fun h1 h2 ↦ ⟨?_, h2⟩
        have := hα'q.isIntegral_quadConj h1
        rwa [hα.quadConj_quadConj] at this
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ hn.2
  have hq2 := hq1.isQuadraticIrrational_quadConj
  have hne1 : |γ₁| ≠ 1 := fun h ↦ by
    rcases (abs_eq zero_le_one).mp h with h | h
    · exact hq1.1 ⟨1, by rw [h]; norm_num⟩
    · exact hq1.1 ⟨-1, by rw [h]; norm_num⟩
  -- `|γ₂| < 1`
  have hγ2 : |quadConj γ₁| < 1 := by
    rcases lt_or_gt_of_ne hne1 with h | h
    · exact hlt.trans h
    · exact (isIntegral_of_cfPeriod_le hq1 h hlt hS hpos hirr1 hper1).2
  -- the Proposition for `1/γ₂`
  have hγ2pos : 0 < |quadConj γ₁| := abs_pos.mpr hq2.1.ne_zero
  have hγ1pos : 0 < |γ₁| := abs_pos.mpr hq1.1.ne_zero
  have hinv := hq2.inv
  rw [hq1.quadConj_quadConj] at hinv
  have hδ := isIntegral_of_cfPeriod_le (γ := (quadConj γ₁)⁻¹) (S := S) (B := B) hinv.1
    (by rw [abs_inv]; exact (one_lt_inv₀ hγ2pos).mpr hγ2)
    (by rw [hinv.2, abs_inv, abs_inv]; exact (inv_lt_inv₀ hγ1pos hγ2pos).mpr hlt) hS hpos
    (fun n hn ↦ by rw [inv_pow]; exact (hirr2 n hn).inv)
    (fun n hn ↦ by
      rw [inv_pow, cfPeriod_eq_of_tailEquiv (hirr2 n hn).inv (hirr2 n hn)
        (tailEquiv_inv (hirr2 n hn))]
      exact hper2 n hn)
  rw [hinv.2, abs_inv] at hδ
  have hγ1 : 1 < |γ₁| := (inv_lt_one₀ hγ1pos).mp hδ.2
  exact hunit (hunitγ (isIntegral_of_cfPeriod_le hq1 hγ1 hlt hS hpos hirr1 hper1).1 hδ.1)

/-- The odd powers of an irrational square root of a rational number are irrational. -/
theorem irrational_pow_two_mul_add_one {α : ℝ} (hα : Irrational α) {s : ℚ} (hs : α ^ 2 = s)
    (k : ℕ) : Irrational (α ^ (2 * k + 1)) := by
  rintro ⟨r, hr⟩
  have hs0 : (s : ℝ) ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ hα.ne_zero
  have : α = r / s ^ k := by
    rw [eq_div_iff (pow_ne_zero _ hs0), ← hs, ← pow_mul, hr]
    ring
  exact hα ⟨r / s ^ k, by rw [this]; push_cast; rfl⟩

/-- Theorem 2 (b) for `β > 1`: `β' = -β`, so `β²ⁿ⁺¹ - β'²ⁿ⁺¹ = 2 β²ⁿ⁺¹`, and bounded periods
would make `β` a Pisot number, while `|β'| = β > 1`. -/
theorem tendsto_cfPeriod_pow_odd_of_one_lt (hβ : IsQuadraticIrrational β) (h1 : 1 < β)
    (hsq : ∃ r : ℚ, β ^ 2 = r) :
    Tendsto (fun n : ℕ ↦ cfPeriod (β ^ (2 * n + 1))) atTop atTop := by
  obtain ⟨s, hs⟩ := hsq
  have hconj : quadConj β = -β := by
    have := hβ.add_quadConj (a := 1) (b := 0) (c := -s) one_ne_zero
      (by push_cast; rw [hs]; ring)
    simp only [Rat.cast_zero, Rat.cast_one, neg_zero, zero_div] at this
    linarith
  rw [tendsto_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  set S := (fun n ↦ 2 * n + 1) '' {n | cfPeriod (β ^ (2 * n + 1)) < B} with hSdef
  have hS : S.Infinite := (Nat.frequently_atTop_iff_infinite.mp hB).image
    fun a _ b _ h ↦ by
      have : 2 * a + 1 = 2 * b + 1 := h
      omega
  have hPis := isPisot_of_cfPeriod_le hβ h1 hS
    (by rintro _ ⟨k, -, rfl⟩; exact irrational_pow_two_mul_add_one hβ.1 hs k) one_pos
    (by
      rintro _ ⟨k, -, rfl⟩
      rw [hconj, (Nat.odd_iff.mpr (by omega) : Odd (2 * k + 1)).neg_pow]
      have := pow_pos (zero_lt_one.trans h1) (2 * k + 1)
      linarith)
    (B := B) (by rintro _ ⟨k, hk, rfl⟩; exact le_of_lt hk)
  have := hβ.abs_quadConj_lt_one hPis
  rw [hconj, abs_neg, abs_of_pos (zero_lt_one.trans h1)] at this
  linarith

/-- **Theorem 2 (b) of Corvaja–Zannier** (p. 1): if `α > 0` is an irrational square root of a
rational number, the period of the continued fraction of `α²ⁿ⁺¹` tends to infinity. -/
theorem tendsto_cfPeriod_pow_odd {α : ℝ} (hα : IsQuadraticIrrational α) (h0 : 0 < α)
    (hsq : ∃ r : ℚ, α ^ 2 = r) :
    Tendsto (fun n : ℕ ↦ cfPeriod (α ^ (2 * n + 1))) atTop atTop := by
  have hne : α ≠ 1 := fun h ↦ hα.1 ⟨1, by rw [h]; norm_num⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs⟩ := hsq
    have hs' : α⁻¹ ^ 2 = ((s⁻¹ : ℚ) : ℝ) := by
      rw [inv_pow, hs]
      push_cast
      rfl
    refine (tendsto_cfPeriod_pow_odd_of_one_lt hα.inv.1 ((one_lt_inv₀ h0).mpr hlt)
      ⟨_, hs'⟩).congr fun n ↦ ?_
    have hirr := irrational_pow_two_mul_add_one hα.inv.1.1 hs' n
    rw [show α ^ (2 * n + 1) = (α⁻¹ ^ (2 * n + 1))⁻¹ by rw [inv_pow, inv_inv]]
    exact (cfPeriod_eq_of_tailEquiv hirr.inv hirr (tailEquiv_inv hirr)).symm
  · exact tendsto_cfPeriod_pow_odd_of_one_lt hα hgt hsq

end Real
