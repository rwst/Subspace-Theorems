/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.ThreeVariable

/-!
# The points with a small gap lie on few lines

A point `(b^t, b^r, p)` of Bugeaud–Evertse 2008, §7, with a small gap `s = t - r`,
`4 s ≤ ε t`, is counted in two variables. The point `y = (b^t - b^r, p)` has size between
`b^t / 2` and `b^t`. Its first coordinate is `b^r (b^s - 1)`, so `|y₀|_l = |b^r|_l` at the primes
`l ∣ b`. It solves a system of the quantitative Subspace Theorem at `∞` and the primes of `b`:

* at `∞` the forms `ξ X₀ - X₁` and `X₀`, with exponents `-ε` and `1`;
* at `l ∣ b` the coordinates, with exponents `(1 - ε/4) g_l` and `0`, where `∑_l g_l = -1`.

The exponents sum to `-3ε/4`. So Evertse–Ferretti's count puts the points into
`K ε⁻³ (1 + log ε⁻¹)²` lines (`Real.exists_lines_of_small_gap`). Two points on a line satisfy
`(b^{t₁} - b^{r₁}) p₂ = (b^{t₂} - b^{r₂}) p₁`; when `r₁ < r₂` this forces `b ∣ p₂`, because
`b^{s₁} - 1` is prime to `b` (`Int.dvd_of_pow_sub_pow_mul_eq`). So a line holds at most one point
of a doubling sequence with `b ∤ p_n`.

## Main results

* `Int.dvd_of_pow_sub_pow_mul_eq`: **one point per line**.
* `Real.gap_hyps`, `Real.gap_mem`: the system (`Real.gapForms`, `Real.gapExp`, `Real.gapPadic`)
  is admissible, and the point `Real.gapPoint b r t p` of an approximation with a small gap
  solves it.
* `Real.exists_lines_of_small_gap`: **the two-variable step**.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7;
J.-H. Evertse, R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*, Ann.
of Math. **177** (2013), 513–590;
R. Stephan, *The exponent `1/4` in three complexity bounds: integer bases, continued fractions, and
the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), Lemmas 3.6–3.7.
-/

@[expose] public section

open Finset

/-- **One point per line.** If `(b^{t₁} - b^{r₁}) p₂ = (b^{t₂} - b^{r₂}) p₁` with `r₁ < t₁`,
`r₁ < r₂ ≤ t₂` and `b ≠ 0`, then `b ∣ p₂`: cancelling `b^{r₁}` leaves `(b^{s₁} - 1) p₂` divisible
by `b`, and `b^{s₁} - 1` is prime to `b`.
Lemma 3.7 of Stephan's *The exponent `1/4` in three complexity bounds* (2026, arXiv:2610.30937). -/
theorem Int.dvd_of_pow_sub_pow_mul_eq {b p₁ p₂ : ℤ} {r₁ t₁ r₂ t₂ : ℕ} (hb : b ≠ 0) (h₁ : r₁ < t₁)
    (hr : r₁ < r₂) (h₂ : r₂ ≤ t₂) (h : (b ^ t₁ - b ^ r₁) * p₂ = (b ^ t₂ - b ^ r₂) * p₁) :
    b ∣ p₂ := by
  obtain ⟨s, rfl⟩ : ∃ s, t₁ = r₁ + (s + 1) := ⟨t₁ - r₁ - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r₂ = r₁ + (k + 1) := ⟨r₂ - r₁ - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, t₂ = r₁ + (k + 1) + u := ⟨t₂ - (r₁ + (k + 1)), by omega⟩
  have hcop : IsCoprime b (b ^ (s + 1) - 1) := ⟨b ^ s, -1, by ring⟩
  refine hcop.dvd_of_dvd_mul_left ⟨b ^ k * (b ^ u - 1) * p₁, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero r₁ hb)
  linear_combination h

namespace Real

variable {b : ℕ}

/-- **The forms of the two-variable step**: `ξ X₀ - X₁` and `X₀`. -/
def gapForms : Fin 2 → Fin 2 → Fin 3 → ℤ := ![![![0, 1, 0], ![-1, 0, 0]], ![![1, 0, 0], 0]]

theorem abs_gapForms_le (i j : Fin 2) (m : Fin 3) : |(gapForms i j m : ℝ)| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [gapForms]

theorem one_le_abs_det_gapForms (ξ : ℝ) :
    (1 : ℝ) ≤ |(Matrix.of fun i j ↦ quadVal ξ (gapForms i j)).det| := by
  simp [Matrix.det_fin_two, quadVal, gapForms]

/-- **The exponents at `∞`**: `-ε`, `1`. -/
noncomputable def gapExp (ε : ℝ) : Fin 2 → ℝ := ![-ε, 1]

/-- **The exponents at `l ∣ b`**: `(1 - ε/4) g_l`, `0`. -/
noncomputable def gapPadic (b : ℕ) (ε : ℝ) : Nat.Primes → Fin 2 → ℝ := fun l ↦
  ![(1 - ε / 4) * baseExp b l, 0]

/-- **The point** `(b^t - b^r, p)`. -/
def gapPoint (b r t : ℕ) (p : ℤ) : Fin 2 → ℤ := ![(b : ℤ) ^ t - (b : ℤ) ^ r, p]

theorem cast_gapPoint (b r t : ℕ) (p : ℤ) :
    (fun i ↦ (gapPoint b r t p i : ℚ)) = ![(b : ℚ) ^ t - (b : ℚ) ^ r, (p : ℚ)] := by
  ext i
  fin_cases i <;> simp [gapPoint]

/-- **The system is admissible**: for `0 < ε ≤ 1` the exponents meet the hypotheses of
`Real.SubspaceBoundWith` with `δ = ε / 2`, at `∞` and the primes of `b`. -/
theorem gap_hyps (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ i, gapExp ε i ≤ 1) ∧ (∃ i, gapExp ε i = 1) ∧
      (∃ i, gapExp ε i ≤ 1 - ε / 2 / (2 * ((2 : ℕ) : ℝ))) ∧
      (∀ l ∈ basePrimes b, ∀ i, gapPadic b ε l i ≤ 0) ∧
      (∀ l ∈ basePrimes b, ∃ i, gapPadic b ε l i = 0) ∧
      ∑ i, gapExp ε i + ∑ l ∈ basePrimes b, ∑ i, gapPadic b ε l i ≤ -(ε / 2) := by
  have hθ0 : 0 ≤ 1 - ε / 4 := by linarith
  have hgsum : ∑ l ∈ basePrimes b, baseExp b l = -1 := sum_factorization_log_div hb
  refine ⟨fun i ↦ by fin_cases i <;> simp [gapExp]; linarith, ⟨1, by simp [gapExp]⟩,
    ⟨0, ?_⟩, fun l _ i ↦ ?_, fun l _ ↦ ⟨1, by simp [gapPadic]⟩, ?_⟩
  · change -ε ≤ 1 - ε / 2 / (2 * ((2 : ℕ) : ℝ))
    push_cast
    linarith
  · fin_cases i
    · simp only [gapPadic, Fin.zero_eta, Matrix.cons_val_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hθ0 (baseExp_nonpos hb l)
    · simp [gapPadic]
  · have h1 : ∑ l ∈ basePrimes b, ∑ i, gapPadic b ε l i =
        (1 - ε / 4) * ∑ l ∈ basePrimes b, baseExp b l := by
      rw [mul_sum]
      refine sum_congr rfl fun l _ ↦ ?_
      simp [gapPadic, Fin.sum_univ_two]
    rw [h1, hgsum]
    simp only [gapExp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linarith

/-- **The point of an approximation with a small gap solves the system**: for `0 < ε ≤ 1`,
`r < t`, `|p| ≤ b^t`, `|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}` and `4 (t - r) ≤ ε t`, the point
`(b^t - b^r, p)` is nonzero, of size `X` with `b^t - b^r ≤ X ≤ b^t`, and solves the inequalities
of `Real.SubspaceBoundWith` for `gapForms`, the constant `1` and the exponents `gapExp ε`,
`gapPadic b ε`. -/
theorem gap_mem (hb : 2 ≤ b) {ξ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {r t : ℕ} {p : ℤ}
    (hrt : r < t) (hp : |(p : ℝ)| ≤ (b : ℝ) ^ t)
    (happ : |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε))
    (hgap : 4 * ((t : ℝ) - r) ≤ ε * t) :
    gapPoint b r t p ≠ 0 ∧
      (∀ i, |∑ j, quadVal ξ (gapForms i j) * (gapPoint b r t p j : ℝ)| ≤
        1 * (⨆ j, |(gapPoint b r t p j : ℝ)|) ^ gapExp ε i) ∧
      (∀ l ∈ basePrimes b, ∀ i, ((padicNorm (l : ℕ) (gapPoint b r t p i : ℚ) : ℚ) : ℝ) ≤
        (⨆ j, |(gapPoint b r t p j : ℝ)|) ^ gapPadic b ε l i) ∧
      (b : ℝ) ^ t - b ^ r ≤ ⨆ j, |(gapPoint b r t p j : ℝ)| ∧
      (⨆ j, |(gapPoint b r t p j : ℝ)|) ≤ (b : ℝ) ^ t ∧ 2 * (b : ℝ) ^ r ≤ (b : ℝ) ^ t := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  set θ : ℝ := 1 - ε / 4 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  set x : Fin 2 → ℤ := gapPoint b r t p with hx
  -- `b^t / 2 ≤ b^t - b^r ≤ |x| ≤ b^t`
  have hbr : 2 * (b : ℝ) ^ r ≤ (b : ℝ) ^ t := by
    obtain ⟨u, rfl⟩ : ∃ u, t = r + (u + 1) := ⟨t - r - 1, by omega⟩
    have : (2 : ℝ) ≤ (b : ℝ) ^ (u + 1) :=
      le_trans (by exact_mod_cast hb) (le_self_pow₀ hbR.le (by omega))
    rw [pow_add]
    nlinarith [pow_pos hb0 r]
  have hbr0 : 0 < (b : ℝ) ^ r := by positivity
  have hx0 : ((x 0 : ℤ) : ℝ) = (b : ℝ) ^ t - b ^ r := by simp [x, gapPoint]
  have hX : (⨆ i, |(x i : ℝ)|) ≤ (b : ℝ) ^ t := by
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · change |((x 0 : ℤ) : ℝ)| ≤ _
      rw [hx0, abs_of_pos (by linarith)]; linarith
    · simpa [x, gapPoint] using hp
  have hX' : (b : ℝ) ^ t - b ^ r ≤ ⨆ i, |(x i : ℝ)| := by
    refine le_ciSup_of_le (Set.finite_range _).bddAbove 0 ?_
    change _ ≤ |((x 0 : ℤ) : ℝ)|
    rw [hx0]; exact le_abs_self _
  set X := ⨆ i, |(x i : ℝ)| with hXdef
  have hX0 : 0 < X := by linarith
  have hx0' : x ≠ 0 := fun h ↦ by
    have := congrArg (fun y : Fin 2 → ℤ ↦ ((y 0 : ℤ) : ℝ)) h
    simp only [hx0, Pi.zero_apply, Int.cast_zero] at this
    linarith
  have hinf : ∀ i, |∑ j, quadVal ξ (gapForms i j) * x j| ≤ 1 * X ^ gapExp ε i := by
    intro i
    fin_cases i
    · have : ∑ j, quadVal ξ (gapForms 0 j) * x j = (b : ℝ) ^ t * ξ - b ^ r * ξ - p := by
        simp [gapForms, quadVal, Fin.sum_univ_two, x, gapPoint]; ring
      simp only [Fin.zero_eta, this, one_mul, gapExp, Matrix.cons_val_zero]
      exact happ.trans (rpow_le_rpow_of_nonpos hX0 hX (by linarith))
    · have : ∑ j, quadVal ξ (gapForms 1 j) * x j = (b : ℝ) ^ t - b ^ r := by
        simp [gapForms, quadVal, Fin.sum_univ_two, x, gapPoint]
      simp only [Fin.mk_one, this, one_mul, gapExp, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        rpow_one]
      rw [abs_of_pos (by linarith)]
      exact hX'
  have hpad : ∀ l ∈ basePrimes b, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤
      X ^ gapPadic b ε l i := by
    intro l _ i
    have := Fact.mk l.2
    fin_cases i
    · -- `|b^r (b^s - 1)|_l ≤ |b^r|_l = (b^r)^{g_l} ≤ X^{θ g_l}`
      obtain ⟨u, rfl⟩ : ∃ u, t = r + u := ⟨t - r, by omega⟩
      have hq : ((x 0 : ℤ) : ℚ) = (b : ℚ) ^ r * (((b : ℤ) ^ u - 1 : ℤ) : ℚ) := by
        simp [x, gapPoint, pow_add]; ring
      have hle : ((padicNorm (l : ℕ) ((x 0 : ℤ) : ℚ) : ℚ) : ℝ) ≤
          ((padicNorm (l : ℕ) ((b : ℚ) ^ r) : ℚ) : ℝ) := by
        rw [hq, padicNorm.mul]
        have h1 := padicNorm.of_int (p := (l : ℕ)) ((b : ℤ) ^ u - 1)
        have h0 : 0 ≤ padicNorm (l : ℕ) ((b : ℚ) ^ r) := padicNorm.nonneg _
        exact_mod_cast mul_le_of_le_one_right h0 h1
      refine (hle.trans_eq (padicNorm_pow_eq_rpow hb l r)).trans ?_
      change ((b : ℝ) ^ r) ^ baseExp b l ≤ X ^ (θ * baseExp b l)
      rw [rpow_mul hX0.le]
      refine rpow_le_rpow_of_nonpos (rpow_pos_of_pos hX0 _) ?_ (baseExp_nonpos hb l)
      -- `X^θ ≤ (b^t)^θ = b^{t θ} ≤ b^r`
      calc X ^ θ ≤ ((b : ℝ) ^ (r + u)) ^ θ := rpow_le_rpow hX0.le hX hθ0
        _ = (b : ℝ) ^ (((r + u : ℕ) : ℝ) * θ) := by rw [← rpow_natCast, ← rpow_mul hb0.le]
        _ ≤ (b : ℝ) ^ (r : ℝ) := by
            refine rpow_le_rpow_of_exponent_le hbR.le ?_
            rw [hθ]; push_cast at hgap ⊢; nlinarith
        _ = (b : ℝ) ^ r := rpow_natCast _ _
    · change ((padicNorm (l : ℕ) ((p : ℤ) : ℚ) : ℚ) : ℝ) ≤ X ^ (0 : ℝ)
      rw [rpow_zero]
      exact_mod_cast padicNorm.of_int p
  exact ⟨hx0', hinf, hpad, hX', hX, hbr⟩

/-- **The two-variable step for small gaps.** For `ξ` real algebraic and `b ≥ 2` there is `K > 0`
such that for `0 < ε ≤ 1` the points `(b^t - b^r, p)` with `r < t`, `|p| ≤ b^t`,
`|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}`, a small gap `4 (t - r) ≤ ε t` and `K ε⁻¹ ≤ t log b` lie on at
most `K ε⁻³ (1 + log ε⁻¹)²` lines.
First proved as Lemma 3.6 of Stephan's *The exponent `1/4` in three complexity bounds* (2026,
arXiv:2610.30937). -/
theorem exists_lines_of_small_gap (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset (Submodule ℚ (Fin 2 → ℚ)),
      (#T : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ (r t : ℕ) (p : ℤ), r < t → |(p : ℝ)| ≤ (b : ℝ) ^ t →
        |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε) → 4 * ((t : ℝ) - r) ≤ ε * t →
        K * ε⁻¹ ≤ t * log b → ∃ U ∈ T, ![(b : ℚ) ^ t - (b : ℚ) ^ r, (p : ℚ)] ∈ U := by
  classical
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceBoundAt_three hξ (basePrimes b) 2 le_rfl (by norm_num)
  refine ⟨32 * K₀ + 1, by positivity, fun ε hε hε1 ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gap_hyps hb hε hε1
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hBE gapForms 1 le_rfl abs_gapForms_le 1 one_pos le_rfl
    (one_le_abs_det_gapForms ξ) 1 le_rfl (gapExp ε) (gapPadic b ε) δ hδ0 hδ1 h1 h2 h3 h4 h5 h6
  refine ⟨T, ?_, hTtop, ?_⟩
  · -- `K₀ (2 ε⁻¹)³ (1 + log 2 + log ε⁻¹)² ≤ 32 K₀ ε⁻³ (1 + log ε⁻¹)²`
    refine hTcard.trans ?_
    have hδinv : δ⁻¹ = 2 * ε⁻¹ := by rw [hδ, inv_div, div_eq_mul_inv]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast, hδinv,
      log_mul (by norm_num) (by positivity)]
    have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
    have hlog2 : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h1 : (1 + (log 2 + log ε⁻¹)) ^ 2 ≤ 4 * (1 + log ε⁻¹) ^ 2 := by nlinarith
    have h2 : 0 ≤ ε⁻¹ ^ 3 := by positivity
    calc K₀ * (2 * ε⁻¹) ^ 3 * (1 + (log 2 + log ε⁻¹)) ^ 2
        = 8 * K₀ * ε⁻¹ ^ 3 * (1 + (log 2 + log ε⁻¹)) ^ 2 := by ring
      _ ≤ 8 * K₀ * ε⁻¹ ^ 3 * (4 * (1 + log ε⁻¹) ^ 2) := by gcongr
      _ = 32 * K₀ * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by ring
      _ ≤ (32 * K₀ + 1) * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by gcongr; linarith
  intro r t p hrt hp happ hgap hthr
  obtain ⟨hx0, hinf, hpad, hX', hX, hbr⟩ := gap_mem hb hε hε1 hrt hp happ hgap
  set X := ⨆ i, |(gapPoint b r t p i : ℝ)| with hXdef
  -- the threshold `2 K₀ ε⁻¹ ≤ t log b - log 2 ≤ log X`
  have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log 1⁻¹) ≤ log X := by
    simp only [log_one, inv_one, add_zero]
    have hlogX : log ((b : ℝ) ^ t) - log 2 ≤ log X := by
      rw [← log_div (by positivity) (by norm_num)]
      have : 0 < (b : ℝ) ^ r := by positivity
      exact log_le_log (by positivity) (by linarith)
    rw [log_pow] at hlogX
    have hδinv : δ⁻¹ = 2 * ε⁻¹ := by rw [hδ, inv_div, div_eq_mul_inv]
    have hlog2 : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    rw [hδinv]
    nlinarith
  obtain ⟨U, hU, hmem⟩ := hTmem _ hx0 hinf hpad hthr'
  exact ⟨U, hU, cast_gapPoint b r t p ▸ hmem⟩

end Real
