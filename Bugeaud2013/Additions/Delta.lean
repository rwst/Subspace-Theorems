/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Additions.Asymptotics
public import Bugeaud2013.Additions.CFPoints
public import Bugeaud2013.Additions.Complexity
public import Bugeaud2013.Additions.Count
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The exponent `δ` in (6.1)

**(6.1)** If `1 ≤ aₙ`, the number `α = [0; a₁, a₂, …]` is algebraic of degree at least `3` and
the quantitative Subspace Theorem `Real.SubspaceBound α b` holds, then for `(b + 1) δ < 1` and
every `C` the complexity of `a₁ a₂ …` exceeds `C n (log n)^δ` for infinitely many `n`
(`Nat.frequently_lt_encard_factors`). With Evertse–Ferretti 2013 (`Real.subspaceBound_three`)
this is `δ < 1/4` (`Nat.frequently_lt_encard_factors_of_lt_quarter`); the weaker count of
Evertse–Schlickewei 2002, `δ^{-(n+4)}` in `n = 4` variables, gives `δ < 1/9`
(`Nat.frequently_lt_encard_factors_of_lt_ninth`).

**Proof.** Otherwise `p(ℓ) ≤ C ℓ (log ℓ)^δ` for all large `ℓ`. The alphabet is finite, so
`aₙ ≤ A`. At the lengths `ℓ_k = Nat.lenSeq E k`, `Nat.exists_config` gives repetitions, and
`Nat.cfPoint_of_config` the points `v_k = Nat.spadeVec a j r` of height `H_k = q_w q_{w+r}`,
for every `ε ≤ ε_N` with `ε_N⁻¹ ≍ (log ℓ_{2N})^δ ≍ (N log N)^δ`. The heights double
(`Real.Doubling`), so by `Real.card_le_of_cfPoints` the `N` points `N ≤ k < 2N` number at
most `K ε_N^{-(b+1)} (1 + log ε_N⁻¹)³ = O(N^γ)` with `γ < 1`, which fails for large `N`
(`Real.eventually_lt_half`).
-/

@[expose] public section

open Filter Real

namespace Nat

variable {a : ℕ → ℕ} {A : ℕ}

theorem le_two_mul_log_contDen (ha : ∀ n, 1 ≤ a (n + 1)) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) - 1) * Real.log 2 ≤ 2 * Real.log (contDen a n) := by
  have h := contDen_sq_mul_two_pow_le ha 0 (n - 1)
  rw [contDen_zero, show 0 + (n - 1) + 1 = n by omega, one_pow, one_mul] at h
  have h' : ((2 : ℝ) ^ (n - 1)) ≤ (contDen a n : ℝ) ^ 2 := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow, Nat.cast_sub hn] at this
  push_cast at this
  linarith

theorem log_contDen_le (ha : ∀ n, 1 ≤ a (n + 1)) (hA : ∀ n, a (n + 1) ≤ A) (n : ℕ) :
    Real.log (contDen a n) ≤ n * Real.log (A + 1) := by
  have := Real.log_le_log (contDen_pos_real ha n) (contDen_le_pow ha hA n)
  rwa [Real.log_pow] at this

/-- The height `H = q_w q_{w+r}` of a repetition of length `u ≥ ℓ/4`, `u ≤ r`, is between
`2^{ℓ/8}` and `(A + 1)^{2(w+r)}`. -/
theorem log_height_bounds (ha : ∀ n, 1 ≤ a (n + 1)) (hA : ∀ n, a (n + 1) ≤ A) {j r u ℓ : ℕ}
    (hur : u ≤ r) (hℓu : ℓ ≤ 4 * u) :
    (ℓ : ℝ) * Real.log 2 / 8 ≤ Real.log ((contDen a (j + 1) : ℝ) * contDen a (j + 1 + r)) ∧
      Real.log ((contDen a (j + 1) : ℝ) * contDen a (j + 1 + r)) ≤
        2 * ((j + 1 + r : ℕ) : ℝ) * Real.log (A + 1) := by
  rw [Real.log_mul (contDen_pos_real ha _).ne' (contDen_pos_real ha _).ne']
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlA : 0 ≤ Real.log (A + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)])
  constructor
  · have h1 : 0 ≤ Real.log (contDen a (j + 1)) :=
      Real.log_nonneg (by exact_mod_cast one_le_contDen ha _)
    have h2 := le_two_mul_log_contDen ha (n := j + 1 + r) (by omega)
    have h3 : (ℓ : ℝ) ≤ 4 * (((j + 1 + r : ℕ) : ℝ) - 1) := by
      have : ℓ ≤ 4 * (j + r) := by omega
      have : (ℓ : ℝ) ≤ 4 * ((j : ℝ) + r) := by exact_mod_cast this
      push_cast; linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hl2
    linarith
  · have h1 := log_contDen_le ha hA (j + 1)
    have h2 := log_contDen_le ha hA (j + 1 + r)
    have h3 : ((j + 1 : ℕ) : ℝ) * Real.log (A + 1) ≤ ((j + 1 + r : ℕ) : ℝ) * Real.log (A + 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show j + 1 ≤ j + 1 + r by omega)) hlA
    linarith

/-- **The points of a repetition.** A repetition of length `u ≥ ℓ/4` with `w + r ≤ M ℓ` gives a
`Real.CFPoint` for every `ε ≥ 0` with `8 M ε log (A + 1) ≤ log 2`. -/
theorem cfPoint_of_config (ha : ∀ n, 1 ≤ a (n + 1)) (hA : ∀ n, a (n + 1) ≤ A) {j r u ℓ : ℕ}
    (hu : 1 ≤ u) (hur : u ≤ r) (hr : 2 ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m)
    (hne : 1 ≤ j → a (j + 1) ≠ a (j + 1 + r)) (hℓu : ℓ ≤ 4 * u) {M ε : ℝ}
    (hm : ((j + 1 + r : ℕ) : ℝ) ≤ M * ℓ) (hε : 0 ≤ ε)
    (hεM : ε * (8 * M * Real.log (A + 1)) ≤ Real.log 2) :
    CFPoint (contFrac a) A ε (spadeVec a j r) ((contDen a (j + 1) : ℝ) * contDen a (j + 1 + r))
      (contDen a (j + 1)) := by
  refine cfPoint_spadeVec ha hA hu hur hr hrep hne ?_
  have hH : 0 < (contDen a (j + 1) : ℝ) * contDen a (j + 1 + r) :=
    mul_pos (contDen_pos_real ha _) (contDen_pos_real ha _)
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hH ε) (by positivity), Real.log_rpow hH,
    Real.log_pow]
  have hup := (log_height_bounds (j := j) ha hA hur hℓu).2
  have hlA : 0 ≤ Real.log (A + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)])
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h1 := mul_le_mul_of_nonneg_left hup hε
  have h2 : ε * (2 * ((j + 1 + r : ℕ) : ℝ) * Real.log (A + 1)) ≤
      ε * (2 * (M * ℓ) * Real.log (A + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hlA) hε
  have h3 : ε * (2 * (M * ℓ) * Real.log (A + 1)) =
      (ℓ : ℝ) / 4 * (ε * (8 * M * Real.log (A + 1))) := by ring
  have h4 : (ℓ : ℝ) / 4 * (ε * (8 * M * Real.log (A + 1))) ≤ (ℓ : ℝ) / 4 * Real.log 2 :=
    mul_le_mul_of_nonneg_left hεM (by positivity)
  have h5 : (ℓ : ℝ) / 4 * Real.log 2 ≤ u * Real.log 2 := by
    have : (ℓ : ℝ) ≤ 4 * u := by exact_mod_cast hℓu
    exact mul_le_mul_of_nonneg_right (by linarith) hl2
  linarith

/-- The length bound `w + r ≤ 2 p + ℓ + 1` with `p ≤ C ℓ (log ℓ)^δ`. -/
theorem cast_le_of_le_floor {m ℓ : ℕ} {C δ : ℝ} (hC : 0 ≤ C) (hℓ : 1 ≤ ℓ)
    (hm : m ≤ 2 * ⌊C * ℓ * Real.log ℓ ^ δ⌋₊ + ℓ + 1) :
    (m : ℝ) ≤ (2 * C * Real.log ℓ ^ δ + 2) * ℓ := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hm' : (m : ℝ) ≤ 2 * (⌊C * ℓ * Real.log ℓ ^ δ⌋₊ : ℝ) + ℓ + 1 := by exact_mod_cast hm
  have h0 : 0 ≤ C * ℓ * Real.log ℓ ^ δ :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hℓ') _)
  have := Nat.floor_le h0
  have e : (2 * C * Real.log ℓ ^ δ + 2) * ℓ = 2 * (C * ℓ * Real.log ℓ ^ δ) + 2 * ℓ := by ring
  linarith

theorem one_le_log_of_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- **(6.1) with the exponent of a quantitative Subspace Theorem.** If `1 ≤ aₙ`, `α` has degree
at least `3`, `Real.SubspaceBound α b` holds and `(b + 1) δ < 1`, then for every `C` the number
of factors of length `n` of `a₁ a₂ …` exceeds `C n (log n)^δ` for infinitely many `n`. -/
theorem frequently_lt_encard_factors (ha : ∀ n, 1 ≤ a (n + 1))
    (hdeg : 3 ≤ (minpoly ℚ (contFrac a)).natDegree) {b δ : ℝ}
    (hSB : SubspaceBound (contFrac a) b) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hbδ : (b + 1) * δ < 1)
    (C : ℝ) :
    ∃ᶠ n in atTop, ∀ k : ℕ, (Function.factors (fun i ↦ a (i + 1)) n).encard = k →
      C * n * Real.log n ^ δ < k := by
  by_contra hne
  rw [not_frequently] at hne
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  -- the complexity bound
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℕ, ∀ ℓ, L₁ ≤ ℓ → (Function.factors (fun i ↦ a (i + 1)) ℓ).encard ≤
      (⌊C' * ℓ * Real.log ℓ ^ δ⌋₊ : ℕ) := by
    obtain ⟨L₁, h⟩ := eventually_atTop.mp (hne.and (eventually_ge_atTop 1))
    refine ⟨L₁, fun ℓ hℓ ↦ ?_⟩
    obtain ⟨hn, hℓ1⟩ := h ℓ hℓ
    push Not at hn
    obtain ⟨k, hk, hkC⟩ := hn
    rw [hk]
    have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    have hlog : 0 ≤ Real.log ℓ ^ δ := Real.rpow_nonneg (Real.log_nonneg hℓ1') _
    have : (k : ℝ) ≤ C' * ℓ * Real.log ℓ ^ δ := hkC.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hlog)
    exact_mod_cast Nat.le_floor this
  -- the alphabet is finite
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ n, a (n + 1) ≤ A := by
    have hfin_n : (Function.factors (fun i ↦ a (i + 1)) (L₁ + 1)).Finite :=
      Set.finite_of_encard_le_coe (hL₁ _ (by omega))
    have hfin : (Set.range fun i ↦ a (i + 1)).Finite := by
      refine (hfin_n.image fun l ↦ l.headD 0).subset ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Function.factor _ i (L₁ + 1), ⟨i, rfl⟩, by rw [Function.factor_succ]; rfl⟩
    obtain ⟨A, hA⟩ := hfin.bddAbove
    exact ⟨A, fun n ↦ hA ⟨n, rfl⟩⟩
  have hA1 : 1 ≤ A := (ha 0).trans (hA 0)
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  -- the constants of the count
  have halg : IsAlgebraic ℚ (contFrac a) := by
    by_contra h
    have h0 := minpoly.eq_zero (fun hi : IsIntegral ℚ (contFrac a) ↦ h hi.isAlgebraic)
    rw [h0] at hdeg
    simp at hdeg
  obtain ⟨c, hc, D, hLq⟩ := exists_pos_le_abs_quadVal halg hdeg
  have hα : |contFrac a| ≤ 1 :=
    abs_le.mpr ⟨by linarith [contFrac_pos ha], (contFrac_lt_one ha).le⟩
  obtain ⟨K, hK, hcount⟩ := card_le_of_cfPoints hSB hA1' hc hLq hα
  -- the repetitions
  set L₀ := max L₁ 16 with hL₀
  have hconf : ∀ ℓ : ℕ, ∃ j r u : ℕ, L₀ ≤ ℓ → 1 ≤ u ∧ u ≤ r ∧ 2 ≤ r ∧ ℓ ≤ 4 * u ∧
      j + 1 + r ≤ 2 * ⌊C' * ℓ * Real.log ℓ ^ δ⌋₊ + ℓ + 1 ∧
      (∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) ∧
      (1 ≤ j → a (j + 1) ≠ a (j + 1 + r)) := by
    intro ℓ
    by_cases h : L₀ ≤ ℓ
    · obtain ⟨j, r, u, h'⟩ := exists_config (a := a) (by omega) (hL₁ ℓ (by omega))
      exact ⟨j, r, u, fun _ ↦ h'⟩
    · exact ⟨0, 0, 0, fun h' ↦ absurd h' h⟩
  choose J R U hJRU using hconf
  -- the lengths
  set B : ℝ := 64 * A * (2 * C' + 2) with hB
  have hB0 : 0 ≤ B := by positivity
  set n₀ := max L₀ (⌈4 * B⌉₊ + 1) with hn₀
  have hn₀1 : 1 ≤ n₀ := by omega
  have hBn : 4 * B ≤ n₀ :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 * B⌉₊ ≤ n₀ by omega))
  set E := n₀ ^ 2 with hE
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ hn₀1
  have hEn : n₀ ≤ E := Nat.le_self_pow two_ne_zero n₀
  have hℓL : ∀ k, L₀ ≤ lenSeq E k := fun k ↦
    ((le_max_left _ _).trans hEn).trans (le_lenSeq k)
  have hℓ16 : ∀ k, (16 : ℝ) ≤ lenSeq E k := fun k ↦ by
    exact_mod_cast (show 16 ≤ lenSeq E k from le_trans (by omega) (hℓL k))
  have hlogℓ : ∀ k, 1 ≤ Real.log (lenSeq E k) := fun k ↦ one_le_log_of_le (by linarith [hℓ16 k])
  -- the points
  set j : ℕ → ℕ := fun k ↦ J (lenSeq E k) with hj
  set r : ℕ → ℕ := fun k ↦ R (lenSeq E k) with hr
  set Hs : ℕ → ℝ := fun k ↦ (contDen a (j k + 1) : ℝ) * contDen a (j k + 1 + r k) with hHs
  have hcf := fun k ↦ hJRU (lenSeq E k) (hℓL k)
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlo : ∀ k, (lenSeq E k : ℝ) * Real.log 2 / 8 ≤ Real.log (Hs k) := fun k ↦
    (log_height_bounds ha hA (hcf k).2.1 (hcf k).2.2.2.1).1
  have hhi : ∀ k, Real.log (Hs k) ≤ 2 * ((j k + 1 + r k : ℕ) : ℝ) * Real.log (A + 1) :=
    fun k ↦ (log_height_bounds ha hA (hcf k).2.1 (hcf k).2.2.2.1).2
  have hm : ∀ k, ((j k + 1 + r k : ℕ) : ℝ) ≤
      (2 * C' * Real.log (lenSeq E k) ^ δ + 2) * lenSeq E k := fun k ↦
    cast_le_of_le_floor (by linarith) (by linarith [hℓL k, show 16 ≤ L₀ by omega])
      (hcf k).2.2.2.2.1
  -- the heights double
  have hDoub : Doubling Hs := by
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · have h1 := hlo k
      have h2 := mul_le_mul_of_nonneg_right (hℓ16 k) (Real.log_nonneg one_le_two)
      linarith
    · set ℓ := (lenSeq E k : ℝ)
      set t := Real.log (lenSeq E k)
      set m := ((j k + 1 + r k : ℕ) : ℝ)
      have hm0 : 0 ≤ m := Nat.cast_nonneg _
      have hℓ0 : 0 ≤ ℓ := by linarith [hℓ16 k]
      have hlA : Real.log (A + 1) ≤ A := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < A + 1); linarith
      have hm2 : m ≤ (2 * C' + 2) * ℓ * t := by
        have h1 : t ^ δ ≤ t := Real.rpow_le_self_of_one_le (hlogℓ k) (by nlinarith)
        have h2 : (2 * C' * t ^ δ + 2) * ℓ ≤ (2 * C' + 2) * ℓ * t := by
          have : 2 * C' * t ^ δ + 2 ≤ (2 * C' + 2) * t := by nlinarith [hlogℓ k]
          nlinarith
        exact (hm k).trans h2
      have h1 : m * Real.log (A + 1) ≤ m * A := mul_le_mul_of_nonneg_left hlA hm0
      have h2 : m * A ≤ (2 * C' + 2) * ℓ * t * A := mul_le_mul_of_nonneg_right hm2 (by linarith)
      have h3 := mul_log_lenSeq_le hB0 hn₀1 hBn k
      have h4 : 4 * ((2 * C' + 2) * ℓ * t * A) = B * ℓ * t / 16 := by rw [hB]; ring
      have h5 := hlo (k + 1)
      have h6 : (lenSeq E (k + 1) : ℝ) / 16 ≤ (lenSeq E (k + 1) : ℝ) * Real.log 2 / 8 := by
        have := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (lenSeq E (k + 1)) : (0 : ℝ) ≤ _)
        linarith
      have h7 := hhi k
      linarith
  -- the exponent `ε`
  set LE := Real.log E with hLE
  have hLE1 : 1 ≤ LE := one_le_log_of_le (by
    have : 16 ≤ E := le_trans (by omega) hEn
    exact_mod_cast le_trans (by norm_num) this)
  have hlA0 : Real.log 2 ≤ Real.log (A + 1) := Real.log_le_log two_pos (by linarith)
  have hl20 : 0 < Real.log 2 := by linarith
  set c₀ := 8 * Real.log (A + 1) / Real.log 2 with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    rw [hc₀, le_div_iff₀ hl20]; linarith
  have hδ1 : δ ≤ 1 := by nlinarith
  have hT : Tendsto (fun N : ℕ ↦ 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  obtain ⟨N, hN1, hthr, hfin⟩ := ((eventually_ge_atTop 1).and
    ((eventually_le_two_pow (c₀ := c₀) (C := C') (L := LE) hK (by linarith) (by linarith) hδ
      hδ1 hLE1).and (hT.eventually (eventually_lt_half (c₀ := c₀) (C := C') (L := LE) hK hc₀1
        (by linarith) hb hδ hbδ hLE1)))).exists
  set e := epsInv c₀ C' δ LE (2 * N + 1) with he
  have hx1 : (1 : ℝ) ≤ 2 * N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have he1 : 1 ≤ e := by
    have := two_mul_le_epsInv (c₀ := c₀) (C := C') (δ := δ) (by linarith) (by linarith) hLE1 hx1
    linarith
  set M := 2 * C' * Real.log (lenSeq E (2 * N)) ^ δ + 2 with hM
  have hM2 : 2 ≤ M := by
    have : 0 ≤ Real.log (lenSeq E (2 * N)) ^ δ :=
      Real.rpow_nonneg (by linarith [hlogℓ (2 * N)]) _
    nlinarith
  have heM : e = c₀ * M := by
    have hlog2N : Real.log (lenSeq E (2 * N)) =
        (2 * N + 1) * LE + 2 * (2 * N + 1) * Real.log (2 * N + 1) := by
      rw [log_lenSeq hE1]; push_cast; ring
    rw [he, hM, hlog2N]; rfl
  set ε := e⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.mpr (by linarith)
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ he1
  have hεM : ε * (8 * M * Real.log (A + 1)) = Real.log 2 := by
    have hlA : Real.log (A + 1) ≠ 0 := by linarith
    rw [hε, heM, hc₀]
    field_simp
  -- the points `N ≤ k < 2 N`
  have hpts : ∀ k ∈ Finset.Ico N (2 * N), CFPoint (contFrac a) A ε (spadeVec a (j k) (r k))
      (Hs k) (contDen a (j k + 1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hu, hur, hr2, hℓu, -, hrep, hne⟩ := hcf k
    refine cfPoint_of_config ha hA hu hur hr2 hrep hne hℓu (M := M) ?_ hε0.le hεM.le
    refine (hm k).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    have hmono : (lenSeq E k : ℝ) ≤ lenSeq E (2 * N) := by
      exact_mod_cast lenSeq_mono hE1 (by omega : k ≤ 2 * N)
    have hlog := Real.log_le_log (by linarith [hℓ16 k]) hmono
    have := Real.rpow_le_rpow (by linarith [hlogℓ k]) hlog hδ
    rw [hM]
    nlinarith
  have hthr' : ∀ k ∈ Finset.Ico N (2 * N), K * ε⁻¹ ^ K ≤ Real.log (Hs k) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [hε, inv_inv]
    have h1 := hDoub.pow_mul_le (Nat.zero_le k)
    rw [Nat.sub_zero] at h1
    have h2 : (2 : ℝ) ^ N ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk.1
    have h3 := hDoub.one_le_log 0
    have h4 : (2 : ℝ) ^ k ≤ 2 ^ k * Real.log (Hs 0) := le_mul_of_one_le_right (by positivity) h3
    linarith
  have hcnt := hcount ε hε0 hε1 Hs (fun k ↦ (contDen a (j k + 1) : ℝ))
    (fun k ↦ spadeVec a (j k) (r k)) (Finset.Ico N (2 * N)) hDoub hpts hthr'
  rw [Nat.card_Ico, show 2 * N - N = N by omega, hε, inv_inv] at hcnt
  have : (2 * (N : ℝ) + 1 - 1) / 2 = N := by ring
  linarith

theorem isAlgebraic_of_three_le_natDegree {α : ℝ} (hdeg : 3 ≤ (minpoly ℚ α).natDegree) :
    IsAlgebraic ℚ α := by
  by_contra h
  have h0 := minpoly.eq_zero (fun hi : IsIntegral ℚ α ↦ h hi.isAlgebraic)
  rw [h0] at hdeg
  simp at hdeg

/-- **(6.1) with `δ < 1/4`** (Evertse–Ferretti 2013). -/
theorem frequently_lt_encard_factors_of_lt_quarter (ha : ∀ n, 1 ≤ a (n + 1))
    (hdeg : 3 ≤ (minpoly ℚ (contFrac a)).natDegree) {δ : ℝ} (hδ : 0 ≤ δ) (hδ4 : δ < 1 / 4)
    (C : ℝ) :
    ∃ᶠ n in atTop, ∀ k : ℕ, (Function.factors (fun i ↦ a (i + 1)) n).encard = k →
      C * n * Real.log n ^ δ < k :=
  frequently_lt_encard_factors ha hdeg
    (subspaceBound_three (isAlgebraic_of_three_le_natDegree hdeg)) (by norm_num) hδ
    (by linarith) C

/-- **(6.1) with `δ < 1/9`**, the exponent of Evertse–Schlickewei 2002. -/
theorem frequently_lt_encard_factors_of_lt_ninth (ha : ∀ n, 1 ≤ a (n + 1))
    (hdeg : 3 ≤ (minpoly ℚ (contFrac a)).natDegree) {δ : ℝ} (hδ : 0 ≤ δ) (hδ9 : δ < 1 / 9)
    (C : ℝ) :
    ∃ᶠ n in atTop, ∀ k : ℕ, (Function.factors (fun i ↦ a (i + 1)) n).encard = k →
      C * n * Real.log n ^ δ < k :=
  frequently_lt_encard_factors ha hdeg
    ((subspaceBound_three (isAlgebraic_of_three_le_natDegree hdeg)).mono
      (show (3 : ℝ) ≤ 8 by norm_num))
    (by norm_num) hδ (by linarith) C

end Nat
