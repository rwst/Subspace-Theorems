/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.RealFormCount

/-!
# The three-variable step (Bugeaud–Evertse 2008, §7, (7.3)–(7.11))

The approximations `|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}` of Lemma 6.1 give the points
`x = (b^t, b^r, p) ∈ ℤ³`, which BE08 split into `k = ⌊2/ε⌋ + 1` classes by `⌊k r / t⌋ = ℓ`. On one
class the points solve a system of the quantitative Subspace Theorem in three variables over
`S = {∞} ∪ {l ∣ b}`:

* at `∞` the forms `X₁, X₂, ξ X₁ - ξ X₂ - X₃` with exponents `1, (ℓ + 1)/k, -ε`;
* at `l ∣ b` the coordinates `X₁, X₂, X₃` with exponents `g_l, g_l ℓ/k, 0`, where
  `g_l = -v_l(b) log l / log b`, so that `|b^t|_l = (b^t)^{g_l}` and `∑_l g_l = -1`.

The exponents sum to `1/k - ε = -δ` with `δ = ε - 1/k ≥ ε/2`. BE.0
(`Real.subspaceBoundAt_three`, Evertse–Ferretti 2013) puts the points of one class above the
threshold `K δ⁻¹` into `K δ⁻³ (1 + log δ⁻¹)²` planes; summing over the `k ≤ 3/ε` classes gives
`K' ε⁻⁴ (1 + log ε⁻¹)²` planes (`Real.exists_planes_of_approx`). This replaces the paper's
`(ε⁻¹)^{8+η}` from Evertse–Schlickewei 2002.

## Main results

* `Real.padicNorm_pow_eq_rpow`: `|b^r|_l = (b^r)^{g_l}`.
* `Real.sum_factorization_log_div`: `∑_{l ∣ b} g_l = -1`.
* `Real.exists_planes_of_approx`: **the three-variable step**.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Finset

namespace Real

variable {b : ℕ}

/-- **The `l`-adic norm of `b^r`** is `(b^r)^{g_l}` with `g_l = -v_l(b) log l / log b`. -/
theorem padicNorm_pow_eq_rpow (hb : 2 ≤ b) (l : Nat.Primes) (r : ℕ) :
    ((padicNorm (l : ℕ) ((b : ℚ) ^ r) : ℚ) : ℝ) =
      ((b : ℝ) ^ r) ^ (-(b.factorization l : ℝ) * log l / log b) := by
  have := Fact.mk l.2
  have hb0 : (b : ℚ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))
  rw [padicNorm.eq_zpow_of_nonzero hb0]
  have hv : padicValRat l ((b : ℚ) ^ r) = r * b.factorization l := by
    rw [show ((b : ℚ) ^ r) = ((b ^ r : ℕ) : ℚ) by push_cast; rfl, padicValRat.of_nat,
      padicValNat.pow, Nat.factorization_def b l.2]
    push_cast; ring
  rw [hv]
  have hl : (0 : ℝ) < l := by exact_mod_cast l.2.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlogb : log b ≠ 0 := (log_pos (by exact_mod_cast (by omega : 1 < b))).ne'
  push_cast
  rw [← rpow_intCast, ← rpow_natCast, ← rpow_mul hbR.le, rpow_def_of_pos hl, rpow_def_of_pos hbR]
  congr 1
  push_cast
  field_simp

/-- **`∑_{l ∣ b} g_l = -1`**: `log b = ∑_{l ∣ b} v_l(b) log l`. -/
theorem sum_factorization_log_div (hb : 2 ≤ b) :
    ∑ l ∈ (b.primeFactors.subtype Nat.Prime : Finset Nat.Primes),
      (-(b.factorization l : ℝ) * log l / log b) = -1 := by
  rw [sum_subtype_eq_sum_filter (f := fun l : ℕ ↦ -(b.factorization l : ℝ) * log l / log b),
    filter_true_of_mem fun _ hx ↦ Nat.prime_of_mem_primeFactors hx]
  have hlogb : log b ≠ 0 := (log_pos (by exact_mod_cast (by omega : 1 < b))).ne'
  have h := log_nat_eq_sum_factorization b
  rw [Finsupp.sum, Nat.support_factorization] at h
  simp only [neg_mul, neg_div, sum_neg_distrib, ← sum_div, ← h, div_self hlogb]

/-- **The three-variable step** (Bugeaud–Evertse 2008, (7.3)–(7.11), with Evertse–Ferretti's
count). For `ξ` real algebraic and `b ≥ 2` there is `K > 0` such that for `0 < ε ≤ 1` the points
`(b^t, b^r, p)` with `r < t`, `|p| ≤ b^t`, `|b^t ξ - b^r ξ - p| ≤ (b^t)^{-ε}` and
`K ε⁻¹ ≤ t log b` lie in at most `K ε⁻⁴ (1 + log ε⁻¹)²` proper subspaces of `ℚ³`. -/
theorem exists_planes_of_approx (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)),
      (#T : ℝ) ≤ K * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ (r t : ℕ) (p : ℤ), r < t → |(p : ℝ)| ≤ (b : ℝ) ^ t →
        |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε) → K * ε⁻¹ ≤ t * log b →
        ∃ U ∈ T, ![(b : ℚ) ^ t, (b : ℚ) ^ r, (p : ℚ)] ∈ U := by
  classical
  set S : Finset Nat.Primes := b.primeFactors.subtype Nat.Prime with hS
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceBoundAt_three hξ S 3 (by norm_num) (by norm_num)
  refine ⟨96 * K₀, by positivity, fun ε hε hε1 ↦ ?_⟩
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < log b := log_pos hbR
  -- the classes and the weight `δ = ε - 1/k`
  set k : ℕ := ⌊2 / ε⌋₊ + 1 with hk
  have hk2 : 2 / ε < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hk3 : (k : ℝ) ≤ 3 * ε⁻¹ := by
    have : (⌊2 / ε⌋₊ : ℝ) ≤ 2 / ε := Nat.floor_le (by positivity)
    have : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
    rw [hk]; push_cast; rw [div_eq_mul_inv] at *; linarith
  have hkpos : (0 : ℝ) < k := by positivity
  set δ := ε - 1 / k with hδ
  have hkε : 1 / k < ε / 2 := by
    rw [div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hε] at hk2
    linarith
  have hδ0 : ε / 2 ≤ δ := by rw [hδ]; linarith
  have hδpos : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; have : 0 < 1 / (k : ℝ) := by positivity
                         linarith
  have hδinv : δ⁻¹ ≤ 2 * ε⁻¹ := by
    calc δ⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hδ0
      _ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  -- the forms, the exponents
  set g : Nat.Primes → ℝ := fun l ↦ -(b.factorization l : ℝ) * log l / log b with hg
  have hg0 : ∀ l, g l ≤ 0 := fun l ↦ by
    have : 0 ≤ log (l : ℝ) := log_natCast_nonneg _
    simp only [hg, neg_mul, neg_div]
    exact neg_nonpos.mpr (div_nonneg (by positivity) hlogb.le)
  have hgsum : ∑ l ∈ S, g l = -1 := sum_factorization_log_div hb
  set P : Fin 3 → Fin 3 → Fin 3 → ℤ :=
    ![![![1, 0, 0], 0, 0], ![0, ![1, 0, 0], 0], ![![0, 1, 0], ![0, -1, 0], ![-1, 0, 0]]] with hP
  have hPB : ∀ i j m, |(P i j m : ℝ)| ≤ 1 := by
    intro i j m; fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [P]
  have hdet : (1 : ℝ) ≤ |(Matrix.of fun i j ↦ quadVal ξ (P i j)).det| := by
    simp [Matrix.det_fin_three, quadVal, P]
  set e : ℕ → Fin 3 → ℝ := fun ℓ ↦ ![1, ((ℓ : ℝ) + 1) / k, -ε] with he
  set f : ℕ → Nat.Primes → Fin 3 → ℝ := fun ℓ l ↦ ![g l, g l * ℓ / k, 0] with hf
  have hclass := fun ℓ (hℓ : ℓ < k) ↦ hBE P 1 le_rfl hPB 1 one_pos le_rfl hdet 1 le_rfl (e ℓ)
    (f ℓ) δ hδpos hδ1
    (fun i ↦ by
      have : ((ℓ : ℝ) + 1) / k ≤ 1 := by
        rw [div_le_one hkpos]; exact_mod_cast hℓ
      fin_cases i <;> simp [e] <;> linarith)
    ⟨0, by simp [e]⟩ ⟨2, by simp [e]; linarith⟩
    (fun l _ i ↦ by
      have hgl := hg0 l
      have hgl2 : g l * ℓ / k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hgl (by positivity))
          hkpos.le
      fin_cases i <;> simp [f, hgl, hgl2])
    (fun l _ ↦ ⟨2, by simp [f]⟩)
    (by
      have h1 : ∑ l ∈ S, ∑ i, f ℓ l i = (1 + ℓ / k) * ∑ l ∈ S, g l := by
        rw [mul_sum]
        refine sum_congr rfl fun l _ ↦ ?_
        simp [f, Fin.sum_univ_three]
        ring
      rw [h1, hgsum]
      simp only [e, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hδ]
      field_simp
      ring_nf
      linarith)
  choose! T hTcard hTtop hTmem using hclass
  refine ⟨(range k).biUnion T, ?_, ?_, ?_⟩
  · -- the count
    have hlog2 : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
    have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
    have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
    have hlogδ : 1 + log δ⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      have : log δ⁻¹ ≤ log (2 * ε⁻¹) := log_le_log (by positivity) hδinv
      rw [log_mul (by norm_num) (by positivity)] at this
      linarith
    have hlogδ0 : 0 ≤ 1 + log δ⁻¹ := by have := log_nonneg hδinv1; linarith
    have hcard : (#((range k).biUnion T) : ℝ) ≤ k * (K₀ * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2) := by
      calc (#((range k).biUnion T) : ℝ) ≤ ∑ ℓ ∈ range k, (#(T ℓ) : ℝ) := by
            exact_mod_cast card_biUnion_le
        _ ≤ ∑ _ℓ ∈ range k, K₀ * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2 :=
            sum_le_sum fun ℓ hℓ ↦ hTcard ℓ (mem_range.mp hℓ)
        _ = k * (K₀ * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2) := by
            rw [sum_const, card_range, nsmul_eq_mul]
    refine hcard.trans ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
    calc (k : ℝ) * (K₀ * δ⁻¹ ^ 3 * (1 + log δ⁻¹) ^ 2)
        ≤ (3 * ε⁻¹) * (K₀ * (2 * ε⁻¹) ^ 3 * (2 * (1 + log ε⁻¹)) ^ 2) := by gcongr
      _ = 96 * K₀ * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 2 := by ring
  · intro U hU
    obtain ⟨ℓ, hℓ, hUℓ⟩ := mem_biUnion.mp hU
    exact hTtop ℓ (mem_range.mp hℓ) U hUℓ
  · intro r t p hrt hp happ hthr
    -- the class of `(r, t)`
    set ℓ := k * r / t with hℓdef
    have htpos : 0 < t := by omega
    have hℓk : ℓ < k := by
      rw [hℓdef, Nat.div_lt_iff_lt_mul htpos]
      exact Nat.mul_lt_mul_of_pos_left hrt (by omega)
    have hℓ1 : (ℓ : ℝ) * t ≤ k * r := by exact_mod_cast Nat.div_mul_le_self (k * r) t
    have hℓ2 : (k : ℝ) * r < (ℓ + 1) * t := by
      have := Nat.lt_mul_div_succ (k * r) htpos
      have : (k * r : ℝ) < t * (ℓ + 1) := by exact_mod_cast this
      linarith
    have htR : (0 : ℝ) < t := by exact_mod_cast htpos
    set x : Fin 3 → ℤ := ![(b : ℤ) ^ t, (b : ℤ) ^ r, p] with hx
    have hbt : (1 : ℝ) ≤ (b : ℝ) ^ t := one_le_pow₀ hbR.le
    have hX : (⨆ i, |(x i : ℝ)|) = (b : ℝ) ^ t := by
      have hbr : (b : ℝ) ^ r ≤ (b : ℝ) ^ t := pow_le_pow_right₀ hbR.le hrt.le
      refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
      · fin_cases i <;> simp [x, abs_of_pos hb0, hbr, hp]
      · refine le_ciSup_of_le (Set.finite_range _).bddAbove 0 ?_
        simp [x, abs_of_pos hb0]
    have hpow : ∀ y : ℝ, ((b : ℝ) ^ t) ^ y = (b : ℝ) ^ (t * y) := fun y ↦ by
      rw [← rpow_natCast, ← rpow_mul hb0.le]
    have hpowr : (b : ℝ) ^ r = (b : ℝ) ^ (r : ℝ) := (rpow_natCast _ _).symm
    have hx0 : x ≠ 0 := fun h ↦ by
      have := congrFun h 0
      simp [x] at this
      omega
    have hinf : ∀ i, |∑ j, quadVal ξ (P i j) * x j| ≤ 1 * (⨆ k, |(x k : ℝ)|) ^ e ℓ i := by
      rw [hX]
      intro i
      fin_cases i
      · simp [x, P, e, quadVal, Fin.sum_univ_three, abs_of_pos hb0]
      · simp only [x, P, e, quadVal, Fin.sum_univ_three]
        simp only [Int.reduceNeg, Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, Pi.zero_apply, Matrix.cons_val_one, Int.cast_zero, zero_mul,
          add_zero, Matrix.cons_val, Int.cast_pow, Int.cast_natCast, Int.cast_one, one_mul,
          zero_add, abs_pow, Nat.abs_cast]
        rw [hpow, hpowr]
        refine rpow_le_rpow_of_exponent_le hbR.le ?_
        rw [mul_div_assoc', le_div_iff₀ hkpos]
        linarith
      · simp only [x, P, e, quadVal, Fin.sum_univ_three]
        simp only [one_mul]
        convert happ using 2 <;> first | rfl | (simp; ring)
    have hpad : ∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤
        (⨆ k, |(x k : ℝ)|) ^ f ℓ l i := by
      rw [hX]
      have hcast : ∀ n : ℕ, (((b : ℤ) ^ n : ℤ) : ℚ) = (b : ℚ) ^ n := fun n ↦ by push_cast; rfl
      intro l _ i
      fin_cases i
      · change ((padicNorm (l : ℕ) (((b : ℤ) ^ t : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((b : ℝ) ^ t) ^ g l
        rw [hcast t, padicNorm_pow_eq_rpow hb l t]
      · change ((padicNorm (l : ℕ) (((b : ℤ) ^ r : ℤ) : ℚ) : ℚ) : ℝ) ≤
          ((b : ℝ) ^ t) ^ (g l * ℓ / k)
        rw [hcast r, padicNorm_pow_eq_rpow hb l r, hpowr, ← rpow_mul hb0.le, hpow]
        refine rpow_le_rpow_of_exponent_le hbR.le ?_
        have hgl := hg0 l
        change (r : ℝ) * g l ≤ t * (g l * ℓ / k)
        rw [show (t : ℝ) * (g l * ℓ / k) = g l * (ℓ * t / k) by ring]
        have : (ℓ : ℝ) * t / k ≤ r := by rw [div_le_iff₀ hkpos]; linarith
        nlinarith
      · change ((padicNorm (l : ℕ) ((p : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((b : ℝ) ^ t) ^ (0 : ℝ)
        rw [rpow_zero]
        exact_mod_cast padicNorm.of_int p
    have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log (1 : ℝ)⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) := by
      rw [hX, log_pow]
      simp only [log_one, inv_one, add_zero, mul_one]
      calc K₀ * δ⁻¹ ≤ K₀ * (2 * ε⁻¹) := by gcongr
        _ ≤ 96 * K₀ * ε⁻¹ := by
            have : 0 ≤ K₀ * ε⁻¹ := by positivity
            linarith
        _ ≤ t * log b := hthr
    obtain ⟨U, hU, hmem⟩ := hTmem ℓ hℓk x hx0 hinf hpad hthr'
    refine ⟨U, mem_biUnion.mpr ⟨ℓ, mem_range.mpr hℓk, hU⟩, ?_⟩
    convert hmem using 1
    ext i
    fin_cases i <;> simp [x]

end Real
