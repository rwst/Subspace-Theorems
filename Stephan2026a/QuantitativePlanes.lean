/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.RealFormCount
public import Stephan2026a.SteeringWord

-- Used only inside proofs.
import Stephan2026a.SubspaceStep

/-!
# The kernel points lie in few planes

**Problem 5.2, step 2.** A pair `2 ≤ a < c` with gap `s = c - a` gives the integer point

```text
x = (3^c, 2^s 3^a, 2^c (m_c - m_a)),       N = x₀ - x₁ - x₂ = 2^c (ε_c - ε_a),
```

(`SteeringWord.kernelPoint`, `SteeringWord.kernelNum`), of size `3^c`. When
`|ε_c - ε_a| ≤ (3^c)^{-ε}` it solves a system of the quantitative Subspace Theorem at `∞`, `2`
and `3`: with `λ = log 2 / log 3`, so that `(3^c)^λ = 2^c`, and the class `ℓ = ⌊k s / c⌋` of the
gap among `k = ⌊2/ε⌋ + 1` classes,

* at `∞` the forms `X₀ - X₁ - X₂`, `X₁`, `X₂` with exponents `λ - ε`, `1 - (1 - λ) ℓ / k`, `1`;
* at `2` the coordinates with exponents `0`, `-λ ℓ / k`, `-λ`;
* at `3` the coordinates with exponents `-1`, `-(1 - (ℓ + 1) / k)`, `0`.

The exponents sum to `1/k - ε = -δ`, `δ ≥ ε/2`, exactly in `λ`; the only numerical fact used
is `λ ≤ 2/3` (`2^3 ≤ 3^2`). Evertse–Ferretti's count (`Real.subspaceBoundAt_three`) puts the
points of one class above the threshold `K δ⁻¹` into `K δ⁻³ (1 + log δ⁻¹)²` planes, and the
`k ≤ 3/ε` classes into `K' ε⁻⁴ (1 + log ε⁻¹)²` planes (`SteeringWord.exists_planes_of_violators`).
This is the three-variable step of Bugeaud–Evertse 2008, §7, with `(3^c, 2^s 3^a, 2^c M)` in place
of `(b^t, b^r, p)`; the third coordinate is not `S`-integral, and its `2`-adic smallness pays for
`2^c` as in Theorem 4.5.

## Main definitions

* `SteeringWord.kernelPoint a c`: the point `(3^c, 2^s 3^a, 2^c (m_c - m_a))`.
* `SteeringWord.kernelNum a c`: `N = 3^c - 2^s 3^a - 2^c (m_c - m_a)`.

## Main results

* `SteeringWord.kernelNum_eq`: `N = 2^c (ε_c - ε_a)`; `abs_kernelNum_lt`: `|N| < 2^c`;
  `odd_kernelNum`: `N` is odd.
* `SteeringWord.exists_planes_of_violators`: **the three-variable step**.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §4.3 and
Problem 5.2; Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
Arith. **133** (2008), 221–250, §7; J.-H. Evertse, R. G. Ferretti, *A further improvement of the
quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590.
-/

@[expose] public section

open Finset Real

namespace SteeringWord

/-- **The kernel point** `(3^c, 2^s 3^a, 2^c (m_c - m_a))`, `s = c - a`, of a pair `a < c`. -/
def kernelPoint (a c : ℕ) : Fin 3 → ℤ := ![3 ^ c, 2 ^ (c - a) * 3 ^ a, 2 ^ c * (m c - m a)]

/-- **The kernel numerator** `N = 3^c - 2^s 3^a - 2^c (m_c - m_a) = 2^c (ε_c - ε_a)`. -/
def kernelNum (a c : ℕ) : ℤ := 3 ^ c - 2 ^ (c - a) * 3 ^ a - 2 ^ c * (m c - m a)

variable {a c : ℕ}

theorem two_pow_sub_mul_three_pow_eq (hac : a ≤ c) :
    (2 : ℚ) ^ (c - a) * 3 ^ a = 2 ^ c * (3 / 2) ^ a := by
  have h : (2 : ℚ) ^ c = 2 ^ (c - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hac]
  rw [h, div_pow]
  field_simp

/-- `N = 2^c (ε_c - ε_a)`. -/
theorem kernelNum_eq (hac : a ≤ c) : (kernelNum a c : ℚ) = 2 ^ c * (eps c - eps a) := by
  have h := two_pow_sub_mul_three_pow_eq hac
  have h3 : (2 : ℚ) ^ c * (3 / 2) ^ c = 3 ^ c := by rw [← mul_pow]; norm_num
  simp only [kernelNum, eps]
  push_cast
  rw [h]
  linear_combination -h3

/-- `N = 2^c (ε_c - ε_a)`, over `ℝ`. -/
theorem kernelNum_eq_real (hac : a ≤ c) :
    (kernelNum a c : ℝ) = 2 ^ c * ((eps c : ℝ) - eps a) := by
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (kernelNum_eq hac)
  simpa using h

/-- `|N| < 2^c`. -/
theorem abs_kernelNum_lt (hac : a ≤ c) : |kernelNum a c| < 2 ^ c := by
  have h : |(kernelNum a c : ℚ)| < 2 ^ c := by
    rw [kernelNum_eq hac, abs_mul, abs_of_pos (by positivity)]
    calc (2 : ℚ) ^ c * |eps c - eps a| < 2 ^ c * 1 :=
          mul_lt_mul_of_pos_left (abs_eps_sub_lt_one c a) (by positivity)
      _ = 2 ^ c := mul_one _
  exact_mod_cast h

/-- `N` is odd: `3^c` is odd, `2^s 3^a` and `2^c (m_c - m_a)` are even. -/
theorem odd_kernelNum (hac : a < c) : Odd (kernelNum a c) := by
  obtain ⟨s, hs⟩ : ∃ s, c - a = s + 1 := ⟨c - a - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have h2c : (2 : ℤ) ^ c = 2 * 2 ^ d := by rw [hd, pow_succ, mul_comm]
  have h2s : (2 : ℤ) ^ (c - a) = 2 * 2 ^ s := by rw [hs, pow_succ, mul_comm]
  have h : kernelNum a c = 3 ^ c - 2 * (2 ^ s * 3 ^ a + 2 ^ d * (m c - m a)) := by
    rw [kernelNum, h2c, h2s]
    ring
  rw [h]
  exact (Odd.pow ⟨1, by norm_num⟩).sub_even (even_two_mul _)

/-- `2^c ≤ 2^s 3^a ≤ 3^c`. -/
theorem two_pow_le_two_pow_sub_mul_three_pow (hac : a ≤ c) :
    (2 : ℤ) ^ c ≤ 2 ^ (c - a) * 3 ^ a ∧ (2 : ℤ) ^ (c - a) * 3 ^ a ≤ 3 ^ c := by
  constructor
  · calc (2 : ℤ) ^ c = 2 ^ (c - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hac]
      _ ≤ 2 ^ (c - a) * 3 ^ a :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
            (by positivity)
  · calc (2 : ℤ) ^ (c - a) * 3 ^ a ≤ 3 ^ (c - a) * 3 ^ a :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
            (by positivity)
      _ = 3 ^ c := by rw [← pow_add, Nat.sub_add_cancel hac]

/-- `0 < 2^c (m_c - m_a) < 3^c` for `2 ≤ a < c`. -/
theorem kernelPoint_two_bounds (ha : 2 ≤ a) (hac : a < c) :
    0 < (2 : ℤ) ^ c * (m c - m a) ∧ (2 : ℤ) ^ c * (m c - m a) < 3 ^ c := by
  have hM := m_strictMono ha hac
  have hN := abs_kernelNum_lt hac.le
  have hY := two_pow_le_two_pow_sub_mul_three_pow hac.le
  rw [abs_lt, kernelNum] at hN
  exact ⟨mul_pos (by positivity) (by omega), by linarith⟩

/-- `λ = log_3 2 > 0`. -/
theorem logb_three_two_pos : 0 < logb 3 2 :=
  logb_pos (by norm_num : (1 : ℝ) < 3) (by norm_num : (1 : ℝ) < 2)

/-- `3 log 2 ≤ 2 log 3`, from `2^3 ≤ 3^2`. -/
theorem three_mul_log_two_le : 3 * log 2 ≤ 2 * log 3 := by
  have := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 3) (by norm_num : (2 : ℝ) ^ 3 ≤ 3 ^ 2)
  rw [log_pow, log_pow] at this
  exact_mod_cast this

/-- `λ = log_3 2 ≤ 2/3`. -/
theorem logb_three_two_le : logb 3 2 ≤ 2 / 3 := by
  rw [logb, div_le_iff₀ (log_pos (by norm_num))]
  linarith [three_mul_log_two_le]

/-- `3^{λ x} = 2^x`. -/
theorem three_rpow_logb_mul (x : ℝ) : (3 : ℝ) ^ (logb 3 2 * x) = 2 ^ x := by
  rw [rpow_mul (by norm_num), rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-- `2^n = 3^{λ n}`. -/
theorem two_pow_eq_three_rpow (n : ℕ) : (2 : ℝ) ^ n = (3 : ℝ) ^ (logb 3 2 * n) := by
  rw [three_rpow_logb_mul, rpow_natCast]

/-- The size of an integer point is that of a coordinate that dominates the others. -/
theorem iSup_abs_eq_of_le {n : ℕ} {x : Fin n → ℤ} (i₀ : Fin n) (h : ∀ i, |x i| ≤ |x i₀|) :
    (⨆ i, |(x i : ℝ)|) = |(x i₀ : ℝ)| := by
  have : Nonempty (Fin n) := ⟨i₀⟩
  refine le_antisymm (ciSup_le fun i ↦ ?_)
    (le_ciSup (f := fun i ↦ |(x i : ℝ)|) (Set.finite_range _).bddAbove i₀)
  exact_mod_cast h i

/-- The size of the kernel point is `3^c`. -/
theorem iSup_abs_kernelPoint (ha : 2 ≤ a) (hac : a < c) :
    (⨆ i, |(kernelPoint a c i : ℝ)|) = 3 ^ c := by
  have hY := two_pow_le_two_pow_sub_mul_three_pow hac.le
  have hZ := kernelPoint_two_bounds ha hac
  rw [iSup_abs_eq_of_le 0 fun i ↦ ?_]
  · simp [kernelPoint]
  fin_cases i
  · exact le_rfl
  · change |(2 : ℤ) ^ (c - a) * 3 ^ a| ≤ |(3 : ℤ) ^ c|
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    exact hY.2
  · change |(2 : ℤ) ^ c * (m c - m a)| ≤ |(3 : ℤ) ^ c|
    rw [abs_of_pos hZ.1, abs_of_pos (by positivity)]
    exact hZ.2.le

/-- `|z|_p ≤ 1` for an integer `z`, over `ℝ`. -/
theorem padicNorm_intCast_le_one (p : ℕ) [Fact p.Prime] (z : ℤ) :
    ((padicNorm p (z : ℚ) : ℚ) : ℝ) ≤ 1 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (padicNorm.of_int (p := p) z)
  rwa [Rat.cast_one] at h

/-- `|z|_p ≤ p^{-n}` for an integer `z` divisible by `p^n`, over `ℝ`. -/
theorem padicNorm_intCast_le_of_dvd {p : ℕ} [Fact p.Prime] {n : ℕ} {z : ℤ}
    (hz : (p : ℤ) ^ n ∣ z) : ((padicNorm p (z : ℚ) : ℚ) : ℝ) ≤ (1 / p : ℝ) ^ n := by
  have h := (Rat.cast_le (K := ℝ)).mpr (padicNorm_le_of_dvd hz)
  rwa [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at h

/-- **The three-variable step** (Bugeaud–Evertse 2008, (7.3)–(7.11), for the kernel points, with
Evertse–Ferretti's count). There is `K > 0` such that for `0 < ε ≤ 1` the kernel points of the
pairs `2 ≤ a < c` with `|ε_c - ε_a| ≤ (3^c)^{-ε}` and `K ε⁻¹ ≤ c log 3` lie in at most
`K ε⁻⁴ (1 + log ε⁻¹)²` proper subspaces of `ℚ³`. -/
theorem exists_planes_of_violators :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)),
      (#T : ℝ) ≤ K * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ a c : ℕ, 2 ≤ a → a < c → |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) →
        K * ε⁻¹ ≤ c * log 3 → ∃ U ∈ T, (fun i ↦ (kernelPoint a c i : ℚ)) ∈ U := by
  classical
  set S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} with hS
  have h23 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ ⟨3, Nat.prime_three⟩ := by decide
  obtain ⟨K₀, hK₀, hBE⟩ := subspaceBoundAt_three isAlgebraic_zero S 3 (by norm_num) (by norm_num)
  refine ⟨96 * K₀, by positivity, fun ε hε hε1 ↦ ?_⟩
  set lam := logb 3 2 with hlam
  have hlam0 : 0 < lam := logb_three_two_pos
  have hlam1 : lam ≤ 2 / 3 := logb_three_two_le
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
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  have hδinv : δ⁻¹ ≤ 2 * ε⁻¹ := by
    calc δ⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hδ0
      _ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  -- the forms, the exponents
  set P : Fin 3 → Fin 3 → Fin 3 → ℤ :=
    ![![![1, 0, 0], ![-1, 0, 0], ![-1, 0, 0]], ![0, ![1, 0, 0], 0], ![0, 0, ![1, 0, 0]]] with hP
  have hPB : ∀ i j m, |(P i j m : ℝ)| ≤ 1 := by
    intro i j m; fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [P]
  have hdet : (1 : ℝ) ≤ |(Matrix.of fun i j ↦ quadVal 0 (P i j)).det| := by
    simp [Matrix.det_fin_three, quadVal, P]
  set e : ℕ → Fin 3 → ℝ := fun ℓ ↦ ![lam - ε, 1 - (1 - lam) * ℓ / k, 1] with he
  set f : ℕ → Nat.Primes → Fin 3 → ℝ := fun ℓ l ↦
    if (l : ℕ) = 2 then ![0, -(lam * ℓ / k), -lam] else ![-1, -(1 - (ℓ + 1) / k), 0] with hf
  have hf2 : ∀ ℓ : ℕ, f ℓ ⟨2, Nat.prime_two⟩ = (![0, -(lam * ℓ / k), -lam] : Fin 3 → ℝ) :=
    fun _ ↦ rfl
  have hf3 : ∀ ℓ : ℕ, f ℓ ⟨3, Nat.prime_three⟩ =
      (![-1, -(1 - ((ℓ : ℝ) + 1) / k), 0] : Fin 3 → ℝ) := fun _ ↦ rfl
  have hclass := fun ℓ (hℓ : ℓ < k) ↦ hBE P 1 le_rfl hPB 1 one_pos le_rfl hdet 1 le_rfl (e ℓ)
    (f ℓ) δ hδpos hδ1
    (fun i ↦ by
      have : 0 ≤ (1 - lam) * ℓ / k := div_nonneg (mul_nonneg (by linarith) ℓ.cast_nonneg)
        hkpos.le
      fin_cases i <;> simp [e] <;> linarith)
    ⟨2, by simp [e]⟩
    ⟨0, by simp [e]; linarith⟩
    (fun l hl i ↦ by
      have hℓk : ((ℓ : ℝ) + 1) / k ≤ 1 := by rw [div_le_one hkpos]; exact_mod_cast hℓ
      have hℓ0 : 0 ≤ lam * ℓ / k := by positivity
      rcases mem_insert.mp hl with rfl | hl
      · rw [hf2]; fin_cases i <;> simp <;> linarith
      · obtain rfl := Finset.mem_singleton.mp hl
        rw [hf3]; fin_cases i <;> simp; linarith)
    (fun l hl ↦ by
      rcases mem_insert.mp hl with rfl | hl
      · exact ⟨0, by rw [hf2]; simp⟩
      · obtain rfl := Finset.mem_singleton.mp hl
        exact ⟨2, by rw [hf3]; simp⟩)
    (by
      rw [hS, sum_pair (ι := Nat.Primes) h23, hf2, hf3]
      simp only [e, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hδ]
      field_simp
      ring_nf
      linarith)
  choose! T hTcard hTtop hTmem using hclass
  refine ⟨(range k).biUnion T, ?_, ?_, ?_⟩
  · -- the count
    have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
    have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
    have hlogδ : 1 + log δ⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      have : log δ⁻¹ ≤ log (2 * ε⁻¹) := log_le_log (by positivity) hδinv
      rw [log_mul (by norm_num) (by positivity)] at this
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have := log_nonneg hεinv
      linarith
    have hlogδ0 : 0 ≤ 1 + log δ⁻¹ := by have := log_nonneg hδinv1; linarith
    have hcard : (#((range k).biUnion T) : ℝ) ≤
        k * (K₀ * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2) := by
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
  · intro a c ha hac happ hthr
    -- the class of the gap `s`
    set s := c - a with hs
    set ℓ := k * s / c with hℓdef
    have hcpos : 0 < c := by omega
    have hℓk : ℓ < k := by
      rw [hℓdef, Nat.div_lt_iff_lt_mul hcpos]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have hℓ1 : (ℓ : ℝ) * c ≤ k * s := by exact_mod_cast Nat.div_mul_le_self (k * s) c
    have hℓ2 : (k : ℝ) * s < (ℓ + 1) * c := by
      have := Nat.lt_mul_div_succ (k * s) hcpos
      have : (k * s : ℝ) < c * (ℓ + 1) := by exact_mod_cast this
      linarith
    have hsa : (s : ℝ) + a = c := by rw [hs]; exact_mod_cast Nat.sub_add_cancel hac.le
    set x := kernelPoint a c with hx
    have hX := iSup_abs_kernelPoint ha hac
    have hx0 : x ≠ 0 := fun h ↦ by
      have := congrFun h 0
      simp [x, kernelPoint] at this
    -- everything as a power of `3`
    have hpow : ∀ y : ℝ, ((3 : ℝ) ^ c) ^ y = (3 : ℝ) ^ (c * y) := fun y ↦ by
      rw [← rpow_natCast, ← rpow_mul (by norm_num)]
    have h3 : ∀ n : ℕ, (3 : ℝ) ^ n = (3 : ℝ) ^ (n : ℝ) := fun n ↦ (rpow_natCast 3 n).symm
    have hle : ∀ y z : ℝ, y ≤ z → (3 : ℝ) ^ y ≤ (3 : ℝ) ^ z := fun y z h ↦
      rpow_le_rpow_of_exponent_le (by norm_num) h
    have hZ := kernelPoint_two_bounds ha hac
    have hinf : ∀ i, |∑ j, quadVal 0 (P i j) * x j| ≤ 1 * (⨆ k, |(x k : ℝ)|) ^ e ℓ i := by
      rw [hX]
      intro i
      fin_cases i
      · change |∑ j, quadVal 0 (P 0 j) * (x j : ℝ)| ≤ 1 * ((3 : ℝ) ^ c) ^ (lam - ε)
        have hN : ∑ j, quadVal 0 (P 0 j) * (x j : ℝ) = kernelNum a c := by
          simp [P, quadVal, x, kernelPoint, kernelNum, Fin.sum_univ_three]
          ring
        rw [hN, kernelNum_eq_real hac.le, abs_mul, abs_of_pos (by positivity), one_mul]
        calc (2 : ℝ) ^ c * |(eps c : ℝ) - eps a| ≤ 2 ^ c * ((3 : ℝ) ^ c) ^ (-ε) :=
              mul_le_mul_of_nonneg_left happ (by positivity)
          _ = ((3 : ℝ) ^ c) ^ (lam - ε) := by
              rw [hpow, hpow, two_pow_eq_three_rpow, ← rpow_add (by norm_num)]
              congr 1
              ring
      · change |∑ j, quadVal 0 (P 1 j) * (x j : ℝ)| ≤
          1 * ((3 : ℝ) ^ c) ^ (1 - (1 - lam) * ℓ / k)
        have h1 : ∑ j, quadVal 0 (P 1 j) * (x j : ℝ) = (2 : ℝ) ^ s * 3 ^ a := by
          simp [P, quadVal, x, kernelPoint, Fin.sum_univ_three, hs]
        rw [h1, abs_of_pos (by positivity), one_mul, two_pow_eq_three_rpow, h3,
          ← rpow_add (by norm_num), hpow]
        refine hle _ _ ?_
        have hcl : (c : ℝ) * ℓ / k ≤ s := by rw [div_le_iff₀ hkpos]; linarith
        have h1l : 0 ≤ 1 - lam := by linarith
        calc lam * s + a = c - (1 - lam) * s := by linarith
          _ ≤ c - (1 - lam) * (c * ℓ / k) := by nlinarith
          _ = c * (1 - (1 - lam) * ℓ / k) := by ring
      · change |∑ j, quadVal 0 (P 2 j) * (x j : ℝ)| ≤ 1 * ((3 : ℝ) ^ c) ^ (1 : ℝ)
        have h2 : ∑ j, quadVal 0 (P 2 j) * (x j : ℝ) = ((2 ^ c * (m c - m a) : ℤ) : ℝ) := by
          simp [P, quadVal, x, kernelPoint, Fin.sum_univ_three]
        rw [h2, one_mul, rpow_one, abs_of_pos (by exact_mod_cast hZ.1)]
        exact_mod_cast hZ.2.le
    have hpad : ∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤
        (⨆ k, |(x k : ℝ)|) ^ f ℓ l i := by
      rw [hX]
      intro l hl i
      rcases mem_insert.mp hl with rfl | hl
      · have := Fact.mk Nat.prime_two
        rw [hf2]
        fin_cases i
        · change ((padicNorm 2 (x 0 : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ c) ^ (0 : ℝ)
          rw [rpow_zero]
          exact padicNorm_intCast_le_one 2 _
        · change ((padicNorm 2 (x 1 : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ c) ^ (-(lam * ℓ / k))
          calc ((padicNorm 2 (x 1 : ℚ) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ s :=
                padicNorm_intCast_le_of_dvd (by
                  change ((2 : ℕ) : ℤ) ^ s ∣ 2 ^ s * 3 ^ a
                  exact_mod_cast dvd_mul_right _ _)
            _ = (3 : ℝ) ^ (-(lam * s)) := by
                rw [one_div_pow, one_div, two_pow_eq_three_rpow, ← rpow_neg (by norm_num)]
            _ ≤ (3 : ℝ) ^ (c * (-(lam * ℓ / k))) := hle _ _ (by
                have hcl : (c : ℝ) * ℓ / k ≤ s := by rw [div_le_iff₀ hkpos]; linarith
                have : (c : ℝ) * (lam * ℓ / k) = lam * (c * ℓ / k) := by ring
                nlinarith)
            _ = ((3 : ℝ) ^ c) ^ (-(lam * ℓ / k)) := (hpow _).symm
        · change ((padicNorm 2 (x 2 : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ c) ^ (-lam)
          calc ((padicNorm 2 (x 2 : ℚ) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ c :=
                padicNorm_intCast_le_of_dvd (by
                  change ((2 : ℕ) : ℤ) ^ c ∣ 2 ^ c * (m c - m a)
                  exact_mod_cast dvd_mul_right _ _)
            _ = ((3 : ℝ) ^ c) ^ (-lam) := by
                rw [one_div_pow, one_div, two_pow_eq_three_rpow, ← rpow_neg (by norm_num),
                  hpow]
                congr 1
                ring
      · obtain rfl := Finset.mem_singleton.mp hl
        have := Fact.mk Nat.prime_three
        rw [hf3]
        fin_cases i
        · change ((padicNorm 3 (x 0 : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ c) ^ (-1 : ℝ)
          calc ((padicNorm 3 (x 0 : ℚ) : ℚ) : ℝ) ≤ (1 / 3 : ℝ) ^ c :=
                padicNorm_intCast_le_of_dvd (by
                  change ((3 : ℕ) : ℤ) ^ c ∣ 3 ^ c
                  exact_mod_cast dvd_refl _)
            _ = ((3 : ℝ) ^ c) ^ (-1 : ℝ) := by
                rw [rpow_neg_one, one_div_pow, one_div]
        · change ((padicNorm 3 (x 1 : ℚ) : ℚ) : ℝ) ≤
            ((3 : ℝ) ^ c) ^ (-(1 - ((ℓ : ℝ) + 1) / k))
          calc ((padicNorm 3 (x 1 : ℚ) : ℚ) : ℝ) ≤ (1 / 3 : ℝ) ^ a :=
                padicNorm_intCast_le_of_dvd (by
                  change ((3 : ℕ) : ℤ) ^ a ∣ 2 ^ s * 3 ^ a
                  exact_mod_cast dvd_mul_left _ _)
            _ = (3 : ℝ) ^ (-(a : ℝ)) := by
                rw [one_div_pow, one_div, h3, ← rpow_neg (by norm_num)]
            _ ≤ (3 : ℝ) ^ (c * (-(1 - ((ℓ : ℝ) + 1) / k))) := hle _ _ (by
                have : (s : ℝ) ≤ c * (((ℓ : ℝ) + 1) / k) := by
                  rw [mul_div_assoc', le_div_iff₀ hkpos]
                  linarith
                linarith)
            _ = ((3 : ℝ) ^ c) ^ (-(1 - ((ℓ : ℝ) + 1) / k)) := (hpow _).symm
        · change ((padicNorm 3 (x 2 : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ c) ^ (0 : ℝ)
          rw [rpow_zero]
          exact padicNorm_intCast_le_one 3 _
    have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 1 + log (1 : ℝ)⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) := by
      rw [hX, log_pow]
      simp only [log_one, inv_one, add_zero, mul_one]
      calc K₀ * δ⁻¹ ≤ K₀ * (2 * ε⁻¹) := by gcongr
        _ ≤ 96 * K₀ * ε⁻¹ := by
            have : 0 ≤ K₀ * ε⁻¹ := by positivity
            linarith
        _ ≤ c * log 3 := hthr
    obtain ⟨U, hU, hmem⟩ := hTmem ℓ hℓk x hx0 hinf hpad hthr'
    exact ⟨U, mem_biUnion.mpr ⟨ℓ, mem_range.mpr hℓk, hU⟩, hmem⟩

end SteeringWord
