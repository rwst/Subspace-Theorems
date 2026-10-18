/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.ConstantGap

-- Used only inside proofs.
import Mathlib.Data.Set.Finite.Lattice

/-!
# The kernel, and the main theorem

**Theorem 4.5.** For every rational `θ ∈ (0, 1)` the set `V(θ)` is finite: only finitely many
pairs `2 ≤ a < c` satisfy `‖(3/2)^c - (3/2)^a‖ ≤ θ^c`. The unknown integer `M` nearest to
`(3/2)^c - (3/2)^a` becomes a third coordinate: the integer point

```text
x = (2^c M, 3^c, 2^s 3^a),        s = c - a,
```

with the forms `X₁ - X₂ - X₀`, `X₂`, `X₀` at `∞` and the coordinate forms at `2` and `3`, has
double product `|N| M 3^(-c) ≤ θ^c` with `N = 2^c ((3/2)^c - (3/2)^a - M)`, and size `3^c`.
Of the nine factors, those of the `S`-unit coordinates `3^c` and `2^s 3^a` cancel exactly by the
accounting principle; the `2`-adic smallness of `2^c M` pays for `2^c`. The gap `s` enters only
through `2^s 3^a`, whose archimedean factor `2^s` is repaid by its `2`-adic factor `2^(-s)`: one
application of Theorem 4.1 covers all gaps at once. The points lie in finitely many planes
`w₀ X₀ + w₁ X₁ + w₂ X₂ = 0`, that is `w₀ M + w₁ (3/2)^c + w₂ (3/2)^a = 0`, and on each plane:

* if `w₀ = 0`, the ratio `(3/2)^(c-a) = -w₂ / w₁` is constant, so the gap is constant and
  Corollary 4.3 applies — this is the one place where three variables cannot finish the job, as
  the constant-gap points form a one-parameter family inside one plane;
* if `w₀ ≠ 0`, the distance is a fixed combination `|β₁ (3/2)^c + β₂ (3/2)^a|`; it is positive by
  Lemma 2.8, and since the ratio `(3/2)^(c-a)` cannot accumulate, a positive floor `|β₂|` or
  `|β₁| / 2` bounds `c`, except on finitely many gaps, which are Corollary 4.3 again.

**Theorem 4.7 = Theorem 1.1, the main theorem**: `p_T(k) / k → ∞`, by Theorem 3.2.

## Main results

* `SteeringWord.finite_kernelViolators`: **Theorem 4.5**, the kernel (K).
* `SteeringWord.exists_forall_lt_complexity`: **Theorem 1.1**, for every `C` there is `K` with
  `p_T(k) > C k` for all `k ≥ K`.
* `SteeringWord.tendsto_complexity_div`: **Theorem 1.1**, `p_T(k) / k → ∞`.

## Implementation notes

The paper orders the coordinates `(3^c, 2^s 3^a, 2^c M)`; here `2^c M` comes first. All the
inputs (Theorem 4.1 and with it the Subspace Theorem, Ridout's theorem behind Lemma 4.2) are
proved in `DiophantineApproximation`, so the main theorem depends on Lean's three standard axioms
and nothing else. Every step is ineffective: no bound on the exceptional sets is obtained.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §4.3.
-/

public section

namespace SteeringWord

open Function Filter

private theorem three_halves_pow_injective :
    Function.Injective fun n : ℕ ↦ (3 / 2 : ℚ) ^ n :=
  (pow_right_strictMono₀ (by norm_num : (1 : ℚ) < 3 / 2)).injective

/-- A positive floor on the kernel distance bounds `c`. -/
private theorem finite_kernelViolators_of_le (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) {b : ℚ}
    (hb : 0 < b) :
    {p | p ∈ kernelViolators θ ∧
      b ≤ ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt}.Finite := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hθ1
  refine ((Set.finite_Iio n).prod (Set.finite_Iio n)).subset ?_
  rintro ⟨a, c⟩ ⟨⟨-, hac, hdist⟩, hbdist⟩
  have hc : c < n := by
    by_contra hcn
    have : θ ^ c ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1.le (not_lt.mp hcn)
    simp only at hdist hbdist
    linarith
  exact ⟨Set.mem_Iio.mpr (by simp only at hac ⊢; omega), Set.mem_Iio.mpr hc⟩

/-- **The exceptional planes.** On a plane `w₀ M + w₁ (3/2)^c + w₂ (3/2)^a = 0`, `w ≠ 0`, lie only
finitely many pairs of `V(θ)`; here `M` is the integer nearest to `(3/2)^c - (3/2)^a`. -/
theorem finite_kernelViolators_of_relation {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {w₀ w₁ w₂ : ℚ}
    (hw : ¬(w₀ = 0 ∧ w₁ = 0 ∧ w₂ = 0)) :
    {p | p ∈ kernelViolators θ ∧
      w₀ * (round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℚ) + w₁ * (3 / 2 : ℚ) ^ p.2
        + w₂ * (3 / 2 : ℚ) ^ p.1 = 0}.Finite := by
  set F := {p | p ∈ kernelViolators θ ∧
      w₀ * (round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℚ) + w₁ * (3 / 2 : ℚ) ^ p.2
        + w₂ * (3 / 2 : ℚ) ^ p.1 = 0} with hFdef
  rcases eq_or_ne w₀ 0 with hw₀ | hw₀
  · -- `w₀ = 0`: the ratio `(3/2)^(c-a)` is constant, so the gap is constant
    rcases F.eq_empty_or_nonempty with hF | ⟨p₀, hp₀⟩
    · rw [hF]
      exact Set.finite_empty
    have hw₁ : w₁ ≠ 0 := by
      intro h1
      have h := hp₀.2
      rw [hw₀, h1, zero_mul, zero_mul, zero_add, zero_add] at h
      exact hw ⟨hw₀, h1, (mul_eq_zero.mp h).resolve_right (by positivity)⟩
    have hconst : ∀ p ∈ F, (3 / 2 : ℚ) ^ (p.2 - p.1) = -w₂ / w₁ := fun p hp ↦ by
      have h := hp.2
      rw [hw₀, zero_mul, zero_add] at h
      have hsplit : (3 / 2 : ℚ) ^ p.2 = (3 / 2 : ℚ) ^ p.1 * (3 / 2 : ℚ) ^ (p.2 - p.1) := by
        rw [← pow_add]
        congr 1
        have := hp.1.2.1
        omega
      rw [hsplit] at h
      have h' : (3 / 2 : ℚ) ^ (p.2 - p.1) * w₁ + w₂ = 0 := by
        have hfac : (3 / 2 : ℚ) ^ p.1 * ((3 / 2 : ℚ) ^ (p.2 - p.1) * w₁ + w₂) = 0 := by
          rw [← h]
          ring
        exact (mul_eq_zero.mp hfac).resolve_left (by positivity)
      rw [eq_div_iff hw₁]
      linear_combination h'
    refine (finite_kernelViolators_gap_le (p₀.2 - p₀.1) hθ0 hθ1).subset fun p hp ↦ ⟨hp.1, ?_⟩
    have h := three_halves_pow_injective ((hconst p hp).trans (hconst p₀ hp₀).symm)
    have := hp.1.2.1
    omega
  -- `w₀ ≠ 0`: the distance is a fixed combination `|β₁ (3/2)^c + β₂ (3/2)^a|`
  set β₁ : ℚ := 1 + w₁ / w₀ with hβ₁def
  set β₂ : ℚ := w₂ / w₀ - 1 with hβ₂def
  have hdisteq : ∀ p ∈ F, ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt
      = |β₁ * (3 / 2 : ℚ) ^ p.2 + β₂ * (3 / 2 : ℚ) ^ p.1| := fun p hp ↦ by
    have hM : ((round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℤ) : ℚ)
        = -(w₁ / w₀) * (3 / 2 : ℚ) ^ p.2 - (w₂ / w₀) * (3 / 2 : ℚ) ^ p.1 := by
      field_simp
      linear_combination hp.2
    rw [Rat.distToNearestInt, hM, hβ₁def, hβ₂def]
    congr 1
    ring
  rcases eq_or_ne β₁ 0 with hβ₁0 | hβ₁0
  · rcases eq_or_ne β₂ 0 with hβ₂0 | hβ₂0
    · -- both vanish: the distance is zero, against Lemma 2.8
      refine Set.finite_empty.subset fun p hp ↦ ?_
      have hpos := distToNearestInt_orbit_pos (a := p.1) (c := p.2) (by have := hp.1.1; omega)
        hp.1.2.1
      rw [hdisteq p hp, hβ₁0, hβ₂0, zero_mul, zero_mul, add_zero, abs_zero] at hpos
      exact lt_irrefl 0 hpos
    · -- the distance is `|β₂| (3/2)^a ≥ |β₂|`
      refine (finite_kernelViolators_of_le θ hθ0 hθ1 (abs_pos.mpr hβ₂0)).subset
        fun p hp ↦ ⟨hp.1, ?_⟩
      rw [hdisteq p hp, hβ₁0, zero_mul, zero_add, abs_mul,
        abs_of_pos (by positivity : (0 : ℚ) < (3 / 2) ^ p.1)]
      nlinarith [abs_nonneg β₂, one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 3 / 2) (n := p.1)]
  · -- `β₁ ≠ 0`: for gaps `≥ s₁` the distance is `≥ |β₁| / 2`; smaller gaps are Corollary 4.3
    obtain ⟨s₁, hs₁⟩ := pow_unbounded_of_one_lt (2 * |β₂| / |β₁|) (by norm_num : (1 : ℚ) < 3 / 2)
    have hβ₁pos : 0 < |β₁| := abs_pos.mpr hβ₁0
    have hs₁' : 2 * |β₂| < |β₁| * (3 / 2 : ℚ) ^ s₁ := by
      rw [div_lt_iff₀ hβ₁pos] at hs₁
      linarith
    refine ((finite_kernelViolators_gap_le s₁ hθ0 hθ1).union
      (finite_kernelViolators_of_le θ hθ0 hθ1 (by positivity : 0 < |β₁| / 2))).subset
      fun p hp ↦ ?_
    by_cases hg : p.2 ≤ p.1 + s₁
    · exact Or.inl ⟨hp.1, hg⟩
    right
    refine ⟨hp.1, ?_⟩
    rw [hdisteq p hp]
    push Not at hg
    set u₂ : ℚ := (3 / 2 : ℚ) ^ p.1 with hu₂def
    have hu₂pos : 0 < u₂ := by positivity
    have hu₁ : (3 / 2 : ℚ) ^ p.2 = (3 / 2 : ℚ) ^ (p.2 - p.1) * u₂ := by
      rw [hu₂def, ← pow_add]
      congr 1
      omega
    have hpow : (3 / 2 : ℚ) ^ s₁ ≤ (3 / 2 : ℚ) ^ (p.2 - p.1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hone : (1 : ℚ) ≤ (3 / 2 : ℚ) ^ (p.2 - p.1) * u₂ := by
      rw [← hu₁]
      exact one_le_pow₀ (by norm_num)
    have h1 : 2 * |β₂| * u₂ ≤ |β₁| * ((3 / 2 : ℚ) ^ (p.2 - p.1) * u₂) := by
      have := mul_le_mul_of_nonneg_right
        (le_trans hs₁'.le (mul_le_mul_of_nonneg_left hpow (abs_nonneg β₁))) hu₂pos.le
      linarith
    have h2 : |β₁ * (3 / 2 : ℚ) ^ p.2| - |β₂ * u₂| ≤ |β₁ * (3 / 2 : ℚ) ^ p.2 + β₂ * u₂| := by
      have := abs_sub_abs_le_abs_sub (β₁ * (3 / 2 : ℚ) ^ p.2) (-(β₂ * u₂))
      rwa [abs_neg, sub_neg_eq_add] at this
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (3 / 2) ^ p.2),
      abs_of_pos hu₂pos, hu₁] at h2
    rw [hu₁]
    nlinarith [h1, h2, hone, hβ₁pos]

/-- **Theorem 4.5, exponential pair repulsion: the kernel (K) holds.** For every rational
`θ ∈ (0, 1)`, only finitely many pairs `2 ≤ a < c` satisfy `‖(3/2)^c - (3/2)^a‖ ≤ θ^c`.
Ineffective. -/
theorem finite_kernelViolators {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (kernelViolators θ).Finite := by
  classical
  set M : ℕ × ℕ → ℤ := fun p ↦ round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) with hMdef
  set x : ℕ × ℕ → Fin 3 → ℤ := fun p ↦ ![2 ^ p.2 * M p, 3 ^ p.2, 2 ^ (p.2 - p.1) * 3 ^ p.1]
    with hxdef
  set N : ℕ × ℕ → ℤ := fun p ↦ 3 ^ p.2 - 2 ^ (p.2 - p.1) * 3 ^ p.1 - 2 ^ p.2 * M p with hNdef
  have hx2 : ∀ p : ℕ × ℕ, p.1 ≤ p.2 →
      ((2 ^ (p.2 - p.1) * 3 ^ p.1 : ℤ) : ℚ) = 2 ^ p.2 * (3 / 2) ^ p.1 := fun p hp ↦ by
    have h : (2 : ℚ) ^ p.2 = 2 ^ (p.2 - p.1) * 2 ^ p.1 := by rw [← pow_add, Nat.sub_add_cancel hp]
    push_cast
    rw [h, div_pow]
    field_simp
  have hNabs : ∀ p ∈ kernelViolators θ, |(N p : ℚ)|
      = 2 ^ p.2 * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt := fun p hp ↦ by
    have hN : (N p : ℚ) = 2 ^ p.2 * ((3 / 2 : ℚ) ^ p.2 - (3 / 2) ^ p.1 - M p) := by
      have := hx2 p hp.2.1.le
      simp only [hNdef]
      push_cast at this ⊢
      rw [this, div_pow, div_pow]
      field_simp
    rw [hN, abs_mul, abs_of_pos (by positivity)]
    rfl
  have hM : ∀ p ∈ kernelViolators θ, |(M p : ℚ)| ≤ (3 / 2 : ℚ) ^ p.2 := fun p hp ↦ by
    have h := abs_le.mp (abs_sub_round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1))
    have hlt : (3 / 2 : ℚ) ^ p.1 < (3 / 2) ^ p.2 := pow_lt_pow_right₀ (by norm_num) hp.2.1
    have h1 : (1 : ℚ) ≤ (3 / 2) ^ p.1 := one_le_pow₀ (by norm_num)
    exact abs_le.mpr ⟨by simp only [hMdef]; linarith, by simp only [hMdef]; linarith⟩
  have hx0 : ∀ p ∈ kernelViolators θ, |((2 ^ p.2 * M p : ℤ) : ℚ)| ≤ 3 ^ p.2 := fun p hp ↦ by
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ p.2)]
    calc (2 : ℚ) ^ p.2 * |(M p : ℚ)| ≤ 2 ^ p.2 * (3 / 2) ^ p.2 :=
          mul_le_mul_of_nonneg_left (hM p hp) (by positivity)
      _ = 3 ^ p.2 := by rw [← mul_pow]; norm_num
  -- the double product of Theorem 4.1 at `x p`
  set P : ℕ × ℕ → ℚ := fun p ↦ |(N p : ℚ)| * |((2 ^ (p.2 - p.1) * 3 ^ p.1 : ℤ) : ℚ)|
    * |((2 ^ p.2 * M p : ℤ) : ℚ)|
    * (padicNorm 2 ((2 ^ p.2 * M p : ℤ) : ℚ) * padicNorm 2 ((3 ^ p.2 : ℤ) : ℚ)
      * padicNorm 2 ((2 ^ (p.2 - p.1) * 3 ^ p.1 : ℤ) : ℚ))
    * (padicNorm 3 ((2 ^ p.2 * M p : ℤ) : ℚ) * padicNorm 3 ((3 ^ p.2 : ℤ) : ℚ)
      * padicNorm 3 ((2 ^ (p.2 - p.1) * 3 ^ p.1 : ℤ) : ℚ)) with hPdef
  have hP : ∀ p ∈ kernelViolators θ, P p ≤ 1 * θ ^ p.2 := fun p hp ↦ by
    obtain ⟨a, c⟩ := p
    obtain ⟨ha, hac, hd⟩ := hp
    simp only at ha hac hd
    have h2 : padicNorm 2 ((2 ^ c * M (a, c) : ℤ) : ℚ) * padicNorm 2 ((3 ^ c : ℤ) : ℚ)
        * padicNorm 2 ((2 ^ (c - a) * 3 ^ a : ℤ) : ℚ) ≤ (1 / 2 : ℚ) ^ c * 1 * (1 / 2) ^ (c - a) :=
      mul_le_mul (mul_le_mul (padicNorm_le_of_dvd (by push_cast; exact Dvd.intro _ rfl))
        (padicNorm.of_int _) (padicNorm.nonneg _) (by positivity))
        (padicNorm_le_of_dvd (by push_cast; exact Dvd.intro _ rfl)) (padicNorm.nonneg _)
        (by positivity)
    have h3 : padicNorm 3 ((2 ^ c * M (a, c) : ℤ) : ℚ) * padicNorm 3 ((3 ^ c : ℤ) : ℚ)
        * padicNorm 3 ((2 ^ (c - a) * 3 ^ a : ℤ) : ℚ) ≤ 1 * (1 / 3 : ℚ) ^ c * (1 / 3) ^ a :=
      mul_le_mul (mul_le_mul (padicNorm.of_int _)
        (padicNorm_le_of_dvd (by push_cast; exact dvd_refl _)) (padicNorm.nonneg _)
        (by positivity))
        (padicNorm_le_of_dvd (by push_cast; exact Dvd.intro_left _ rfl)) (padicNorm.nonneg _)
        (by positivity)
    have hN : |(N (a, c) : ℚ)| ≤ 2 ^ c * θ ^ c := by
      rw [hNabs (a, c) ⟨by omega, hac, hd⟩]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    have hx2' : |((2 ^ (c - a) * 3 ^ a : ℤ) : ℚ)| = 2 ^ (c - a) * 3 ^ a := by
      push_cast
      exact abs_of_pos (by positivity)
    have e2c : (2 : ℚ) ^ c * (1 / 2) ^ c = 1 := by rw [← mul_pow]; norm_num
    have e2s : (2 : ℚ) ^ (c - a) * (1 / 2) ^ (c - a) = 1 := by rw [← mul_pow]; norm_num
    have e3a : (3 : ℚ) ^ a * (1 / 3) ^ a = 1 := by rw [← mul_pow]; norm_num
    have e3c : (3 : ℚ) ^ c * (1 / 3) ^ c = 1 := by rw [← mul_pow]; norm_num
    calc P (a, c) ≤ (2 ^ c * θ ^ c) * (2 ^ (c - a) * 3 ^ a) * 3 ^ c
          * ((1 / 2 : ℚ) ^ c * 1 * (1 / 2) ^ (c - a)) * (1 * (1 / 3 : ℚ) ^ c * (1 / 3) ^ a) := by
          simp only [hPdef]
          rw [hx2']
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hN
            (by positivity)) (hx0 (a, c) ⟨by omega, hac, hd⟩) (abs_nonneg _) (by positivity))
            h2 (mul_nonneg (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _))
              (padicNorm.nonneg _)) (by positivity)) h3
            (mul_nonneg (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _))
              (padicNorm.nonneg _)) (by positivity)
      _ = θ ^ c * ((2 ^ c * (1 / 2) ^ c) * (2 ^ (c - a) * (1 / 2) ^ (c - a))
          * (3 ^ a * (1 / 3) ^ a) * (3 ^ c * (1 / 3) ^ c)) := by ring
      _ = 1 * θ ^ c := by rw [e2c, e2s, e3a, e3c]; ring
  -- the size of `x p`
  have hsize : ∀ p ∈ kernelViolators θ, ⨆ i, |((x p i : ℤ) : ℝ)| ≤ 1 * 3 ^ p.2 := fun p hp ↦ by
    have hz0 : |2 ^ p.2 * M p| ≤ 3 ^ p.2 := by exact_mod_cast hx0 p hp
    have hz2 : |2 ^ (p.2 - p.1) * 3 ^ p.1| ≤ (3 : ℤ) ^ p.2 := by
      rw [abs_of_pos (by positivity)]
      calc (2 : ℤ) ^ (p.2 - p.1) * 3 ^ p.1 ≤ 3 ^ (p.2 - p.1) * 3 ^ p.1 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
              (by positivity)
        _ = 3 ^ p.2 := by rw [← pow_add, Nat.sub_add_cancel hp.2.1.le]
    rw [one_mul]
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · simpa [hxdef] using (show (|2 ^ p.2 * M p| : ℝ) ≤ ((3 ^ p.2 : ℤ) : ℝ) by exact_mod_cast hz0)
    · simp [hxdef]
    · simpa [hxdef] using
        (show (|2 ^ (p.2 - p.1) * 3 ^ p.1| : ℝ) ≤ ((3 ^ p.2 : ℤ) : ℝ) by exact_mod_cast hz2)
  have hsize0 : ∀ p, 0 < ⨆ i, |((x p i : ℤ) : ℝ)| := fun p ↦ by
    refine lt_of_lt_of_le ?_ (le_ciSup (Set.finite_range _).bddAbove 1)
    simp only [hxdef, Matrix.cons_val_one, Matrix.cons_val_zero]
    positivity
  -- Theorem 4.1 with `n = 3`
  have hθ0' : (0 : ℝ) < θ := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨ε, hε, c₀, hc₀⟩ := exists_forall_mul_pow_le_rpow_neg hθ0' hθ1' 1 one_pos
  set L : Fin 3 → Fin 3 → ℚ := ![![-1, 1, -1], ![0, 0, 1], ![1, 0, 0]] with hLdef
  have hL : LinearIndependent ℚ L := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 = 0 := by simpa [hLdef, Fin.sum_univ_three] using congrFun hg 1
    intro i
    fin_cases i
    · exact h0
    · simpa [hLdef, Fin.sum_univ_three, h0] using congrFun hg 2
    · simpa [hLdef, Fin.sum_univ_three, h0] using congrFun hg 0
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_prod_le L hL hε
  have hcover : ∀ p ∈ kernelViolators θ, c₀ ≤ p.2 →
      ∃ V ∈ T, (fun i ↦ ((x p i : ℤ) : ℚ)) ∈ V := fun p hp hc ↦ by
    refine hmem (x p) (fun h ↦ ?_) ?_
    · have := congrFun h 1
      simp only [hxdef, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at this
      have : (0 : ℚ) < ((3 ^ p.2 : ℤ) : ℚ) := by push_cast; positivity
      linarith
    · have hLHS : (∏ i, |∑ j, (L i j : ℝ) * (x p j : ℝ)|)
          * ((∏ i, ((padicNorm 2 (x p i) : ℚ) : ℝ)) * ∏ i, ((padicNorm 3 (x p i) : ℚ) : ℝ))
          = ((P p : ℚ) : ℝ) := by
        simp only [hPdef, hNdef, hxdef, hLdef, Fin.prod_univ_three, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
        push_cast
        ring_nf
      rw [hLHS]
      exact le_trans (by exact_mod_cast hP p hp) (hc₀ p.2 hc _ (hsize0 p) (hsize p hp))
  -- each plane carries finitely many of the points
  have hfin : ∀ V ∈ T, {p | p ∈ kernelViolators θ ∧ (fun i ↦ ((x p i : ℤ) : ℚ)) ∈ V}.Finite :=
    fun V hV ↦ by
      obtain ⟨w, hw0, hwV⟩ := exists_ne_zero_forall_sum_mul_eq_zero (hT V hV)
      have hw : ¬(w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) := fun ⟨h0, h1, h2⟩ ↦ hw0 (funext fun i ↦ by
        fin_cases i <;> assumption)
      refine (finite_kernelViolators_of_relation hθ0 hθ1 hw).subset fun p ⟨hp, hpV⟩ ↦ ⟨hp, ?_⟩
      have h := hwV _ hpV
      simp only [Fin.sum_univ_three, hxdef, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
      rw [hx2 p hp.2.1.le] at h
      have h2c : (0 : ℚ) < 2 ^ p.2 := by positivity
      have hdiv : (2 : ℚ) ^ p.2 * (w 0 * (M p : ℚ) + w 1 * (3 / 2 : ℚ) ^ p.2
          + w 2 * (3 / 2 : ℚ) ^ p.1) = 0 := by
        rw [← h, div_pow]
        push_cast
        field_simp
      exact (mul_eq_zero.mp hdiv).resolve_left h2c.ne'
  refine (((Set.finite_Iio c₀).prod (Set.finite_Iio c₀)).union
    (T.finite_toSet.biUnion fun V hV ↦ hfin V hV)).subset fun p hp ↦ ?_
  rcases lt_or_ge p.2 c₀ with h | h
  · exact Or.inl ⟨Set.mem_Iio.mpr (by have := hp.2.1; omega), Set.mem_Iio.mpr h⟩
  · obtain ⟨V, hV, hxV⟩ := hcover p hp h
    exact Or.inr (Set.mem_biUnion hV ⟨hp, hxV⟩)

/-- **Theorem 1.1, the main theorem**: the subword complexity of the steering word is
superlinear — for every `C` there is a `K` with `p_T(k) > C k` for all `k ≥ K`. -/
theorem exists_forall_lt_complexity (C : ℕ) : ∃ K : ℕ, ∀ k, K ≤ k → C * k < complexity t k :=
  forall_lt_complexity_of_kernel (fun _ hθ0 hθ1 ↦ finite_kernelViolators hθ0 hθ1) C

/-- **Theorem 1.1, the main theorem**: `p_T(k) / k → ∞`. -/
theorem tendsto_complexity_div : Tendsto (fun k : ℕ ↦ (complexity t k : ℝ) / k) atTop atTop :=
  tendsto_complexity_div_of_kernel fun _ hθ0 hθ1 ↦ finite_kernelViolators hθ0 hθ1

end SteeringWord
