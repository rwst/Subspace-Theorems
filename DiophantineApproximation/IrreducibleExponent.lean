/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Gelfond
public import DiophantineApproximation.MahlerExponent

/-!
# Restricting Mahler's exponent to irreducible polynomials

That `Real.mahlerExponent` does not change when the polynomials are required to be **primitive**
is bookkeeping: dividing by the content divides the value and the height by the same integer, and
the inequality only improves. That it does not change when they are required to be **irreducible**
is a theorem, and the theorem is Gelfond's inequality.

The difficulty is that the replacement is destructive. A solution `P` is replaced by *one of its
irreducible factors*, and nothing in the hypothesis `|P ξ| ≤ H(P) ^ (-w)` says that any single
factor is small: the smallness could be spread over all of them. What rules that out is the lower
half of Gelfond's inequality — the product of the heights of the factors is at most
`2 ^ deg` times the height of the product — so if every factor were a *bad* approximation the
product of the bad bounds would contradict the good bound on `P`. The loss `2 ^ deg` is the whole
content of the argument, and it reproduces itself along a factorization rather than accumulating
because the recursion is run at the scale `λ = 2 ^ (-n)`, the unique scale with `λ ^ 2 * 2 ^ n ≤ λ`.

## Main results

* `Polynomial.supNorm_mul_supNorm_le_two_pow_int`: **Gelfond's inequality over `ℤ`**, for the
  naive height, consumed from `ArithmeticHeights` 2.3 at a single complex place.
* `Polynomial.supNorm_map_complex`: the naive height of an integer polynomial is the sup norm of
  its complex image, which is what makes that consumption possible.
* `Polynomial.exists_irreducible_dvd_aeval_eq_zero`: a primitive integer polynomial with a real
  root has an irreducible factor with the same root.
* `Polynomial.IsPrimitive.of_dvd` and
  `Polynomial.one_le_natDegree_of_not_isUnit_of_dvd`: a divisor of a primitive polynomial is
  primitive, and a nonunit divisor of one has degree at least one.
* `Real.mahlerExponent_eq_iSup_irreducible`: **restricting to irreducible polynomials does not
  change Mahler's exponent.**

## Implementation notes

⚠ **The integer form of Gelfond's inequality needs only the archimedean half of
`ArithmeticHeights` 2.3.** That milestone proves the inequality for `Polynomial.mulHeight` over a
number field, where the nonarchimedean local factors are handled by the multivariate Gauss lemma
and the archimedean ones by the Mahler measure. Over `ℤ` with the naive height there is nothing to
normalize: the naive height *is* the sup norm of the complex image, so
`Polynomial.supNorm_mul_supNorm_le_two_pow_int` is `Polynomial.supNorm_mul_supNorm_le_two_pow` —
the local statement on `ℂ[X]` — transported along `Polynomial.map`, and the Gauss-lemma half of
2.3 is not consumed at all.

⚠ **The reduction to primitive polynomials is not cosmetic; it bounds the number of factors.**
An arbitrary integer polynomial has constant irreducible factors — the primes dividing its
content — and there can be arbitrarily many of them, so the `δ ^ (number of factors)` that the
argument pays would not be bounded below. A *primitive* polynomial has no constant irreducible
factor at all, so every factor has degree at least one and there are at most `deg P ≤ n` of them.
This is why `Real.infinite_primitive_mahlerSet` is a prerequisite and not a corollary.

⚠ **The recursion is on the degree, not on a factorization.** Mathlib's
`UniqueFactorizationMonoid.normalizedFactors` would give the multiset of irreducible factors, and
the argument could be run over it; splitting `P = A * B` at a single nonunit factorization and
recursing on `natDegree` is shorter, because the only fact needed about the splitting is that the
two parts have smaller degree — which is exactly what primitivity gives.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1 and
Lemma A.3. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University
Press (2006), §1.6.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/

public section

open Polynomial
open scoped ENNReal NNReal

namespace Polynomial

/-! ### Gelfond's inequality over `ℤ` -/

theorem supNorm_map_complex (P : ℤ[X]) :
    (P.map (Int.castRingHom ℂ)).supNorm = P.supNorm := by
  have hc : ∀ i : ℕ, ‖(P.map (Int.castRingHom ℂ)).coeff i‖ = ‖P.coeff i‖ := by
    intro i
    rw [coeff_map]
    simp [Int.norm_eq_abs]
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (P.map (Int.castRingHom ℂ)).exists_eq_supNorm
    rw [hi, hc]
    exact P.le_supNorm i
  · obtain ⟨i, hi⟩ := P.exists_eq_supNorm
    rw [hi, ← hc]
    exact (P.map (Int.castRingHom ℂ)).le_supNorm i

/-- **Gelfond's inequality over `ℤ`.** The naive heights of two integer polynomials multiply to at
most `2 ^ (deg P + deg Q)` times the naive height of their product. It is `ArithmeticHeights` 2.3
at a single complex place — the Gauss-lemma half of that milestone is not used, because over `ℤ`
there is nothing to normalize. -/
theorem supNorm_mul_supNorm_le_two_pow_int (P Q : ℤ[X]) :
    P.supNorm * Q.supNorm ≤ 2 ^ (P.natDegree + Q.natDegree) * (P * Q).supNorm := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := fun _ _ h ↦ Int.cast_injective h
  have h := Polynomial.supNorm_mul_supNorm_le_two_pow (P.map (Int.castRingHom ℂ))
    (Q.map (Int.castRingHom ℂ))
  rw [← Polynomial.map_mul, supNorm_map_complex, supNorm_map_complex, supNorm_map_complex,
    natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at h
  exact h

theorem IsPrimitive.of_dvd {A B : ℤ[X]} (hAB : A ∣ B) (hB : B.IsPrimitive) : A.IsPrimitive :=
  fun _ hr ↦ hB _ (hr.trans hAB)

/-- A nonunit factor of a primitive polynomial has degree at least one: a constant factor of a
primitive polynomial is a unit. -/
theorem one_le_natDegree_of_not_isUnit_of_dvd {A B : ℤ[X]} (hAB : A ∣ B) (hB : B.IsPrimitive)
    (hA : ¬ IsUnit A) : 1 ≤ A.natDegree := by
  by_contra h
  obtain ⟨c, hc⟩ := (Polynomial.natDegree_eq_zero (p := A)).1 (by omega)
  have hcA : C c ∣ A := ⟨1, by rw [mul_one, hc]⟩
  exact hA (by rw [← hc]; exact isUnit_C.2 (hB c (hcA.trans hAB)))

/-- A primitive polynomial has no irreducible constant factor, so every irreducible factor has
degree at least one. -/
theorem one_le_natDegree_of_irreducible_dvd {A B : ℤ[X]} (hAB : A ∣ B) (hB : B.IsPrimitive)
    (hA : Irreducible A) : 1 ≤ A.natDegree :=
  one_le_natDegree_of_not_isUnit_of_dvd hAB hB hA.not_isUnit

/-- Every primitive integer polynomial with a real root has an irreducible factor with the same
root. -/
theorem exists_irreducible_dvd_aeval_eq_zero {α : ℝ} :
    ∀ d : ℕ, ∀ S : ℤ[X], S.natDegree = d → S.IsPrimitive → aeval α S = 0 →
      ∃ Q : ℤ[X], Q ∣ S ∧ Irreducible Q ∧ aeval α Q = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro S hdS hprim hval
    have hS0 : S ≠ 0 := by
      intro h
      have h2 : IsUnit (2 : ℤ) := hprim 2 (by rw [h]; exact dvd_zero _)
      rcases Int.isUnit_iff.1 h2 with h3 | h3 <;> norm_num at h3
    have hSu : ¬ IsUnit S := by
      intro hu
      obtain ⟨r, hr⟩ := (Polynomial.natDegree_eq_zero (p := S)).1
        (Polynomial.natDegree_eq_zero_of_isUnit hu)
      have hru : IsUnit r := hprim r ⟨1, by rw [mul_one, hr]⟩
      rw [← hr] at hval
      simp only [eq_intCast] at hval
      rcases Int.isUnit_iff.1 hru with h3 | h3 <;> rw [h3] at hval <;> norm_num at hval
    by_cases hirr : Irreducible S
    · exact ⟨S, dvd_rfl, hirr, hval⟩
    obtain ⟨A, B, hSAB, hAu, hBu⟩ : ∃ A B : ℤ[X], S = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
      rw [irreducible_iff] at hirr
      push Not at hirr
      obtain ⟨A, B, hSAB, hAu, hBu⟩ := hirr hSu
      exact ⟨A, B, hSAB, hAu, hBu⟩
    have hA0 : A ≠ 0 := fun h ↦ hS0 (by rw [hSAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h ↦ hS0 (by rw [hSAB, h, mul_zero])
    have hAdvd : A ∣ S := ⟨B, hSAB⟩
    have hBdvd : B ∣ S := ⟨A, by rw [hSAB, mul_comm]⟩
    have hA1 : 1 ≤ A.natDegree :=
      one_le_natDegree_of_not_isUnit_of_dvd hAdvd hprim hAu
    have hB1 : 1 ≤ B.natDegree :=
      one_le_natDegree_of_not_isUnit_of_dvd hBdvd hprim hBu
    have hsum : A.natDegree + B.natDegree = d := by
      rw [← hdS, hSAB, Polynomial.natDegree_mul hA0 hB0]
    have hvalAB : aeval α A * aeval α B = 0 := by rw [← map_mul, ← hSAB]; exact hval
    rcases mul_eq_zero.1 hvalAB with hz | hz
    · obtain ⟨Q, hQA, hQirr, hQval⟩ :=
        ih A.natDegree (by omega) A rfl (Polynomial.IsPrimitive.of_dvd hAdvd hprim) hz
      exact ⟨Q, hQA.trans hAdvd, hQirr, hQval⟩
    · obtain ⟨Q, hQB, hQirr, hQval⟩ :=
        ih B.natDegree (by omega) B rfl (Polynomial.IsPrimitive.of_dvd hBdvd hprim) hz
      exact ⟨Q, hQB.trans hBdvd, hQirr, hQval⟩

end Polynomial

namespace Real

variable {ξ : ℝ} {n : ℕ}

/-! ### Extracting an irreducible factor -/

/-- The scale at which the recursion below closes: `λ = 2 ^ (-n)` is the unique choice with
`λ ^ 2 * 2 ^ n ≤ λ`, and that identity is exactly what makes the loss in Gelfond's inequality
reproduce itself along a factorization instead of accumulating. -/
private theorem exists_irreducible_factor_aux {w δ : ℝ} (hw : 0 ≤ w) (hδ : 0 ≤ δ) :
    ∀ d : ℕ, ∀ P : ℤ[X], P.natDegree = d → 1 ≤ d → P.natDegree ≤ n → P.IsPrimitive →
      aeval ξ P ≠ 0 →
      |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * P.supNorm) ^ w) < δ ^ d →
      ∃ Q : ℤ[X], Q ∣ P ∧ Irreducible Q ∧
        |aeval ξ Q| * ((((2 : ℝ) ^ n)⁻¹ * Q.supNorm) ^ w) < δ ^ Q.natDegree := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P hdP hd1 hdeg hprim hval hstar
    by_cases hirr : Irreducible P
    · exact ⟨P, dvd_rfl, hirr, by rw [hdP]; exact hstar⟩
    have hP0 : P ≠ 0 := fun h ↦ hval (by rw [h]; simp)
    have hPu : ¬ IsUnit P := by
      intro hu
      have hd0 : P.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    obtain ⟨A, B, hPAB, hAu, hBu⟩ : ∃ A B : ℤ[X], P = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
      rw [irreducible_iff] at hirr
      push Not at hirr
      obtain ⟨A, B, hPAB, hAu, hBu⟩ := hirr hPu
      exact ⟨A, B, hPAB, hAu, hBu⟩
    have hA0 : A ≠ 0 := fun h ↦ hP0 (by rw [hPAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h ↦ hP0 (by rw [hPAB, h, mul_zero])
    have hAdvd : A ∣ P := ⟨B, hPAB⟩
    have hBdvd : B ∣ P := ⟨A, by rw [hPAB, mul_comm]⟩
    have hAprim : A.IsPrimitive := Polynomial.IsPrimitive.of_dvd hAdvd hprim
    have hBprim : B.IsPrimitive := Polynomial.IsPrimitive.of_dvd hBdvd hprim
    have hA1 : 1 ≤ A.natDegree :=
      Polynomial.one_le_natDegree_of_not_isUnit_of_dvd hAdvd hprim hAu
    have hB1 : 1 ≤ B.natDegree :=
      Polynomial.one_le_natDegree_of_not_isUnit_of_dvd hBdvd hprim hBu
    have hsum : A.natDegree + B.natDegree = d := by
      rw [← hdP, hPAB, Polynomial.natDegree_mul hA0 hB0]
    have hvalA : aeval ξ A ≠ 0 := fun h ↦ hval (by rw [hPAB, map_mul, h, zero_mul])
    have hvalB : aeval ξ B ≠ 0 := fun h ↦ hval (by rw [hPAB, map_mul, h, mul_zero])
    -- one of the two factors inherits the hypothesis
    have hkey : |aeval ξ A| * ((((2 : ℝ) ^ n)⁻¹ * A.supNorm) ^ w) < δ ^ A.natDegree ∨
        |aeval ξ B| * ((((2 : ℝ) ^ n)⁻¹ * B.supNorm) ^ w) < δ ^ B.natDegree := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hA, hB⟩ := hcon
      have hAn : (1 : ℝ) ≤ A.supNorm := Polynomial.one_le_supNorm hA0
      have hBn : (1 : ℝ) ≤ B.supNorm := Polynomial.one_le_supNorm hB0
      have hPn : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
      have hL0 : (0 : ℝ) < (((2 : ℝ) ^ n)⁻¹) := by positivity
      have hgel : A.supNorm * B.supNorm
          ≤ 2 ^ (A.natDegree + B.natDegree) * P.supNorm := by
        rw [hPAB]
        exact Polynomial.supNorm_mul_supNorm_le_two_pow_int A B
      have hstep : δ ^ d ≤ |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * P.supNorm) ^ w) := by
        calc δ ^ d = δ ^ A.natDegree * δ ^ B.natDegree := by rw [← pow_add, hsum]
          _ ≤ (|aeval ξ A| * ((((2 : ℝ) ^ n)⁻¹ * A.supNorm) ^ w))
                * (|aeval ξ B| * ((((2 : ℝ) ^ n)⁻¹ * B.supNorm) ^ w)) := by
              exact mul_le_mul hA hB (pow_nonneg hδ _) (by positivity)
          _ = |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * A.supNorm) ^ w
                * (((2 : ℝ) ^ n)⁻¹ * B.supNorm) ^ w) := by
              rw [hPAB, map_mul, abs_mul]; ring
          _ ≤ |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * P.supNorm) ^ w) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              refine Real.rpow_le_rpow (by positivity) ?_ hw
              have hle : ((2 : ℝ) ^ n)⁻¹ * A.supNorm * (((2 : ℝ) ^ n)⁻¹ * B.supNorm)
                  = ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * (A.supNorm * B.supNorm)) := by ring
              rw [hle]
              have h2 : (A.supNorm * B.supNorm) ≤ 2 ^ n * P.supNorm := by
                refine hgel.trans ?_
                gcongr
                · norm_num
                · omega
              calc ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * (A.supNorm * B.supNorm))
                  ≤ ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * (2 ^ n * P.supNorm)) := by gcongr
                _ = ((2 : ℝ) ^ n)⁻¹ * P.supNorm := by field_simp
      exact absurd hstar (not_lt.2 hstep)
    rcases hkey with hk | hk
    · obtain ⟨Q, hQA, hQirr, hQstar⟩ :=
        ih A.natDegree (by omega) A rfl hA1 (by omega) hAprim hvalA hk
      exact ⟨Q, hQA.trans hAdvd, hQirr, hQstar⟩
    · obtain ⟨Q, hQB, hQirr, hQstar⟩ :=
        ih B.natDegree (by omega) B rfl hB1 (by omega) hBprim hvalB hk
      exact ⟨Q, hQB.trans hBdvd, hQirr, hQstar⟩

/-- **Restricting to irreducible polynomials does not change Mahler's exponent.** Unlike the
restriction to primitive polynomials, this one is a theorem with content: the *whole* solution
`P` is replaced by one of its irreducible factors, and nothing says that a factor of a small value
is small. What makes it work is Gelfond's inequality, `ArithmeticHeights` 2.3, which bounds the
product of the heights of the factors by the height of the product — so the factors cannot all be
bad at once — together with the height gap, which turns the small value of the surviving factor
into a large height. -/
theorem mahlerExponent_eq_iSup_irreducible (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ
      = ⨆ (w : ℝ≥0) (_ : {P ∈ mahlerSet n ξ (w : ℝ) | Irreducible P}.Infinite), (w : ℝ≥0∞) := by
  refine le_antisymm (mahlerExponent_le_iff.2 fun w hw ↦ ?_)
    (iSup₂_le fun w hw ↦ le_mahlerExponent (Set.Infinite.mono (fun _ hP ↦ hP.1) hw))
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  lift c to ℝ≥0 using ne_top_of_lt hc
  have hcw : (c : ℝ) < (w : ℝ) := by exact_mod_cast hc
  rcases eq_or_ne c 0 with h0 | h0
  · simp [h0]
  have hc0 : (0 : ℝ) < (c : ℝ) := c.coe_nonneg.lt_of_ne' fun h ↦ h0 (NNReal.coe_eq_zero.1 h)
  have hw0 : (0 : ℝ) < (w : ℝ) := hc0.trans hcw
  refine le_iSup₂ (f := fun (w : ℝ≥0)
    (_ : {P ∈ mahlerSet n ξ (w : ℝ) | Irreducible P}.Infinite) ↦ (w : ℝ≥0∞)) c ?_
  refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ n B
  have hΛ1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hΛ0 : (0 : ℝ) < (2 : ℝ) ^ n := zero_lt_one.trans_le hΛ1
  have hΛc0 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ (-(c : ℝ)) := Real.rpow_pos_of_pos hΛ0 _
  have hΛc1 : ((2 : ℝ) ^ n) ^ (-(c : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by linarith)
  set δ : ℝ := min δ₀ 1 * ((2 : ℝ) ^ n) ^ (-(c : ℝ)) with hδdef
  have hm0 : (0 : ℝ) < min δ₀ 1 := lt_min hδ₀0 zero_lt_one
  have hδ0 : 0 < δ := mul_pos hm0 hΛc0
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    calc min δ₀ 1 * ((2 : ℝ) ^ n) ^ (-(c : ℝ)) ≤ 1 * 1 :=
          mul_le_mul (min_le_right _ _) hΛc1 hΛc0.le zero_le_one
      _ = 1 := one_mul 1
  have hδΛ : δ * ((2 : ℝ) ^ n) ^ (c : ℝ) = min δ₀ 1 := by
    rw [hδdef, mul_assoc, ← Real.rpow_add hΛ0, neg_add_cancel, Real.rpow_zero, mul_one]
  -- the value of `(Λ⁻¹ * H) ^ c`
  have hpow : ∀ H : ℝ, 0 ≤ H →
      (((2 : ℝ) ^ n)⁻¹ * H) ^ (c : ℝ) = ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * H ^ (c : ℝ) := fun H hH ↦ by
    rw [Real.mul_rpow (by positivity) hH, Real.inv_rpow hΛ0.le, ← Real.rpow_neg hΛ0.le]
  -- a primitive solution of large height
  obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm
    (infinite_primitive_mahlerSet hw0 hw) (fun _ hP ↦ hP.1.1)
    (max 1 ((δ ^ n * ((2 : ℝ) ^ n) ^ (c : ℝ))⁻¹ ^ ((w : ℝ) - c)⁻¹))).nonempty
  obtain ⟨⟨hdeg, hpos, hle⟩, hprim⟩ := hPmem
  have hP0 : P ≠ 0 := ne_zero_of_mem_mahlerSet ⟨hdeg, hpos, hle⟩
  have hH1 : (1 : ℝ) < P.supNorm := lt_of_le_of_lt (le_max_left _ _) hPh
  have hH0 : (0 : ℝ) < P.supNorm := zero_lt_one.trans hH1
  have hd1 : 1 ≤ P.natDegree := by
    by_contra h
    obtain ⟨r, hr⟩ := (Polynomial.natDegree_eq_zero (p := P)).1 (by omega)
    have hru : IsUnit r := hprim r ⟨1, by rw [mul_one, hr]⟩
    rcases Int.isUnit_iff.1 hru with hu | hu <;>
      · rw [← hr, hu, Polynomial.supNorm_C] at hH1
        simp at hH1
  -- the hypothesis of the extraction
  have hstar : |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * P.supNorm) ^ (c : ℝ)) < δ ^ P.natDegree := by
    have hkey : ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * P.supNorm ^ (-((w : ℝ) - c)) < δ ^ n := by
      have h1 : P.supNorm ^ (-((w : ℝ) - c)) < δ ^ n * ((2 : ℝ) ^ n) ^ (c : ℝ) :=
        Real.rpow_neg_lt_of_max_lt (by linarith) (by positivity) hPh
      calc ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * P.supNorm ^ (-((w : ℝ) - c))
          < ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * (δ ^ n * ((2 : ℝ) ^ n) ^ (c : ℝ)) := by gcongr
        _ = δ ^ n := by
            rw [← mul_assoc, mul_comm (((2 : ℝ) ^ n) ^ (-(c : ℝ))) (δ ^ n), mul_assoc,
              ← Real.rpow_add hΛ0, neg_add_cancel, Real.rpow_zero, mul_one]
    calc |aeval ξ P| * ((((2 : ℝ) ^ n)⁻¹ * P.supNorm) ^ (c : ℝ))
        = |aeval ξ P| * (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * P.supNorm ^ (c : ℝ)) := by
          rw [hpow _ hH0.le]
      _ ≤ P.supNorm ^ (-(w : ℝ)) * (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * P.supNorm ^ (c : ℝ)) := by
          gcongr
      _ = ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * P.supNorm ^ (-((w : ℝ) - c)) := by
          rw [show -((w : ℝ) - c) = -(w : ℝ) + (c : ℝ) by ring, Real.rpow_add hH0]
          ring
      _ < δ ^ n := hkey
      _ ≤ δ ^ P.natDegree := pow_le_pow_of_le_one hδ0.le hδ1 hdeg
  obtain ⟨Q, hQP, hQirr, hQstar⟩ :=
    exists_irreducible_factor_aux hc0.le hδ0.le P.natDegree P rfl hd1 hdeg hprim
      (fun h ↦ by rw [h] at hpos; simp at hpos) hstar
  -- read the two conditions off the extraction
  have hQdeg : Q.natDegree ≤ n := (Polynomial.natDegree_le_of_dvd hQP hP0).trans hdeg
  have hQ1 : 1 ≤ Q.natDegree :=
    Polynomial.one_le_natDegree_of_irreducible_dvd hQP hprim hQirr
  have hQval : aeval ξ Q ≠ 0 := by
    obtain ⟨R, hR⟩ := hQP
    intro h
    rw [hR, map_mul, h, zero_mul] at hpos
    simp at hpos
  have hQ0 : Q ≠ 0 := hQirr.ne_zero
  have hQH1 : (1 : ℝ) ≤ Q.supNorm := Polynomial.one_le_supNorm hQ0
  have hQH0 : (0 : ℝ) < Q.supNorm := zero_lt_one.trans_le hQH1
  have hQc0 : (0 : ℝ) < Q.supNorm ^ (-(c : ℝ)) := Real.rpow_pos_of_pos hQH0 _
  have hQc1 : Q.supNorm ^ (-(c : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQH1 (by linarith)
  have hQkey : |aeval ξ Q| < min δ₀ 1 * Q.supNorm ^ (-(c : ℝ)) := by
    have h1 : |aeval ξ Q| * (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * Q.supNorm ^ (c : ℝ)) < δ := by
      rw [← hpow _ hQH0.le]
      exact lt_of_lt_of_le hQstar
        ((pow_le_pow_of_le_one hδ0.le hδ1 hQ1).trans_eq (pow_one δ))
    have e1 : ((2 : ℝ) ^ n) ^ (-(c : ℝ)) * ((2 : ℝ) ^ n) ^ ((c : ℝ)) = 1 := by
      rw [← Real.rpow_add hΛ0, neg_add_cancel, Real.rpow_zero]
    have e2 : Q.supNorm ^ (c : ℝ) * Q.supNorm ^ (-(c : ℝ)) = 1 := by
      rw [← Real.rpow_add hQH0, add_neg_cancel, Real.rpow_zero]
    have hfac : (0 : ℝ) < ((2 : ℝ) ^ n) ^ ((c : ℝ)) * Q.supNorm ^ (-(c : ℝ)) := by positivity
    have h2 := mul_lt_mul_of_pos_right h1 hfac
    rw [← hδΛ]
    calc |aeval ξ Q|
        = |aeval ξ Q| * (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * Q.supNorm ^ (c : ℝ))
            * (((2 : ℝ) ^ n) ^ ((c : ℝ)) * Q.supNorm ^ (-(c : ℝ))) := by
          rw [mul_assoc, show (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * Q.supNorm ^ (c : ℝ))
              * (((2 : ℝ) ^ n) ^ ((c : ℝ)) * Q.supNorm ^ (-(c : ℝ)))
              = (((2 : ℝ) ^ n) ^ (-(c : ℝ)) * ((2 : ℝ) ^ n) ^ ((c : ℝ)))
                * (Q.supNorm ^ (c : ℝ) * Q.supNorm ^ (-(c : ℝ))) by ring, e1, e2, mul_one, mul_one]
      _ < δ * (((2 : ℝ) ^ n) ^ ((c : ℝ)) * Q.supNorm ^ (-(c : ℝ))) := h2
      _ = δ * ((2 : ℝ) ^ n) ^ ((c : ℝ)) * Q.supNorm ^ (-(c : ℝ)) := by ring
  refine ⟨Q, ⟨⟨hQdeg, abs_pos.2 hQval, ?_⟩, hQirr⟩, ?_⟩
  · refine hQkey.le.trans ?_
    calc min δ₀ 1 * Q.supNorm ^ (-(c : ℝ)) ≤ 1 * Q.supNorm ^ (-(c : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hQc0.le
      _ = Q.supNorm ^ (-(c : ℝ)) := one_mul _
  · refine hδ₀ Q hQdeg (abs_pos.2 hQval) (hQkey.trans_le ?_)
    calc min δ₀ 1 * Q.supNorm ^ (-(c : ℝ)) ≤ δ₀ * 1 :=
          mul_le_mul (min_le_left _ _) hQc1 hQc0.le hδ₀0.le
      _ = δ₀ := mul_one _

end Real

/-! ### Acceptance criteria -/

section Examples

/-- **Gelfond's inequality bounds a factor.** This is the form the extraction uses: a factor of
an integer polynomial is at most `2 ^ deg` times as tall as what it divides. -/
example (P Q : ℤ[X]) (hQ : Q ≠ 0) :
    P.supNorm ≤ 2 ^ (P.natDegree + Q.natDegree) * (P * Q).supNorm := by
  refine le_trans ?_ (Polynomial.supNorm_mul_supNorm_le_two_pow_int P Q)
  nlinarith [Polynomial.one_le_supNorm hQ, Polynomial.supNorm_nonneg P]

/-- **Rejection test: the constant in Gelfond's inequality cannot be dropped.** The product of
the naive heights of two factors can exceed the naive height of the product:
`(2 X + 1) (X − 2) = 2 X² − 3 X − 2` has height `3`, while both factors have height `2`. -/
example : ¬ ∀ P Q : ℤ[X], P.supNorm * Q.supNorm ≤ (P * Q).supNorm := by
  intro h
  have hprod : ((C 2 * X + C 1) * (C 1 * X + C (-2)) : ℤ[X])
      = C 2 * X ^ 2 + C (-3) * X + C (-2) := by
    simp only [map_neg, map_ofNat, map_one]
    ring
  have hub : ∀ i : ℕ, ‖((C 2 * X + C 1) * (C 1 * X + C (-2)) : ℤ[X]).coeff i‖ ≤ 3 := by
    intro i
    rw [hprod, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    rcases i with _ | _ | _ | i <;> norm_num [Int.norm_eq_abs]
  have h2 := Polynomial.supNorm_le_of_forall hub
  have h1 := h (C 2 * X + C 1) (C 1 * X + C (-2))
  rw [Polynomial.supNorm_linear, Polynomial.supNorm_linear,
    show max |((2 : ℤ) : ℝ)| |((1 : ℤ) : ℝ)| * max |((1 : ℤ) : ℝ)| |((-2 : ℤ) : ℝ)| = 4 by
      norm_num] at h1
  linarith

end Examples
