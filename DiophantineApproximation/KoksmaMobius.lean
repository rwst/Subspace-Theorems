/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IrreducibleExponent

-- Used only inside proofs.
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Möbius invariance of Koksma's exponent

`Real.mahlerExponent` is invariant under the rational Möbius group for a reason that stays inside
`DiophantineApproximation/MahlerExponent.lean`: a solution is a polynomial, a Möbius map acts on
polynomials by substitution, and substitution moves the naive height by a bounded factor.
`Real.koksmaExponent` is invariant for a reason that does not: a solution is the **minimal
polynomial of an approximant**, and the transform of a minimal polynomial is neither primitive nor
irreducible.

The fix is not to transport irreducibility but to *extract* it. The transform `R` of a minimal
polynomial has the transformed approximant among its roots; its primitive part has an irreducible
factor with the same root, and that factor is the minimal polynomial wanted. The price is that the
height must now be controlled **downwards** — a factor must not be much taller than what it
divides — and that is Gelfond's inequality again. So Gelfond, which on Mahler's side is needed
only for the optional restriction to irreducible polynomials, is on Koksma's side a prerequisite
for the Möbius invariance itself.

## Main results

* `Real.exists_mem_koksmaSet_of_root`: **from any integer polynomial with a good root to a Koksma
  approximant**, at the cost of the constant `2 ^ n` in the exponent.
* `Real.koksmaExponent_le_intAffine` and `Real.koksmaExponent_le_inv`: the two generators, by
  `Polynomial.scaleRoots` followed by a substitution, and by `Polynomial.reflect`.
* `Real.koksmaExponent_inv`, `Real.koksmaExponent_add_intCast`,
  `Real.koksmaExponent_intCast_mul`, `Real.koksmaExponent_div_intCast`,
  `Real.koksmaExponent_mul_ratCast`, `Real.koksmaExponent_add_ratCast`: the group they generate.
* `Real.koksmaExponent_mobius`: **Koksma's exponent is invariant under the rational Möbius
  group.**
* `Polynomial.supNorm_scaleRoots_le`: scaling the roots by an integer multiplies the naive height
  by at most `max 1 |t| ^ n`.

## Implementation notes

⚠ **The generators point the other way.** On Mahler's side the transform carries a solution *at
the image* back to a solution *at the source*, so the generator reads `E (T ξ) ≤ E ξ`; on
Koksma's side it carries an approximant of `ξ` forward to an approximant of `T ξ`, so it reads
`E ξ ≤ E (T ξ)`. Both assemble into the same group, because both generating families are closed
under inverses once inversion is available.

⚠ **Inversion needs the approximants bounded away from `0`, and that is not free.** The distance
is distorted by `(|ξ| * |α|)⁻¹`, so a lower bound on `|α|` is needed; it comes from `|ξ - α|`
being small, which is only true once the height is large, so the threshold on the height of the
source polynomial carries two conditions instead of one. The affine generator needs no such care.

⚠ **The infinitude is again a gap lemma, but a different one.** On Mahler's side the surviving
object is judged by its *value* at `ξ` and the gap is
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`. Here it is judged by the distance from `ξ` to
one of its *roots*, and the corresponding statement,
`Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`, is Northcott plus the finiteness of the
real roots of finitely many polynomials.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1 and
Lemma A.5.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/

public section

open Polynomial
open scoped ENNReal NNReal

namespace Polynomial

/-- Scaling the roots by an integer multiplies the naive height by at most `max 1 |t| ^ n`. -/
theorem supNorm_scaleRoots_le {P : ℤ[X]} {t : ℤ} {n : ℕ} (hP : P.natDegree ≤ n) :
    (P.scaleRoots t).supNorm ≤ max 1 |(t : ℝ)| ^ n * P.supNorm := by
  obtain ⟨i, hi⟩ := (P.scaleRoots t).exists_eq_supNorm
  rw [hi, coeff_scaleRoots, norm_mul, norm_pow, Int.norm_eq_abs, Int.norm_eq_abs]
  have h1 : |(t : ℝ)| ^ (P.natDegree - i) ≤ max 1 |(t : ℝ)| ^ n := by
    calc |(t : ℝ)| ^ (P.natDegree - i) ≤ max 1 |(t : ℝ)| ^ (P.natDegree - i) :=
          pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
      _ ≤ max 1 |(t : ℝ)| ^ n := by
          refine pow_le_pow_right₀ (le_max_left _ _) ?_
          omega
  calc |((P.coeff i : ℤ) : ℝ)| * |(t : ℝ)| ^ (P.natDegree - i)
      ≤ P.supNorm * (max 1 |(t : ℝ)| ^ n) := by
        refine mul_le_mul (abs_coeff_le_supNorm P i) h1 (by positivity) (supNorm_nonneg _)
    _ = max 1 |(t : ℝ)| ^ n * P.supNorm := by ring

end Polynomial

namespace Real

variable {n : ℕ}

/-- **From any integer polynomial with a good root to a Koksma approximant.** The polynomial that
a Möbius map produces from a minimal polynomial is neither primitive nor irreducible; its
primitive part has an irreducible factor with the same root, and that factor is a legitimate
Koksma approximant of the same order. The height is controlled *downwards* by Gelfond's
inequality, `ArithmeticHeights` 2.3 in its integer form — a factor cannot be much taller than what
it divides — and that costs the constant `2 ^ n` in the exponent `-v - 1`. -/
theorem exists_mem_koksmaSet_of_root {η : ℝ} {R : ℤ[X]} {β : ℝ} {v A : ℝ}
    (hv : 0 ≤ v) (hA : 0 < A) (hdeg : R.natDegree ≤ n) (hR0 : R ≠ 0) (hroot : aeval β R = 0)
    (hbnd : |η - β| ≤ A * R.supNorm ^ (-v - 1)) :
    ∃ Q : ℤ[X], Q.natDegree ≤ n ∧ Q.IsPrimitive ∧ Irreducible Q ∧ aeval β Q = 0 ∧
      |η - β| ≤ (A * ((2 : ℝ) ^ n) ^ (v + 1)) * Q.supNorm ^ (-v - 1) := by
  have hRc : R.content ≠ 0 := fun h ↦ hR0 (Polynomial.content_eq_zero_iff.1 h)
  have hRS : R = C R.content * R.primPart := Polynomial.eq_C_content_mul_primPart R
  have hS0 : R.primPart ≠ 0 := Polynomial.primPart_ne_zero R
  have hSprim : R.primPart.IsPrimitive := Polynomial.isPrimitive_primPart R
  have hSdeg : R.primPart.natDegree ≤ n := by rw [Polynomial.natDegree_primPart]; exact hdeg
  have hSroot : aeval β R.primPart = 0 := by
    have h := hroot
    conv_lhs at h => rw [hRS]
    rw [map_mul] at h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd (by simpa using h1) (by exact_mod_cast hRc : ((R.content : ℤ) : ℝ) ≠ 0)
    · exact h1
  have hcR : (1 : ℝ) ≤ |((R.content : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hRc
  have hSnorm : R.primPart.supNorm ≤ R.supNorm := by
    conv_rhs => rw [hRS]
    rw [Polynomial.supNorm_C_mul, Int.norm_eq_abs]
    nlinarith [Polynomial.supNorm_nonneg R.primPart]
  obtain ⟨Q, hQS, hQirr, hQroot⟩ :=
    Polynomial.exists_irreducible_dvd_aeval_eq_zero R.primPart.natDegree R.primPart rfl hSprim
      hSroot
  obtain ⟨Q', hQ'⟩ := hQS
  have hQ0 : Q ≠ 0 := hQirr.ne_zero
  have hQ'0 : Q' ≠ 0 := fun h ↦ hS0 (by rw [hQ', h, mul_zero])
  have hQdeg : Q.natDegree ≤ n :=
    (Polynomial.natDegree_le_of_dvd ⟨Q', hQ'⟩ hS0).trans hSdeg
  have hQ'1 : (1 : ℝ) ≤ Q'.supNorm := Polynomial.one_le_supNorm hQ'0
  have hQ1 : (1 : ℝ) ≤ Q.supNorm := Polynomial.one_le_supNorm hQ0
  have hQ0' : (0 : ℝ) < Q.supNorm := zero_lt_one.trans_le hQ1
  have hR1 : (1 : ℝ) ≤ R.supNorm := Polynomial.one_le_supNorm hR0
  have hR0' : (0 : ℝ) < R.supNorm := zero_lt_one.trans_le hR1
  -- Gelfond: the factor is not much taller than the product
  have hQnorm : Q.supNorm ≤ (2 : ℝ) ^ n * R.supNorm := by
    have hgel := Polynomial.supNorm_mul_supNorm_le_two_pow_int Q Q'
    rw [← hQ'] at hgel
    have hdsum : Q.natDegree + Q'.natDegree = R.primPart.natDegree := by
      rw [hQ', Polynomial.natDegree_mul hQ0 hQ'0]
    have h2 : (2 : ℝ) ^ (Q.natDegree + Q'.natDegree) ≤ 2 ^ n := by
      refine pow_le_pow_right₀ (by norm_num) ?_
      omega
    calc Q.supNorm ≤ Q.supNorm * Q'.supNorm := by nlinarith
      _ ≤ 2 ^ (Q.natDegree + Q'.natDegree) * R.primPart.supNorm := hgel
      _ ≤ (2 : ℝ) ^ n * R.supNorm := by
          refine mul_le_mul h2 hSnorm (Polynomial.supNorm_nonneg _) (by positivity)
  refine ⟨Q, hQdeg, Polynomial.IsPrimitive.of_dvd ⟨Q', hQ'⟩ hSprim, hQirr, hQroot,
    hbnd.trans ?_⟩
  -- transport the height
  have hkey : R.supNorm ^ (-v - 1) ≤ ((2 : ℝ) ^ n) ^ (v + 1) * Q.supNorm ^ (-v - 1) := by
    rw [show -v - 1 = -(v + 1) by ring]
    exact Real.rpow_neg_le_mul_rpow_neg (by linarith) hR0' hQ0' (by positivity) hQnorm
  calc A * R.supNorm ^ (-v - 1) ≤ A * (((2 : ℝ) ^ n) ^ (v + 1) * Q.supNorm ^ (-v - 1)) :=
        mul_le_mul_of_nonneg_left hkey hA.le
    _ = A * ((2 : ℝ) ^ n) ^ (v + 1) * Q.supNorm ^ (-v - 1) := by ring

/-! ### The two generators -/

/-- **An integer affine map does not lower Koksma's exponent.** The approximant `α` is carried to
`t α + s` by `Polynomial.scaleRoots` followed by a substitution `X ↦ X - s`, both of which raise
the naive height by at most a constant. -/
theorem koksmaExponent_le_intAffine (n : ℕ) (ξ : ℝ) {t : ℤ} (ht : t ≠ 0) (s : ℤ) :
    koksmaExponent n ξ ≤ koksmaExponent n ((t : ℝ) * ξ + s) := by
  refine koksmaExponent_le_iff.2 fun w hw ↦ ?_
  rcases eq_or_ne w 0 with h0 | h0
  · simp [h0]
  have hw0 : (0 : ℝ) < (w : ℝ) := w.coe_nonneg.lt_of_ne' fun h ↦ h0 (NNReal.coe_eq_zero.1 h)
  have htR : (0 : ℝ) < |(t : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 ht)
  have hC₁1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), ((X - C s : ℤ[X]) ^ i).supNorm :=
    Polynomial.one_le_sum_supNorm_pow _ n
  have htn : (1 : ℝ) ≤ max 1 |(t : ℝ)| ^ n := one_le_pow₀ (le_max_left _ _)
  set K : ℝ := (∑ i ∈ Finset.range (n + 1), ((X - C s : ℤ[X]) ^ i).supNorm)
    * max 1 |(t : ℝ)| ^ n with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; nlinarith
  have hK0 : (0 : ℝ) < K := zero_lt_one.trans_le hK1
  have hA0 : (0 : ℝ) < |(t : ℝ)| * K ^ ((w : ℝ) + 1) := by positivity
  have hmain : ENNReal.ofReal (w : ℝ) ≤ koksmaExponent n ((t : ℝ) * ξ + s) := by
    refine le_koksmaExponent_of_infinite
      (A := |(t : ℝ)| * K ^ ((w : ℝ) + 1) * ((2 : ℝ) ^ n) ^ ((w : ℝ) + 1)) (by positivity) ?_
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨δ, hδ0, hδ⟩ :=
      Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt ((t : ℝ) * ξ + s) n B
    obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
      (max 1 ((δ / |(t : ℝ)|)⁻¹ ^ ((w : ℝ) + 1)⁻¹))).nonempty
    obtain ⟨hdeg, hprim, hirr, α, hα, hpos, hle⟩ := hPmem
    have hP0 : P ≠ 0 := hirr.ne_zero
    have hPH1 : (1 : ℝ) < P.supNorm := lt_of_le_of_lt (le_max_left _ _) hPh
    have hPH0 : (0 : ℝ) < P.supNorm := zero_lt_one.trans hPH1
    have hRdeg : ((P.scaleRoots t).comp (X - C s)).natDegree ≤ n := by
      refine natDegree_comp_le.trans ?_
      rw [Polynomial.natDegree_scaleRoots, Polynomial.natDegree_X_sub_C, mul_one]
      exact hdeg
    have hR0 : (P.scaleRoots t).comp (X - C s) ≠ 0 := by
      intro h
      refine Polynomial.scaleRoots_ne_zero hP0 t ?_
      have h2 := congrArg (fun p : ℤ[X] ↦ p.comp (X + C s)) h
      simp only [Polynomial.zero_comp] at h2
      rwa [Polynomial.comp_assoc, show ((X - C s : ℤ[X]).comp (X + C s)) = X by simp,
        Polynomial.comp_X] at h2
    have hRroot : aeval ((t : ℝ) * α + s) ((P.scaleRoots t).comp (X - C s)) = 0 := by
      rw [Polynomial.aeval_comp, show aeval ((t : ℝ) * α + s) (X - C s : ℤ[X]) = (t : ℝ) * α by
        simp]
      simpa using Polynomial.scaleRoots_aeval_eq_zero (A := ℝ) (p := P) (a := α) (r := t) hα
    have hRnorm : ((P.scaleRoots t).comp (X - C s)).supNorm ≤ K * P.supNorm := by
      have h1 : (P.scaleRoots t).natDegree ≤ n := by
        rw [Polynomial.natDegree_scaleRoots]; exact hdeg
      calc ((P.scaleRoots t).comp (X - C s)).supNorm
          ≤ (∑ i ∈ Finset.range (n + 1), ((X - C s : ℤ[X]) ^ i).supNorm)
              * (P.scaleRoots t).supNorm := Polynomial.supNorm_comp_le h1
        _ ≤ (∑ i ∈ Finset.range (n + 1), ((X - C s : ℤ[X]) ^ i).supNorm)
              * (max 1 |(t : ℝ)| ^ n * P.supNorm) :=
            mul_le_mul_of_nonneg_left (Polynomial.supNorm_scaleRoots_le hdeg) (by linarith)
        _ = K * P.supNorm := by rw [hKdef]; ring
    have hdist : |((t : ℝ) * ξ + s) - ((t : ℝ) * α + s)| = |(t : ℝ)| * |ξ - α| := by
      rw [show (t : ℝ) * ξ + (s : ℝ) - ((t : ℝ) * α + (s : ℝ)) = (t : ℝ) * (ξ - α) by ring,
        abs_mul]
    have hRH0 : (0 : ℝ) < ((P.scaleRoots t).comp (X - C s)).supNorm :=
      Polynomial.supNorm_pos hR0
    have hbnd : |((t : ℝ) * ξ + s) - ((t : ℝ) * α + s)|
        ≤ |(t : ℝ)| * K ^ ((w : ℝ) + 1)
            * ((P.scaleRoots t).comp (X - C s)).supNorm ^ (-(w : ℝ) - 1) := by
      rw [hdist]
      calc |(t : ℝ)| * |ξ - α| ≤ |(t : ℝ)| * P.supNorm ^ (-(w : ℝ) - 1) := by gcongr
        _ ≤ |(t : ℝ)| * (K ^ ((w : ℝ) + 1)
              * ((P.scaleRoots t).comp (X - C s)).supNorm ^ (-(w : ℝ) - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ htR.le
            rw [show -(w : ℝ) - 1 = -((w : ℝ) + 1) by ring]
            exact Real.rpow_neg_le_mul_rpow_neg (by linarith) hPH0 hRH0 hK0 hRnorm
        _ = _ := by ring
    obtain ⟨Q, hQdeg, hQprim, hQirr, hQroot, hQbnd⟩ :=
      exists_mem_koksmaSet_of_root w.coe_nonneg hA0 hRdeg hR0 hRroot hbnd
    have hdpos : 0 < |((t : ℝ) * ξ + s) - ((t : ℝ) * α + s)| := by
      rw [hdist]; positivity
    refine ⟨Q, ⟨hQdeg, hQprim, hQirr, (t : ℝ) * α + s, hQroot, hdpos, hQbnd⟩, ?_⟩
    refine hδ Q ((t : ℝ) * α + s) hQdeg hQirr.ne_zero hQroot hdpos ?_
    rw [hdist]
    have hsmall : P.supNorm ^ (-((w : ℝ) + 1)) < δ / |(t : ℝ)| :=
      Real.rpow_neg_lt_of_max_lt (by linarith) (by positivity) hPh
    rw [show -(w : ℝ) - 1 = -((w : ℝ) + 1) by ring] at hle
    calc |(t : ℝ)| * |ξ - α| ≤ |(t : ℝ)| * P.supNorm ^ (-((w : ℝ) + 1)) := by gcongr
      _ < |(t : ℝ)| * (δ / |(t : ℝ)|) := by gcongr
      _ = δ := by field_simp
  rwa [ENNReal.ofReal_coe_nnreal] at hmain

/-- **Inversion does not lower Koksma's exponent.** The approximant `α` is carried to `α⁻¹` by
`Polynomial.reflect`, which permutes the coefficients and so preserves the naive height *exactly*;
the distance is distorted by the bounded factor `(|ξ| * |α|)⁻¹`, and `α` is bounded away from `0`
because it is close to `ξ`. -/
theorem koksmaExponent_le_inv (n : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    koksmaExponent n ξ ≤ koksmaExponent n ξ⁻¹ := by
  refine koksmaExponent_le_iff.2 fun w hw ↦ ?_
  rcases eq_or_ne w 0 with h0 | h0
  · simp [h0]
  have hw0 : (0 : ℝ) < (w : ℝ) := w.coe_nonneg.lt_of_ne' fun h ↦ h0 (NNReal.coe_eq_zero.1 h)
  have hξ0 : (0 : ℝ) < |ξ| := abs_pos.2 hξ
  have hmain : ENNReal.ofReal (w : ℝ) ≤ koksmaExponent n ξ⁻¹ := by
    refine le_koksmaExponent_of_infinite
      (A := 2 / |ξ| ^ 2 * ((2 : ℝ) ^ n) ^ ((w : ℝ) + 1)) (by positivity) ?_
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨δ, hδ0, hδ⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt ξ⁻¹ n B
    obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
      (max 1 ((min (|ξ| / 2) (δ * |ξ| ^ 2 / 2))⁻¹ ^ ((w : ℝ) + 1)⁻¹))).nonempty
    obtain ⟨hdeg, hprim, hirr, α, hα, hpos, hle⟩ := hPmem
    have hP0 : P ≠ 0 := hirr.ne_zero
    have hPH1 : (1 : ℝ) < P.supNorm := lt_of_le_of_lt (le_max_left _ _) hPh
    have hPH0 : (0 : ℝ) < P.supNorm := zero_lt_one.trans hPH1
    rw [show -(w : ℝ) - 1 = -((w : ℝ) + 1) by ring] at hle
    have hsmall : P.supNorm ^ (-((w : ℝ) + 1)) < min (|ξ| / 2) (δ * |ξ| ^ 2 / 2) :=
      Real.rpow_neg_lt_of_max_lt (by linarith) (by positivity) hPh
    have hclose : |ξ - α| < |ξ| / 2 := lt_of_le_of_lt hle (lt_of_lt_of_le hsmall (min_le_left _ _))
    have hα2 : |ξ| / 2 < |α| := by
      have h1 := abs_sub_abs_le_abs_sub ξ α
      linarith
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, abs_zero] at hα2
      linarith
    have : Invertible α := invertibleOfNonzero hα0
    have hinvOf : (⅟α : ℝ) = α⁻¹ := invOf_eq_inv α
    -- the reversed polynomial
    have hRdeg : (P.reflect P.natDegree).natDegree ≤ n :=
      Polynomial.natDegree_reflect_le.trans (by rw [max_self]; exact hdeg)
    have hR0 : P.reflect P.natDegree ≠ 0 := by
      intro h
      exact hP0 (Polynomial.reverse_eq_zero.1 h)
    have hRroot : aeval α⁻¹ (P.reflect P.natDegree) = 0 := by
      have h := (Polynomial.eval₂_reflect_eq_zero_iff (algebraMap ℤ ℝ) α P.natDegree P
        le_rfl).2 (by rw [← aeval_def]; exact hα)
      rw [hinvOf, ← aeval_def] at h
      exact h
    have hRnorm : (P.reflect P.natDegree).supNorm = P.supNorm :=
      Polynomial.supNorm_reflect _ P
    have hdist : |ξ⁻¹ - α⁻¹| = |ξ - α| / (|ξ| * |α|) := by
      rw [show ξ⁻¹ - α⁻¹ = (α - ξ) / (ξ * α) by field_simp, abs_div, abs_mul,
        abs_sub_comm α ξ]
    have hα0' : (0 : ℝ) < |α| := lt_trans (by positivity) hα2
    have hdpos : 0 < |ξ⁻¹ - α⁻¹| := by
      rw [hdist]
      exact div_pos hpos (by positivity)
    have hdle : |ξ⁻¹ - α⁻¹| ≤ 2 / |ξ| ^ 2 * |ξ - α| := by
      rw [hdist, div_le_iff₀ (by positivity : (0 : ℝ) < |ξ| * |α|)]
      have h1 : (1 : ℝ) ≤ 2 / |ξ| ^ 2 * (|ξ| * |α|) := by
        rw [show 2 / |ξ| ^ 2 * (|ξ| * |α|) = 2 * |α| / |ξ| by field_simp,
          le_div_iff₀ hξ0]
        linarith
      calc |ξ - α| = |ξ - α| * 1 := (mul_one _).symm
        _ ≤ |ξ - α| * (2 / |ξ| ^ 2 * (|ξ| * |α|)) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = 2 / |ξ| ^ 2 * |ξ - α| * (|ξ| * |α|) := by ring
    have hbnd : |ξ⁻¹ - α⁻¹|
        ≤ 2 / |ξ| ^ 2 * (P.reflect P.natDegree).supNorm ^ (-(w : ℝ) - 1) := by
      rw [hRnorm, show -(w : ℝ) - 1 = -((w : ℝ) + 1) by ring]
      calc |ξ⁻¹ - α⁻¹| ≤ 2 / |ξ| ^ 2 * |ξ - α| := hdle
        _ ≤ 2 / |ξ| ^ 2 * P.supNorm ^ (-((w : ℝ) + 1)) := by gcongr
    obtain ⟨Q, hQdeg, hQprim, hQirr, hQroot, hQbnd⟩ :=
      exists_mem_koksmaSet_of_root w.coe_nonneg (by positivity) hRdeg hR0 hRroot hbnd
    refine ⟨Q, ⟨hQdeg, hQprim, hQirr, α⁻¹, hQroot, hdpos, hQbnd⟩, ?_⟩
    refine hδ Q α⁻¹ hQdeg hQirr.ne_zero hQroot hdpos ?_
    calc |ξ⁻¹ - α⁻¹| ≤ 2 / |ξ| ^ 2 * |ξ - α| := hdle
      _ ≤ 2 / |ξ| ^ 2 * P.supNorm ^ (-((w : ℝ) + 1)) := by gcongr
      _ < 2 / |ξ| ^ 2 * (δ * |ξ| ^ 2 / 2) := by
          gcongr
          exact lt_of_lt_of_le hsmall (min_le_right _ _)
      _ = δ := by field_simp
  rwa [ENNReal.ofReal_coe_nnreal] at hmain

/-! ### Assembling the Möbius group -/

theorem koksmaExponent_inv (n : ℕ) (ξ : ℝ) :
    koksmaExponent n ξ⁻¹ = koksmaExponent n ξ := by
  rcases eq_or_ne ξ 0 with h | h
  · rw [h, inv_zero]
  refine le_antisymm ?_ (koksmaExponent_le_inv n h)
  have h2 := koksmaExponent_le_inv n (inv_ne_zero h)
  rwa [inv_inv] at h2

theorem koksmaExponent_add_intCast (n : ℕ) (ξ : ℝ) (s : ℤ) :
    koksmaExponent n (ξ + s) = koksmaExponent n ξ := by
  refine le_antisymm ?_ ?_
  · have h := koksmaExponent_le_intAffine n (ξ + s) (t := 1) one_ne_zero (-s)
    rwa [show ((1 : ℤ) : ℝ) * (ξ + (s : ℝ)) + ((-s : ℤ) : ℝ) = ξ by push_cast; ring] at h
  · simpa using koksmaExponent_le_intAffine n ξ (t := 1) one_ne_zero s

theorem koksmaExponent_div_intCast (n : ℕ) (ξ : ℝ) {t : ℤ} (ht : t ≠ 0) :
    koksmaExponent n (ξ / t) = koksmaExponent n ξ := by
  have htR : ((t : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 ht
  rcases eq_or_ne ξ 0 with h | h
  · rw [h, zero_div]
  refine le_antisymm ?_ ?_
  · have h2 := koksmaExponent_le_intAffine n (ξ / ((t : ℤ) : ℝ)) ht 0
    rwa [show ((t : ℤ) : ℝ) * (ξ / ((t : ℤ) : ℝ)) + ((0 : ℤ) : ℝ) = ξ by
      push_cast; rw [add_zero]; field_simp] at h2
  · rw [← koksmaExponent_inv n ξ, ← koksmaExponent_inv n (ξ / ((t : ℤ) : ℝ))]
    have h3 := koksmaExponent_le_intAffine n ξ⁻¹ ht 0
    rwa [show ((t : ℤ) : ℝ) * ξ⁻¹ + ((0 : ℤ) : ℝ) = (ξ / ((t : ℤ) : ℝ))⁻¹ by
      push_cast; rw [add_zero, inv_div, div_eq_mul_inv]] at h3

theorem koksmaExponent_intCast_mul (n : ℕ) (ξ : ℝ) {t : ℤ} (ht : t ≠ 0) :
    koksmaExponent n ((t : ℝ) * ξ) = koksmaExponent n ξ := by
  have h := koksmaExponent_div_intCast n (((t : ℤ) : ℝ) * ξ) ht
  rw [mul_div_cancel_left₀ _ (Int.cast_ne_zero.2 ht)] at h
  exact h.symm

theorem koksmaExponent_mul_ratCast (n : ℕ) (ξ : ℝ) {r : ℚ} (hr : r ≠ 0) :
    koksmaExponent n (ξ * r) = koksmaExponent n ξ := by
  have hnum : (r.num : ℤ) ≠ 0 := Rat.num_ne_zero.2 hr
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_nz
  have hdenR : (((r.den : ℤ)) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hden
  rw [show ξ * (r : ℝ) = (((r.num : ℤ) : ℝ) * ξ) / (((r.den : ℤ)) : ℝ) by
    rw [Rat.cast_def]; push_cast; field_simp]
  rw [koksmaExponent_div_intCast n _ hden, koksmaExponent_intCast_mul n ξ hnum]

theorem koksmaExponent_add_ratCast (n : ℕ) (ξ : ℝ) (r : ℚ) :
    koksmaExponent n (ξ + r) = koksmaExponent n ξ := by
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_nz
  have hdenR : (((r.den : ℤ)) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hden
  rw [show ξ + (r : ℝ)
      = ((((r.den : ℤ)) : ℝ) * ξ + ((r.num : ℤ) : ℝ)) / (((r.den : ℤ)) : ℝ) by
    rw [Rat.cast_def]; push_cast; field_simp]
  rw [koksmaExponent_div_intCast n _ hden, koksmaExponent_add_intCast n _ r.num,
    koksmaExponent_intCast_mul n ξ hden]

/-- **Koksma's exponent is invariant under the rational Möbius group.** -/
theorem koksmaExponent_mobius (n : ℕ) (ξ : ℝ) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0)
    (hden : (c : ℝ) * ξ + d ≠ 0) :
    koksmaExponent n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) = koksmaExponent n ξ := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : (d : ℝ) ≠ 0 := by simpa using hden
    have hdq : d ≠ 0 := Rat.cast_ne_zero.1 hd
    have ha : a ≠ 0 := fun h ↦ hdet (by rw [h]; ring)
    have key : ((a : ℝ) * ξ + b) / (((0 : ℚ) : ℝ) * ξ + d)
        = ξ * ((a / d : ℚ) : ℝ) + ((b / d : ℚ) : ℝ) := by
      push_cast
      rw [zero_mul, zero_add]
      field_simp
    rw [key, koksmaExponent_add_ratCast, koksmaExponent_mul_ratCast _ _ (div_ne_zero ha hdq)]
  · have hcR : (c : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hc
    have hx : ξ + ((d / c : ℚ) : ℝ) ≠ 0 := by
      intro h
      refine hden ?_
      have hξ' : ξ = -((d : ℝ) / (c : ℝ)) := by push_cast at h; linarith
      rw [hξ']
      field_simp
      ring
    have hr : (b * c - a * d) / c ^ 2 ≠ 0 :=
      div_ne_zero (fun h ↦ hdet (by linear_combination -h)) (pow_ne_zero 2 hc)
    have hden' : ξ * (c : ℝ) + (d : ℝ) ≠ 0 := by rw [mul_comm]; exact hden
    have key : ((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)
        = (ξ + ((d / c : ℚ) : ℝ))⁻¹ * (((b * c - a * d) / c ^ 2 : ℚ) : ℝ) + ((a / c : ℚ) : ℝ) := by
      push_cast
      push_cast at hx
      field_simp [hden']
      ring
    rw [key, koksmaExponent_add_ratCast, koksmaExponent_mul_ratCast _ _ hr,
      koksmaExponent_inv, koksmaExponent_add_ratCast]

/-! ### Acceptance criteria -/

/-- Koksma's exponent is a projective invariant of `ξ` over `ℚ`. -/
example (n : ℕ) (ξ : ℝ) : koksmaExponent n (1 / ξ) = koksmaExponent n ξ := by
  rw [one_div, koksmaExponent_inv]

/-- Translation by a rational leaves it alone. -/
example (n : ℕ) (ξ : ℝ) :
    koksmaExponent n (ξ + ((1 / 2 : ℚ) : ℝ)) = koksmaExponent n ξ :=
  koksmaExponent_add_ratCast n ξ (1 / 2)

/-- A genuine Möbius map, with the determinant hypothesis discharged by `norm_num`. -/
example (n : ℕ) (ξ : ℝ) (h : ((2 : ℚ) : ℝ) * ξ + ((3 : ℚ) : ℝ) ≠ 0) :
    koksmaExponent n ((((1 : ℚ) : ℝ) * ξ + ((0 : ℚ) : ℝ))
      / (((2 : ℚ) : ℝ) * ξ + ((3 : ℚ) : ℝ))) = koksmaExponent n ξ :=
  koksmaExponent_mobius n ξ (a := 1) (b := 0) (c := 2) (d := 3) (by norm_num) h

/-- **Rejection test: the determinant hypothesis of `koksmaExponent_mobius` is load-bearing.**
At `a = b = c = d = 1` the determinant vanishes, the map is constant `1`, and the exponent of `√2`
is not the exponent of `1`. -/
example : ¬ ∀ ξ : ℝ, (1 : ℝ) * ξ + 1 ≠ 0 →
    koksmaExponent 1 (((1 : ℝ) * ξ + 1) / ((1 : ℝ) * ξ + 1)) = koksmaExponent 1 ξ := by
  intro h
  have hne : (1 : ℝ) * √2 + 1 ≠ 0 := by positivity
  have h1 := h (√2) hne
  rw [div_self hne] at h1
  have h2 : koksmaExponent 1 (1 : ℝ) = 0 := by
    simpa using koksmaExponent_one_ratCast 1
  rw [h2] at h1
  have h3 := one_le_koksmaExponent_one irrational_sqrt_two
  rw [← h1] at h3
  exact absurd h3 (by norm_num)

end Real
