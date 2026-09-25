/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.OneLinearForm
public import DiophantineApproximation.KoksmaComparison

/-!
# Approximation by algebraic numbers of bounded degree

**Layer 7.2** (Schmidt; Bombieri–Gubler, Corollary 7.3.5). Let `α` be a complex algebraic number,
let `D` be a degree bound and let `ε > 0`. Then only finitely many algebraic numbers `ξ` of degree
at most `D` satisfy

```text
‖α - ξ‖ ≤ H(f_ξ) ^ (-D - 1 - ε),
```

where `f_ξ` is the primitive integer minimal polynomial of `ξ` and `H` is its naive height.

The Subspace Theorem does not appear in this file. Layer 7.1 does all of its work through
`Complex.finite_setOf_norm_sum_mul_le_fin`, applied to the `D + 1` coefficients `1, α, …, α ^ D`
and to the coefficient vector of `f_ξ`: the mean value theorem turns an approximation of `α` by a
root of `f_ξ` into a small value of `f_ξ` at `α`, which is a small value of one linear form with
algebraic coefficients at an integer point.

## Main results

* `Polynomial.norm_aeval_sub_aeval_le`: **the mean value theorem for an integer polynomial at two
  complex points**, with a constant depending only on the degree bound, the naive height and the
  two points.
* `Rat.mulHeight_coeff_le_supNorm`: the projective height over `ℚ` of the coefficient vector of an
  integer polynomial is at most its naive height.
* `Complex.finite_setOf_exists_root_norm_sub_le`: Layer 7.2 counted by minimal polynomials —
  finitely many primitive irreducible integer polynomials of degree at most `D` have a root that
  close to `α`.
* `Complex.finite_setOf_norm_sub_le`: **Layer 7.2**, counted by the approximants themselves.
* `Real.koksmaExponent_le_of_isAlgebraic`: the same statement in the language of Layer 1.3,
  `w_D^*(α) ≤ D` for a real algebraic `α`.

## Implementation notes

⚠ **The statement quantifies over the minimal polynomial, and it is the height of *that* that the
exponent is read against.** There is no function `ξ ↦ H(f_ξ)` in the library, because the
primitive integer minimal polynomial is defined only up to sign; the set counted here is
therefore `{ξ | ∃ P, P primitive irreducible, P ξ = 0, deg P ≤ D, ‖α - ξ‖ ≤ H(P) ^ (-D-1-ε)}`,
and `Polynomial.supNorm_eq_of_isPrimitive_of_irreducible` says that any two witnesses have the
same naive height, so the existential is Bombieri–Gubler's `H(f_ξ)` and the degree of the witness
is the degree of `ξ`. That rigidity lemma is Layer 1.3's, stated there for a real root; it is a
statement about any `ℚ`-algebra that is a domain, and this layer generalized it in place.

⚠ **The mean value theorem had to be proved again over `ℂ`.** Layer 1.3's
`Polynomial.abs_aeval_sub_aeval_le` runs on `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`
over the unordered interval `Set.uIcc`, and there is no interval between two complex numbers. The
telescoping identity `z ^ k - w ^ k = z * (z ^ (k-1) - w ^ (k-1)) + w ^ (k-1) * (z - w)` gives the
same constant `(n + 1) ^ 2 * H(P) * max 1 (max ‖z‖ ‖w‖) ^ n` with no analysis at all, and the
proof is shorter than the real one.

⚠ **The constant is absorbed by half of `ε`, and what is left over is Northcott's theorem.** The
mean value theorem gives `‖f_ξ(α)‖ ≤ C * H ^ (-D - ε)` with `C = (D+1)^2 * (‖α‖+1)^D`, and
`C ≤ H ^ (ε/2)` as soon as `H ≥ C ^ (2/ε)`, so above that height Layer 7.1 applies with `ε/2`.
Below it the polynomials have bounded degree and bounded height, and
`Polynomial.finite_setOf_natDegree_le_supNorm_le` counts them. This is the "familiar argument
already used at the end of Example 7.2.7" that Bombieri–Gubler wave at, and it is why the theorem
is proved by counting *polynomials* first: a bounded set of numbers is not finite, a bounded set
of integer polynomials of bounded degree is.

⚠ **The conjugates of `α` are the one family Layer 7.1 cannot see.** Layer 7.1 needs
`0 < ‖∑ i, α ^ i * x i‖`, which fails exactly when `f_ξ(α) = 0`, that is when `ξ` is a conjugate
of `α`. The rigidity lemma disposes of them: a primitive irreducible polynomial vanishing at `α`
is the minimal polynomial of `α` up to sign, so all of those `ξ` are roots of *one* polynomial,
whose height is a bound the Northcott branch already carries. Bombieri–Gubler's "we may assume
that `ξ` is not a conjugate of `α`" is that sentence.

⚠ **`mulHeight x ≤ H(P)` is where Layer 7.1's projective height meets Layer 1.2's sup norm.**
The set Layer 7.1 counts is cut out by the height of the integer point over `ℚ`, and the exponent
here is read against the naive height of the polynomial, which is the sup norm of that point. The
inequality needed is `mulHeight ≤ sup norm` (`Rat.mulHeight_intCast_le_iSup`), in the direction
that makes the hypothesis weaker; for the *primitive* minimal polynomial the two agree, but
primitivity is not what makes the step work.

⚠ **No hypothesis `1 ≤ D` is needed, and `D = 0` is vacuous.** A primitive irreducible integer
polynomial of degree `0` would be a constant of content one, that is a unit, and units are not
irreducible — so there are no algebraic numbers of degree `0` and the set is empty.

⚠ **Remark 7.3.6 is not needed and is not proved here.** The dictionary
`H(f_ξ) ≍ H(ξ) ^ deg ξ` between the naive height of the minimal polynomial and the absolute
height of the number it names would restate the exponent against `H(ξ)`; the milestone is the
inequality against `H(f_ξ)`, which is what the mean value theorem produces.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Corollary 7.3.5. W.M. Schmidt, *Diophantine Approximation*, Springer Lecture Notes in Mathematics
785 (1980), Ch. VIII, Theorem 9A.

This is part of Layer 7.2 of the `DiophantineApproximation` roadmap.
-/

public section

open Finset Height Polynomial
open scoped ENNReal

namespace Complex

/-- The telescoping bound `‖z ^ k - w ^ k‖ ≤ k * M ^ k * ‖z - w‖`, with `M` an upper bound for
`1`, `‖z‖` and `‖w‖`. The sharp power is `M ^ (k - 1)`, which is useless here: the truncated
subtraction would have to be carried through every consumer, and `M ≥ 1` makes the difference
free. -/
private theorem norm_pow_sub_pow_le (z w : ℂ) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ k * max 1 (max ‖z‖ ‖w‖) ^ k * ‖z - w‖ := by
  set M := max 1 (max ‖z‖ ‖w‖) with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  have hMz : ‖z‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMw : ‖w‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hd : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
  induction k with
  | zero => simp
  | succ k ih =>
      have hid : z ^ (k + 1) - w ^ (k + 1) = z * (z ^ k - w ^ k) + w ^ k * (z - w) := by ring
      have hstep : M ^ k ≤ M ^ (k + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ k)
      have hpk : (0 : ℝ) ≤ M ^ k := pow_nonneg hM0 k
      calc ‖z ^ (k + 1) - w ^ (k + 1)‖
          = ‖z * (z ^ k - w ^ k) + w ^ k * (z - w)‖ := by rw [hid]
        _ ≤ ‖z‖ * ‖z ^ k - w ^ k‖ + ‖w‖ ^ k * ‖z - w‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_pow]
        _ ≤ M * ((k : ℝ) * M ^ k * ‖z - w‖) + M ^ k * ‖z - w‖ := by gcongr
        _ = ((k : ℝ) * M ^ (k + 1) + M ^ k) * ‖z - w‖ := by rw [pow_succ]; ring
        _ ≤ ((k : ℝ) + 1) * M ^ (k + 1) * ‖z - w‖ := by nlinarith
        _ = ((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * ‖z - w‖ := by push_cast; ring

end Complex

namespace Polynomial

/-- **The mean value theorem for an integer polynomial at two complex points.** The increment of
`P` between `z` and `w` is at most `(n + 1) ^ 2 * H(P) * max 1 (max ‖z‖ ‖w‖) ^ n` times the
distance, for any bound `n` on the degree. -/
theorem norm_aeval_sub_aeval_le {P : ℤ[X]} {n : ℕ} (hP : P.natDegree ≤ n) (z w : ℂ) :
    ‖aeval z P - aeval w P‖
      ≤ ((n : ℝ) + 1) ^ 2 * P.supNorm * max 1 (max ‖z‖ ‖w‖) ^ n * ‖z - w‖ := by
  set M := max 1 (max ‖z‖ ‖w‖) with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  have hd : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
  have hH : (0 : ℝ) ≤ P.supNorm := Polynomial.supNorm_nonneg P
  have hsum : aeval z P - aeval w P
      = ∑ i ∈ Finset.range (n + 1), ((P.coeff i : ℤ) : ℂ) * (z ^ i - w ^ i) := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP) z, aeval_eq_sum_range' (Nat.lt_succ_of_le hP) w,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [zsmul_eq_mul, zsmul_eq_mul]; ring
  rw [hsum]
  calc ‖∑ i ∈ Finset.range (n + 1), ((P.coeff i : ℤ) : ℂ) * (z ^ i - w ^ i)‖
      ≤ ∑ i ∈ Finset.range (n + 1), ‖((P.coeff i : ℤ) : ℂ) * (z ^ i - w ^ i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), P.supNorm * ((n : ℝ) * M ^ n * ‖z - w‖) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [norm_mul]
        have hci : ‖((P.coeff i : ℤ) : ℂ)‖ ≤ P.supNorm := by
          simpa [Complex.norm_intCast] using P.abs_coeff_le_supNorm i
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hzw : ‖z ^ i - w ^ i‖ ≤ (n : ℝ) * M ^ n * ‖z - w‖ := by
          refine (Complex.norm_pow_sub_pow_le z w i).trans ?_
          gcongr
        exact mul_le_mul hci hzw (norm_nonneg _) hH
    _ = ((n : ℝ) + 1) * (P.supNorm * ((n : ℝ) * M ^ n * ‖z - w‖)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((n : ℝ) + 1) ^ 2 * P.supNorm * M ^ n * ‖z - w‖ := by
        have hpn : (0 : ℝ) ≤ M ^ n := pow_nonneg hM0 n
        have hprod : (0 : ℝ) ≤ P.supNorm * M ^ n * ‖z - w‖ := by positivity
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hprod]

/-- The value of an integer polynomial of degree at most `D` at a complex point, written as the
linear form in its `D + 1` coefficients that Layer 7.1 counts. -/
theorem aeval_eq_sum_fin {P : ℤ[X]} {D : ℕ} (hP : P.natDegree ≤ D) (z : ℂ) :
    aeval z P = ∑ i : Fin (D + 1), z ^ (i : ℕ) * ((P.coeff i : ℤ) : ℂ) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP) z,
    Fin.sum_univ_eq_sum_range (fun i ↦ z ^ i * ((P.coeff i : ℤ) : ℂ)) (D + 1)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [zsmul_eq_mul]; ring

end Polynomial

namespace Rat

/-- **The height of the coefficient vector is at most the naive height.** The projective height
over `ℚ` of the first `D + 1` coefficients of an integer polynomial is at most its sup norm,
because the finite part of the height of an integer point is at most `1`. It is stated in the
`Rat` namespace and not in `Polynomial`, where `mulHeight` is the height of the polynomial
itself. -/
theorem mulHeight_coeff_le_supNorm {P : ℤ[X]} {D : ℕ}
    (hx : (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≠ 0) :
    mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≤ P.supNorm := by
  refine (Rat.mulHeight_intCast_le_iSup Rat.infinitePlace hx).trans ?_
  refine Real.iSup_le (fun i ↦ ?_) (Polynomial.supNorm_nonneg P)
  rw [Rat.infinitePlace_apply]
  simpa using P.abs_coeff_le_supNorm i

end Rat

namespace Complex

/-- A nonzero integer polynomial has finitely many complex roots. -/
theorem finite_setOf_aeval_eq_zero {P : ℤ[X]} (hP : P ≠ 0) :
    {ξ : ℂ | aeval ξ P = 0}.Finite := by
  have hmap : P.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff ((Int.castRingHom ℂ).injective_int)).2 hP
  refine (Polynomial.finite_setOfPred_isRoot hmap).subset fun ξ hξ ↦ ?_
  simp only [Set.mem_ofPred_eq] at hξ ⊢
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hξ

/-- **A height above which no minimal polynomial vanishes at `α`.** The primitive irreducible
integer polynomials vanishing at a complex number are one polynomial and its negative, so their
naive heights are bounded; at a transcendental `α` there are none and the bound is vacuous. -/
theorem exists_supNorm_le_of_aeval_eq_zero (α : ℂ) :
    ∃ b : ℝ, ∀ P : ℤ[X], P.IsPrimitive → Irreducible P → aeval α P = 0 → P.supNorm ≤ b := by
  by_cases h : ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval α P = 0
  · obtain ⟨P₀, h1, h2, h3⟩ := h
    exact ⟨P₀.supNorm, fun Q hq1 hq2 hq3 ↦
      (Polynomial.supNorm_eq_of_isPrimitive_of_irreducible hq1 hq2 hq3 h1 h2 h3).le⟩
  · exact ⟨0, fun P h1 h2 h3 ↦ absurd ⟨P, h1, h2, h3⟩ h⟩

/-- **Layer 7.2, counted by minimal polynomials.** For a complex algebraic `α`, a degree bound `D`
and `ε > 0`, only finitely many primitive irreducible integer polynomials of degree at most `D`
have a complex root `ξ` with `‖α - ξ‖ ≤ H(P) ^ (-D - 1 - ε)`. This is the form the proof produces:
the polynomials are what Layer 7.1 counts, and the approximants are their roots. -/
theorem finite_setOf_exists_root_norm_sub_le {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    {P : ℤ[X] | P.natDegree ≤ D ∧ P.IsPrimitive ∧ Irreducible P ∧
      ∃ ξ : ℂ, aeval ξ P = 0 ∧ ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite := by
  classical
  obtain ⟨b, hb⟩ := exists_supNorm_le_of_aeval_eq_zero α
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  set C : ℝ := ((D : ℝ) + 1) ^ 2 * (‖α‖ + 1) ^ D with hCdef
  have hC1 : 1 ≤ C := by
    have h1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : (1 : ℝ) ≤ (‖α‖ + 1) ^ D := one_le_pow₀ (by linarith [norm_nonneg α])
    rw [hCdef]
    nlinarith
  set B : ℝ := max b (C ^ (2 / ε)) with hBdef
  set T : Set (Fin (D + 1) → ℤ) :=
    {x | 0 < ‖∑ i : Fin (D + 1), α ^ (i : ℕ) * ((x i : ℤ) : ℂ)‖ ∧
      ‖∑ i : Fin (D + 1), α ^ (i : ℕ) * ((x i : ℤ) : ℂ)‖
        ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ^ (-(D : ℝ) - ε / 2)} with hTdef
  have hT : T.Finite :=
    Complex.finite_setOf_norm_sum_mul_le_fin
      (α := fun i : Fin (D + 1) ↦ α ^ (i : ℕ))
      (fun i ↦ (hα.isIntegral.pow (i : ℕ)).isAlgebraic) (by linarith : (0 : ℝ) < ε / 2)
  set S : Set ℤ[X] := {P | P.natDegree ≤ D ∧ (fun i : Fin (D + 1) ↦ P.coeff i) ∈ T} with hSdef
  have hS : S.Finite := by
    refine Set.Finite.of_finite_image
      (f := fun P : ℤ[X] ↦ fun i : Fin (D + 1) ↦ P.coeff (i : ℕ)) ?_ ?_
    · exact hT.subset (by rintro _ ⟨Q, hQ, rfl⟩; exact hQ.2)
    · rintro Q hQ R hR hQR
      ext i
      rcases le_or_gt i D with hi | hi
      · exact congrFun hQR ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [coeff_eq_zero_of_natDegree_lt (hQ.1.trans_lt hi),
          coeff_eq_zero_of_natDegree_lt (hR.1.trans_lt hi)]
  refine Set.Finite.subset ((Polynomial.finite_setOf_natDegree_le_supNorm_le D B).union hS) ?_
  rintro P ⟨hdeg, hprim, hirr, ξ, hξ, hle⟩
  by_cases hBP : P.supNorm ≤ B
  · exact Or.inl ⟨hdeg, hBP⟩
  have hBlt : B < P.supNorm := not_le.mp hBP
  have hP0 : P ≠ 0 := hirr.ne_zero
  have hH1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  have hH0 : (0 : ℝ) < P.supNorm := lt_of_lt_of_le zero_lt_one hH1
  have hHnn : (0 : ℝ) ≤ P.supNorm := hH0.le
  -- `ξ` is not a conjugate of `α`: its minimal polynomial is too tall to vanish at `α`
  have hne : aeval α P ≠ 0 := fun h ↦
    absurd (hb P hprim hirr h) (not_le.2 (lt_of_le_of_lt (le_max_left b _) hBlt))
  -- the mean value theorem, on an interval bounded by `α` alone
  have hexpneg : -(D : ℝ) - 1 - ε ≤ 0 := by linarith
  have hsmall : ‖α - ξ‖ ≤ 1 := hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hH1 hexpneg)
  have hMb : max 1 (max ‖α‖ ‖ξ‖) ≤ ‖α‖ + 1 := by
    have hxi : ‖ξ‖ ≤ ‖α‖ + 1 := by
      have h1 : ‖ξ‖ - ‖α‖ ≤ ‖ξ - α‖ := norm_sub_norm_le ξ α
      rw [norm_sub_rev] at h1
      linarith
    exact max_le (by linarith [norm_nonneg α]) (max_le (by linarith) hxi)
  have hmv : ‖aeval α P‖ ≤ C * P.supNorm * ‖α - ξ‖ := by
    have h := Polynomial.norm_aeval_sub_aeval_le hdeg α ξ
    rw [hξ, sub_zero] at h
    refine h.trans ?_
    have hM0 : (0 : ℝ) ≤ max 1 (max ‖α‖ ‖ξ‖) := le_trans zero_le_one (le_max_left _ _)
    have hpow : max 1 (max ‖α‖ ‖ξ‖) ^ D ≤ (‖α‖ + 1) ^ D := pow_le_pow_left₀ hM0 hMb D
    have hd : (0 : ℝ) ≤ ‖α - ξ‖ := norm_nonneg _
    have hsq : (0 : ℝ) ≤ ((D : ℝ) + 1) ^ 2 * P.supNorm := by positivity
    rw [hCdef]
    nlinarith [mul_nonneg hsq hd]
  have hadd : (1 : ℝ) + (-(D : ℝ) - 1 - ε) = -(D : ℝ) - ε := by ring
  have hkey : ‖aeval α P‖ ≤ C * P.supNorm ^ (-(D : ℝ) - ε) := by
    calc ‖aeval α P‖ ≤ C * P.supNorm * ‖α - ξ‖ := hmv
      _ ≤ C * P.supNorm * P.supNorm ^ (-(D : ℝ) - 1 - ε) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = C * (P.supNorm ^ (1 : ℝ) * P.supNorm ^ (-(D : ℝ) - 1 - ε)) := by
          rw [Real.rpow_one]; ring
      _ = C * P.supNorm ^ (-(D : ℝ) - ε) := by rw [← Real.rpow_add hH0, hadd]
  -- the constant is absorbed by half of `ε`
  have hCle : C ≤ P.supNorm ^ (ε / 2) := by
    have h1 : C ^ (2 / ε) ≤ P.supNorm := (le_max_right b _).trans hBlt.le
    have h2 : (C ^ (2 / ε)) ^ (ε / 2) ≤ P.supNorm ^ (ε / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 (by linarith)
    have hmul : 2 / ε * (ε / 2) = 1 := by field_simp
    rwa [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ C), hmul, Real.rpow_one] at h2
  have hfinal : ‖aeval α P‖ ≤ P.supNorm ^ (-(D : ℝ) - ε / 2) := by
    have hnn : (0 : ℝ) ≤ P.supNorm ^ (-(D : ℝ) - ε) := Real.rpow_nonneg hHnn _
    calc ‖aeval α P‖ ≤ C * P.supNorm ^ (-(D : ℝ) - ε) := hkey
      _ ≤ P.supNorm ^ (ε / 2) * P.supNorm ^ (-(D : ℝ) - ε) :=
          mul_le_mul_of_nonneg_right hCle hnn
      _ = P.supNorm ^ (ε / 2 + (-(D : ℝ) - ε)) := (Real.rpow_add hH0 _ _).symm
      _ = P.supNorm ^ (-(D : ℝ) - ε / 2) := by
          rw [show ε / 2 + (-(D : ℝ) - ε) = -(D : ℝ) - ε / 2 by ring]
  -- and the height of the coefficient vector is at most the naive height
  have hxne : (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≠ 0 := by
    intro h
    refine hP0 (Polynomial.ext fun i ↦ ?_)
    rw [coeff_zero]
    rcases le_or_gt i D with hi | hi
    · have hc := congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      simp only [Pi.zero_apply] at hc
      exact_mod_cast hc
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hi)
  have hmh : mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ≤ P.supNorm :=
    Rat.mulHeight_coeff_le_supNorm hxne
  have hmh1 : (1 : ℝ) ≤ mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) :=
    Height.one_le_mulHeight _
  have hcmp : P.supNorm ^ (-(D : ℝ) - ε / 2)
      ≤ mulHeight (fun i : Fin (D + 1) ↦ ((P.coeff (i : ℕ) : ℤ) : ℚ)) ^ (-(D : ℝ) - ε / 2) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hmh (by linarith)
  have hsum : ∑ i : Fin (D + 1), α ^ (i : ℕ) * ((P.coeff (i : ℕ) : ℤ) : ℂ) = aeval α P :=
    (Polynomial.aeval_eq_sum_fin hdeg α).symm
  refine Or.inr ⟨hdeg, ?_, ?_⟩
  · rw [hsum]
    exact norm_pos_iff.mpr hne
  · rw [hsum]
    exact hfinal.trans hcmp

/-- **Layer 7.2** (Schmidt; Bombieri–Gubler, Corollary 7.3.5). **Approximation by algebraic
numbers of bounded degree.** For a complex algebraic `α`, a degree bound `D` and `ε > 0`, only
finitely many complex algebraic numbers `ξ` of degree at most `D` satisfy
`‖α - ξ‖ ≤ H(f_ξ) ^ (-D - 1 - ε)`, where `f_ξ` is the primitive integer minimal polynomial of `ξ`
and `H` is its naive height. -/
theorem finite_setOf_norm_sub_le {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧ P.natDegree ≤ D ∧
      ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite := by
  refine Set.Finite.subset
    ((finite_setOf_exists_root_norm_sub_le hα D hε).biUnion
      (t := fun P ↦ {ξ : ℂ | aeval ξ P = 0}) ?_) ?_
  · rintro P ⟨-, -, hirr, -⟩
    exact finite_setOf_aeval_eq_zero hirr.ne_zero
  · rintro ξ ⟨P, hprim, hirr, hroot, hdeg, hle⟩
    exact Set.mem_biUnion (show P ∈ _ from ⟨hdeg, hprim, hirr, ξ, hroot, hle⟩) hroot

end Complex

namespace Real

/-- **Layer 7.2 in the language of Layer 1.3**: Koksma's exponent of a real algebraic number is at
most the degree bound, `w_n^*(α) ≤ n`. This is one of the two upper bounds Layer 7.3 needs; the
other, `w_n^* ≤ deg α - 1`, is Liouville's inequality and is Layer 1.3's. -/
theorem koksmaExponent_le_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (n : ℕ) :
    koksmaExponent n α ≤ (n : ℝ≥0∞) := by
  refine koksmaExponent_le_iff.2 fun w hinf ↦ ?_
  by_contra hlt
  push Not at hlt
  have hlt' : (n : ℝ) < (w : ℝ) := by exact_mod_cast hlt
  have hε : (0 : ℝ) < (w : ℝ) - n := by linarith
  have halg : IsAlgebraic ℚ ((α : ℝ) : ℂ) := hα.algebraMap
  refine hinf (Set.Finite.subset (Complex.finite_setOf_exists_root_norm_sub_le halg n hε) ?_)
  rintro P ⟨hdeg, hprim, hirr, β, hβ, -, hle⟩
  refine ⟨hdeg, hprim, hirr, ((β : ℝ) : ℂ), ?_, ?_⟩
  · rw [show ((β : ℝ) : ℂ) = IsScalarTower.toAlgHom ℤ ℝ ℂ β from rfl,
      Polynomial.aeval_algHom_apply, hβ, map_zero]
  · have hexp : -(n : ℝ) - 1 - ((w : ℝ) - n) = -(w : ℝ) - 1 := by ring
    have hcast : ((α : ℝ) : ℂ) - ((β : ℝ) : ℂ) = ((α - β : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, hcast, Complex.norm_real]
    exact hle

end Real

/-!
## Acceptance criteria
-/

namespace Complex

/-- Layer 7.2 in the shape the roadmap states it. -/
example {α : ℂ} (hα : IsAlgebraic ℚ α) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧ P.natDegree ≤ D ∧
      ‖α - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)}.Finite :=
  finite_setOf_norm_sub_le hα D hε

/-- **Acceptance test: the existential is Bombieri–Gubler's `H(f_ξ)`.** Two primitive irreducible
integer polynomials with a common complex root have the same naive height, so the height the
exponent is read against depends on `ξ` alone. -/
example {ξ : ℂ} {P Q : ℤ[X]} (hPp : P.IsPrimitive) (hPi : Irreducible P) (hPξ : aeval ξ P = 0)
    (hQp : Q.IsPrimitive) (hQi : Irreducible Q) (hQξ : aeval ξ Q = 0) : P.supNorm = Q.supNorm :=
  Polynomial.supNorm_eq_of_isPrimitive_of_irreducible hPp hPi hPξ hQp hQi hQξ

/-- **Acceptance test: the theorem is not vacuous.** An algebraic number of degree at most `D` is
its own best approximation, at distance zero, so the set counted is nonempty whenever `α` itself
has degree at most `D` — the content is that it is finite, not that it is empty. -/
example (D : ℕ) (hD : 1 ≤ D) {ε : ℝ} :
    (0 : ℂ) ∈ {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧
      P.natDegree ≤ D ∧ ‖(0 : ℂ) - ξ‖ ≤ P.supNorm ^ (-(D : ℝ) - 1 - ε)} := by
  refine ⟨X, (monic_X (R := ℤ)).isPrimitive, irreducible_X, by simp, ?_, ?_⟩
  · simpa using hD
  · simp

/-- **Rejection test: the degree bound alone leaves infinitely many.** The algebraic numbers of
degree at most one are the rationals, and there are infinitely many of them; it is the
approximation inequality, not the bound on the degree, that makes the set of Layer 7.2 finite. -/
example :
    {ξ : ℂ | ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0 ∧
      P.natDegree ≤ 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ (m : ℂ)) (fun m m' hmm ↦ ?_) fun m ↦ ?_
  · have h : ((m : ℂ)) = ((m' : ℂ)) := hmm
    exact_mod_cast h
  refine ⟨X - C (m : ℤ), (monic_X_sub_C (m : ℤ)).isPrimitive, irreducible_X_sub_C _, by simp, ?_⟩
  rw [natDegree_X_sub_C]

end Complex
