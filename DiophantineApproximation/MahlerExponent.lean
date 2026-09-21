/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IrrationalityExponent
public import DiophantineApproximation.PolynomialSupNorm

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Mahler's and Koksma's exponents

Layer 1.1 measured how well a real number is approximated by *rationals*. Layer 1.2 measures how
well it is approximated by *algebraic numbers of bounded degree*, and there are two ways to say
it, which Mahler and Koksma chose independently:

* `Real.mahlerExponent n ξ` — the supremum of the `w` for which `0 < |P ξ| ≤ H(P) ^ (-w)` has
  infinitely many solutions among the integer polynomials `P` of degree at most `n`;
* `Real.koksmaExponent n ξ` — the supremum of the `w` for which `0 < |ξ - α| ≤ H(α) ^ (-w-1)` has
  infinitely many solutions among the real algebraic numbers `α` of degree at most `n`.

Here `H` is the **naive height**, the largest absolute value of a coefficient, and it is Mathlib's
`Polynomial.supNorm`; an algebraic number is measured by the height of its primitive irreducible
integer minimal polynomial, which is how `koksmaSet` is written — the approximants of `ξ` *are*
those polynomials, and the algebraic number is the root they carry.

At `n = 1` the two exponents coincide and both are the irrationality exponent of Layer 1.1,
shifted by one; that identity, in both directions and for both exponents, is the acceptance test
of this file. The invariance of `Real.mahlerExponent` under the rational Möbius group is proved
here as well, by the same decomposition into an affine part and an inversion that Layer 1.1 used;
the corresponding statement for `Real.koksmaExponent` needs Gelfond's inequality and is in
`DiophantineApproximation/KoksmaMobius.lean`.

## Main results

* `Real.mahlerExponent` and `Real.koksmaExponent`: the definitions, on the named sets
  `Real.mahlerSet` and `Real.koksmaSet` whose infinitude they are the supremum over, with the
  order API `Real.le_mahlerExponent`, `Real.mahlerExponent_le_iff`,
  `Real.infinite_mahlerSet_of_lt` and their Koksma counterparts.
* `Real.le_mahlerExponent_of_infinite` and `Real.le_koksmaExponent_of_infinite`: **a constant in
  front of `H(P) ^ (-w)` does not change the exponent.**
* `Real.mahlerExponent_mono` and `Real.koksmaExponent_mono`: monotonicity in the degree.
* `Real.mahlerExponent_one_add_one` and `Real.koksmaExponent_one_add_one`:
  `w_1 = w_1^* = irrationalityExponent - 1`, and `Real.koksmaExponent_one_eq_mahlerExponent_one`.
* `Real.mahlerExponent_one_ratCast`, `Real.koksmaExponent_one_ratCast` and
  `Real.one_le_mahlerExponent_one`: the value `0` at a rational and Dirichlet's bound `1` at an
  irrational.
* `Real.infinite_primitive_mahlerSet` and `Real.mahlerExponent_eq_iSup_primitive`: **restricting
  to primitive polynomials does not change Mahler's exponent.**
* `Real.mahlerExponent_mobius`: **invariance under the rational Möbius group**, with the special
  cases it is assembled from (`Real.mahlerExponent_inv`, `_add_intCast`, `_intCast_mul`,
  `_div_intCast`, `_mul_ratCast`, `_add_ratCast`) and the two generators
  `Real.mahlerExponent_intAffine_le` and `Real.mahlerExponent_inv_le`.
* `Real.rpow_neg_lt_of_max_lt`, `Real.rpow_neg_le_rpow_neg` and
  `Real.rpow_neg_le_mul_rpow_neg`: the three real-analysis steps that every proof below runs on.

## Implementation notes

⚠ **Mathlib already has the naive height and says so.** `Polynomial.supNorm` is the Gauss norm of
the coefficient norm at `c = 1`, its own module documentation calls it "the *(naive) height*", and
it declines the name only because `Height` is taken. The `naiveHeight` abbreviation this roadmap
pinned is therefore not introduced: it would hide `Polynomial.le_supNorm` and
`Polynomial.exists_eq_supNorm`, which are what every proof here uses. What was missing is the
arithmetic of that norm and **Northcott's theorem for integer polynomials**; both are in
`DiophantineApproximation/PolynomialSupNorm.lean`.

⚠ **The height gap, not a fibre count, is what keeps the solutions infinite.** Every step of this
layer replaces a solution `P` by some other polynomial — its primitive part, an irreducible
factor, a Möbius transform — and each time the question is whether the *images* are still
infinitely many. The naive answer, counting the fibres of the replacement, is available for the
primitive part and useless for the others. The answer that works every time is
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`: below a threshold that depends only on the
height bound, a **nonzero** value at `ξ` forces the naive height above that bound, whatever
polynomial produced the value. Combined with the fact that an infinite set of bounded degree has
unbounded height, it turns "the images take small values" into "the images are tall", which is
what infinitude means here.

⚠ **The two degree-one identifications are not mirror images.** On Mahler's side the work is that
the leading coefficient is the *denominator* and the height is `max |m| n`, so the height has to
be shown comparable to the denominator — `H ≤ (|ξ| + 1) * N` — before `LiouvilleWith`'s
`atTop` quantifier over denominators can be fed. On Koksma's side the approximants must be in
**lowest terms**, because only then is the linear polynomial they name primitive and hence
irreducible; reducing a fraction lowers its height, which improves the approximation, but it also
threatens to make the heights bounded, and ruling that out is again the height gap — applied to
`N' * (ξ - m / N)`, which tends to `0` because the exponent exceeds `1`.

⚠ **The Möbius decomposition of Layer 1.1 transfers verbatim, and the inversion is free.** The
group is generated by the integer affine maps and by `ξ ↦ ξ⁻¹`; on polynomials the first is
`Polynomial.comp` with a linear substitution and the second is `Polynomial.reflect n`. Composition
multiplies the naive height by a constant that the exponent absorbs, but **reflection permutes the
coefficients, so it preserves the naive height exactly** — that step needs no gap lemma, no
constant and no threshold, and it is the only one in the layer that does not.

⚠ **`Real.le_irrationalityExponent_iff` was the wrong tool and
`Real.liouvilleWith_iff_frequently_max` was the right one.** Layer 1.1 proved both; only the
second, which measures by the naive height `max |m| n` of the fraction rather than by its
denominator, matches the height that Layer 1.2 normalizes by, and using it is what keeps the
degree-one proofs to a single change of variable.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1 and
§3.2. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
(2006), §1.6.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter Polynomial
open scoped ENNReal NNReal

namespace Real

variable {n : ℕ} {ξ : ℝ}

/-! ### The two exponents -/

/-- The integer polynomials that witness `mahlerExponent n ξ ≥ w`: degree at most `n`, a nonzero
value at `ξ`, and `|P ξ| ≤ H(P) ^ (-w)` for the naive height `H = Polynomial.supNorm`. -/
@[expose] def mahlerSet (n : ℕ) (ξ : ℝ) (w : ℝ) : Set ℤ[X] :=
  {P | P.natDegree ≤ n ∧ 0 < |aeval ξ P| ∧ |aeval ξ P| ≤ P.supNorm ^ (-w)}

/-- **Mahler's exponent `w_n`**: the supremum of the orders `w` to which `ξ` is a near-root of
infinitely many integer polynomials of degree at most `n`. -/
@[expose] noncomputable def mahlerExponent (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ≥0) (_ : (mahlerSet n ξ (w : ℝ)).Infinite), (w : ℝ≥0∞)

/-- The integer polynomials that witness `koksmaExponent n ξ ≥ w`: a primitive irreducible
polynomial of degree at most `n` — that is, the minimal polynomial of each of its roots — with a
real root `α` satisfying `0 < |ξ - α| ≤ H(P) ^ (-w - 1)`. -/
@[expose] def koksmaSet (n : ℕ) (ξ : ℝ) (w : ℝ) : Set ℤ[X] :=
  {P | P.natDegree ≤ n ∧ P.IsPrimitive ∧ Irreducible P ∧
    ∃ α : ℝ, aeval α P = 0 ∧ 0 < |ξ - α| ∧ |ξ - α| ≤ P.supNorm ^ (-w - 1)}

/-- **Koksma's exponent `w_n^*`**: the supremum of the orders `w` to which `ξ` is approximated by
infinitely many real algebraic numbers of degree at most `n`. The normalization is `-w - 1`, so
that `koksmaExponent 1 = mahlerExponent 1 = irrationalityExponent - 1`. -/
@[expose] noncomputable def koksmaExponent (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ≥0) (_ : (koksmaSet n ξ (w : ℝ)).Infinite), (w : ℝ≥0∞)

/-! ### The order API -/

theorem ne_zero_of_mem_mahlerSet {w : ℝ} {P : ℤ[X]} (h : P ∈ mahlerSet n ξ w) : P ≠ 0 := by
  rintro rfl
  simpa using h.2.1

theorem ne_zero_of_mem_koksmaSet {w : ℝ} {P : ℤ[X]} (h : P ∈ koksmaSet n ξ w) : P ≠ 0 :=
  h.2.2.1.ne_zero

theorem mahlerSet_subset_of_le {w w' : ℝ} (h : w ≤ w') :
    mahlerSet n ξ w' ⊆ mahlerSet n ξ w := by
  rintro P hP
  refine ⟨hP.1, hP.2.1, hP.2.2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_supNorm (ne_zero_of_mem_mahlerSet hP))
    (by linarith)

theorem koksmaSet_subset_of_le {w w' : ℝ} (h : w ≤ w') :
    koksmaSet n ξ w' ⊆ koksmaSet n ξ w := by
  rintro P ⟨hdeg, hprim, hirr, α, hα, hpos, hle⟩
  refine ⟨hdeg, hprim, hirr, α, hα, hpos, hle.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_supNorm hirr.ne_zero) (by linarith)

theorem mahlerSet_mono {n n' : ℕ} (h : n ≤ n') {w : ℝ} :
    mahlerSet n ξ w ⊆ mahlerSet n' ξ w := fun _ hP ↦ ⟨hP.1.trans h, hP.2.1, hP.2.2⟩

theorem koksmaSet_mono {n n' : ℕ} (h : n ≤ n') {w : ℝ} :
    koksmaSet n ξ w ⊆ koksmaSet n' ξ w := fun _ hP ↦ ⟨hP.1.trans h, hP.2⟩

theorem le_mahlerExponent {w : ℝ≥0} (h : (mahlerSet n ξ (w : ℝ)).Infinite) :
    (w : ℝ≥0∞) ≤ mahlerExponent n ξ :=
  le_iSup₂ (f := fun (w : ℝ≥0) (_ : (mahlerSet n ξ (w : ℝ)).Infinite) ↦ (w : ℝ≥0∞)) w h

theorem le_koksmaExponent {w : ℝ≥0} (h : (koksmaSet n ξ (w : ℝ)).Infinite) :
    (w : ℝ≥0∞) ≤ koksmaExponent n ξ :=
  le_iSup₂ (f := fun (w : ℝ≥0) (_ : (koksmaSet n ξ (w : ℝ)).Infinite) ↦ (w : ℝ≥0∞)) w h

theorem mahlerExponent_le_iff {c : ℝ≥0∞} :
    mahlerExponent n ξ ≤ c ↔ ∀ w : ℝ≥0, (mahlerSet n ξ (w : ℝ)).Infinite → (w : ℝ≥0∞) ≤ c :=
  iSup₂_le_iff

theorem koksmaExponent_le_iff {c : ℝ≥0∞} :
    koksmaExponent n ξ ≤ c ↔ ∀ w : ℝ≥0, (koksmaSet n ξ (w : ℝ)).Infinite → (w : ℝ≥0∞) ≤ c :=
  iSup₂_le_iff

/-- Both exponents are monotone in the degree, because the defining set is. -/
theorem mahlerExponent_mono {n n' : ℕ} (h : n ≤ n') (ξ : ℝ) :
    mahlerExponent n ξ ≤ mahlerExponent n' ξ :=
  mahlerExponent_le_iff.2 fun _ hw ↦ le_mahlerExponent (Set.Infinite.mono (mahlerSet_mono h) hw)

theorem koksmaExponent_mono {n n' : ℕ} (h : n ≤ n') (ξ : ℝ) :
    koksmaExponent n ξ ≤ koksmaExponent n' ξ :=
  koksmaExponent_le_iff.2 fun _ hw ↦ le_koksmaExponent (Set.Infinite.mono (koksmaSet_mono h) hw)

theorem infinite_mahlerSet_of_lt {w : ℝ} (h : ENNReal.ofReal w < mahlerExponent n ξ) :
    (mahlerSet n ξ w).Infinite := by
  rw [mahlerExponent, lt_iSup_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [lt_iSup_iff] at hq
  obtain ⟨hinf, hlt⟩ := hq
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  exact Set.Infinite.mono (mahlerSet_subset_of_le hlt.1.le) hinf

theorem infinite_koksmaSet_of_lt {w : ℝ} (h : ENNReal.ofReal w < koksmaExponent n ξ) :
    (koksmaSet n ξ w).Infinite := by
  rw [koksmaExponent, lt_iSup_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [lt_iSup_iff] at hq
  obtain ⟨hinf, hlt⟩ := hq
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  exact Set.Infinite.mono (koksmaSet_subset_of_le hlt.1.le) hinf

/-- The arithmetic that absorbs a constant into the exponent: for `a < w` and a height above
`max 1 (A ^ (w - a)⁻¹)`, the bound `A * H ^ (-w)` implies the bound `H ^ (-a)`. -/
private theorem const_mul_rpow_le {A w a H : ℝ} (hA : 0 < A) (haw : a < w)
    (hH : max 1 (A ^ (w - a)⁻¹) < H) : A * H ^ (-w) ≤ H ^ (-a) := by
  have hH1 : (1 : ℝ) < H := lt_of_le_of_lt (le_max_left _ _) hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans hH1
  have hAle : A ≤ H ^ (w - a) := by
    have h1 : A = (A ^ (w - a)⁻¹) ^ (w - a) := by
      rw [← Real.rpow_mul hA.le, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _)
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hH)) (by linarith)
  calc A * H ^ (-w) ≤ H ^ (w - a) * H ^ (-w) := by gcongr
    _ = H ^ (-a) := by rw [← Real.rpow_add hH0]; ring_nf

/-- **Absorbing a constant.** A constant in front of `H(P) ^ (-w)` does not change the exponent:
an infinite set of solutions of bounded degree has unbounded height, and above a height that
depends only on the constant and on the loss in the exponent the constant is swallowed. -/
theorem le_mahlerExponent_of_infinite {w A : ℝ} (hA : 0 < A)
    (h : {P : ℤ[X] | P.natDegree ≤ n ∧ 0 < |aeval ξ P| ∧
        |aeval ξ P| ≤ A * P.supNorm ^ (-w)}.Infinite) :
    ENNReal.ofReal w ≤ mahlerExponent n ξ := by
  rcases le_or_gt w 0 with hw | hw
  · simp [ENNReal.ofReal_of_nonpos hw]
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  lift a to ℝ≥0 using ne_top_of_lt ha
  have ha' : (a : ℝ) < w := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at ha
    exact ha.1
  refine le_mahlerExponent (Set.Infinite.mono ?_
    (Polynomial.infinite_sep_lt_supNorm h (fun P hP ↦ hP.1) (max 1 (A ^ (w - (a : ℝ))⁻¹))))
  rintro P ⟨⟨hdeg, hpos, hle⟩, hBP⟩
  exact ⟨hdeg, hpos, hle.trans (const_mul_rpow_le hA ha' hBP)⟩

theorem le_koksmaExponent_of_infinite {w A : ℝ} (hA : 0 < A)
    (h : {P : ℤ[X] | P.natDegree ≤ n ∧ P.IsPrimitive ∧ Irreducible P ∧
        ∃ α : ℝ, aeval α P = 0 ∧ 0 < |ξ - α| ∧
          |ξ - α| ≤ A * P.supNorm ^ (-w - 1)}.Infinite) :
    ENNReal.ofReal w ≤ koksmaExponent n ξ := by
  rcases le_or_gt w 0 with hw | hw
  · simp [ENNReal.ofReal_of_nonpos hw]
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  lift a to ℝ≥0 using ne_top_of_lt ha
  have ha' : (a : ℝ) < w := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at ha
    exact ha.1
  refine le_koksmaExponent (Set.Infinite.mono ?_
    (Polynomial.infinite_sep_lt_supNorm h (fun P hP ↦ hP.1) (max 1 (A ^ (w - (a : ℝ))⁻¹))))
  rintro P ⟨⟨hdeg, hprim, hirr, α, hα, hpos, hle⟩, hBP⟩
  refine ⟨hdeg, hprim, hirr, α, hα, hpos, hle.trans ?_⟩
  have hkey := const_mul_rpow_le (A := A) (w := w + 1) (a := (a : ℝ) + 1) (H := P.supNorm)
    hA (by linarith) (by rwa [show w + 1 - ((a : ℝ) + 1) = w - (a : ℝ) by ring])
  calc A * P.supNorm ^ (-w - 1) = A * P.supNorm ^ (-(w + 1)) := by
        rw [show -w - 1 = -(w + 1) by ring]
    _ ≤ P.supNorm ^ (-((a : ℝ) + 1)) := hkey
    _ = P.supNorm ^ (-(a : ℝ) - 1) := by rw [show -((a : ℝ) + 1) = -(a : ℝ) - 1 by ring]

/-! ### Degree one: the irrationality exponent -/

/-- **From a polynomial of degree one to a fraction.** A member of `mahlerSet 1 ξ w` of height
above `1` has a nonzero leading coefficient, and after a sign change it reads `a X + b` with
`a > 0`; the fraction `-b / a` then approximates `ξ` to order `w + 1` in the naive height, with
the constant `|ξ| + 2`. The height is comparable to the denominator, which is what makes the
denominators tend to infinity along the set. -/
private theorem exists_frac_of_mem_mahlerSet {w : ℝ} (hw : 0 ≤ w) {P : ℤ[X]}
    (hP : P ∈ mahlerSet 1 ξ w) (hP1 : 1 < P.supNorm) :
    ∃ (N : ℕ) (m : ℤ), P.supNorm ≤ (|ξ| + 1) * N ∧ ξ ≠ m / N ∧
      |ξ - m / N| < (|ξ| + 2) / (max |(m : ℝ)| (N : ℝ)) ^ (w + 1) := by
  obtain ⟨hdeg, hpos, hle⟩ := hP
  have hH0 : (0 : ℝ) < P.supNorm := zero_lt_one.trans hP1
  have hPeq : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_natDegree_le_one hdeg
  have hval : aeval ξ P = (P.coeff 1 : ℝ) * ξ + (P.coeff 0 : ℝ) := by
    conv_lhs => rw [hPeq]
    simp
  have hnorm : P.supNorm = max |((P.coeff 1 : ℤ) : ℝ)| |((P.coeff 0 : ℤ) : ℝ)| := by
    conv_lhs => rw [hPeq]
    exact Polynomial.supNorm_linear _ _
  have hle1 : |aeval ξ P| ≤ 1 :=
    hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hP1.le (by linarith))
  -- the leading coefficient cannot vanish: otherwise the height *is* the value
  have ha0 : P.coeff 1 ≠ 0 := by
    intro h0
    rw [h0] at hnorm hval
    rw [Int.cast_zero, abs_zero, max_eq_right (abs_nonneg _)] at hnorm
    rw [Int.cast_zero, zero_mul, zero_add] at hval
    rw [hval] at hle1
    rw [hnorm] at hP1
    linarith
  -- normalize the sign of the leading coefficient
  obtain ⟨a, b, hapos, hval', hnorm'⟩ : ∃ a b : ℤ, 0 < a ∧
      |(a : ℝ) * ξ + (b : ℝ)| = |aeval ξ P| ∧ max |(a : ℝ)| |(b : ℝ)| = P.supNorm := by
    rcases ha0.lt_or_gt with h | h
    · refine ⟨-P.coeff 1, -P.coeff 0, by omega, ?_, ?_⟩
      · rw [hval]
        push_cast
        rw [show -((P.coeff 1 : ℤ) : ℝ) * ξ + -((P.coeff 0 : ℤ) : ℝ)
          = -(((P.coeff 1 : ℤ) : ℝ) * ξ + ((P.coeff 0 : ℤ) : ℝ)) by ring, abs_neg]
      · rw [hnorm]
        push_cast
        rw [abs_neg, abs_neg]
    · exact ⟨P.coeff 1, P.coeff 0, h, by rw [hval], hnorm.symm⟩
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have ha1' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hapos
  -- the height is at most `(|ξ| + 1)` times the denominator
  have hbnd : P.supNorm ≤ (|ξ| + 1) * (a : ℝ) := by
    rw [← hnorm']
    refine max_le (by rw [abs_of_pos ha0']; nlinarith [abs_nonneg ξ]) ?_
    have h1 : |(b : ℝ)| - |(a : ℝ) * ξ| ≤ |(a : ℝ) * ξ + (b : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (-((a : ℝ) * ξ)) (b : ℝ)
      rw [abs_neg] at this
      calc |(b : ℝ)| - |(a : ℝ) * ξ| ≤ |-((a : ℝ) * ξ) - (b : ℝ)| := by
            have h2 := abs_sub_abs_le_abs_sub (b : ℝ) (-((a : ℝ) * ξ))
            rw [abs_neg] at h2
            rw [abs_sub_comm]
            linarith
        _ = |(a : ℝ) * ξ + (b : ℝ)| := by rw [← abs_neg]; ring_nf
    rw [hval'] at h1
    rw [abs_mul, abs_of_pos ha0'] at h1
    nlinarith
  have hcast : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hapos.le
  have hfrac : ξ - ((-b : ℤ) : ℝ) / (a : ℝ) = ((a : ℝ) * ξ + (b : ℝ)) / (a : ℝ) := by
    field_simp
    push_cast
    ring
  have habs : |ξ - ((-b : ℤ) : ℝ) / (a : ℝ)| = |aeval ξ P| / (a : ℝ) := by
    rw [hfrac, abs_div, abs_of_pos ha0', hval']
  have hmax : max |((-b : ℤ) : ℝ)| (a : ℝ) = P.supNorm := by
    rw [show |((-b : ℤ) : ℝ)| = |(b : ℝ)| by push_cast; rw [abs_neg],
      show ((a : ℤ) : ℝ) = |(a : ℝ)| from (abs_of_pos ha0').symm, max_comm, hnorm']
  refine ⟨a.toNat, -b, ?_, ?_, ?_⟩
  · rwa [hcast]
  · rw [hcast]
    intro heq
    have hz : |ξ - ((-b : ℤ) : ℝ) / (a : ℝ)| = 0 := by rw [heq, sub_self, abs_zero]
    rw [habs] at hz
    exact absurd hz (ne_of_gt (div_pos hpos ha0'))
  · rw [hcast, habs, hmax]
    have hHw : (0 : ℝ) < P.supNorm ^ (w + 1) := Real.rpow_pos_of_pos hH0 _
    rw [div_lt_div_iff₀ ha0' hHw]
    calc |aeval ξ P| * P.supNorm ^ (w + 1) ≤ P.supNorm ^ (-w) * P.supNorm ^ (w + 1) := by
          gcongr
      _ = P.supNorm := by
          rw [← Real.rpow_add hH0, show -w + (w + 1) = 1 by ring, Real.rpow_one]
      _ ≤ (|ξ| + 1) * (a : ℝ) := hbnd
      _ < (|ξ| + 2) * (a : ℝ) := by nlinarith

/-- Half of the degree-one identification: **every rational approximation of order `μ` is a linear
integer polynomial small at `ξ` of order `μ - 1`.** The denominator becomes the leading
coefficient, and the naive height of the fraction is the naive height of the polynomial. -/
theorem irrationalityExponent_le_mahlerExponent_one_add_one (ξ : ℝ) :
    irrationalityExponent ξ ≤ mahlerExponent 1 ξ + 1 := by
  rw [irrationalityExponent_le_iff]
  intro μ hμ
  rcases le_or_gt (μ : ℝ) 1 with h1 | h1
  · exact le_trans (by exact_mod_cast h1 : (μ : ℝ≥0∞) ≤ 1) le_add_self
  obtain ⟨A, hA⟩ :=
    (liouvilleWith_iff_frequently_max (ξ := ξ) (μ := (μ : ℝ)) (by positivity)).1 hμ
  have hinf : {P : ℤ[X] | P.natDegree ≤ 1 ∧ 0 < |aeval ξ P| ∧
      |aeval ξ P| ≤ max A 1 * P.supNorm ^ (-((μ : ℝ) - 1))}.Infinite := by
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨N, hNk, hN1, m, hne, hlt⟩ :=
      frequently_atTop.1 ((eventually_ge_atTop 1).and_frequently hA) (⌈B⌉₊ + 1)
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    refine ⟨C (N : ℤ) * X + C (-m), ⟨natDegree_linear_le, ?_, ?_⟩, ?_⟩
    all_goals
      have hv : aeval ξ (C (N : ℤ) * X + C (-m)) = (N : ℝ) * (ξ - (m : ℝ) / (N : ℝ)) := by
        have h1 : aeval ξ (C (N : ℤ) * X + C (-m)) = (N : ℝ) * ξ + -(m : ℝ) := by simp
        rw [h1]
        field_simp
        ring
      have hh : (C (N : ℤ) * X + C (-m) : ℤ[X]).supNorm = max |(m : ℝ)| (N : ℝ) := by
        rw [Polynomial.supNorm_linear]
        rw [show |((-m : ℤ) : ℝ)| = |(m : ℝ)| by push_cast; rw [abs_neg],
          Int.cast_natCast,
          show |(N : ℝ)| = (N : ℝ) from abs_of_pos hN0, max_comm]
      have hH0 : (0 : ℝ) < max |(m : ℝ)| (N : ℝ) := lt_of_lt_of_le hN0 (le_max_right _ _)
    · rw [hv, abs_mul, abs_of_pos hN0]
      have : ξ - (m : ℝ) / (N : ℝ) ≠ 0 := sub_ne_zero.2 hne
      positivity
    · rw [hv, hh, abs_mul, abs_of_pos hN0]
      have hμ0 : (0 : ℝ) < (max |(m : ℝ)| (N : ℝ)) ^ (μ : ℝ) := Real.rpow_pos_of_pos hH0 _
      calc (N : ℝ) * |ξ - (m : ℝ) / (N : ℝ)|
          ≤ (N : ℝ) * (A / (max |(m : ℝ)| (N : ℝ)) ^ (μ : ℝ)) := by gcongr
        _ ≤ (N : ℝ) * (max A 1 / (max |(m : ℝ)| (N : ℝ)) ^ (μ : ℝ)) := by
            gcongr
            exact le_max_left _ _
        _ ≤ (max |(m : ℝ)| (N : ℝ)) * (max A 1 / (max |(m : ℝ)| (N : ℝ)) ^ (μ : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _)
              (div_nonneg (le_trans zero_le_one (le_max_right A 1)) hμ0.le)
        _ = max A 1 * (max |(m : ℝ)| (N : ℝ)) ^ (-((μ : ℝ) - 1)) := by
            rw [show -((μ : ℝ) - 1) = 1 - (μ : ℝ) by ring, Real.rpow_sub hH0, Real.rpow_one]
            field_simp
    · rw [hh]
      refine lt_of_lt_of_le ?_ (le_max_right _ _)
      calc B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
        _ < ((⌈B⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
        _ ≤ (N : ℝ) := by exact_mod_cast hNk
  have h2 := le_mahlerExponent_of_infinite (n := 1) (ξ := ξ)
    (lt_of_lt_of_le zero_lt_one (le_max_right A 1)) hinf
  calc (μ : ℝ≥0∞) = ENNReal.ofReal ((μ : ℝ) - 1) + 1 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one,
          show (μ : ℝ) - 1 + 1 = (μ : ℝ) by ring, ENNReal.ofReal_coe_nnreal]
    _ ≤ mahlerExponent 1 ξ + 1 := add_le_add h2 le_rfl

/-- The other half: **every linear integer polynomial small at `ξ` is a rational approximation**,
one order better, because the leading coefficient is the denominator and is comparable to the
height. -/
theorem mahlerExponent_one_add_one_le_irrationalityExponent (ξ : ℝ) :
    mahlerExponent 1 ξ + 1 ≤ irrationalityExponent ξ := by
  have hkey : ∀ w : ℝ≥0, (mahlerSet 1 ξ (w : ℝ)).Infinite →
      (w : ℝ≥0∞) ≤ irrationalityExponent ξ - 1 := by
    intro w hw
    refine ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_
    have hfr : ∃ᶠ N : ℕ in atTop, ∃ m : ℤ, ξ ≠ m / N ∧
        |ξ - m / N| < (|ξ| + 2) / (max |(m : ℝ)| (N : ℝ)) ^ ((w : ℝ) + 1) := by
      rw [frequently_atTop]
      intro k
      obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
        (max 1 ((k : ℝ) * (|ξ| + 1)))).nonempty
      obtain ⟨N, m, hbnd, hne, hlt⟩ :=
        exists_frac_of_mem_mahlerSet w.coe_nonneg hPmem (lt_of_le_of_lt (le_max_left _ _) hPh)
      refine ⟨N, ?_, m, hne, hlt⟩
      have hk : (k : ℝ) * (|ξ| + 1) < (|ξ| + 1) * (N : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hPh) hbnd
      have hξ : (0 : ℝ) < |ξ| + 1 := by positivity
      have : (k : ℝ) < (N : ℝ) := by nlinarith
      exact_mod_cast this.le
    have h := le_irrationalityExponent_of_frequently_max (ξ := ξ) (μ := (w : ℝ) + 1)
      (C := |ξ| + 2) (by positivity) hfr
    rwa [ENNReal.ofReal_add w.coe_nonneg zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_coe_nnreal] at h
  calc mahlerExponent 1 ξ + 1 ≤ irrationalityExponent ξ - 1 + 1 :=
        add_le_add (mahlerExponent_le_iff.2 hkey) le_rfl
    _ = irrationalityExponent ξ := tsub_add_cancel_of_le (one_le_irrationalityExponent ξ)

/-- **Mahler's exponent at `n = 1` is the irrationality exponent, shifted by one.** -/
theorem mahlerExponent_one_add_one (ξ : ℝ) :
    mahlerExponent 1 ξ + 1 = irrationalityExponent ξ :=
  le_antisymm (mahlerExponent_one_add_one_le_irrationalityExponent ξ)
    (irrationalityExponent_le_mahlerExponent_one_add_one ξ)

/-! ### Degree one: Koksma's exponent -/

/-- A coprime pair names a primitive irreducible linear integer polynomial — the minimal
polynomial of the fraction it names. Irreducibility over `ℤ` is Gauss's lemma against
irreducibility over `ℚ`, where a polynomial of degree one has nothing to factor. -/
private theorem isPrimitive_and_irreducible_linear {a b : ℤ} (ha : a ≠ 0)
    (hab : Int.gcd a b = 1) :
    (C a * X + C b : ℤ[X]).IsPrimitive ∧ Irreducible (C a * X + C b : ℤ[X]) := by
  have hprim : (C a * X + C b : ℤ[X]).IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h1 : r ∣ a := by
      have h := hr 1
      rwa [Polynomial.coeff_linear_one] at h
    have h0 : r ∣ b := by
      have h := hr 0
      rwa [Polynomial.coeff_linear_zero] at h
    exact (Int.isCoprime_iff_gcd_eq_one.2 hab).isUnit_of_dvd' h1 h0
  refine ⟨hprim, ?_⟩
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  refine irreducible_of_degree_eq_one ?_
  rw [Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X]
  exact degree_linear (by simpa using ha)

/-- The fraction named by a linear integer polynomial with nonzero leading coefficient. The
denominator is the absolute value of that coefficient, and the naive height of the fraction is the
naive height of the polynomial. -/
private theorem exists_frac_aux {a b : ℤ} (ha : a ≠ 0) :
    ∃ (N : ℕ) (m : ℤ), 0 < N ∧ ((N : ℕ) : ℝ) = |(a : ℝ)| ∧
      (m : ℝ) / (N : ℝ) = -(b : ℝ) / (a : ℝ) ∧
      max |(m : ℝ)| ((N : ℕ) : ℝ) = max |(a : ℝ)| |(b : ℝ)| := by
  have ha' : (0 : ℝ) < |(a : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 ha)
  rcases ha.lt_or_gt with h | h
  · refine ⟨(-a).toNat, b, by omega, ?_, ?_, ?_⟩
    · rw [show (((-a).toNat : ℕ) : ℝ) = ((-a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast
      rw [abs_of_neg (by exact_mod_cast h)]
    · rw [show (((-a).toNat : ℕ) : ℝ) = ((-a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast
      rw [div_neg, neg_div]
    · rw [show (((-a).toNat : ℕ) : ℝ) = ((-a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast
      rw [abs_of_neg (by exact_mod_cast h : (a : ℝ) < 0), max_comm]
  · refine ⟨a.toNat, -b, by omega, ?_, ?_, ?_⟩
    · rw [show ((a.toNat : ℕ) : ℝ) = ((a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      rw [abs_of_pos (by exact_mod_cast h)]
    · rw [show ((a.toNat : ℕ) : ℝ) = ((a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast
      rw [neg_div]
    · rw [show ((a.toNat : ℕ) : ℝ) = ((a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      push_cast
      rw [abs_neg, abs_of_pos (by exact_mod_cast h : (0 : ℝ) < (a : ℝ)), max_comm]

/-- **From an algebraic approximation of degree one to a fraction.** A member of
`koksmaSet 1 ξ w` of height above `1` is the minimal polynomial of a rational number, which
approximates `ξ` to order `w + 1` in the naive height. -/
private theorem exists_frac_of_mem_koksmaSet {w : ℝ} (hw : 0 ≤ w) {P : ℤ[X]}
    (hP : P ∈ koksmaSet 1 ξ w) (hP1 : 1 < P.supNorm) :
    ∃ (N : ℕ) (m : ℤ), P.supNorm ≤ (|ξ| + 1) * N ∧ ξ ≠ m / N ∧
      |ξ - m / N| < 2 / (max |(m : ℝ)| (N : ℝ)) ^ (w + 1) := by
  obtain ⟨hdeg, hprim, hirr, α, hα, hpos, hle⟩ := hP
  have hH0 : (0 : ℝ) < P.supNorm := zero_lt_one.trans hP1
  have hPeq : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_natDegree_le_one hdeg
  have ha0 : P.coeff 1 ≠ 0 := by
    intro h0
    have hd0 : P.natDegree = 0 := by
      conv_lhs => rw [hPeq]
      rw [h0, map_zero, zero_mul, zero_add, natDegree_C]
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hd0
    exact hirr.not_isUnit (by rw [← hc]; exact isUnit_C.2 (hprim c ⟨1, by rw [mul_one, hc]⟩))
  have ha0' : ((P.coeff 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 ha0
  have hnorm : P.supNorm = max |((P.coeff 1 : ℤ) : ℝ)| |((P.coeff 0 : ℤ) : ℝ)| := by
    conv_lhs => rw [hPeq]
    exact Polynomial.supNorm_linear _ _
  have haα : ((P.coeff 1 : ℤ) : ℝ) * α + ((P.coeff 0 : ℤ) : ℝ) = 0 := by
    have h := hα
    conv_lhs at h => rw [hPeq]
    simpa using h
  obtain ⟨N, m, hN0, hNa, hfrac, hmax⟩ := exists_frac_aux (b := P.coeff 0) ha0
  have hαfrac : (m : ℝ) / (N : ℝ) = α := by
    rw [hfrac, div_eq_iff ha0']
    linear_combination -haα
  have hle1 : |ξ - α| ≤ 1 :=
    hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hP1.le (by linarith))
  have hαbnd : |α| ≤ |ξ| + 1 := by
    have h2 := abs_sub_abs_le_abs_sub α ξ
    rw [abs_sub_comm α ξ] at h2
    linarith
  have hmaxeq : max |(m : ℝ)| ((N : ℕ) : ℝ) = P.supNorm := by rw [hmax, hnorm]
  refine ⟨N, m, ?_, ?_, ?_⟩
  · -- the height is at most `(|ξ| + 1)` times the denominator
    rw [← hmaxeq, hmax, hNa]
    refine max_le (by nlinarith [abs_nonneg ξ, abs_nonneg ((P.coeff 1 : ℤ) : ℝ)]) ?_
    have hb : ((P.coeff 0 : ℤ) : ℝ) = -(α * ((P.coeff 1 : ℤ) : ℝ)) := by linarith
    rw [hb, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right hαbnd (abs_nonneg _)
  · rw [hαfrac]
    exact fun h ↦ absurd (by rw [h, sub_self, abs_zero] : |ξ - α| = 0) (ne_of_gt hpos)
  · rw [hαfrac, hmaxeq]
    have hHw : (0 : ℝ) < P.supNorm ^ (w + 1) := Real.rpow_pos_of_pos hH0 _
    rw [lt_div_iff₀ hHw]
    calc |ξ - α| * P.supNorm ^ (w + 1) ≤ P.supNorm ^ (-w - 1) * P.supNorm ^ (w + 1) := by
          gcongr
      _ = 1 := by rw [← Real.rpow_add hH0, show -w - 1 + (w + 1) = 0 by ring, Real.rpow_zero]
      _ < 2 := by norm_num

/-- The Koksma half of the degree-one identification, easy direction: a rational approximant of
`ξ` of order `w + 1` is an algebraic approximant of degree one. -/
theorem koksmaExponent_one_add_one_le_irrationalityExponent (ξ : ℝ) :
    koksmaExponent 1 ξ + 1 ≤ irrationalityExponent ξ := by
  have hkey : ∀ w : ℝ≥0, (koksmaSet 1 ξ (w : ℝ)).Infinite →
      (w : ℝ≥0∞) ≤ irrationalityExponent ξ - 1 := by
    intro w hw
    refine ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_
    have hfr : ∃ᶠ N : ℕ in atTop, ∃ m : ℤ, ξ ≠ m / N ∧
        |ξ - m / N| < 2 / (max |(m : ℝ)| (N : ℝ)) ^ ((w : ℝ) + 1) := by
      rw [frequently_atTop]
      intro k
      obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
        (max 1 ((k : ℝ) * (|ξ| + 1)))).nonempty
      obtain ⟨N, m, hbnd, hne, hlt⟩ :=
        exists_frac_of_mem_koksmaSet w.coe_nonneg hPmem (lt_of_le_of_lt (le_max_left _ _) hPh)
      refine ⟨N, ?_, m, hne, hlt⟩
      have hk : (k : ℝ) * (|ξ| + 1) < (|ξ| + 1) * (N : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hPh) hbnd
      have hξ : (0 : ℝ) < |ξ| + 1 := by positivity
      have : (k : ℝ) < (N : ℝ) := by nlinarith
      exact_mod_cast this.le
    have h := le_irrationalityExponent_of_frequently_max (ξ := ξ) (μ := (w : ℝ) + 1)
      (C := 2) (by positivity) hfr
    rwa [ENNReal.ofReal_add w.coe_nonneg zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_coe_nnreal] at h
  calc koksmaExponent 1 ξ + 1 ≤ irrationalityExponent ξ - 1 + 1 :=
        add_le_add (koksmaExponent_le_iff.2 hkey) le_rfl
    _ = irrationalityExponent ξ := tsub_add_cancel_of_le (one_le_irrationalityExponent ξ)

/-- The Koksma half of the degree-one identification, hard direction. A rational approximation
`m / N` is put in lowest terms first, which is what makes the linear polynomial it names primitive
and hence irreducible; the reduction *lowers* the height, so the quality of the approximation only
improves. That the reduced heights are still unbounded is not arithmetic: it is
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`, the gap below which a nonzero value at `ξ`
forces a tall polynomial, applied to `N' * (ξ - m / N)`, which tends to `0` because the exponent
exceeds `1`. -/
theorem irrationalityExponent_le_koksmaExponent_one_add_one (ξ : ℝ) :
    irrationalityExponent ξ ≤ koksmaExponent 1 ξ + 1 := by
  rw [irrationalityExponent_le_iff]
  intro μ hμ
  rcases le_or_gt (μ : ℝ) 1 with h1 | h1
  · exact le_trans (by exact_mod_cast h1 : (μ : ℝ≥0∞) ≤ 1) le_add_self
  obtain ⟨A, hA⟩ :=
    (liouvilleWith_iff_frequently_max (ξ := ξ) (μ := (μ : ℝ)) (by positivity)).1 hμ
  have hA'0 : (0 : ℝ) < max A 1 := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hinf : {P : ℤ[X] | P.natDegree ≤ 1 ∧ P.IsPrimitive ∧ Irreducible P ∧
      ∃ α : ℝ, aeval α P = 0 ∧ 0 < |ξ - α| ∧
        |ξ - α| ≤ max A 1 * P.supNorm ^ (-((μ : ℝ) - 1) - 1)}.Infinite := by
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨δ, hδ0, hδ⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ 1 B
    obtain ⟨N, hNk, hN1, m, hne, hlt⟩ := frequently_atTop.1
      ((eventually_ge_atTop 1).and_frequently hA) (⌈(max A 1 / δ) ^ ((μ : ℝ) - 1)⁻¹⌉₊ + 1)
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNz : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hN1
    -- put the fraction in lowest terms
    have hg0 : 0 < Int.gcd m (N : ℤ) :=
      Nat.pos_of_ne_zero fun h ↦ hNz (Int.gcd_eq_zero_iff.1 h).2
    have hg0' : (0 : ℤ) < (Int.gcd m (N : ℤ) : ℤ) := by exact_mod_cast hg0
    have hgm : ((Int.gcd m (N : ℤ) : ℕ) : ℤ) * (m / (Int.gcd m (N : ℤ) : ℕ)) = m :=
      Int.mul_ediv_cancel' (Int.gcd_dvd_left m (N : ℤ))
    have hgN : ((Int.gcd m (N : ℤ) : ℕ) : ℤ) * ((N : ℤ) / (Int.gcd m (N : ℤ) : ℕ)) = (N : ℤ) :=
      Int.mul_ediv_cancel' (Int.gcd_dvd_right m (N : ℤ))
    set m' : ℤ := m / (Int.gcd m (N : ℤ) : ℕ) with hm'def
    set N' : ℤ := (N : ℤ) / (Int.gcd m (N : ℤ) : ℕ) with hN'def
    have hcop : Int.gcd m' N' = 1 := Int.gcd_div_gcd_div_gcd hg0
    have hNZ1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN1
    have hN'0 : (0 : ℤ) < N' := by nlinarith
    have hN'0' : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast hN'0
    obtain ⟨hprim, hirr⟩ := isPrimitive_and_irreducible_linear (a := N') (b := -m') hN'0.ne'
      (by rw [Int.gcd_comm] at hcop; simpa using hcop)
    have hgR : (0 : ℝ) < ((Int.gcd m (N : ℤ) : ℕ) : ℝ) := by exact_mod_cast hg0
    have hmR : (m : ℝ) = ((Int.gcd m (N : ℤ) : ℕ) : ℝ) * (m' : ℝ) := by exact_mod_cast hgm.symm
    have hNR : ((N : ℕ) : ℝ) = ((Int.gcd m (N : ℤ) : ℕ) : ℝ) * (N' : ℝ) := by
      exact_mod_cast hgN.symm
    have hαeq : (m' : ℝ) / (N' : ℝ) = (m : ℝ) / (N : ℝ) := by
      rw [hmR, hNR, mul_div_mul_left _ _ hgR.ne']
    have hval : ∀ y : ℝ, aeval y (C N' * X + C (-m')) = (N' : ℝ) * y + -(m' : ℝ) := fun y ↦ by
      simp
    have haevalα : aeval ((m' : ℝ) / (N' : ℝ)) (C N' * X + C (-m') : ℤ[X]) = 0 := by
      rw [hval]
      field_simp
      ring
    have haevalξ : aeval ξ (C N' * X + C (-m') : ℤ[X])
        = (N' : ℝ) * (ξ - (m : ℝ) / (N : ℝ)) := by
      rw [hval, ← hαeq]
      field_simp
      ring
    have hsup : (C N' * X + C (-m') : ℤ[X]).supNorm = max |(N' : ℝ)| |(m' : ℝ)| := by
      rw [Polynomial.supNorm_linear]
      push_cast
      rw [abs_neg]
    have hg1 : (1 : ℝ) ≤ ((Int.gcd m (N : ℤ) : ℕ) : ℝ) := by exact_mod_cast hg0
    have hsuple : (C N' * X + C (-m') : ℤ[X]).supNorm ≤ max |(m : ℝ)| ((N : ℕ) : ℝ) := by
      rw [hsup]
      refine max_le (le_trans ?_ (le_max_right _ _)) (le_trans ?_ (le_max_left _ _))
      · rw [abs_of_pos hN'0', hNR]
        nlinarith
      · rw [hmR, abs_mul, abs_of_pos hgR]
        nlinarith [abs_nonneg ((m' : ℤ) : ℝ)]
    have hHpos : (0 : ℝ) < max |(m : ℝ)| ((N : ℕ) : ℝ) := lt_of_lt_of_le hN0 (le_max_right _ _)
    have hsup1 : (1 : ℝ) ≤ (C N' * X + C (-m') : ℤ[X]).supNorm :=
      Polynomial.one_le_supNorm hirr.ne_zero
    have hsup0 : (0 : ℝ) < (C N' * X + C (-m') : ℤ[X]).supNorm := zero_lt_one.trans_le hsup1
    have hμ0 : (0 : ℝ) < (μ : ℝ) := by linarith
    have hne' : ξ - (m : ℝ) / (N : ℝ) ≠ 0 := sub_ne_zero.2 hne
    -- the quality of the reduced approximation
    have hquality : |ξ - (m : ℝ) / (N : ℝ)|
        ≤ max A 1 / (C N' * X + C (-m') : ℤ[X]).supNorm ^ (μ : ℝ) := by
      refine hlt.le.trans ?_
      have hden : (C N' * X + C (-m') : ℤ[X]).supNorm ^ (μ : ℝ)
          ≤ (max |(m : ℝ)| ((N : ℕ) : ℝ)) ^ (μ : ℝ) :=
        Real.rpow_le_rpow hsup0.le hsuple hμ0.le
      gcongr
      exact le_max_left A 1
    refine ⟨C N' * X + C (-m'), ⟨natDegree_linear_le, hprim, hirr,
      (m' : ℝ) / (N' : ℝ), haevalα, ?_, ?_⟩, ?_⟩
    · rw [hαeq]
      exact abs_pos.2 hne'
    · rw [hαeq, show -((μ : ℝ) - 1) - 1 = -(μ : ℝ) by ring, Real.rpow_neg hsup0.le]
      rw [← div_eq_mul_inv]
      exact hquality
    · -- the reduced height is above `B`
      refine hδ _ natDegree_linear_le (by rw [haevalξ]; positivity) ?_
      have hsplit : ((N : ℕ) : ℝ) ^ (μ : ℝ)
          = ((N : ℕ) : ℝ) ^ ((μ : ℝ) - 1) * ((N : ℕ) : ℝ) := by
        conv_lhs => rw [show (μ : ℝ) = ((μ : ℝ) - 1) + 1 by ring]
        rw [Real.rpow_add hN0, Real.rpow_one]
      have hNμ0 : (0 : ℝ) < ((N : ℕ) : ℝ) ^ ((μ : ℝ) - 1) := Real.rpow_pos_of_pos hN0 _
      have hbig : max A 1 / δ < ((N : ℕ) : ℝ) ^ ((μ : ℝ) - 1) := by
        have hc : (0 : ℝ) ≤ max A 1 / δ := div_nonneg hA'0.le hδ0.le
        have hlt1 : (max A 1 / δ) ^ ((μ : ℝ) - 1)⁻¹ < ((N : ℕ) : ℝ) := by
          calc (max A 1 / δ) ^ ((μ : ℝ) - 1)⁻¹
              ≤ (⌈(max A 1 / δ) ^ ((μ : ℝ) - 1)⁻¹⌉₊ : ℝ) := Nat.le_ceil _
            _ < ((⌈(max A 1 / δ) ^ ((μ : ℝ) - 1)⁻¹⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
            _ ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hNk
        have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg hc _) hlt1
          (by linarith : (0 : ℝ) < (μ : ℝ) - 1)
        rwa [← Real.rpow_mul hc, inv_mul_cancel₀ (by linarith), Real.rpow_one] at h2
      have hlast : |ξ - (m : ℝ) / (N : ℝ)| < max A 1 / ((N : ℕ) : ℝ) ^ (μ : ℝ) := by
        refine hlt.trans_le ?_
        have hden : ((N : ℕ) : ℝ) ^ (μ : ℝ) ≤ (max |(m : ℝ)| ((N : ℕ) : ℝ)) ^ (μ : ℝ) :=
          Real.rpow_le_rpow hN0.le (le_max_right _ _) hμ0.le
        gcongr
        exact le_max_left A 1
      calc |aeval ξ (C N' * X + C (-m') : ℤ[X])|
          = (N' : ℝ) * |ξ - (m : ℝ) / (N : ℝ)| := by rw [haevalξ, abs_mul, abs_of_pos hN'0']
        _ ≤ ((N : ℕ) : ℝ) * |ξ - (m : ℝ) / (N : ℝ)| := by
            have hNN : (N' : ℝ) ≤ ((N : ℕ) : ℝ) := by rw [hNR]; nlinarith
            gcongr
        _ < ((N : ℕ) : ℝ) * (max A 1 / ((N : ℕ) : ℝ) ^ (μ : ℝ)) := by gcongr
        _ = max A 1 / ((N : ℕ) : ℝ) ^ ((μ : ℝ) - 1) := by rw [hsplit]; field_simp
        _ < δ := by rw [div_lt_iff₀ hNμ0]; rw [div_lt_iff₀ hδ0] at hbig; linarith
  have h2 := le_koksmaExponent_of_infinite (n := 1) (ξ := ξ) hA'0 hinf
  calc (μ : ℝ≥0∞) = ENNReal.ofReal ((μ : ℝ) - 1) + 1 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one,
          show (μ : ℝ) - 1 + 1 = (μ : ℝ) by ring, ENNReal.ofReal_coe_nnreal]
    _ ≤ koksmaExponent 1 ξ + 1 := add_le_add h2 le_rfl

/-- **Koksma's exponent at `n = 1` is the irrationality exponent, shifted by one** — which is
exactly what the normalization `-w - 1` was chosen for. -/
theorem koksmaExponent_one_add_one (ξ : ℝ) :
    koksmaExponent 1 ξ + 1 = irrationalityExponent ξ :=
  le_antisymm (koksmaExponent_one_add_one_le_irrationalityExponent ξ)
    (irrationalityExponent_le_koksmaExponent_one_add_one ξ)

/-- **Mahler's and Koksma's exponents agree at `n = 1`.** -/
theorem koksmaExponent_one_eq_mahlerExponent_one (ξ : ℝ) :
    koksmaExponent 1 ξ = mahlerExponent 1 ξ :=
  WithTop.add_right_cancel ENNReal.one_ne_top
    ((koksmaExponent_one_add_one ξ).trans (mahlerExponent_one_add_one ξ).symm)

/-! ### Restricting the polynomials: primitive -/

/-- The arithmetic that turns a large height into a small value: above `max 1 (δ⁻¹ ^ w⁻¹)` the
quantity `H ^ (-w)` is below `δ`. -/
theorem rpow_neg_lt_of_max_lt {w δ H : ℝ} (hw : 0 < w) (hδ : 0 < δ)
    (hH : max 1 (δ⁻¹ ^ w⁻¹) < H) : H ^ (-w) < δ := by
  have hH1 : (1 : ℝ) < H := lt_of_le_of_lt (le_max_left _ _) hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans hH1
  have hpos : (0 : ℝ) < H ^ w := Real.rpow_pos_of_pos hH0 w
  have h1 : δ⁻¹ < H ^ w := by
    have h2 : δ⁻¹ = (δ⁻¹ ^ w⁻¹) ^ w := by
      rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hw.ne', Real.rpow_one]
    rw [h2]
    exact Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _)
      (lt_of_le_of_lt (le_max_right _ _) hH) hw
  rw [Real.rpow_neg hH0.le, inv_eq_one_div, div_lt_iff₀ hpos]
  calc (1 : ℝ) = δ * δ⁻¹ := by field_simp
    _ < δ * H ^ w := by gcongr

/-- If one positive quantity is at most `K` times another, the *second* with a nonpositive
exponent is at most `K ^ u` times the first with that exponent. This is how a height comparison
in one direction becomes a comparison of approximation qualities in the other. -/
theorem rpow_neg_le_mul_rpow_neg {u a b K : ℝ} (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (h : b ≤ K * a) : a ^ (-u) ≤ K ^ u * b ^ (-u) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _), one_mul]
  calc b ^ u ≤ (K * a) ^ u := Real.rpow_le_rpow hb.le h hu
    _ = K ^ u * a ^ u := Real.mul_rpow hK.le ha.le

/-- Lowering the exponent of a base at least `1`. -/
theorem rpow_neg_le_rpow_neg {w a b : ℝ} (hw : 0 ≤ w) (ha : 1 ≤ a) (hab : a ≤ b) :
    b ^ (-w) ≤ a ^ (-w) := by
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans_le ha
  have hb0 : (0 : ℝ) < b := ha0.trans_le hab
  rw [Real.rpow_neg ha0.le, Real.rpow_neg hb0.le]
  gcongr

/-- **The primitive solutions are already infinitely many.** Dividing by the content only improves
the inequality — it divides the value and the height by the same nonzero integer, and the height
carries a nonpositive exponent — so the primitive parts are again solutions. That they are
*infinitely many* is not a counting argument on the fibres of `Polynomial.primPart`: it is
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt`, the height gap, which turns a small nonzero
value at `ξ` into a large height whatever polynomial produced it. -/
theorem infinite_primitive_mahlerSet {w : ℝ} (hw0 : 0 < w) (hw : (mahlerSet n ξ w).Infinite) :
    {P ∈ mahlerSet n ξ w | P.IsPrimitive}.Infinite := by
  refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
  obtain ⟨δ, hδ0, hδ⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ n B
  obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
    (max 1 (δ⁻¹ ^ w⁻¹))).nonempty
  obtain ⟨hdeg, hpos, hle⟩ := hPmem
  have hP0 : P ≠ 0 := ne_zero_of_mem_mahlerSet ⟨hdeg, hpos, hle⟩
  have hc0 : P.content ≠ 0 := fun h ↦ hP0 (Polynomial.content_eq_zero_iff.1 h)
  have hcR : (1 : ℝ) ≤ |((P.content : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hc0
  have hPQ : P = C P.content * P.primPart := Polynomial.eq_C_content_mul_primPart P
  have hvalQ : aeval ξ P = ((P.content : ℤ) : ℝ) * aeval ξ P.primPart := by
    conv_lhs => rw [hPQ]
    simp
  have hnormQ : P.supNorm = |((P.content : ℤ) : ℝ)| * P.primPart.supNorm := by
    conv_lhs => rw [hPQ]
    rw [Polynomial.supNorm_C_mul, Int.norm_eq_abs]
  have hQdeg : P.primPart.natDegree ≤ n := by rw [Polynomial.natDegree_primPart]; exact hdeg
  have hQ1 : (1 : ℝ) ≤ P.primPart.supNorm :=
    Polynomial.one_le_supNorm (Polynomial.primPart_ne_zero P)
  have hQpos : 0 < |aeval ξ P.primPart| := by
    rw [hvalQ, abs_mul] at hpos
    nlinarith [abs_nonneg (aeval ξ P.primPart), abs_nonneg ((P.content : ℤ) : ℝ)]
  have hQle : |aeval ξ P.primPart| ≤ |aeval ξ P| := by
    rw [hvalQ, abs_mul]
    nlinarith [abs_nonneg (aeval ξ P.primPart)]
  have hQnorm : P.primPart.supNorm ≤ P.supNorm := by
    rw [hnormQ]
    nlinarith
  refine ⟨P.primPart, ⟨⟨hQdeg, hQpos, hQle.trans (hle.trans
    (rpow_neg_le_rpow_neg hw0.le hQ1 hQnorm))⟩, Polynomial.isPrimitive_primPart P⟩, ?_⟩
  exact hδ _ hQdeg hQpos
    (lt_of_le_of_lt (hQle.trans hle) (rpow_neg_lt_of_max_lt hw0 hδ0 hPh))

/-- **Restricting to primitive polynomials does not change Mahler's exponent.** -/
theorem mahlerExponent_eq_iSup_primitive (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ
      = ⨆ (w : ℝ≥0) (_ : {P ∈ mahlerSet n ξ (w : ℝ) | P.IsPrimitive}.Infinite), (w : ℝ≥0∞) := by
  refine le_antisymm (mahlerExponent_le_iff.2 fun w hw ↦ ?_)
    (iSup₂_le fun w hw ↦ le_mahlerExponent (Set.Infinite.mono (fun _ hP ↦ hP.1) hw))
  rcases eq_or_ne w 0 with h0 | h0
  · simp [h0]
  have hw0 : (0 : ℝ) < (w : ℝ) :=
    w.coe_nonneg.lt_of_ne' fun h ↦ h0 (NNReal.coe_eq_zero.1 h)
  exact le_iSup₂ (f := fun (w : ℝ≥0)
    (_ : {P ∈ mahlerSet n ξ (w : ℝ) | P.IsPrimitive}.Infinite) ↦ (w : ℝ≥0∞)) w
    (infinite_primitive_mahlerSet hw0 hw)

/-! ### Invariance under the rational Möbius group -/

/-- **An integer affine substitution does not raise Mahler's exponent.** The substitution
`P ↦ P.comp (t X + s)` sends a solution at `t ξ + s` to a solution at `ξ`, multiplying the height
by at most a constant, which the exponent absorbs; that the images are infinitely many is again
the height gap. No hypothesis on `t` is needed — at `t = 0` the left side is the exponent of an
integer translate of `0`, which is `0`. -/
theorem mahlerExponent_intAffine_le (n : ℕ) (ξ : ℝ) (t s : ℤ) :
    mahlerExponent n ((t : ℝ) * ξ + s) ≤ mahlerExponent n ξ := by
  refine mahlerExponent_le_iff.2 fun w hw ↦ ?_
  rcases eq_or_ne w 0 with h0 | h0
  · simp [h0]
  have hw0 : (0 : ℝ) < (w : ℝ) :=
    w.coe_nonneg.lt_of_ne' fun h ↦ h0 (NNReal.coe_eq_zero.1 h)
  have hK1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), ((C t * X + C s : ℤ[X]) ^ i).supNorm :=
    Polynomial.one_le_sum_supNorm_pow _ n
  have hK0 : (0 : ℝ) < ∑ i ∈ Finset.range (n + 1), ((C t * X + C s : ℤ[X]) ^ i).supNorm :=
    zero_lt_one.trans_le hK1
  have hmain : ENNReal.ofReal (w : ℝ) ≤ mahlerExponent n ξ := by
    refine le_mahlerExponent_of_infinite
      (A := (∑ i ∈ Finset.range (n + 1), ((C t * X + C s : ℤ[X]) ^ i).supNorm) ^ (w : ℝ))
      (Real.rpow_pos_of_pos hK0 _) ?_
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨δ, hδ0, hδ⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ n B
    obtain ⟨P, hPmem, hPh⟩ := (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1)
      (max 1 (δ⁻¹ ^ ((w : ℝ))⁻¹))).nonempty
    obtain ⟨hdeg, hpos, hle⟩ := hPmem
    have hval : aeval ξ (P.comp (C t * X + C s)) = aeval ((t : ℝ) * ξ + s) P := by
      rw [Polynomial.aeval_comp]
      congr 1
      simp
    have hdeg' : (P.comp (C t * X + C s)).natDegree ≤ n := by
      refine natDegree_comp_le.trans ?_
      calc P.natDegree * (C t * X + C s : ℤ[X]).natDegree ≤ n * 1 :=
            Nat.mul_le_mul hdeg natDegree_linear_le
        _ = n := by ring
    have hnorm := Polynomial.supNorm_comp_le (q := C t * X + C s) hdeg
    have hpos' : 0 < |aeval ξ (P.comp (C t * X + C s))| := by rw [hval]; exact hpos
    have hne0 : P.comp (C t * X + C s) ≠ 0 := fun h ↦ by
      rw [h] at hpos'; simp at hpos'
    have hsup1 : (1 : ℝ) ≤ (P.comp (C t * X + C s)).supNorm := Polynomial.one_le_supNorm hne0
    have hP1 : (1 : ℝ) ≤ P.supNorm :=
      Polynomial.one_le_supNorm (ne_zero_of_mem_mahlerSet ⟨hdeg, hpos, hle⟩)
    have hsmall : |aeval ξ (P.comp (C t * X + C s))| ≤ P.supNorm ^ (-(w : ℝ)) := by
      rw [hval]; exact hle
    refine ⟨P.comp (C t * X + C s), ⟨hdeg', hpos', hsmall.trans ?_⟩,
      hδ _ hdeg' hpos' (lt_of_le_of_lt hsmall (rpow_neg_lt_of_max_lt hw0 hδ0 hPh))⟩
    -- the height changed by at most the constant
    have hstep := rpow_neg_le_rpow_neg (w := (w : ℝ)) hw0.le hsup1 hnorm
    rw [Real.mul_rpow hK0.le (by linarith)] at hstep
    calc P.supNorm ^ (-(w : ℝ))
        = (∑ i ∈ Finset.range (n + 1), ((C t * X + C s : ℤ[X]) ^ i).supNorm) ^ (w : ℝ)
            * ((∑ i ∈ Finset.range (n + 1), ((C t * X + C s : ℤ[X]) ^ i).supNorm) ^ (-(w : ℝ))
              * P.supNorm ^ (-(w : ℝ))) := by
          rw [← mul_assoc, ← Real.rpow_add hK0, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ _ := by gcongr
  rwa [ENNReal.ofReal_coe_nnreal] at hmain

/-- **Inversion does not raise Mahler's exponent.** The substitution is `Polynomial.reflect n`,
which permutes the coefficients and so preserves the naive height *exactly*; the value at `ξ` is
the value at `ξ⁻¹` times `ξ ^ n`. Unlike every other step of this section, no height gap is
needed: the heights of the images are literally the heights of the sources. -/
theorem mahlerExponent_inv_le (n : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    mahlerExponent n ξ⁻¹ ≤ mahlerExponent n ξ := by
  have : Invertible ξ⁻¹ := invertibleOfNonzero (inv_ne_zero hξ)
  have hinvOf : (⅟(ξ⁻¹) : ℝ) = ξ := by rw [invOf_eq_inv, inv_inv]
  refine mahlerExponent_le_iff.2 fun w hw ↦ ?_
  have hmain : ENNReal.ofReal (w : ℝ) ≤ mahlerExponent n ξ := by
    refine le_mahlerExponent_of_infinite (A := max (|ξ| ^ n) 1)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_
    refine Polynomial.infinite_of_forall_exists_lt_supNorm fun B ↦ ?_
    obtain ⟨P, hPmem, hPh⟩ :=
      (Polynomial.infinite_sep_lt_supNorm hw (fun _ hP ↦ hP.1) B).nonempty
    obtain ⟨hdeg, hpos, hle⟩ := hPmem
    have hval : aeval ξ (P.reflect n) = aeval ξ⁻¹ P * ξ ^ n := by
      have h := Polynomial.eval₂_reflect_mul_pow (algebraMap ℤ ℝ) ξ⁻¹ n P hdeg
      rw [hinvOf] at h
      rw [aeval_def, aeval_def, ← h, mul_assoc, ← mul_pow, inv_mul_cancel₀ hξ, one_pow, mul_one]
    have hnorm : (P.reflect n).supNorm = P.supNorm := Polynomial.supNorm_reflect n P
    have hdeg' : (P.reflect n).natDegree ≤ n :=
      Polynomial.natDegree_reflect_le.trans (by rw [max_eq_left hdeg])
    have hξn : (0 : ℝ) < |ξ| ^ n := by positivity
    have hpos' : 0 < |aeval ξ (P.reflect n)| := by
      rw [hval, abs_mul, abs_pow]
      exact mul_pos hpos hξn
    refine ⟨P.reflect n, ⟨hdeg', hpos', ?_⟩, by rw [hnorm]; exact hPh⟩
    rw [hval, abs_mul, abs_pow, hnorm]
    calc |aeval ξ⁻¹ P| * |ξ| ^ n ≤ P.supNorm ^ (-(w : ℝ)) * |ξ| ^ n := by gcongr
      _ = |ξ| ^ n * P.supNorm ^ (-(w : ℝ)) := by ring
      _ ≤ max (|ξ| ^ n) 1 * P.supNorm ^ (-(w : ℝ)) := by
          gcongr
          · exact Real.rpow_nonneg (Polynomial.supNorm_nonneg P) _
          · exact le_max_left _ _
  rwa [ENNReal.ofReal_coe_nnreal] at hmain

theorem mahlerExponent_inv (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ⁻¹ = mahlerExponent n ξ := by
  rcases eq_or_ne ξ 0 with h | h
  · rw [h, inv_zero]
  refine le_antisymm (mahlerExponent_inv_le n h) ?_
  have h2 := mahlerExponent_inv_le n (inv_ne_zero h)
  rwa [inv_inv] at h2

theorem mahlerExponent_add_intCast (n : ℕ) (ξ : ℝ) (s : ℤ) :
    mahlerExponent n (ξ + s) = mahlerExponent n ξ := by
  refine le_antisymm ?_ ?_
  · simpa using mahlerExponent_intAffine_le n ξ 1 s
  · have h := mahlerExponent_intAffine_le n (ξ + s) 1 (-s)
    rw [show ((1 : ℤ) : ℝ) * (ξ + (s : ℝ)) + ((-s : ℤ) : ℝ) = ξ by push_cast; ring] at h
    exact h

theorem mahlerExponent_div_intCast (n : ℕ) (ξ : ℝ) {t : ℤ} (ht : t ≠ 0) :
    mahlerExponent n (ξ / t) = mahlerExponent n ξ := by
  have htR : ((t : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 ht
  refine le_antisymm ?_ ?_
  · rw [← mahlerExponent_inv n (ξ / t), ← mahlerExponent_inv n ξ,
      show (ξ / ((t : ℤ) : ℝ))⁻¹ = ((t : ℤ) : ℝ) * ξ⁻¹ + ((0 : ℤ) : ℝ) by
        push_cast; rw [add_zero, inv_div, div_eq_mul_inv]]
    exact mahlerExponent_intAffine_le n ξ⁻¹ t 0
  · conv_lhs => rw [show ξ = ((t : ℤ) : ℝ) * (ξ / ((t : ℤ) : ℝ)) + ((0 : ℤ) : ℝ) by
      push_cast; rw [add_zero]; field_simp]
    exact mahlerExponent_intAffine_le n (ξ / t) t 0

theorem mahlerExponent_intCast_mul (n : ℕ) (ξ : ℝ) {t : ℤ} (ht : t ≠ 0) :
    mahlerExponent n ((t : ℝ) * ξ) = mahlerExponent n ξ := by
  have h := mahlerExponent_div_intCast n (((t : ℤ) : ℝ) * ξ) ht
  rw [mul_div_cancel_left₀ _ (Int.cast_ne_zero.2 ht)] at h
  exact h.symm

theorem mahlerExponent_mul_ratCast (n : ℕ) (ξ : ℝ) {r : ℚ} (hr : r ≠ 0) :
    mahlerExponent n (ξ * r) = mahlerExponent n ξ := by
  have hnum : (r.num : ℤ) ≠ 0 := Rat.num_ne_zero.2 hr
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_nz
  have hdenR : (((r.den : ℤ)) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hden
  rw [show ξ * (r : ℝ) = (((r.num : ℤ) : ℝ) * ξ) / (((r.den : ℤ)) : ℝ) by
    rw [Rat.cast_def]; push_cast; field_simp]
  rw [mahlerExponent_div_intCast n _ hden, mahlerExponent_intCast_mul n ξ hnum]

theorem mahlerExponent_add_ratCast (n : ℕ) (ξ : ℝ) (r : ℚ) :
    mahlerExponent n (ξ + r) = mahlerExponent n ξ := by
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_nz
  have hdenR : (((r.den : ℤ)) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hden
  rw [show ξ + (r : ℝ)
      = ((((r.den : ℤ)) : ℝ) * ξ + ((r.num : ℤ) : ℝ)) / (((r.den : ℤ)) : ℝ) by
    rw [Rat.cast_def]; push_cast; field_simp]
  rw [mahlerExponent_div_intCast n _ hden, mahlerExponent_add_intCast n _ r.num,
    mahlerExponent_intCast_mul n ξ hden]

/-- **Mahler's exponent is invariant under the rational Möbius group.** Exactly as for the
irrationality exponent in Layer 1.1, the map is decomposed into an affine part and an inversion;
here the affine part is a polynomial substitution and the inversion is `Polynomial.reflect n`. -/
theorem mahlerExponent_mobius (n : ℕ) (ξ : ℝ) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0)
    (hden : (c : ℝ) * ξ + d ≠ 0) :
    mahlerExponent n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) = mahlerExponent n ξ := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : (d : ℝ) ≠ 0 := by simpa using hden
    have hdq : d ≠ 0 := Rat.cast_ne_zero.1 hd
    have ha : a ≠ 0 := fun h ↦ hdet (by rw [h]; ring)
    have key : ((a : ℝ) * ξ + b) / (((0 : ℚ) : ℝ) * ξ + d)
        = ξ * ((a / d : ℚ) : ℝ) + ((b / d : ℚ) : ℝ) := by
      push_cast
      rw [zero_mul, zero_add]
      field_simp
    rw [key, mahlerExponent_add_ratCast, mahlerExponent_mul_ratCast _ _ (div_ne_zero ha hdq)]
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
    rw [key, mahlerExponent_add_ratCast, mahlerExponent_mul_ratCast _ _ hr,
      mahlerExponent_inv, mahlerExponent_add_ratCast]

/-! ### Two named values -/

/-- At a rational number the exponents of degree one vanish. The shift by one in
`mahlerExponent 1 ξ + 1 = irrationalityExponent ξ` is therefore a real shift: the irrationality
exponent is `1` there, not `0`. -/
@[simp] theorem mahlerExponent_one_ratCast (q : ℚ) : mahlerExponent 1 (q : ℝ) = 0 := by
  have h := mahlerExponent_one_add_one (q : ℝ)
  rw [irrationalityExponent_ratCast] at h
  refine le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 ?_) bot_le
  rw [h, zero_add]

@[simp] theorem koksmaExponent_one_ratCast (q : ℚ) : koksmaExponent 1 (q : ℝ) = 0 := by
  rw [koksmaExponent_one_eq_mahlerExponent_one, mahlerExponent_one_ratCast]

/-- **Dirichlet's theorem on Mahler's exponent**: an irrational number is a root of linear
integer polynomials to order at least one. -/
theorem one_le_mahlerExponent_one (hξ : Irrational ξ) : 1 ≤ mahlerExponent 1 ξ := by
  have h := mahlerExponent_one_add_one ξ
  have h2 := two_le_irrationalityExponent hξ
  rw [← h, show (2 : ℝ≥0∞) = 1 + 1 by norm_num] at h2
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h2

theorem one_le_koksmaExponent_one (hξ : Irrational ξ) : 1 ≤ koksmaExponent 1 ξ := by
  rw [koksmaExponent_one_eq_mahlerExponent_one]
  exact one_le_mahlerExponent_one hξ

/-! ### Acceptance criteria -/

/-- The definition of `mahlerExponent` in the shape the roadmap pinned it. -/
example (n : ℕ) (ξ : ℝ) : mahlerExponent n ξ =
    ⨆ (w : ℝ≥0) (_ : {P : ℤ[X] | P.natDegree ≤ n ∧ 0 < |aeval ξ P| ∧
      |aeval ξ P| ≤ P.supNorm ^ (-(w : ℝ))}.Infinite), (w : ℝ≥0∞) := rfl

/-- **Mahler's and Koksma's exponents agree at `n = 1`, and both are the irrationality exponent
shifted by one.** This is the acceptance test of the layer: the two definitions, which look
nothing alike — one quantifies over polynomials, the other over algebraic numbers — meet the
object of Layer 1.1 at the only degree where all three are defined. -/
example (ξ : ℝ) :
    koksmaExponent 1 ξ = mahlerExponent 1 ξ ∧ mahlerExponent 1 ξ + 1 = irrationalityExponent ξ :=
  ⟨koksmaExponent_one_eq_mahlerExponent_one ξ, mahlerExponent_one_add_one ξ⟩

/-- Dirichlet at a concrete irrational. -/
example : 1 ≤ mahlerExponent 1 (√2) := one_le_mahlerExponent_one irrational_sqrt_two

/-- Monotonicity in the degree. -/
example (ξ : ℝ) : mahlerExponent 3 ξ ≤ mahlerExponent 5 ξ := mahlerExponent_mono (by norm_num) ξ

/-- The exponent is a projective invariant of `ξ` over `ℚ`. -/
example (n : ℕ) (ξ : ℝ) : mahlerExponent n (1 / ξ) = mahlerExponent n ξ := by
  rw [one_div, mahlerExponent_inv]

/-- **Rejection test: `mahlerExponent 1` is not the irrationality exponent.** The normalization
of Layer 1.2 is `−w` and that of Layer 1.1 is `−μ`; the two differ by exactly the denominator,
and at a rational the difference is the whole value. -/
example : ¬ ∀ ξ : ℝ, mahlerExponent 1 ξ = irrationalityExponent ξ := by
  intro h
  have h1 := h ((0 : ℚ) : ℝ)
  rw [irrationalityExponent_ratCast, mahlerExponent_one_ratCast] at h1
  exact absurd h1 (by norm_num)

/-- **Rejection test: the determinant hypothesis of `mahlerExponent_mobius` is load-bearing.**
At `a = b = c = d = 1` the determinant vanishes, the map is constant `1`, and the exponent of `√2`
is not the exponent of `1`. -/
example : ¬ ∀ ξ : ℝ, (1 : ℝ) * ξ + 1 ≠ 0 →
    mahlerExponent 1 (((1 : ℝ) * ξ + 1) / ((1 : ℝ) * ξ + 1)) = mahlerExponent 1 ξ := by
  intro h
  have hne : (1 : ℝ) * √2 + 1 ≠ 0 := by positivity
  have h1 := h (√2) hne
  rw [div_self hne] at h1
  have h2 : mahlerExponent 1 (1 : ℝ) = 0 := by
    simpa using mahlerExponent_one_ratCast 1
  rw [h2] at h1
  have h3 := one_le_mahlerExponent_one irrational_sqrt_two
  rw [← h1] at h3
  exact absurd h3 (by norm_num)

end Real
