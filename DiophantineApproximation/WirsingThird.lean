/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WirsingSystem
public import DiophantineApproximation.BoxPrinciple

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Wirsing's third inequality

For every `ξ` that is not algebraic of degree at most `n`,

`w_n(ξ) ≤ w_n^*(ξ) (w_n(ξ) + 1 - n)`,

which is Wirsing's lower bound `w_n^* ≥ w / (w - n + 1)` for `w = w_n(ξ)`, cleared of its
division. At `w = n` — the generic value, and the one the box principle guarantees from below — it
reads `n ≤ w_n^*(ξ)`: Wirsing's conjecture holds at every `ξ` whose Mahler exponent is as small as
it can be.

The proof is the one Wirsing gave in 1961. For each height `H`, `DiophantineApproximation/
WirsingSystem.lean` produces an integer polynomial `P` of degree at most `n` which is at most
`H ^ (-w)` at `ξ`, at most `H` at `n - 1` further points, and of naive height at most
`K H ^ (w - n + 1)`. Because `w` exceeds the Mahler exponent, `H(P)` cannot be small: it is at
least `H ^ (w / w')` for any `w'` between the exponent and `w`. That makes `P` large at every test
point relative to its height, so it has a root near each of them — hence exactly one root near
`ξ`, and that root is real. The root `α` then satisfies `|ξ - α| ≪ |P ξ| / H(P)`, and feeding
`H(P) ≪ H ^ (w - n + 1)` into `H ^ (-w)` turns that into `|ξ - α| ≪ H(P) ^ (-w/(w-n+1) - 1)`.

## Main results

* `Real.mahlerExponent_le_koksmaExponent_mul`: **Wirsing's third inequality.**
* `Real.le_koksmaExponent_of_mahlerExponent_lt`: the construction behind it, at one pair of
  exponents `w' < w` straddling `w_n(ξ)`.
* `Real.irrational_of_aeval_ne_zero` and `Real.mahlerExponent_degree_zero`: the two degenerate
  cases the statement has to survive.

## Implementation notes

⚠ **The two degenerate cases are real.** At `n = 0` the hypothesis holds for every `ξ` and both
exponents vanish, so the inequality is `0 ≤ 0`; `Real.mahlerExponent_degree_zero` is needed to see
it, because a constant polynomial has `|P ξ| = H(P)`, and `H(P) ≤ H(P) ^ (-w)` forces
`H(P) = 1`. At `w_n(ξ) = ⊤` the right-hand side is `w_n^* ⬝ ⊤`, which is `⊤` exactly when
`w_n^* ≠ 0`, and that is Dirichlet's theorem at degree one — so the proof needs `ξ` to be
irrational, which is `Real.irrational_of_aeval_ne_zero`.

⚠ **The limit `w ↓ w_n(ξ)` is taken at the very end, and only there.** The construction needs a
`w` *strictly above* the Mahler exponent, since what makes `H(P)` large is precisely that
`|P ξ| ≤ H ^ (-w)` is better than the exponent allows. The bound it produces, `w / (w - n + 1)`,
is *decreasing* in `w`, so no single `w` gives the theorem; continuity of `w ↦ w / (w - n + 1)`
at `w_n(ξ)` does.

⚠ **`P` is replaced by an irreducible factor of its primitive part, and Gelfond's inequality pays
for it.** `koksmaSet` asks for the minimal polynomial of the approximant, and the height of a
factor can exceed the height of the product; `Polynomial.supNorm_mul_supNorm_le_two_pow_int` caps
the loss at `2 ^ n`, which is absorbed by the constant `A` of
`Real.le_koksmaExponent_of_infinite`.

## References

Y. Bugeaud, *Exponents of Diophantine approximation*, in: Dynamics and Analytic Number Theory,
Cambridge University Press (2016), Theorem 2.6 and Corollary 2.7; E. Wirsing, *Approximation mit
algebraischen Zahlen beschränkten Grades*, J. reine angew. Math. **206** (1961), 67–77.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter Polynomial
open scoped ENNReal NNReal Topology

namespace Real

variable {n : ℕ} {ξ : ℝ}

/-! ### The two degenerate cases -/

/-- A real number that is not a root of a nonzero integer polynomial of degree at most `n ≥ 1` is
irrational. -/
theorem irrational_of_aeval_ne_zero (hn : 0 < n)
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) : Irrational ξ := by
  rintro ⟨q, rfl⟩
  have hden : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
  refine hξ (C (q.den : ℤ) * X + C (-q.num)) ?_ ?_ ?_
  · intro h0
    have h1 : (C (q.den : ℤ) * X + C (-q.num)).coeff 1 = (q.den : ℤ) := coeff_linear_one _ _
    rw [h0, coeff_zero] at h1
    exact hden h1.symm
  · refine le_trans (natDegree_le_iff_coeff_eq_zero.2 fun m hm ↦ ?_) hn
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
    exact coeff_linear_add_two _ _ i
  · have hd : ((q.den : ℝ)) ≠ 0 := by exact_mod_cast q.den_nz
    have heval : aeval ((q : ℚ) : ℝ) (C (q.den : ℤ) * X + C (-q.num)) =
        (q.den : ℝ) * ((q : ℚ) : ℝ) + (-(q.num) : ℝ) := by
      simp
    rw [heval, Rat.cast_def]
    field_simp
    ring

/-- Mahler's exponent vanishes at degree zero: a nonzero constant polynomial has `|P ξ| = H(P)`,
and `H(P) ≤ H(P) ^ (-w)` forces `H(P) = 1`. -/
theorem mahlerExponent_degree_zero (ξ : ℝ) : mahlerExponent 0 ξ = 0 := by
  refine le_antisymm (mahlerExponent_le_iff.2 fun v hv ↦ absurd ?_ hv) zero_le
  refine Set.Finite.subset (Polynomial.finite_setOf_natDegree_le_supNorm_le 0 1) ?_
  rintro P hP
  obtain ⟨hdeg, hpos, hle⟩ := hP
  have hP0 : P ≠ 0 := ne_zero_of_mem_mahlerSet ⟨hdeg, hpos, hle⟩
  have hC : P = C (P.coeff 0) := (Polynomial.eq_C_of_natDegree_le_zero hdeg)
  have hval : |aeval ξ P| = P.supNorm := by
    conv_lhs => rw [hC]
    conv_rhs => rw [hC]
    rw [aeval_C, supNorm_C]
    simp [Int.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  rw [hval] at hle
  have h2 : P.supNorm ^ (-(v : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (neg_nonpos.2 v.coe_nonneg)
  exact ⟨hdeg, le_trans hle h2⟩

/-- Koksma's exponent vanishes at degree zero as well: a constant polynomial with a root is the
zero polynomial, which is not irreducible, so `koksmaSet 0 ξ w` is empty. -/
theorem koksmaExponent_degree_zero (ξ : ℝ) : koksmaExponent 0 ξ = 0 := by
  refine le_antisymm (koksmaExponent_le_iff.2 fun v hv ↦ absurd ?_ hv) zero_le
  refine Set.Finite.subset Set.finite_empty ?_
  rintro P ⟨hdeg, -, hirr, α, hroot, -, -⟩
  exfalso
  have hC : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
  have hcast : ((P.coeff 0 : ℤ) : ℝ) = 0 := by
    rw [hC] at hroot
    simpa using hroot
  have h0 : P.coeff 0 = 0 := by exact_mod_cast hcast
  rw [h0, map_zero] at hC
  exact hirr.ne_zero hC

/-! ### The construction -/

/-- **Wirsing's construction.** If `w' < w` and the Mahler exponent is below `w'`, then Koksma's
exponent is at least `w / (w - n + 1)`. -/
theorem le_koksmaExponent_of_mahlerExponent_lt (hn : 0 < n)
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) {w w' : ℝ}
    (hnw : (n : ℝ) ≤ w') (hww : w' < w) (hlt : mahlerExponent n ξ < ENNReal.ofReal w') :
    ENNReal.ofReal (w / (w - n + 1)) ≤ koksmaExponent n ξ := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw'0 : 0 < w' := by linarith
  have hw0 : 0 < w := by linarith
  have hwn : (1 : ℝ) ≤ w - n + 1 := by linarith
  set lam : ℝ := w / (w - n + 1) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  set B : ℝ := |ξ| + n + 2 with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    have := abs_nonneg ξ
    rw [hBdef]; linarith
  set D : ℝ := (2 * B + 2) ^ n with hDdef
  have hD0 : 0 < D := by rw [hDdef]; positivity
  set E : ℝ := (8 * B + 8) ^ n with hEdef
  have hE0 : 0 < E := by rw [hEdef]; positivity
  obtain ⟨K, hK0, hK⟩ := exists_poly_small_at_testPoints ξ hn
  -- the polynomials that beat `w'` are finitely many
  have hfin : (mahlerSet n ξ w').Finite := by
    by_contra hcon
    set v : ℝ≥0 := ⟨w', hw'0.le⟩ with hvdef
    have hcoe : ENNReal.ofReal w' = (v : ℝ≥0∞) := by
      rw [ENNReal.ofReal, hvdef, Real.toNNReal_of_nonneg hw'0.le]
      rfl
    have hle : ENNReal.ofReal w' ≤ mahlerExponent n ξ := by
      rw [hcoe]
      exact le_mahlerExponent (w := v) hcon
    exact absurd hlt (not_lt.2 hle)
  obtain ⟨H₀, hH₀⟩ := Polynomial.exists_supNorm_le_of_finite hfin
  set A : ℝ := D * K ^ lam * (2 ^ n : ℝ) ^ (lam + 1) with hAdef
  have hA0 : 0 < A := by
    rw [hAdef]
    have h1 : (0 : ℝ) < K ^ lam := Real.rpow_pos_of_pos hK0 lam
    have h2 : (0 : ℝ) < (2 ^ n : ℝ) ^ (lam + 1) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  refine le_koksmaExponent_of_infinite hA0 ?_
  refine Polynomial.infinite_of_forall_exists_lt_supNorm fun Bnd ↦ ?_
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt ξ n Bnd
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt ξ n H₀
  -- choose the height
  have hθ : 1 < w / w' := (one_lt_div hw'0).2 hww
  have hev1 : ∀ᶠ H : ℝ in atTop, (1 : ℝ) ≤ H := eventually_ge_atTop 1
  have hev2 : ∀ᶠ H : ℝ in atTop, H ^ (-w) < δ₂ :=
    (tendsto_rpow_neg_atTop hw0).eventually_lt_const hδ₂0
  have hev3 : ∀ᶠ H : ℝ in atTop, E ≤ H ^ (w / w' - 1) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop E
  have hev4 : ∀ᶠ H : ℝ in atTop, D * H ^ (-w) < δ₁ := by
    have hten := (tendsto_rpow_neg_atTop hw0).const_mul D
    rw [mul_zero] at hten
    exact hten.eventually_lt_const hδ₁0
  obtain ⟨H, ⟨⟨hH1, hHδ₂⟩, ⟨hHE, hHδ₁⟩⟩⟩ := ((hev1.and hev2).and (hev3.and hev4)).exists
  have hH0 : (0 : ℝ) < H := by linarith
  -- the polynomial
  obtain ⟨P, hP0, hPdeg, hPsup, hPξ, hPtest⟩ := hK w (le_trans hnw hww.le) H hH1
  have hval0 : aeval ξ P ≠ 0 := hξ P hP0 hPdeg
  have hvalpos : 0 < |aeval ξ P| := abs_pos.2 hval0
  have hu1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  have hHtall : H₀ < P.supNorm := hδ₂ P hPdeg hvalpos (lt_of_le_of_lt hPξ hHδ₂)
  have hlow : P.supNorm ^ (-w') < |aeval ξ P| := by
    by_contra hcon
    push Not at hcon
    exact absurd (hH₀ P ⟨hPdeg, hvalpos, hcon⟩) (not_le.2 hHtall)
  -- the height of `P` is large
  have hbig : H ^ (w / w') < P.supNorm := by
    by_contra hcon
    push Not at hcon
    have h1 : P.supNorm ^ w' ≤ (H ^ (w / w')) ^ w' :=
      Real.rpow_le_rpow (by linarith) hcon hw'0.le
    have h2 : (H ^ (w / w')) ^ w' = H ^ w := by
      rw [← Real.rpow_mul hH0.le]
      congr 1
      field_simp
    have h3 : H ^ (-w) ≤ P.supNorm ^ (-w') := by
      rw [Real.rpow_neg hH0.le, Real.rpow_neg (by linarith : (0 : ℝ) ≤ P.supNorm)]
      have h4 : P.supNorm ^ w' ≤ H ^ w := by rw [← h2]; exact h1
      have h5 : (0 : ℝ) < P.supNorm ^ w' := Real.rpow_pos_of_pos (by linarith) w'
      gcongr
    linarith
  -- the real root
  have hsmallall : ∀ j : Fin n, |aeval (testPoint ξ j) P| ≤ H := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · rw [testPoint_zero hj]
      refine le_trans hPξ (le_trans ?_ hH1)
      exact Real.rpow_le_one_of_one_le_of_nonpos hH1 (by linarith)
    · exact hPtest j hj
  have hEH : E * H < P.supNorm := by
    refine lt_of_le_of_lt ?_ hbig
    have hsplit : H ^ (w / w' - 1) * H = H ^ (w / w') := by
      rw [Real.rpow_sub hH0, Real.rpow_one, div_mul_cancel₀ _ (ne_of_gt hH0)]
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_right hHE (by linarith)
  obtain ⟨a, haroot, hadist⟩ :=
    exists_real_root_of_small_at_testPoints ξ hn (le_refl B) hP0 hPdeg hsmallall (by
      rw [hEdef] at hEH; exact hEH)
  have hapos : 0 < |ξ - a| := by
    rw [abs_pos, sub_ne_zero]
    intro h
    rw [← h] at haroot
    exact hval0 haroot
  have hdist : |ξ - a| ≤ D * H ^ (-w) := by
    have h1 : |ξ - a| ≤ |ξ - a| * P.supNorm := by nlinarith [hapos.le]
    have h2 : D * |aeval ξ P| ≤ D * H ^ (-w) := mul_le_mul_of_nonneg_left hPξ hD0.le
    rw [← hDdef] at hadist
    linarith [hadist]
  -- the irreducible factor
  have hprimroot : aeval a P.primPart = 0 := by
    have hPc := P.eq_C_content_mul_primPart
    have hc0 : (P.content : ℝ) ≠ 0 := by
      have : P.content ≠ 0 := fun h ↦ hP0 (Polynomial.content_eq_zero_iff.1 h)
      exact_mod_cast this
    have : (P.content : ℝ) * aeval a P.primPart = 0 := by
      have := haroot
      conv_lhs at this => rw [hPc]
      simpa using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · exact h
  obtain ⟨Q, hQdvd, hQirr, hQroot⟩ := Polynomial.exists_irreducible_dvd_aeval_eq_zero
    P.primPart.natDegree P.primPart rfl P.isPrimitive_primPart hprimroot
  have hQP : Q ∣ P := hQdvd.trans P.primPart_dvd
  have hQprim : Q.IsPrimitive := Polynomial.IsPrimitive.of_dvd hQdvd P.isPrimitive_primPart
  have hQ0 : Q ≠ 0 := hQirr.ne_zero
  have hQdeg : Q.natDegree ≤ n := le_trans (Polynomial.natDegree_le_of_dvd hQP hP0) hPdeg
  have hQsup : Q.supNorm ≤ 2 ^ n * P.supNorm := by
    obtain ⟨R, hR⟩ := hQP
    have hR0 : R ≠ 0 := by
      intro h
      rw [h, mul_zero] at hR
      exact hP0 hR
    have hdegsum : Q.natDegree + R.natDegree = P.natDegree := by
      rw [hR, Polynomial.natDegree_mul hQ0 hR0]
    have hG := Polynomial.supNorm_mul_supNorm_le_two_pow_int Q R
    rw [← hR, hdegsum] at hG
    have hR1 : (1 : ℝ) ≤ R.supNorm := Polynomial.one_le_supNorm hR0
    have hQ1 : (0 : ℝ) ≤ Q.supNorm := Polynomial.supNorm_nonneg Q
    have hpow : (2 : ℝ) ^ P.natDegree ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hPdeg
    nlinarith [Polynomial.supNorm_nonneg P]
  refine ⟨Q, ⟨hQdeg, hQprim, hQirr, a, hQroot, hapos, ?_⟩, ?_⟩
  · -- the quality of the approximation
    have hGl : (H ^ (w - n + 1)) ^ lam = H ^ w := by
      rw [← Real.rpow_mul hH0.le]
      congr 1
      rw [hlamdef]
      field_simp
    have hu_lam : P.supNorm ^ lam ≤ K ^ lam * H ^ w := by
      calc P.supNorm ^ lam ≤ (K * H ^ (w - n + 1)) ^ lam :=
            Real.rpow_le_rpow (by linarith) hPsup hlam0.le
        _ = K ^ lam * (H ^ (w - n + 1)) ^ lam :=
            Real.mul_rpow hK0.le (Real.rpow_nonneg hH0.le _)
        _ = K ^ lam * H ^ w := by rw [hGl]
    have hHw : H ^ (-w) ≤ K ^ lam * P.supNorm ^ (-lam) := by
      have hp1 : (0 : ℝ) < P.supNorm ^ lam := Real.rpow_pos_of_pos (by linarith) lam
      have hp2 : (0 : ℝ) < H ^ w := Real.rpow_pos_of_pos hH0 w
      rw [Real.rpow_neg hH0.le, Real.rpow_neg (by linarith : (0 : ℝ) ≤ P.supNorm),
        ← div_eq_mul_inv, le_div_iff₀ hp1, inv_mul_eq_div, div_le_iff₀ hp2]
      exact hu_lam
    have hstep1 : |ξ - a| * P.supNorm ≤ D * K ^ lam * P.supNorm ^ (-lam) := by
      calc |ξ - a| * P.supNorm ≤ D * |aeval ξ P| := by rw [hDdef]; exact hadist
        _ ≤ D * H ^ (-w) := mul_le_mul_of_nonneg_left hPξ hD0.le
        _ ≤ D * (K ^ lam * P.supNorm ^ (-lam)) := mul_le_mul_of_nonneg_left hHw hD0.le
        _ = D * K ^ lam * P.supNorm ^ (-lam) := by ring
    have hupos : (0 : ℝ) < P.supNorm := by linarith
    have hPu : |ξ - a| ≤ D * K ^ lam * P.supNorm ^ (-lam - 1) := by
      have h1 : |ξ - a| ≤ (D * K ^ lam * P.supNorm ^ (-lam)) / P.supNorm :=
        (le_div_iff₀ hupos).2 hstep1
      have h2 : (D * K ^ lam * P.supNorm ^ (-lam)) / P.supNorm =
          D * K ^ lam * P.supNorm ^ (-lam - 1) := by
        rw [Real.rpow_sub hupos, Real.rpow_one]
        ring
      rw [← h2]
      exact h1
    have hQpos : (0 : ℝ) < Q.supNorm := by
      have := Polynomial.one_le_supNorm hQ0
      linarith
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hratio : (0 : ℝ) < Q.supNorm / 2 ^ n := by positivity
    have hle : Q.supNorm / 2 ^ n ≤ P.supNorm := by
      rw [div_le_iff₀ h2n]
      linarith [hQsup]
    have hnonpos : (-lam - 1 : ℝ) ≤ 0 := by linarith
    have hmono : P.supNorm ^ (-lam - 1) ≤ (Q.supNorm / 2 ^ n) ^ (-lam - 1) :=
      Real.rpow_le_rpow_of_nonpos hratio hle hnonpos
    have hexpand : (Q.supNorm / 2 ^ n) ^ (-lam - 1) =
        ((2 : ℝ) ^ n) ^ (lam + 1) * Q.supNorm ^ (-lam - 1) := by
      rw [Real.div_rpow hQpos.le h2n.le,
        show (-lam - 1 : ℝ) = -(lam + 1) by ring, Real.rpow_neg h2n.le]
      field_simp
    have hDK : (0 : ℝ) < D * K ^ lam := mul_pos hD0 (Real.rpow_pos_of_pos hK0 lam)
    calc |ξ - a| ≤ D * K ^ lam * P.supNorm ^ (-lam - 1) := hPu
      _ ≤ D * K ^ lam * (((2 : ℝ) ^ n) ^ (lam + 1) * Q.supNorm ^ (-lam - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hDK.le
          rw [← hexpand]
          exact hmono
      _ = A * Q.supNorm ^ (-lam - 1) := by rw [hAdef]; ring
  · exact hδ₁ Q a hQdeg hQ0 hQroot hapos (lt_of_le_of_lt hdist hHδ₁)

/-! ### Wirsing's third inequality -/

/-- **Wirsing's third inequality**, `w_n^* ≥ w / (w - n + 1)` for `w = w_n`, cleared of the
division. The truncated subtraction of `ℝ≥0∞` is the right convention because the box principle
gives `n ≤ w_n` under the same hypothesis; at `w_n = n` the statement reads `n ≤ w_n^*`. -/
theorem mahlerExponent_le_koksmaExponent_mul
    (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    mahlerExponent n ξ ≤ koksmaExponent n ξ * (mahlerExponent n ξ + 1 - n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mahlerExponent_degree_zero]
    exact zero_le
  have hbox : (n : ℝ≥0∞) ≤ mahlerExponent n ξ := le_mahlerExponent_of_aeval_ne_zero hξ
  have hirr : Irrational ξ := irrational_of_aeval_ne_zero hn hξ
  have hk1 : (1 : ℝ≥0∞) ≤ koksmaExponent n ξ :=
    le_trans (one_le_koksmaExponent_one hirr) (koksmaExponent_mono hn ξ)
  have hk0 : koksmaExponent n ξ ≠ 0 := by
    intro h
    rw [h] at hk1
    exact absurd hk1 (by norm_num)
  have hposdiff : mahlerExponent n ξ + 1 - (n : ℝ≥0∞) ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    intro hle
    have h0 : (n : ℝ≥0∞) + 1 ≤ mahlerExponent n ξ + 1 := by gcongr
    have h1 : (n : ℝ≥0∞) + 1 ≤ (n : ℝ≥0∞) := le_trans h0 hle
    have h3 : (n : ℝ≥0∞) < (n : ℝ≥0∞) + 1 := ENNReal.lt_add_right (by simp) (by norm_num)
    exact absurd (lt_of_lt_of_le h3 h1) (lt_irrefl _)
  rcases eq_or_ne (mahlerExponent n ξ) ⊤ with htop | hne
  · rw [htop, top_add, ← ENNReal.coe_natCast, ENNReal.top_sub_coe, ENNReal.mul_top hk0]
  set W : ℝ := (mahlerExponent n ξ).toReal with hWdef
  have hW0 : (0 : ℝ) ≤ W := ENNReal.toReal_nonneg
  have hWr : mahlerExponent n ξ = ENNReal.ofReal W := (ENNReal.ofReal_toReal hne).symm
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnW : (n : ℝ) ≤ W := by
    have h1 : ((n : ℝ≥0∞)).toReal ≤ W := ENNReal.toReal_mono hne hbox
    simpa using h1
  have hWn : (1 : ℝ) ≤ W - n + 1 := by linarith
  rcases eq_or_ne (koksmaExponent n ξ) ⊤ with hktop | hkne
  · rw [hktop, ENNReal.top_mul hposdiff]
    exact le_top
  set Kr : ℝ := (koksmaExponent n ξ).toReal with hKdef
  have hKr : koksmaExponent n ξ = ENNReal.ofReal Kr := (ENNReal.ofReal_toReal hkne).symm
  have hKr0 : (0 : ℝ) ≤ Kr := ENNReal.toReal_nonneg
  have hkey : ∀ w : ℝ, W < w → w / (w - n + 1) ≤ Kr := by
    intro w hw
    have h1 : W < (W + w) / 2 := by linarith
    have h2 : (W + w) / 2 < w := by linarith
    have h3 : (n : ℝ) ≤ (W + w) / 2 := by linarith
    have h4 : mahlerExponent n ξ < ENNReal.ofReal ((W + w) / 2) := by
      rw [hWr]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h1
    have h5 := le_koksmaExponent_of_mahlerExponent_lt hn hξ h3 h2 h4
    rw [hKr, ENNReal.ofReal_le_ofReal_iff hKr0] at h5
    exact h5
  have hcont : ContinuousAt (fun x : ℝ ↦ x / (x - n + 1)) W := by
    refine ContinuousAt.div continuousAt_id (by fun_prop) (by linarith)
  have hlim : W / (W - n + 1) ≤ Kr := by
    refine le_of_tendsto (f := fun x : ℝ ↦ x / (x - n + 1)) (x := 𝓝[>] W)
      hcont.continuousWithinAt ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hkey x hx
  have hfinal : W ≤ Kr * (W - n + 1) := by
    rw [div_le_iff₀ (by linarith)] at hlim
    exact hlim
  have hdiff : mahlerExponent n ξ + 1 - (n : ℝ≥0∞) = ENNReal.ofReal (W - n + 1) := by
    rw [hWr, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hW0 zero_le_one,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring
  rw [hdiff, hWr, hKr, ← ENNReal.ofReal_mul hKr0]
  exact ENNReal.ofReal_le_ofReal hfinal

/-! ### Acceptance criteria -/

/-- **Acceptance test: Wirsing's third inequality.** -/
example (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0) :
    mahlerExponent n ξ ≤ koksmaExponent n ξ * (mahlerExponent n ξ + 1 - n) :=
  mahlerExponent_le_koksmaExponent_mul hξ

/-- **Acceptance test: at `w_n = n` it is Wirsing's conjecture.** If Mahler's exponent takes the
value the box principle forces from below, then Koksma's exponent is at least `n` as well. -/
example (hξ : ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → aeval ξ P ≠ 0)
    (hw : mahlerExponent n ξ = n) : (n : ℝ≥0∞) ≤ koksmaExponent n ξ := by
  have h := mahlerExponent_le_koksmaExponent_mul hξ
  rw [hw] at h
  have hone : (n : ℝ≥0∞) + 1 - (n : ℝ≥0∞) = 1 := by
    rw [add_comm]
    exact ENNReal.add_sub_cancel_right (by simp)
  rwa [hone, mul_one] at h

/-- **Rejection test: Wirsing's first two inequalities are false at `n = 0`**, so the hypothesis
`1 ≤ n` that the roadmap's prototypes omit is load-bearing. Both exponents vanish at degree zero,
and `0 + 1 ≤ 0 + 0` is false — as is `0 + 1 ≤ 2 * 0`. The third inequality survives, because at
degree zero it reads `0 ≤ 0`. -/
example (ξ : ℝ) : ¬ (mahlerExponent 0 ξ + 1 ≤ koksmaExponent 0 ξ + (0 : ℕ)) := by
  rw [mahlerExponent_degree_zero, koksmaExponent_degree_zero]
  norm_num

/-- **Rejection test: the hypothesis on `ξ` is load-bearing.** At a rational `ξ` and `n = 1` the
conclusion of the acceptance test above fails: both exponents are `0`, so `1 ≤ w_1^*` is false. -/
example (q : ℚ) : ¬ (1 : ℝ≥0∞) ≤ koksmaExponent 1 (q : ℝ) := by
  rw [koksmaExponent_one_eq_mahlerExponent_one, mahlerExponent_one_ratCast]
  norm_num

end Real
