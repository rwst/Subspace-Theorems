/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Gelfond
public import DiophantineApproximation.IndexRename

/-!
# Roth's lemma in one variable

The base case of Roth's lemma (Bombieri–Gubler, Lemma 6.3.9) is an inequality about a *root*:
if `P` has a zero of multiplicity `k` at `ξ`, then `(X - ξ) ^ k` divides `P`, and Gelfond's
inequality in its lower half bounds the height of a factor by the height of the product. The
height of `(X - ξ) ^ k` is at least `mulHeight₁ ξ ^ k`, because its coefficient vector contains
both `(-ξ) ^ k` and `1` — the leading coefficient of a monic polynomial — so the two-element
vector `![ξ ^ k, 1]` whose height *is* `mulHeight₁ ξ ^ k` is a subfamily of it.

The result is `index * d * h(ξ) ≤ h(P) + d * totalWeight K * log 2`, the book's constant `log 2`
exactly, and the layer's statement asks for `4` in that place — which is the room the induction
needs at every later step.

## Main results

* `Polynomial.mulHeight₁_pow_le_mulHeight_X_sub_C_pow`: the height of `(X - C a) ^ k`.
* `Polynomial.rootMultiplicity_mul_logHeight₁_le`: the estimate, for a univariate polynomial.
* `MvPolynomial.index_le_base`: the estimate in the shape the induction of Roth's lemma consumes,
  for a polynomial in one variable and weight `e`.

## Implementation notes

⚠ **The `4` in the hypothesis is what makes the base case usable, and the reason is not the
`log 2`.** The hypothesis of Roth's lemma reads `h(P) + 4 m d ≤ σ d h(ξ)`, and the base case
needs `h(P) + d h(ξ) log 2 ≤ σ d h(ξ)`: any constant at least `log 2` in the hypothesis would
do here. The constant `4` is fixed by the *inductive* step, where the height of the determinant
of derivatives costs `log p! + 2 (∑ j, d j) log 2 ≤ 4 d` per row.

⚠ **`0 < totalWeight K` is not decoration.** At `totalWeight K = 0` the hypothesis is
`h(P) ≤ σ d h(ξ)` with both sides allowed to vanish, and nothing bounds the multiplicity. That is
why this layer is stated over a number field rather than over an arbitrary field with
`AdmissibleAbsValues`: Roth's theorem is false over function fields.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.9.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height AdmissibleAbsValues

open scoped ENNReal

namespace Polynomial

variable {K : Type*} [Field K] [NumberField K]

/-- **The height of `(X - C a) ^ k` is at least `mulHeight₁ a ^ k`.** Its coefficient vector
contains `(-a) ^ k` in degree `0` and `1` in degree `k`, so `![(-a) ^ k, 1]` is a subfamily. -/
theorem mulHeight₁_pow_le_mulHeight_X_sub_C_pow (a : K) (k : ℕ) :
    mulHeight₁ a ^ k ≤ ((X - C a) ^ k).mulHeight := by
  have hmonic : (((X : K[X]) - C a) ^ k).Monic := (monic_X_sub_C a).pow k
  have hc0 : (((X : K[X]) - C a) ^ k).coeff 0 = (-a) ^ k := by
    rw [coeff_zero_eq_eval_zero]
    simp
  have hck : (((X : K[X]) - C a) ^ k).coeff (((X : K[X]) - C a) ^ k).natDegree = 1 :=
    hmonic.coeff_natDegree
  have hcomp : ![(-a) ^ k, (1 : K)]
      = (fun i : Fin ((((X : K[X]) - C a) ^ k).natDegree + 1) ↦
          (((X : K[X]) - C a) ^ k).coeff (i : ℕ))
        ∘ ![0, Fin.last _] := by
    funext i
    fin_cases i
    · simpa using hc0.symm
    · simpa using hck.symm
  have hle : Height.mulHeight ![(-a) ^ k, (1 : K)] ≤ ((X - C a) ^ k).mulHeight := by
    rw [mulHeight_eq_mulHeight_coeff, hcomp]
    exact Height.mulHeight_comp_le _ _
  refine le_of_eq_of_le ?_ hle
  rw [← mulHeight₁_eq_mulHeight, mulHeight₁_pow, mulHeight₁_neg]

/-- **Roth's lemma in one variable** (Bombieri–Gubler, Lemma 6.3.9). -/
theorem rootMultiplicity_mul_logHeight₁_le {q : K[X]} (hq : q ≠ 0) (a : K) :
    (q.rootMultiplicity a : ℝ) * logHeight₁ a
      ≤ q.logHeight + (q.natDegree : ℝ) * totalWeight K * Real.log 2 := by
  obtain ⟨R, hR⟩ := pow_rootMultiplicity_dvd q a
  have hp0 : (((X : K[X]) - C a) ^ q.rootMultiplicity a) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero a)
  have hR0 : R ≠ 0 := fun h ↦ hq (by rw [hR, h, mul_zero])
  have hdegsum : (((X : K[X]) - C a) ^ q.rootMultiplicity a).natDegree + R.natDegree
      = q.natDegree := by
    conv_rhs => rw [hR]
    rw [natDegree_mul hp0 hR0]
  have hgel := mulHeight_mul_mulHeight_le hp0 hR0
  rw [hdegsum, ← hR] at hgel
  have hstep : mulHeight₁ a ^ q.rootMultiplicity a
      ≤ 2 ^ (q.natDegree * totalWeight K) * q.mulHeight := by
    refine le_trans (mulHeight₁_pow_le_mulHeight_X_sub_C_pow a _) (le_trans ?_ hgel)
    exact le_mul_of_one_le_right (mulHeight_pos _).le R.one_le_mulHeight
  have hlog := Real.log_le_log (by positivity) hstep
  rw [Real.log_pow, ← logHeight₁_eq_log_mulHeight₁, ← logHeight₁_pow,
    Real.log_mul (by positivity) (mulHeight_ne_zero q), Real.log_pow,
    ← logHeight_eq_log_mulHeight] at hlog
  refine le_trans (le_of_eq ?_) (le_of_le_of_eq hlog (by push_cast; ring))
  rw [logHeight₁_pow]

end Polynomial

namespace MvPolynomial

variable {σ : Type*} [Unique σ] {K : Type*} [Field K] [NumberField K]

/-- The exponents of a polynomial in one variable are its degrees. -/
noncomputable def uniqueSingleEquiv (σ : Type*) [Unique σ] : ℕ ≃ (σ →₀ ℕ) where
  toFun n := Finsupp.single default n
  invFun ν := ν default
  left_inv n := by simp
  right_inv ν := (Finsupp.unique_single ν).symm

/-- The height of a polynomial in one variable is the height of the univariate polynomial it
corresponds to. -/
theorem mulHeight_uniqueAlgEquiv (P : MvPolynomial σ K) :
    (uniqueAlgEquiv K σ P).mulHeight = P.mulHeight := by
  rw [Polynomial.mulHeight, MvPolynomial.mulHeight, ← Finsupp.mulHeight_coe_eq,
    ← Finsupp.mulHeight_coe_eq, ← Height.mulHeight_comp_equiv (uniqueSingleEquiv σ)]
  exact congrArg Height.mulHeight (funext fun n ↦ coeff_uniqueAlgEquiv (R := K) (σ := σ) P n)

omit [NumberField K] in
/-- The degree of the univariate polynomial corresponding to a polynomial in one variable. -/
theorem natDegree_uniqueAlgEquiv_le {P : MvPolynomial σ K} {e : ℕ} (hdeg : P.degreeOf default ≤ e) :
    (uniqueAlgEquiv K σ P).natDegree ≤ e := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
  rw [coeff_uniqueAlgEquiv]
  by_contra hc
  have hle := degreeOf_le_iff.mp (le_refl (P.degreeOf default)) _ (mem_support_iff.mpr hc)
  rw [Finsupp.single_eq_same] at hle
  omega

/-- **The base case of Roth's lemma**, in the shape the induction consumes. -/
theorem index_le_base {P : MvPolynomial σ K} (hP : P ≠ 0) {e : ℕ} (he : 1 ≤ e)
    (hdeg : P.degreeOf default ≤ e) (ξ : σ → K) {s : ℝ} (hs : 0 < s)
    (hheight : P.logHeight + 4 * e * totalWeight K ≤ s * (e * logHeight₁ (ξ default))) :
    index (fun _ ↦ (e : ℝ)) ξ P ≤ ENNReal.ofReal s := by
  set q : Polynomial K := uniqueAlgEquiv K σ P with hqdef
  have hq0 : q ≠ 0 := fun h ↦ hP ((uniqueAlgEquiv K σ).injective (by rw [← hqdef, h, map_zero]))
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have htw : (0 : ℝ) < totalWeight K := by
    rw [NumberField.totalWeight_eq_finrank]
    exact_mod_cast Module.finrank_pos
  have hL : 0 ≤ P.logHeight := MvPolynomial.logHeight_nonneg P
  have h4 : (0 : ℝ) < 4 * e * totalWeight K := by positivity
  have hh1 : 0 < logHeight₁ (ξ default) := by
    by_contra hle
    push Not at hle
    nlinarith [hheight, hL, h4, mul_pos hs hep, hle]
  have hbase := Polynomial.rootMultiplicity_mul_logHeight₁_le hq0 (ξ default)
  rw [Polynomial.logHeight_eq_log_mulHeight, mulHeight_uniqueAlgEquiv,
    ← MvPolynomial.logHeight_eq_log_mulHeight] at hbase
  have hdq : (q.natDegree : ℝ) ≤ e := by exact_mod_cast natDegree_uniqueAlgEquiv_le hdeg
  have hlog2 : Real.log 2 ≤ 4 := le_trans (Real.log_le_sub_one_of_pos two_pos) (by norm_num)
  have hk : (q.rootMultiplicity (ξ default) : ℝ) ≤ s * e := by
    have h1 : (q.rootMultiplicity (ξ default) : ℝ) * logHeight₁ (ξ default)
        ≤ s * (e * logHeight₁ (ξ default)) := by
      refine le_trans hbase (le_trans ?_ hheight)
      have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hstep : (q.natDegree : ℝ) * Real.log 2 ≤ (e : ℝ) * 4 :=
        mul_le_mul hdq hlog2 hlog0 (by positivity)
      have hfin : (q.natDegree : ℝ) * totalWeight K * Real.log 2 ≤ 4 * e * totalWeight K := by
        nlinarith [hstep, htw.le]
      linarith
    nlinarith [h1, hh1]
  have hidx : index (fun _ ↦ (e : ℝ)) ξ P
      = ENNReal.ofReal (e : ℝ)⁻¹ * (q.rootMultiplicity (ξ default) : ℝ≥0∞) := by
    have hξ : ξ = fun _ ↦ ξ default := funext fun j ↦ by rw [Subsingleton.elim j default]
    rw [show (fun _ : σ ↦ (e : ℝ)) = fun _ : σ ↦ (e : ℝ) * 1 by funext; ring,
      index_const_mul_weights _ hep (fun _ ↦ zero_le_one), hξ, index_of_unique _ hP]
  rw [hidx, ← ENNReal.ofReal_natCast]
  calc ENNReal.ofReal (e : ℝ)⁻¹ * ENNReal.ofReal (q.rootMultiplicity (ξ default) : ℝ)
      ≤ ENNReal.ofReal (e : ℝ)⁻¹ * ENNReal.ofReal (s * e) := by
        gcongr
    _ = ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end MvPolynomial
