/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Gelfond
public import DiophantineApproximation.BoxMonomial
public import DiophantineApproximation.HeightTransport

/-!
# The height of a determinant of polynomials

The polynomial Roth's lemma runs on is the determinant of a `p × p` matrix whose entries are
Hasse derivatives of one polynomial `P`. Its height has to be bounded by `p` times the height of
`P` plus a constant, and there is no projective bound on the height of a *sum* of polynomials
that could be applied term by term to the Leibniz expansion: `H(N X + 1)` is `N` while both
summands have height `1`. The estimate has to be made at each absolute value and transported
once, which is what `Finsupp.mulHeight_le_pow_of_forall_iSup_le` is for.

Locally there is nothing to it. A product of `n` polynomials costs one factor
`#(support)` per multiplication at an archimedean absolute value — Gelfond's local estimate with
the *smaller* support, so that the constant stays `B ^ n` and does not grow quadratically with
`n` — and nothing at all at a nonarchimedean one, by Gauss's lemma. A sum of `n!` terms costs
`n!` at an archimedean absolute value and nothing at a nonarchimedean one.

## Main results

* `MvPolynomial.iSup_coeff_prod_le` and
  `MvPolynomial.iSup_coeff_prod_le_of_isNonarchimedean`: the local factor of a finite product.
* `MvPolynomial.iSup_coeff_sum_le` and `MvPolynomial.iSup_coeff_sum_le_of_isNonarchimedean`:
  the local factor of a finite sum.
* `MvPolynomial.iSup_coeff_det_le` and `MvPolynomial.iSup_coeff_det_le_of_isNonarchimedean`:
  the local factor of a determinant.
* `MvPolynomial.mulHeight_det_le`: the height of a determinant of polynomials whose local
  factors are bounded against those of one polynomial `P`.
* `MvPolynomial.card_support_le_prod` and `MvPolynomial.card_support_le_two_pow`: a polynomial
  of partial degrees at most `d` has at most `∏ j, (d j + 1) ≤ 2 ^ ∑ j, d j` monomials.

## Implementation notes

⚠ **The support count, not the total degree, is what keeps the constant linear in `n`.**
`MvPolynomial.iSup_coeff_mul_le_two_pow` charges `2 ^ (totalDegree p + totalDegree q)`, and the
accumulated product in a `n`-fold product has total degree `n` times the individual one, so
iterating it costs `2 ^ (D n (n+1) / 2)`. `MvPolynomial.iSup_coeff_mul_le_card_support` charges
the *minimum* of the two support counts, which is always the new factor's, so iterating it costs
`B ^ n` with `B` a bound on one factor's support. In Roth's lemma `n` is the number of columns
and can be as large as the smallest degree, so the difference is the whole estimate.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 1.6.11 and Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height AdmissibleAbsValues

namespace MvPolynomial

/-! ### Counting the monomials in a box -/

section Support

variable {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]

/-- **A polynomial of partial degrees at most `d` has at most `∏ j, (d j + 1)` monomials.** -/
theorem card_support_le_prod {d : σ → ℕ} {P : MvPolynomial σ R} (h : ∀ j, P.degreeOf j ≤ d j) :
    #P.support ≤ ∏ j, (d j + 1) := by
  classical
  have hsub : P.support ⊆ Finset.image (boxMonomial d) Finset.univ := fun ν hν ↦ by
    obtain ⟨I, rfl⟩ := mem_range_boxMonomial_of_mem_support h hν
    exact Finset.mem_image.mpr ⟨I, Finset.mem_univ I, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_image_le) ?_)
  rw [Finset.card_univ, Fintype.card_pi]
  simp

/-- The crude form of `MvPolynomial.card_support_le_prod`. -/
theorem card_support_le_two_pow {d : σ → ℕ} {P : MvPolynomial σ R} (h : ∀ j, P.degreeOf j ≤ d j) :
    #P.support ≤ 2 ^ ∑ j, d j := by
  refine le_trans (card_support_le_prod h) ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun j _ ↦ Nat.lt_two_pow_self

end Support

/-! ### Local estimates for sums and products -/

section Local

variable {K : Type*} [Field K] {σ ι : Type*} {v : AbsoluteValue K ℝ}

/-- The local factors of a polynomial are bounded. -/
theorem bddAbove_range_coeff (P : MvPolynomial σ K) (v : AbsoluteValue K ℝ) :
    BddAbove (Set.range fun ν ↦ v (P.coeff ν)) :=
  Finsupp.bddAbove_range_apply P.coeff v

/-- Each local factor is at most the supremum. -/
theorem le_iSup_coeff (P : MvPolynomial σ K) (v : AbsoluteValue K ℝ) (ν : σ →₀ ℕ) :
    v (P.coeff ν) ≤ ⨆ ρ, v (P.coeff ρ) :=
  le_ciSup (bddAbove_range_coeff P v) ν

/-- The local factor of a supremum is nonnegative. -/
theorem iSup_coeff_nonneg (P : MvPolynomial σ K) (v : AbsoluteValue K ℝ) :
    0 ≤ ⨆ ν, v (P.coeff ν) :=
  Real.iSup_nonneg fun _ ↦ v.nonneg _

/-- The local factor of a sign is the local factor. -/
theorem iSup_coeff_neg (P : MvPolynomial σ K) (v : AbsoluteValue K ℝ) :
    (⨆ ν, v ((-P).coeff ν)) = ⨆ ν, v (P.coeff ν) := by
  simp

/-- The local factor of the polynomial `1`. -/
theorem iSup_coeff_one (v : AbsoluteValue K ℝ) :
    (⨆ ν : σ →₀ ℕ, v ((1 : MvPolynomial σ K).coeff ν)) = 1 := by
  classical
  have h0 : v ((1 : MvPolynomial σ K).coeff 0) = 1 := by
    rw [MvPolynomial.coeff_one, ite_eq_left rfl, map_one]
  refine le_antisymm (Real.iSup_le (fun ν ↦ ?_) zero_le_one) (le_of_eq_of_le h0.symm
    (le_iSup_coeff _ v 0))
  rcases eq_or_ne ν 0 with rfl | h
  · exact le_of_eq h0
  · rw [MvPolynomial.coeff_one, ite_eq_right (Ne.symm h), map_zero]
    exact zero_le_one

/-- **The local factor of a finite product**, with one support count per factor. -/
theorem iSup_coeff_prod_le (s : Finset ι) (f : ι → MvPolynomial σ K) {B C : ℝ} (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hsupp : ∀ a ∈ s, (#(f a).support : ℝ) ≤ B)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∏ a ∈ s, f a).coeff ν)) ≤ (B * C) ^ #s := by
  classical
  induction s using Finset.induction with
  | empty => simpa using le_of_eq (iSup_coeff_one v)
  | insert a s ha ih =>
      have hBC : (0 : ℝ) ≤ B * C := mul_nonneg (le_trans zero_le_one hB) hC
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      refine le_trans (iSup_coeff_mul_le_card_support v (f a) (∏ b ∈ s, f b)) ?_
      refine le_trans (mul_le_mul (le_trans (by exact_mod_cast Nat.cast_le.mpr (min_le_left _ _))
        (hsupp a (Finset.mem_insert_self a s)))
        (mul_le_mul (hf a (Finset.mem_insert_self a s))
          (ih (fun b hb ↦ hsupp b (Finset.mem_insert_of_mem hb))
            fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))
          (iSup_coeff_nonneg _ v) hC)
        (mul_nonneg (iSup_coeff_nonneg _ v) (iSup_coeff_nonneg _ v))
        (le_trans zero_le_one hB)) (le_of_eq (by ring)) |>.trans (le_of_eq rfl)

/-- **The local factor of a finite product at a nonarchimedean absolute value**, by Gauss's
lemma, with no constant. -/
theorem iSup_coeff_prod_le_of_isNonarchimedean (hv : IsNonarchimedean v) (s : Finset ι)
    (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∏ a ∈ s, f a).coeff ν)) ≤ C ^ #s := by
  classical
  induction s using Finset.induction with
  | empty => simpa using le_of_eq (iSup_coeff_one v)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ',
        iSup_coeff_mul hv]
      exact mul_le_mul (hf a (Finset.mem_insert_self a s))
        (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) (iSup_coeff_nonneg _ v) hC

/-- **The local factor of a finite sum**, at the cost of the number of terms. -/
theorem iSup_coeff_sum_le (s : Finset ι) (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∑ a ∈ s, f a).coeff ν)) ≤ #s * C := by
  refine Real.iSup_le (fun ν ↦ ?_) (by positivity)
  rw [coeff_sum]
  refine le_trans (v.sum_le _ _) ?_
  calc ∑ a ∈ s, v ((f a).coeff ν) ≤ ∑ _a ∈ s, C :=
        Finset.sum_le_sum fun a ha ↦ le_trans (le_iSup_coeff _ v ν) (hf a ha)
    _ = #s * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The local factor of a finite sum at a nonarchimedean absolute value**, with no constant. -/
theorem iSup_coeff_sum_le_of_isNonarchimedean (hv : IsNonarchimedean v) (s : Finset ι)
    (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∑ a ∈ s, f a).coeff ν)) ≤ C := by
  refine Real.iSup_le (fun ν ↦ ?_) hC
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  rw [coeff_sum]
  obtain ⟨b, hb, hble⟩ := hv.finset_image_add_of_nonempty (g := fun a ↦ (f a).coeff ν) hs
  exact le_trans hble (le_trans (le_iSup_coeff _ v ν) (hf b hb))

end Local

/-! ### The determinant -/

section Det

variable {K : Type*} [Field K] {σ : Type*} {v : AbsoluteValue K ℝ} {n : ℕ}

/-- **The local factor of a determinant.** -/
theorem iSup_coeff_det_le (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {B C : ℝ} (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hsupp : ∀ i j, (#(A i j).support : ℝ) ≤ B)
    (hA : ∀ i j, (⨆ ν, v ((A i j).coeff ν)) ≤ C) :
    (⨆ ν, v (A.det.coeff ν)) ≤ (n.factorial : ℝ) * (B * C) ^ n := by
  classical
  rw [Matrix.det_apply']
  refine le_trans (iSup_coeff_sum_le (C := (B * C) ^ n) _ _ (by positivity) fun τ _ ↦ ?_)
    (le_of_eq ?_)
  · have hprod : (⨆ ν, v ((∏ i, A (τ i) i).coeff ν)) ≤ (B * C) ^ n := by
      simpa using iSup_coeff_prod_le Finset.univ (fun i ↦ A (τ i) i) hB hC
        (fun i _ ↦ hsupp _ _) fun i _ ↦ hA _ _
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simpa using hprod
  · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **The local factor of a determinant at a nonarchimedean absolute value.** -/
theorem iSup_coeff_det_le_of_isNonarchimedean (hv : IsNonarchimedean v)
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, (⨆ ν, v ((A i j).coeff ν)) ≤ C) :
    (⨆ ν, v (A.det.coeff ν)) ≤ C ^ n := by
  classical
  rw [Matrix.det_apply']
  refine iSup_coeff_sum_le_of_isNonarchimedean hv _ _ (by positivity) fun τ _ ↦ ?_
  have hprod : (⨆ ν, v ((∏ i, A (τ i) i).coeff ν)) ≤ C ^ n := by
    simpa using iSup_coeff_prod_le_of_isNonarchimedean hv Finset.univ (fun i ↦ A (τ i) i) hC
      fun i _ ↦ hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simpa using hprod

variable [AdmissibleAbsValues K]

/-- **The height of a determinant of polynomials.** The entries are compared with one polynomial
`P`, up to a constant at the archimedean absolute values and with no constant at the others,
which is exactly what a Hasse derivative satisfies. -/
theorem mulHeight_det_le (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    {P : MvPolynomial σ K} (hP : P ≠ 0) {B C : ℝ} (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hsupp : ∀ i j, (#(A i j).support : ℝ) ≤ B)
    (harch : ∀ v ∈ archAbsVal (K := K), ∀ i j,
      (⨆ ν, v ((A i j).coeff ν)) ≤ C * ⨆ ν, v (P.coeff ν))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), ∀ i j,
      (⨆ ν, v ((A i j).coeff ν)) ≤ ⨆ ν, v (P.coeff ν)) :
    A.det.mulHeight ≤ ((n.factorial : ℝ) * (B * C) ^ n) ^ totalWeight K * P.mulHeight ^ n := by
  have hone : (1 : ℝ) ≤ (n.factorial : ℝ) * (B * C) ^ n := by
    have h1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have h2 : (1 : ℝ) ≤ (B * C) ^ n := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hB hC)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  refine mulHeight_le_pow_of_forall_iSup_le hP hone (fun v hv ↦ ?_) fun v hv ↦ ?_
  · refine le_trans (iSup_coeff_det_le A hB
      (mul_nonneg (le_trans zero_le_one hC) (iSup_coeff_nonneg P v)) hsupp (harch v hv))
      (le_of_eq ?_)
    rw [mul_pow]
    ring
  · exact iSup_coeff_det_le_of_isNonarchimedean (AdmissibleAbsValues.isNonarchimedean v hv) A
      (iSup_coeff_nonneg P v) (hnon v hv)

end Det

end MvPolynomial
