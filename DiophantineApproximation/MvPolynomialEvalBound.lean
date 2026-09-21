/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BoxMonomial
public import DiophantineApproximation.MvHasseDerivHeight
public import DiophantineApproximation.MvHasseDerivTaylor

/-!
# Local bounds on the value of a polynomial

Step III of Roth's proof bounds `|Q(β)|_v` at every place, twice: trivially away from `S`, and
through the Taylor expansion at the target at the places of `S`. Both bounds are inequalities
between an absolute value and the local factor `⨆ μ, v (Q.coeff μ)` of the height, and this file
proves them for an arbitrary absolute value on an arbitrary field — no number field and no place
appears.

The trivial bound is the triangle inequality: a polynomial with partial degrees at most `d` has
at most `∏ j, (d j + 1)` monomials, and each of them is at most `‖Q‖_v ∏ j, max (|x j|_v) 1 ^ d j`.
At a nonarchimedean absolute value the number of monomials drops out, and that is what makes the
product over all the nonarchimedean places converge.

The Taylor bound is the same inequality applied twice more. Writing `β = α + (β − α)` and
expanding, `Q(β) = ∑_μ (∂_μ Q)(α) ∏ j (β j − α j) ^ μ j`; one surviving term dominates the sum, its
coefficient is bounded by the trivial estimate applied to `∂_μ Q`, and each distance splits as
`|β j − α j|_v = min 1 (|β j − α j|_v) · max (|β j − α j|_v) 1` with the second factor bounded by
`2 max (|β j|_v) 1 max (|α j|_v) 1`. What is left is the truncated product
`∏ j, min 1 (|β j − α j|_v) ^ μ j`, which is what the approximation class of Layer 3.1 makes small.

## Main results

* `MvPolynomial.apply_eval_le` and `MvPolynomial.apply_eval_le_of_isNonarchimedean`: the trivial
  bound, with and without the count of monomials.
* `MvPolynomial.exists_apply_eval_le_taylor`: the Taylor expansion with one surviving term chosen.
* `MvPolynomial.apply_eval_hasseDeriv_le` and `MvPolynomial.prod_apply_sub_le`: the two estimates
  the surviving term is made of.
* `MvPolynomial.exists_apply_eval_le_of_sub`: the three combined — **the local bound at a place
  carrying a target**.
* `MvPolynomial.card_support_le`, `MvPolynomial.totalDegree_le_sum` and
  `MvPolynomial.iSup_coeff_boxMonomial`: the box bookkeeping the estimates run on.
* `MvPolynomial.map_hasseDeriv`: a Hasse derivative commutes with a change of coefficient ring,
  which is how the index at a target in the extension survives differentiation.

## Implementation notes

⚠ **The surviving term is an existential, not a maximum.** `v (∑ …) ≤ #s · max …` needs the
maximum, and the caller needs to know *which* order attains it, because the order is what the
index bound of Layer 2.3 constrains. Returning the order is strictly more informative and costs
nothing.

⚠ **The Taylor bound is proved once, with the archimedean constants, and used at both kinds of
place of `S`.** A constant-free version at the nonarchimedean places is not needed: `S` is finite,
so the constants there are charged a bounded number of times. Only the *trivial* bound has to be
constant-free, because it is used at all but finitely many places.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.4.8, displays (6.14) to (6.17).

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K]


omit [Fintype σ] in
/-- **A Hasse derivative commutes with a change of coefficient ring.** -/
theorem map_hasseDeriv {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    map f (hasseDeriv μ P) = hasseDeriv μ (map f P) := by
  ext n
  rw [coeff_map, hasseDeriv_coeff, hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- The number of monomials of a polynomial with partial degrees at most `d` is at most the
number of points of the box. -/
theorem card_support_le {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) :
    #P.support ≤ ∏ j, (d j + 1) := by
  classical
  have hsub : P.support ⊆ Finset.image (boxMonomial d) Finset.univ := fun ν hν ↦ by
    obtain ⟨I, rfl⟩ := mem_range_boxMonomial_of_mem_support hP hν
    exact Finset.mem_image_of_mem _ (Finset.mem_univ I)
  calc #P.support ≤ #(Finset.image (boxMonomial d) (Finset.univ : Finset (∀ j, Fin (d j + 1)))) :=
        Finset.card_le_card hsub
    _ ≤ #(Finset.univ : Finset (∀ j, Fin (d j + 1))) := Finset.card_image_le
    _ = ∏ j, (d j + 1) := by simp [Fintype.card_pi]

/-- The total degree of a polynomial with partial degrees at most `d` is at most `∑ j, d j`. -/
theorem totalDegree_le_sum {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) :
    P.totalDegree ≤ ∑ j, d j := by
  refine Finset.sup_le fun ν hν ↦ ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
  exact Finset.sum_le_sum fun j _ ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)

/-- The term of the monomial `ν` is bounded by the local factor of `P` times the box. -/
private theorem apply_term_le (v : AbsoluteValue K ℝ) {d : σ → ℕ} {P : MvPolynomial σ K}
    (hP : ∀ j, P.degreeOf j ≤ d j) (x : σ → K) {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
    v (P.coeff ν * ∏ j, x j ^ ν j)
      ≤ (⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j := by
  have hle : ∀ j, ν j ≤ d j := fun j ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)
  have hcoeff : v (P.coeff ν) ≤ ⨆ μ, v (P.coeff μ) :=
    le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) ν
  have hprod : (∏ j, v (x j) ^ ν j) ≤ ∏ j, max (v (x j)) 1 ^ d j := by
    refine Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (v.nonneg _) _) fun j _ ↦ ?_
    calc v (x j) ^ ν j ≤ max (v (x j)) 1 ^ ν j :=
          pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _
      _ ≤ max (v (x j)) 1 ^ d j := pow_le_pow_right₀ (le_max_right _ _) (hle j)
  rw [map_mul, map_prod]
  simp only [map_pow]
  exact mul_le_mul hcoeff hprod (Finset.prod_nonneg fun j _ ↦ by positivity)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _)

/-- **The trivial bound on a value, at an arbitrary absolute value.** -/
theorem apply_eval_le (v : AbsoluteValue K ℝ) {d : σ → ℕ} {P : MvPolynomial σ K}
    (hP : ∀ j, P.degreeOf j ≤ d j) (x : σ → K) :
    v (eval x P) ≤ (∏ j, ((d j : ℝ) + 1)) * (⨆ ν, v (P.coeff ν))
      * ∏ j, max (v (x j)) 1 ^ d j := by
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Finset.prod_nonneg fun j _ ↦ by positivity)
  rw [eval_eq', mul_assoc]
  calc v (∑ ν ∈ P.support, P.coeff ν * ∏ j, x j ^ ν j)
      ≤ ∑ ν ∈ P.support, v (P.coeff ν * ∏ j, x j ^ ν j) := v.sum_le _ _
    _ ≤ ∑ _ν ∈ P.support, (⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j :=
        Finset.sum_le_sum fun ν hν ↦ apply_term_le v hP x hν
    _ = (#P.support : ℝ) * ((⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j, ((d j : ℝ) + 1)) * ((⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j) := by
        refine mul_le_mul_of_nonneg_right ?_ hnn
        calc (#P.support : ℝ) ≤ ((∏ j, (d j + 1) : ℕ) : ℝ) := by
              exact_mod_cast card_support_le hP
          _ = ∏ j, ((d j : ℝ) + 1) := by push_cast; ring

/-- **The trivial bound on a value, at a nonarchimedean absolute value**, with no constant. -/
theorem apply_eval_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) (x : σ → K) :
    v (eval x P) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j := by
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Finset.prod_nonneg fun j _ ↦ by positivity)
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [map_zero, AbsoluteValue.map_zero]
    exact hnn
  rw [eval_eq']
  obtain ⟨ν, hν, hle⟩ :=
    hv.finset_image_add_of_nonempty (fun ν ↦ P.coeff ν * ∏ j, x j ^ ν j)
      (support_nonempty.mpr hP0)
  exact le_trans hle (apply_term_le v hP x hν)


/-- **The local factor of a polynomial with partial degrees at most `d` is computed on the
box.** Off the box every coefficient vanishes, and the supremum is nonnegative. -/
theorem iSup_coeff_boxMonomial (v : AbsoluteValue K ℝ) {d : σ → ℕ} {P : MvPolynomial σ K}
    (hP : ∀ j, P.degreeOf j ≤ d j) :
    (⨆ I : (∀ j, Fin (d j + 1)), v (P.coeff (boxMonomial d I))) = ⨆ ν, v (P.coeff ν) := by
  refine le_antisymm (Real.iSup_le (fun I ↦ le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) _)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _)) ?_
  refine Real.iSup_le (fun ν ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  rcases eq_or_ne (P.coeff ν) 0 with h | h
  · rw [h, AbsoluteValue.map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  · obtain ⟨I, rfl⟩ := mem_range_boxMonomial_of_mem_support hP (mem_support_iff.mpr h)
    exact le_ciSup (Set.Finite.bddAbove (Set.finite_range
      fun I : (∀ j, Fin (d j + 1)) ↦ v (P.coeff (boxMonomial d I)))) I

/-! ### The Taylor expansion at a target -/

section Taylor

variable {F : Type*} [Field F]

/-- **The Taylor expansion of `Q` at `a`, with one surviving term chosen.** -/
theorem exists_apply_eval_le_taylor (W : AbsoluteValue F ℝ) {d : σ → ℕ}
    {Q : MvPolynomial σ F} (hQ : ∀ j, Q.degreeOf j ≤ d j) (a b : σ → F)
    (hb : eval b Q ≠ 0) :
    ∃ ν : σ →₀ ℕ, (∀ j, ν j ≤ d j) ∧ eval a (hasseDeriv ν Q) ≠ 0 ∧
      W (eval b Q) ≤ (∏ j, ((d j : ℝ) + 1))
        * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
  classical
  set s : Finset (σ →₀ ℕ) := Finset.image (boxMonomial d) Finset.univ with hsdef
  have hmem : ∀ μ : σ →₀ ℕ, hasseDeriv μ Q ≠ 0 → μ ∈ s := by
    intro μ hμ
    have hle : ∀ j, μ j ≤ d j := fun j ↦ by
      by_contra hlt
      exact hμ (hasseDeriv_eq_zero_of_lt (lt_of_le_of_lt (hQ j) (not_le.mp hlt)))
    obtain ⟨I, rfl⟩ := exists_boxMonomial_eq hle
    exact Finset.mem_image_of_mem _ (Finset.mem_univ I)
  have hbox : ∀ μ ∈ s, ∀ j, μ j ≤ d j := by
    intro μ hμ j
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hμ
    exact boxMonomial_le d I j
  have hexp : eval b Q = ∑ μ ∈ s, eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j := by
    have hab : a + (b - a) = b := by
      funext j
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have := eval_add_eq_sum_hasseDeriv Q a (b - a) hmem
    rw [hab] at this
    rw [this]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    congr 1
    exact Finsupp.prod_of_support_subset μ (Finset.subset_univ _) _ fun j _ ↦ pow_zero _
  set s' : Finset (σ →₀ ℕ) := s.filter fun μ ↦ eval a (hasseDeriv μ Q) ≠ 0 with hs'def
  have hexp' : eval b Q = ∑ μ ∈ s', eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j := by
    rw [hexp]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun μ hμ hμ' ↦ ?_).symm
    simp only [Finset.mem_filter, not_and, not_not] at hμ'
    rw [hμ' hμ, zero_mul]
  have hne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    rw [h, Finset.sum_empty] at hexp'
    exact hb hexp'
  obtain ⟨ν, hν, hmax⟩ := s'.exists_max_image
    (fun μ ↦ W (eval a (hasseDeriv μ Q)) * ∏ j, W (b j - a j) ^ μ j) hne
  have hνs : ν ∈ s := Finset.mem_of_mem_filter _ hν
  have hνne : eval a (hasseDeriv ν Q) ≠ 0 := (Finset.mem_filter.mp hν).2
  refine ⟨ν, hbox ν hνs, hνne, ?_⟩
  have hnn : (0 : ℝ) ≤ W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j :=
    mul_nonneg (W.nonneg _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (W.nonneg _) _)
  calc W (eval b Q)
      = W (∑ μ ∈ s', eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j) := by rw [← hexp']
    _ ≤ ∑ μ ∈ s', W (eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j) := W.sum_le _ _
    _ ≤ ∑ _μ ∈ s', W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j := by
        refine Finset.sum_le_sum fun μ hμ ↦ ?_
        rw [map_mul, map_prod]
        simp only [map_pow]
        exact hmax μ hμ
    _ = (#s' : ℝ) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j, ((d j : ℝ) + 1)) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
        refine mul_le_mul_of_nonneg_right ?_ hnn
        have h1 : #s' ≤ ∏ j, (d j + 1) := by
          calc #s' ≤ #s := Finset.card_filter_le _ _
            _ ≤ #(Finset.univ : Finset (∀ j, Fin (d j + 1))) := Finset.card_image_le
            _ = ∏ j, (d j + 1) := by simp [Fintype.card_pi]
        calc (#s' : ℝ) ≤ ((∏ j, (d j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
          _ = ∏ j, ((d j : ℝ) + 1) := by push_cast; ring

/-- **The value of a Hasse derivative**, in terms of the local factor of `Q`. -/
theorem apply_eval_hasseDeriv_le (W : AbsoluteValue F ℝ) {d : σ → ℕ} {Q : MvPolynomial σ F}
    (hQ : ∀ j, Q.degreeOf j ≤ d j) (a : σ → F) (ν : σ →₀ ℕ) :
    W (eval a (hasseDeriv ν Q))
      ≤ (∏ j, ((d j : ℝ) + 1)) * (2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ))
        * ∏ j, max (W (a j)) 1 ^ d j := by
  have hdeg : ∀ j, (hasseDeriv ν Q).degreeOf j ≤ d j := fun j ↦
    le_trans (le_trans (degreeOf_hasseDeriv_le ν Q j) (Nat.sub_le _ _)) (hQ j)
  refine le_trans (apply_eval_le W hdeg a) ?_
  have hstep : (⨆ μ, W ((hasseDeriv ν Q).coeff μ)) ≤ 2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ) := by
    refine le_trans (iSup_coeff_hasseDeriv_le W ν Q) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun _ ↦ W.nonneg _)
    exact pow_le_pow_right₀ one_le_two (totalDegree_le_sum hQ)
  have hM : (0 : ℝ) ≤ ∏ j, ((d j : ℝ) + 1) := Finset.prod_nonneg fun j _ ↦ by positivity
  have hP : (0 : ℝ) ≤ ∏ j, max (W (a j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hM) hP

/-- **Splitting the distances into a truncated part and a bounded part.** -/
theorem prod_apply_sub_le (W : AbsoluteValue F ℝ) {d : σ → ℕ} {ν : σ →₀ ℕ}
    (hν : ∀ j, ν j ≤ d j) (a b : σ → F) :
    (∏ j, W (b j - a j) ^ ν j)
      ≤ 2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j) * (∏ j, max (W (b j)) 1 ^ d j)
        * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
  have key : ∀ j, W (b j - a j) ^ ν j
      ≤ 2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
        * min 1 (W (b j - a j)) ^ ν j := by
    intro j
    have ha1 : (1 : ℝ) ≤ max (W (a j)) 1 := le_max_right _ _
    have hb1 : (1 : ℝ) ≤ max (W (b j)) 1 := le_max_right _ _
    have hsplit : W (b j - a j) = min 1 (W (b j - a j)) * max (W (b j - a j)) 1 := by
      rw [max_comm, min_mul_max, one_mul]
    have htri : W (b j - a j) ≤ W (b j) + W (a j) := by
      simpa using W.sub_le (b j) 0 (a j)
    have h2 : max (W (b j - a j)) 1 ≤ 2 * max (W (a j)) 1 * max (W (b j)) 1 := by
      refine max_le (le_trans htri ?_) ?_
      · calc W (b j) + W (a j) ≤ max (W (b j)) 1 + max (W (a j)) 1 := by
              gcongr <;> exact le_max_left _ _
          _ ≤ 2 * max (W (a j)) 1 * max (W (b j)) 1 := by nlinarith
      · nlinarith
    have hmin0 : (0 : ℝ) ≤ min 1 (W (b j - a j)) := le_min zero_le_one (W.nonneg _)
    have hpow : W (b j - a j) ^ ν j
        = min 1 (W (b j - a j)) ^ ν j * max (W (b j - a j)) 1 ^ ν j := by
      rw [← mul_pow, ← hsplit]
    calc W (b j - a j) ^ ν j
        = min 1 (W (b j - a j)) ^ ν j * max (W (b j - a j)) 1 ^ ν j := hpow
      _ ≤ min 1 (W (b j - a j)) ^ ν j * (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ d j := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hmin0 _)
          calc max (W (b j - a j)) 1 ^ ν j
              ≤ (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ ν j :=
                pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) h2 _
            _ ≤ (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ d j :=
                pow_le_pow_right₀ (by nlinarith) (hν j)
      _ = 2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
            * min 1 (W (b j - a j)) ^ ν j := by
          rw [mul_pow, mul_pow]
          ring
  calc (∏ j, W (b j - a j) ^ ν j)
      ≤ ∏ j, (2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
          * min 1 (W (b j - a j)) ^ ν j) :=
        Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (W.nonneg _) _) fun j _ ↦ key j
    _ = 2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j) * (∏ j, max (W (b j)) 1 ^ d j)
          * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum]

/-- **The local bound at a place carrying a target.** -/
theorem exists_apply_eval_le_of_sub (W : AbsoluteValue F ℝ) {d : σ → ℕ} {Q : MvPolynomial σ F}
    (hQ : ∀ j, Q.degreeOf j ≤ d j) (a b : σ → F) (hb : eval b Q ≠ 0) :
    ∃ ν : σ →₀ ℕ, (∀ j, ν j ≤ d j) ∧ eval a (hasseDeriv ν Q) ≠ 0 ∧
      W (eval b Q) ≤ (∏ j, ((d j : ℝ) + 1)) ^ 2 * 4 ^ (∑ j, d j) * (⨆ μ, W (Q.coeff μ))
        * (∏ j, max (W (a j)) 1 ^ d j) ^ 2 * (∏ j, max (W (b j)) 1 ^ d j)
        * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
  obtain ⟨ν, hν, hνne, hbound⟩ := exists_apply_eval_le_taylor W hQ a b hb
  refine ⟨ν, hν, hνne, le_trans hbound ?_⟩
  have hM : (0 : ℝ) ≤ ∏ j, ((d j : ℝ) + 1) := Finset.prod_nonneg fun j _ ↦ by positivity
  have hPa : (0 : ℝ) ≤ ∏ j, max (W (a j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have hPb : (0 : ℝ) ≤ ∏ j, max (W (b j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have hPm : (0 : ℝ) ≤ ∏ j, min 1 (W (b j - a j)) ^ ν j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_min zero_le_one (W.nonneg _)) _
  have hQn : (0 : ℝ) ≤ ⨆ μ, W (Q.coeff μ) := Real.iSup_nonneg fun _ ↦ W.nonneg _
  have h1 := apply_eval_hasseDeriv_le W hQ a ν
  have h2 := prod_apply_sub_le W hν a b
  have hfour : (4 : ℝ) ^ (∑ j, d j) = 2 ^ (∑ j, d j) * 2 ^ (∑ j, d j) := by
    rw [← mul_pow]; norm_num
  calc (∏ j, ((d j : ℝ) + 1)) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j)
      ≤ (∏ j, ((d j : ℝ) + 1))
          * (((∏ j, ((d j : ℝ) + 1)) * (2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ))
              * ∏ j, max (W (a j)) 1 ^ d j)
            * (2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j)
              * (∏ j, max (W (b j)) 1 ^ d j) * ∏ j, min 1 (W (b j - a j)) ^ ν j)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 ?_ ?_) hM
        · exact Finset.prod_nonneg fun j _ ↦ pow_nonneg (W.nonneg _) _
        · positivity
    _ = (∏ j, ((d j : ℝ) + 1)) ^ 2 * 4 ^ (∑ j, d j) * (⨆ μ, W (Q.coeff μ))
          * (∏ j, max (W (a j)) 1 ^ d j) ^ 2 * (∏ j, max (W (b j)) 1 ^ d j)
          * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
        rw [hfour]; ring

end Taylor

end MvPolynomial

end
