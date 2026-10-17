/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import STForMathlib.RingTheory.MvPolynomial.Bezout
public import Mathlib.RingTheory.PowerSeries.WellKnown
-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# The Hilbert function of a complete intersection

For the standard grading of `K[X]` (one block of variables), let `g 0, …, g (t - 1)` be a
regular sequence of forms of degrees `e j` modulo a homogeneous ideal `J`. Each `g j` cuts the
Hilbert function by `H(m) ↦ H(m) - H(m - e j)`, so the Hilbert series are related by
`HS(J + (g)) = ∏ j, (1 - X ^ e j) · HS(J)` (`MvPolynomial.hilbertSeries_sup_span_range`).

For `J = 0` and `t + 1` the number of variables (a complete intersection of dimension `0` in
`ℙ^t`) this gives `HS · (1 - X) = ∏ j, (1 + X + ⋯ + X ^ (e j - 1))`, so the Hilbert function is
nondecreasing, bounded by `∏ j, e j`, and equal to it from degree `∑ j, (e j - 1)` on. This is
Corvaja–Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), Lemma 2.3, with the
degree from which it holds made explicit; no Hilbert polynomial is needed.

## Main definitions

* `MvPolynomial.oneBlock σ`: the standard grading, as the multigrading with one block.
* `MvPolynomial.hilbertSeries J`: `∑ m, dim (K[X]/J)_m X ^ m`, over `ℤ`.

## Main statements

* `MvPolynomial.hilbertFunction_sup_span_singleton_add`: `H_{J+(g)}(m + e) + H_J(m) = H_J(m + e)`
  for a nonzerodivisor `g` of degree `e` modulo `J`, and
  `MvPolynomial.hilbertFunction_sup_span_singleton_of_lt` for `m < e`.
* `MvPolynomial.hilbertSeries_sup_span_range`: the Hilbert series of `J + (g)`.
* `MvPolynomial.hilbertFunction_span_range_le` and
  `MvPolynomial.hilbertFunction_span_range_eq`: Lemma 2.3.
-/

@[expose] public section

open Finset Module

namespace MvPolynomial

variable {σ K : Type*} [Field K]

/-- The standard grading of `K[X]`, as the multigrading with one block. -/
abbrev oneBlock (σ : Type*) : σ → Unit := fun _ ↦ ()

/-- The degree-`d'` component of `p * g` vanishes when `g` is homogeneous of a degree not
below `d'`. -/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_mul_eq_zero {M : Type*}
    [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M] {w : σ → M}
    {g : MvPolynomial σ K} {e : M} (hg : IsWeightedHomogeneous w g e) (p : MvPolynomial σ K)
    {d' : M} (hd' : ¬ e ≤ d') : weightedHomogeneousComponent w d' (p * g) = 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmul : IsWeightedHomogeneous w (monomial u a * g) (Finsupp.weight w u + e) :=
      (isWeightedHomogeneous_monomial w u a rfl).mul hg
    refine hmul.weightedHomogeneousComponent_ne _ fun h ↦ hd' ?_
    rw [h]
    exact le_add_self
  | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]

section Finite

variable [Finite σ]

/-- The Hilbert series `∑ m, dim (K[X]/J)_m X ^ m` of an ideal for the standard grading. -/
noncomputable def hilbertSeries (J : Ideal (MvPolynomial σ K)) : PowerSeries ℤ :=
  PowerSeries.mk fun m ↦ (hilbertFunction (oneBlock σ) J (fun _ ↦ m) : ℤ)

omit [Finite σ] in
theorem coeff_hilbertSeries (J : Ideal (MvPolynomial σ K)) (m : ℕ) :
    PowerSeries.coeff m (hilbertSeries J) = hilbertFunction (oneBlock σ) J (fun _ ↦ m) :=
  PowerSeries.coeff_mk _ _

theorem finrank_inf_le (I : Ideal (MvPolynomial σ K)) (d : Unit → ℕ) :
    finrank K ↥(I.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight (oneBlock σ)) d)
      ≤ finrank K (weightedHomogeneousSubmodule K (multiWeight (oneBlock σ)) d) :=
  Submodule.finrank_mono inf_le_right

/-- **A nonzerodivisor of degree `e` cuts the Hilbert function** by its value `e` steps lower:
`H_{J+(g)}(m + e) + H_J(m) = H_J(m + e)`. -/
theorem hilbertFunction_sup_span_singleton_add {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight (oneBlock σ))) {g : MvPolynomial σ K} {e : ℕ}
    (hg : IsWeightedHomogeneous (multiWeight (oneBlock σ)) g (fun _ ↦ e)) (hg0 : g ≠ 0)
    (hcol : J.colon {g} = J) (m : ℕ) :
    hilbertFunction (oneBlock σ) (J ⊔ Ideal.span {g}) (fun _ ↦ m + e) +
        hilbertFunction (oneBlock σ) J (fun _ ↦ m) =
      hilbertFunction (oneBlock σ) J (fun _ ↦ m + e) := by
  have h := finrank_sup_span_singleton_add_finrank_colon (oneBlock σ) hJ hg hg0 (fun _ ↦ m)
  rw [hcol, show ((fun _ ↦ m) + fun _ ↦ e : Unit → ℕ) = fun _ ↦ m + e from rfl] at h
  have h₁ := finrank_inf_le (J ⊔ Ideal.span {g}) (fun _ ↦ m + e)
  have h₂ := finrank_inf_le J (fun _ ↦ m)
  have h₃ := finrank_inf_le J (fun _ ↦ m + e)
  change _ = _ + finrank K (weightedHomogeneousSubmodule K _ (fun _ ↦ m)) at h
  change finrank K _ + finrank K _ = finrank K _ + _ at h
  unfold hilbertFunction
  change finrank K (weightedHomogeneousSubmodule K _ (fun _ ↦ m + e)) - _ + _ = _
  omega

omit [Finite σ] in
/-- Below the degree of `g`, cutting by `g` does not change the Hilbert function. -/
theorem hilbertFunction_sup_span_singleton_of_lt {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight (oneBlock σ))) {g : MvPolynomial σ K} {e : ℕ}
    (hg : IsWeightedHomogeneous (multiWeight (oneBlock σ)) g (fun _ ↦ e)) {m : ℕ} (hm : m < e) :
    hilbertFunction (oneBlock σ) (J ⊔ Ideal.span {g}) (fun _ ↦ m) =
      hilbertFunction (oneBlock σ) J (fun _ ↦ m) := by
  suffices hEq : (J ⊔ Ideal.span {g}).restrictScalars K ⊓
      weightedHomogeneousSubmodule K (multiWeight (oneBlock σ)) (fun _ ↦ m) ≤
        J.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight (oneBlock σ))
          (fun _ ↦ m) by
    unfold hilbertFunction
    rw [le_antisymm hEq (inf_le_inf_right _ (Submodule.restrictScalars_mono K le_sup_left))]
  refine fun x ⟨hxJ, hx⟩ ↦ ⟨?_, hx⟩
  obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.mp hxJ
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hx' : j + a * g = weightedHomogeneousComponent (multiWeight (oneBlock σ))
      (fun _ ↦ m) (j + a * g) :=
    ((mem_weightedHomogeneousSubmodule K _ _ _).mp hx).weightedHomogeneousComponent_same.symm
  change j + a * g ∈ J
  rw [hx', map_add, hg.weightedHomogeneousComponent_mul_eq_zero a (d' := fun _ ↦ m)
    (fun h ↦ absurd (Pi.le_def.mp h ()) (not_le.mpr hm)), add_zero]
  exact hJ hj _

theorem hilbertSeries_sup_span_singleton {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight (oneBlock σ))) {g : MvPolynomial σ K} {e : ℕ}
    (hg : IsWeightedHomogeneous (multiWeight (oneBlock σ)) g (fun _ ↦ e)) (hg0 : g ≠ 0)
    (hcol : J.colon {g} = J) :
    hilbertSeries (J ⊔ Ideal.span {g}) = (1 - PowerSeries.X ^ e) * hilbertSeries J := by
  ext m
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', coeff_hilbertSeries,
    coeff_hilbertSeries]
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [Nat.add_sub_cancel, coeff_hilbertSeries,
      ← hilbertFunction_sup_span_singleton_add hJ hg hg0 hcol k]
    push_cast
    ring
  · rw [hilbertFunction_sup_span_singleton_of_lt hJ hg (not_le.mp hm), sub_zero]

/-- **The Hilbert series of a section by a regular sequence**:
`HS(J + (g 0, …, g (t - 1))) = ∏ j, (1 - X ^ e j) · HS(J)`. -/
theorem hilbertSeries_sup_span_range : ∀ {t : ℕ} {J : Ideal (MvPolynomial σ K)}
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ℕ},
    J.IsWeightedHomogeneous (multiWeight (oneBlock σ)) →
    (∀ j, IsWeightedHomogeneous (multiWeight (oneBlock σ)) (g j) (fun _ ↦ e j)) →
    IsRegularSeq t J g →
    hilbertSeries (J ⊔ Ideal.span (Set.range g)) =
      (∏ j, (1 - PowerSeries.X ^ e j)) * hilbertSeries J
  | 0, J, g, e, _, _, _ => by simp
  | t + 1, J, g, e, hJ, hg, ⟨hg0, hcol, hreg⟩ => by
    have hJ' : (J ⊔ Ideal.span {g 0}).IsWeightedHomogeneous (multiWeight (oneBlock σ)) :=
      hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨_, (Set.mem_singleton_iff.mp hx) ▸ hg 0⟩)
    rw [sup_span_range_succ, hilbertSeries_sup_span_range (g := Fin.tail g) (e := Fin.tail e) hJ'
      (fun j ↦ hg j.succ) hreg, hilbertSeries_sup_span_singleton hJ (hg 0) hg0 hcol,
      Fin.prod_univ_succ]
    simp only [Fin.tail]
    ring

end Finite

variable [Fintype σ]

/-- The Hilbert function of `K[X]` in degree `m` is `C(|σ| + m - 1, m)`. -/
theorem hilbertFunction_bot (m : ℕ) :
    hilbertFunction (oneBlock σ) (⊥ : Ideal (MvPolynomial σ K)) (fun _ ↦ m) =
      (Fintype.card σ + m - 1).choose m := by
  unfold hilbertFunction
  rw [finrank_multiWeight, card_blockMonomials, Fintype.prod_unique, Submodule.restrictScalars_bot,
    bot_inf_eq, finrank_bot]
  simp [oneBlock]

/-- The Hilbert series of `K[X]` is `(1 - X) ^ (-|σ|)`. -/
theorem hilbertSeries_bot_mul [Nonempty σ] :
    hilbertSeries (⊥ : Ideal (MvPolynomial σ K)) * (1 - PowerSeries.X) ^ Fintype.card σ = 1 := by
  have h : hilbertSeries (⊥ : Ideal (MvPolynomial σ K)) =
      (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
    rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ Fintype.card_pos]
    ext m
    rw [coeff_hilbertSeries, hilbertFunction_bot, PowerSeries.coeff_mk]
    have := Fintype.card_pos (α := σ)
    rw [show Fintype.card σ + m - 1 = (Fintype.card σ - 1) + m by omega, Nat.choose_symm_add]
  rw [h, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  exact (PowerSeries.invOneSubPow ℤ _).val_inv

/-- The polynomial `∏ j, (1 + X + ⋯ + X ^ (e j - 1))`. -/
noncomputable def boxPoly {t : ℕ} (e : Fin t → ℕ) : Polynomial ℤ :=
  ∏ j, ∑ k ∈ range (e j), Polynomial.X ^ k

theorem eval_one_boxPoly {t : ℕ} (e : Fin t → ℕ) : (boxPoly e).eval 1 = ∏ j, (e j : ℤ) := by
  simp [boxPoly, Polynomial.eval_prod, Polynomial.eval_finsetSum]

theorem natDegree_boxPoly_le {t : ℕ} (e : Fin t → ℕ) :
    (boxPoly e).natDegree ≤ ∑ j, (e j - 1) := by
  refine (Polynomial.natDegree_prod_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  exact (Polynomial.natDegree_X_pow_le k).trans (by have := mem_range.mp hk; omega)

theorem coeff_boxPoly_nonneg {t : ℕ} (e : Fin t → ℕ) (k : ℕ) : 0 ≤ (boxPoly e).coeff k := by
  revert k
  refine prod_induction _ (fun p : Polynomial ℤ ↦ ∀ k, 0 ≤ p.coeff k) ?_ ?_ ?_
  · intro p q hp hq k
    rw [Polynomial.coeff_mul]
    exact sum_nonneg fun x _ ↦ mul_nonneg (hp _) (hq _)
  · intro k
    rw [Polynomial.coeff_one]
    split_ifs <;> norm_num
  · intro j _ k
    rw [Polynomial.finsetSum_coeff]
    refine sum_nonneg fun i _ ↦ ?_
    rw [Polynomial.coeff_X_pow]
    split_ifs <;> norm_num

/-- For `t + 1` variables and a regular sequence of `t` forms, `HS · (1 - X) = ∏ j, (1 + ⋯ +
X ^ (e j - 1))`. -/
theorem hilbertSeries_span_range_mul_one_sub {t : ℕ} (hσ : Fintype.card σ = t + 1)
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight (oneBlock σ)) (g j) (fun _ ↦ e j))
    (hreg : IsRegularSeq t ⊥ g) :
    hilbertSeries (Ideal.span (Set.range g)) * (1 - PowerSeries.X) =
      (boxPoly e : PowerSeries ℤ) := by
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  have hbot : (⊥ : Ideal (MvPolynomial σ K)).IsWeightedHomogeneous (multiWeight (oneBlock σ)) :=
    fun p hp d ↦ by rw [(Submodule.mem_bot _).mp hp, map_zero]; exact Submodule.zero_mem _
  have h := hilbertSeries_sup_span_range hbot hg hreg
  rw [bot_sup_eq] at h
  have hX : (1 - PowerSeries.X : PowerSeries ℤ) ^ t ≠ 0 := pow_ne_zero _ fun h0 ↦ by
    simpa using congrArg PowerSeries.constantCoeff h0
  refine mul_right_cancel₀ hX ?_
  have hb : ((boxPoly e : Polynomial ℤ) : PowerSeries ℤ) * (1 - PowerSeries.X) ^ t =
      ∏ j, (1 - PowerSeries.X ^ e j) := by
    rw [boxPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod,
      show (1 - PowerSeries.X : PowerSeries ℤ) ^ t = ∏ _j : Fin t, (1 - PowerSeries.X) by simp,
      ← prod_mul_distrib]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [map_sum, ← geom_sum_mul_neg]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hb, mul_assoc, ← pow_succ', ← hσ, h, mul_assoc, hilbertSeries_bot_mul, mul_one]

/-- The Hilbert function of a complete intersection of dimension `0` is the partial sum of the
coefficients of `∏ j, (1 + ⋯ + X ^ (e j - 1))`. -/
theorem hilbertFunction_span_range_eq_sum {t : ℕ} (hσ : Fintype.card σ = t + 1)
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight (oneBlock σ)) (g j) (fun _ ↦ e j))
    (hreg : IsRegularSeq t ⊥ g) (m : ℕ) :
    (hilbertFunction (oneBlock σ) (Ideal.span (Set.range g)) (fun _ ↦ m) : ℤ) =
      ∑ k ∈ range (m + 1), (boxPoly e).coeff k := by
  have h := hilbertSeries_span_range_mul_one_sub hσ hg hreg
  induction m with
  | zero =>
    have := congrArg (PowerSeries.coeff (R := ℤ) 0) h
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_zero_mul_X, sub_zero,
      Polynomial.coeff_coe, coeff_hilbertSeries] at this
    simpa using this
  | succ m ih =>
    have := congrArg (PowerSeries.coeff (R := ℤ) (m + 1)) h
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X, Polynomial.coeff_coe,
      coeff_hilbertSeries, coeff_hilbertSeries] at this
    rw [sum_range_succ, ← ih, ← this]
    ring

/-- **The Hilbert function of a complete intersection is bounded by its degree**
(Corvaja–Zannier 2004, Lemma 2.3): for `t + 1` variables and a regular sequence of `t` forms of
degrees `e j`, `dim (K[X]/(g))_m ≤ ∏ j, e j` for every `m`. -/
theorem hilbertFunction_span_range_le {t : ℕ} (hσ : Fintype.card σ = t + 1)
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight (oneBlock σ)) (g j) (fun _ ↦ e j))
    (hreg : IsRegularSeq t ⊥ g) (m : ℕ) :
    hilbertFunction (oneBlock σ) (Ideal.span (Set.range g)) (fun _ ↦ m) ≤ ∏ j, e j := by
  have h := hilbertFunction_span_range_eq_sum hσ hg hreg m
  have hn : (boxPoly e).natDegree < max m (boxPoly e).natDegree + 1 := by omega
  have h1 := Polynomial.eval_eq_sum_range' hn 1
  simp only [one_pow, mul_one, eval_one_boxPoly] at h1
  have : ∑ k ∈ range (m + 1), (boxPoly e).coeff k ≤
      ∑ k ∈ range (max m (boxPoly e).natDegree + 1), (boxPoly e).coeff k :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      fun k _ _ ↦ coeff_boxPoly_nonneg e k
  exact_mod_cast h ▸ h1 ▸ this

/-- **The Hilbert function of a complete intersection of dimension `0` is its degree** from
degree `∑ j, (e j - 1)` on (Corvaja–Zannier 2004, Lemma 2.3). -/
theorem hilbertFunction_span_range_eq {t : ℕ} (hσ : Fintype.card σ = t + 1)
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight (oneBlock σ)) (g j) (fun _ ↦ e j))
    (hreg : IsRegularSeq t ⊥ g) {m : ℕ} (hm : ∑ j, (e j - 1) ≤ m) :
    hilbertFunction (oneBlock σ) (Ideal.span (Set.range g)) (fun _ ↦ m) = ∏ j, e j := by
  have h := hilbertFunction_span_range_eq_sum hσ hg hreg m
  have hn : (boxPoly e).natDegree < m + 1 := by have := natDegree_boxPoly_le e; omega
  have h1 := Polynomial.eval_eq_sum_range' hn 1
  simp only [one_pow, mul_one, eval_one_boxPoly] at h1
  exact_mod_cast h.trans h1.symm

end MvPolynomial
