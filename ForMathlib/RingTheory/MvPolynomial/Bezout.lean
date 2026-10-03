/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Associativity

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bézout's theorem for multiprojective complete intersections

Cutting a multihomogeneous ideal `J` by a multihomogeneous nonzerodivisor `g` of multidegree `e`
changes the degrees by `d_β(J + (g)) = ∑ i, e i · d_{β + ε_i}(J)`
(`MvPolynomial.multidegree_sup_span_singleton_of_colon_eq`). Iterating along a regular sequence
`g_1, …, g_t` gives
`d_β(J + (g_1, …, g_t)) = ∑_{f : Fin t → ι} ∏ j, e_j (f j) · d_{β + ε_{f 1} + ⋯ + ε_{f t}}(J)`,
the coefficient extraction from `∏ j, (∑ i, e_j i T_i)`.

On the whole space `ℙ^{n_1} × ⋯ × ℙ^{n_q}` the degrees are `d_α = 1` for `α = n` and `0`
otherwise (`MvPolynomial.multidegree_bot`). Combined with the associativity formula this is
**Bézout's theorem with multiplicities**: for a regular sequence in `K[X]`,
`∑_𝔭 ℓ(K[X]_𝔭 / I_𝔭) · d_β(𝔭)` over the multihomogeneous primes of maximal dimension containing
`I = (g_1, …, g_t)` is the number of `f : Fin t → ι` with `β + ∑ j, ε_{f j} = n`, each weighted by
`∏ j, e_j (f j)`. When every `g_j` has positive degree in every block, `dim I = |n| - t`.

The hypothesis of regularity is what makes the lengths exact. Evertse's Lemma 4 (Acta Arith. 73
(1995)) is an inequality for arbitrary systems of equations, counting only the components of the
expected codimension; it needs in addition that the local rings of `K[X]` are Cohen–Macaulay, and
is in `ForMathlib.RingTheory.MvPolynomial.ExcessBezout`.

## Main definitions

* `MvPolynomial.IsRegularSeq b J g`: `g 0, g 1, …` is a sequence of nonzerodivisors modulo `J`,
  `J + (g 0)`, ….
* `MvPolynomial.bottomType b`: the exponent `n = (n_i)` with `n_i + 1` variables in block `i`.

## Main statements

* `MvPolynomial.multidegree_sup_span_range_of_isRegularSeq`: the degrees of a section by a
  regular sequence.
* `MvPolynomial.totalDegree_hilbertPoly_sup_span_range_of_isRegularSeq`: its dimension, exactly
  `dim J - t` when all degrees are positive.
* `MvPolynomial.multidegree_bot`: the degrees of the whole space.
* `MvPolynomial.sum_localLength_mul_multidegree_eq_bezout`: **Bézout's theorem with
  multiplicities** for complete intersections.
-/

@[expose] public section

open Finset

variable {σ ι K : Type*}

namespace MvPolynomial

variable [Field K] [DecidableEq ι]

/-- `g 0, g 1, …, g (t - 1)` is a regular sequence modulo `J`: each `g j` is nonzero and a
nonzerodivisor modulo `J + (g 0, …, g (j - 1))`. -/
def IsRegularSeq : (t : ℕ) → Ideal (MvPolynomial σ K) → (Fin t → MvPolynomial σ K) → Prop
  | 0, _, _ => True
  | t + 1, J, g => g 0 ≠ 0 ∧ J.colon {g 0} = J ∧ IsRegularSeq t (J ⊔ Ideal.span {g 0}) (Fin.tail g)

theorem sup_span_range_succ {t : ℕ} (J : Ideal (MvPolynomial σ K))
    (g : Fin (t + 1) → MvPolynomial σ K) :
    J ⊔ Ideal.span (Set.range g) = J ⊔ Ideal.span {g 0} ⊔ Ideal.span (Set.range (Fin.tail g)) := by
  conv_lhs => rw [← Fin.cons_self_tail g, Fin.range_cons, Ideal.span_insert, ← sup_assoc]

theorem isWeightedHomogeneous_sup_span_range {b : σ → ι} {t : ℕ}
    {J : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    {g : Fin t → MvPolynomial σ K} {e : Fin t → ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight b) (g j) (e j)) :
    Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span (Set.range g)) :=
  hJ.sup (isWeightedHomogeneous_span fun _ ⟨j, hj⟩ ↦ ⟨e j, hj ▸ hg j⟩)

section Degrees

variable [Finite σ] [Finite ι] {b : σ → ι}

/-- **Sections by a regular sequence lower the dimension by at least the length.** -/
theorem totalDegree_hilbertPoly_sup_span_range_le (hb : Function.Surjective b) :
    ∀ (t : ℕ) (J : Ideal (MvPolynomial σ K)) (g : Fin t → MvPolynomial σ K)
      (e : Fin t → ι → ℕ), J.IsWeightedHomogeneous (multiWeight b) →
      (∀ j, IsWeightedHomogeneous (multiWeight b) (g j) (e j)) → IsRegularSeq t J g →
      (hilbertPoly b (J ⊔ Ideal.span (Set.range g))).totalDegree ≤
        (hilbertPoly b J).totalDegree - t
  | 0, J, g, _, _, _, _ => by simp [Set.range_eq_empty]
  | t + 1, J, g, e, hJ, hg, ⟨hg0, hcol, hreg⟩ => by
    have hJ' : Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span {g 0}) :=
      hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e 0, (Set.mem_singleton_iff.mp hx) ▸ hg 0⟩)
    have h1 := totalDegree_hilbertPoly_sup_span_singleton_le_of_colon_eq hb hJ (hg 0) hg0 hcol
    have h2 := totalDegree_hilbertPoly_sup_span_range_le hb t _ (Fin.tail g) (Fin.tail e) hJ'
      (fun j ↦ hg j.succ) hreg
    rw [sup_span_range_succ]
    omega

/-- **Sections by a regular sequence of positive degrees lower the dimension by exactly the
length.** -/
theorem totalDegree_hilbertPoly_sup_span_range_of_isRegularSeq (hb : Function.Surjective b) :
    ∀ (t : ℕ) (J : Ideal (MvPolynomial σ K)) (g : Fin t → MvPolynomial σ K)
      (e : Fin t → ι → ℕ), J.IsWeightedHomogeneous (multiWeight b) →
      (∀ j, IsWeightedHomogeneous (multiWeight b) (g j) (e j)) → IsRegularSeq t J g →
      (∀ j i, 0 < e j i) → t ≤ (hilbertPoly b J).totalDegree →
      (hilbertPoly b (J ⊔ Ideal.span (Set.range g))).totalDegree =
        (hilbertPoly b J).totalDegree - t
  | 0, J, g, _, _, _, _, _, _ => by simp [Set.range_eq_empty]
  | t + 1, J, g, e, hJ, hg, ⟨hg0, hcol, hreg⟩, he, ht => by
    have hJ' : Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span {g 0}) :=
      hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e 0, (Set.mem_singleton_iff.mp hx) ▸ hg 0⟩)
    have h1 := totalDegree_hilbertPoly_sup_span_singleton_of_colon_eq hb hJ (hg 0) hg0 hcol
      (he 0) (by omega)
    have h2 := totalDegree_hilbertPoly_sup_span_range_of_isRegularSeq hb t _ (Fin.tail g)
      (Fin.tail e) hJ' (fun j ↦ hg j.succ) hreg (fun j ↦ he j.succ) (by omega)
    rw [sup_span_range_succ, h2, h1]
    omega

/-- **The degrees of a section by a regular sequence.** For a regular sequence `g_j` of
multidegrees `e_j` modulo `J`, in every degree `|β| ≥ dim J - t`,
`d_β(J + (g_1, …, g_t)) = ∑_{f : Fin t → ι} ∏ j, e_j (f j) · d_{β + ∑ j, ε_{f j}}(J)`. -/
theorem multidegree_sup_span_range_of_isRegularSeq [Fintype ι] (hb : Function.Surjective b) :
    ∀ (t : ℕ) (J : Ideal (MvPolynomial σ K)) (g : Fin t → MvPolynomial σ K)
      (e : Fin t → ι → ℕ), J.IsWeightedHomogeneous (multiWeight b) →
      (∀ j, IsWeightedHomogeneous (multiWeight b) (g j) (e j)) → IsRegularSeq t J g →
      ∀ β : ι →₀ ℕ, (hilbertPoly b J).totalDegree - t ≤ β.degree →
      multidegree b (J ⊔ Ideal.span (Set.range g)) β =
        ∑ f : Fin t → ι, (∏ j, (e j (f j) : ℚ)) *
          multidegree b J (β + ∑ j, Finsupp.single (f j) 1)
  | 0, J, g, _, _, _, _, β, _ => by simp [Set.range_eq_empty]
  | t + 1, J, g, e, hJ, hg, ⟨hg0, hcol, hreg⟩, β, hβ => by
    have hJ' : Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span {g 0}) :=
      hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e 0, (Set.mem_singleton_iff.mp hx) ▸ hg 0⟩)
    have h1 := totalDegree_hilbertPoly_sup_span_singleton_le_of_colon_eq hb hJ (hg 0) hg0 hcol
    rw [sup_span_range_succ, multidegree_sup_span_range_of_isRegularSeq hb t _ (Fin.tail g)
      (Fin.tail e) hJ' (fun j ↦ hg j.succ) hreg β (by omega)]
    have hstep : ∀ f : Fin t → ι, multidegree b (J ⊔ Ideal.span {g 0})
        (β + ∑ j, Finsupp.single (f j) 1) = ∑ i, (e 0 i : ℚ) *
          multidegree b J (β + ∑ j, Finsupp.single (f j) 1 + Finsupp.single i 1) := by
      intro f
      refine multidegree_sup_span_singleton_of_colon_eq hb hJ (hg 0) hg0 hcol ?_
      rw [map_add, map_sum]
      simp only [Finsupp.degree_single, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one]
      omega
    simp_rw [hstep, Finset.mul_sum]
    rw [Finset.sum_comm, ← (Fin.consEquiv fun _ : Fin (t + 1) ↦ ι).sum_comp,
      Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun f _ ↦ ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.tail]
    rw [add_assoc β, add_comm (Finsupp.single i 1)]
    ring

/-- The exponent `n` of the whole space `ℙ^{n_1} × ⋯ × ℙ^{n_q}`: `n_i + 1` is the number of
variables of block `i`. -/
noncomputable def bottomType (b : σ → ι) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ Nat.card {s // b s = i} - 1

omit [Finite σ] in
theorem bottomType_eq_coneType [Fintype σ] [Fintype ι] (b : σ → ι) :
    bottomType b = coneType b univ := by
  classical
  ext i
  simp [bottomType, coneType, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Finite σ] [Finite ι] in
theorem blockCountPoly_eq_conePoly [Fintype σ] [Fintype ι] (b : σ → ι) :
    blockCountPoly b = conePoly b univ 0 := by
  simp [blockCountPoly, conePoly, shiftPoly, aeval_X_left_apply]

/-- **The degrees of the whole space**: `d_α = 1` for `α = n` and `0` otherwise, in every degree
`|α| ≥ |n|`. -/
theorem multidegree_bot [Fintype ι] (hb : Function.Surjective b) {α : ι →₀ ℕ}
    (hα : (bottomType b).degree ≤ α.degree) :
    multidegree (K := K) b ⊥ α = if α = bottomType b then 1 else 0 := by
  classical
  have := Fintype.ofFinite σ
  rw [bottomType_eq_coneType] at hα ⊢
  rw [multidegree, hilbertPoly_bot hb, blockCountPoly_eq_conePoly,
    (agreeAbove_conePoly b univ 0).1 α hα, coeff_monomial]
  by_cases hαn : α = coneType b univ
  · subst hαn
    simp only [↓reduceIte]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ ↦
      mul_inv_cancel₀ ((Nat.cast_ne_zero (R := ℚ)).mpr (Nat.factorial_ne_zero _))
  · simp [Ne.symm hαn, hαn]

/-- The whole space has dimension `|n|`. -/
theorem totalDegree_hilbertPoly_bot (hb : Function.Surjective b) :
    (hilbertPoly (K := K) b ⊥).totalDegree = (bottomType b).degree := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  have h := agreeAbove_conePoly b univ 0
  rw [bottomType_eq_coneType, hilbertPoly_bot hb, blockCountPoly_eq_conePoly]
  refine le_antisymm h.2 ?_
  have hc := h.1 (coneType b univ) le_rfl
  simp only [coeff_monomial, ↓reduceIte] at hc
  have hne : (conePoly b univ 0).coeff (coneType b univ) ≠ 0 := by
    rw [hc]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      inv_ne_zero ((Nat.cast_ne_zero (R := ℚ)).mpr (Nat.factorial_ne_zero _))
  rw [Finsupp.degree_apply]
  exact le_totalDegree (mem_support_iff.mpr hne)

/-- **Bézout's theorem with multiplicities** for multiprojective complete intersections. Let
`g_1, …, g_t` be a regular sequence in `K[X]` of multidegrees `e_j`, `I = (g_1, …, g_t)`, and `P`
the multihomogeneous primes `𝔭 ⊇ I` of maximal dimension. For every `β` with `|β| = |n| - t`,
`∑_{𝔭 ∈ P} ℓ(K[X]_𝔭 / I_𝔭) · d_β(𝔭) = ∑_{f : β + ∑ j, ε_{f j} = n} ∏ j, e_j (f j)`. -/
theorem sum_localLength_mul_multidegree_eq_bezout [Fintype ι] (hb : Function.Surjective b)
    {t : ℕ} {g : Fin t → MvPolynomial σ K} {e : Fin t → ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (multiWeight b) (g j) (e j)) (hreg : IsRegularSeq t ⊥ g) :
    ∃ (P : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧
        Ideal.span (Set.range g) ≤ 𝔭 ∧ hilbertPoly b 𝔭 ≠ 0 ∧ (hilbertPoly b 𝔭).totalDegree =
          (hilbertPoly b (Ideal.span (Set.range g))).totalDegree) ∧
      (∀ 𝔭 ∈ P, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 (Ideal.span (Set.range g)) = ℓ 𝔭) ∧
      ∀ β : ι →₀ ℕ, β.degree = (bottomType b).degree - t →
        ∑ 𝔭 ∈ P, (ℓ 𝔭 : ℚ) * multidegree b 𝔭 β =
          ∑ f : Fin t → ι with β + ∑ j, Finsupp.single (f j) 1 = bottomType b,
            ∏ j, (e j (f j) : ℚ) := by
  classical
  have hI := isWeightedHomogeneous_sup_span_range (isWeightedHomogeneous_bot (R := K) _) hg
  rw [bot_sup_eq] at hI
  obtain ⟨P, ℓ, hP, hℓ, h⟩ := multidegree_eq_sum_localLength hb hI
  refine ⟨P, ℓ, hP, hℓ, fun β hβ ↦ ?_⟩
  have hdim := totalDegree_hilbertPoly_sup_span_range_le hb t ⊥ g e
    (isWeightedHomogeneous_bot _) hg hreg
  rw [bot_sup_eq, totalDegree_hilbertPoly_bot hb] at hdim
  rw [← h β (by omega)]
  have := multidegree_sup_span_range_of_isRegularSeq hb t ⊥ g e
    (isWeightedHomogeneous_bot _) hg hreg β (by rw [totalDegree_hilbertPoly_bot hb]; omega)
  rw [bot_sup_eq] at this
  rw [this, Finset.sum_filter]
  refine sum_congr rfl fun f _ ↦ ?_
  have hdeg : (bottomType b).degree ≤ (β + ∑ j, Finsupp.single (f j) 1).degree := by
    rw [map_add, map_sum]
    simp only [Finsupp.degree_single, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    omega
  rw [multidegree_bot hb hdeg]
  split_ifs <;> simp

end Degrees

end MvPolynomial
