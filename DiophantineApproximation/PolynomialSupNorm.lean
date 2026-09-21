/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Polynomial.Norm

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The naive height of an integer polynomial

The **naive height** of `P = ∑ aᵢ Xⁱ` is `max |aᵢ|`, and it is the height that Mahler's and
Koksma's exponents are normalized by. Mathlib already has it, under a name that says what it is
rather than what it is used for: `Polynomial.supNorm`, the Gauss norm of the norm of the
coefficient ring at `c = 1`. Nothing is redefined here. What is missing is the API that Layer 1.2
runs on, and it is of two kinds.

The first is arithmetic, and holds over any seminormed ring: subadditivity, the behaviour under
multiplication by a constant, and the invariance under `Polynomial.reflect`, which reverses the
coefficients and so permutes the very set the supremum is taken over.

The second is **Northcott's theorem for integer polynomials**, and it is the reason the exponents
of Layer 1.2 can be defined by an infinite set of solutions and used through a bound on the
height: over `ℤ` a polynomial of bounded degree and bounded naive height lies in a finite set, so
an infinite set of solutions of bounded degree has *unbounded* height, and any constant in front
of `H(P) ^ (-w)` can be absorbed by lowering `w`. Over `ℚ` this fails — `C (1 / n)` has height
`1 / n` — and the failure is exactly the integrality that makes `1 ≤ H(P)` for `P ≠ 0`.

## Main results

* `Polynomial.supNorm_add_le`, `Polynomial.supNorm_sum_le`, `Polynomial.supNorm_C_mul`,
  `Polynomial.supNorm_le_of_forall` and `Polynomial.supNorm_reflect`: the arithmetic of the naive
  height over a seminormed ring. Reflection, which reverses the coefficients, preserves it
  *exactly*.
* `Polynomial.supNorm_linear` and `Polynomial.coeff_linear_zero`, `_one`, `_add_two`: the naive
  height of `a X + b` is `max |a| |b|` — the naive height of the fraction `-b / a` in the sense
  of Layer 1.1.
* `Polynomial.one_le_supNorm` and `Polynomial.supNorm_pos`: over `ℤ`, a nonzero polynomial has
  height at least `1`.
* `Polynomial.finite_setOf_natDegree_le_supNorm_le`: **Northcott for integer polynomials**, the
  finiteness of the polynomials of bounded degree and bounded naive height.
* `Polynomial.infinite_sep_lt_supNorm`: an infinite set of integer polynomials of bounded degree
  still has infinitely many members above any given height, and
  `Polynomial.infinite_of_forall_exists_lt_supNorm`, the converse direction.
* `Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt` and
  `Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`: **the two height gaps**. Below a
  threshold that depends only on the height bound, a nonzero value at `ξ` — respectively a root
  at positive distance less than the threshold from `ξ` — forces the naive height above that
  bound. Layer 1.2 uses one or the other every time it replaces a solution by another polynomial.
* `Polynomial.supNorm_comp_le` and `Polynomial.one_le_sum_supNorm_pow`: a substitution multiplies
  the naive height by at most a constant depending only on the substituted polynomial and the
  degree bound.

## Implementation notes

⚠ **`Polynomial.supNorm` is the naive height and no wrapper is introduced.** Mathlib's own
module documentation says so ("often called the *(naive) height*") and declines the name because
`Height` is taken; a local abbreviation would only hide `Polynomial.le_supNorm` and
`Polynomial.exists_eq_supNorm`, which are what every proof below uses. The zero polynomial has
height `0`, not the junk value `1` of the projective heights — `supNorm` is a norm, not a height —
and every statement of Layer 1.2 excludes it through `0 < |P ξ|` anyway.

The finiteness proof reads a polynomial of degree at most `n` off its coefficient vector on
`Fin (n + 1)`; that map is injective there, and its image lands in a product of finite intervals
of `ℤ`. The bound on a coefficient is `⌈B⌉`, so the statement is for a real bound and no
integrality of `B` is assumed.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1. E.
Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.6.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/

public section

namespace Polynomial

/-! ### The naive height over a seminormed ring -/

section Seminormed

variable {A : Type*} [SeminormedRing A]

theorem supNorm_add_le (P Q : A[X]) : (P + Q).supNorm ≤ P.supNorm + Q.supNorm := by
  obtain ⟨i, hi⟩ := (P + Q).exists_eq_supNorm
  rw [hi, coeff_add]
  exact (norm_add_le _ _).trans (add_le_add (P.le_supNorm i) (Q.le_supNorm i))

theorem supNorm_le_of_forall {P : A[X]} {c : ℝ} (h : ∀ i, ‖P.coeff i‖ ≤ c) : P.supNorm ≤ c := by
  obtain ⟨i, hi⟩ := P.exists_eq_supNorm
  rw [hi]
  exact h i

theorem supNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → A[X]) :
    (∑ i ∈ s, f i).supNorm ≤ ∑ i ∈ s, (f i).supNorm := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (supNorm_add_le _ _).trans (by gcongr)

/-- The naive height is multiplicative in a constant factor: the coefficients are all scaled by
it, and the supremum with them. -/
theorem supNorm_C_mul [NormMulClass A] (c : A) (P : A[X]) :
    (C c * P).supNorm = ‖c‖ * P.supNorm := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (C c * P).exists_eq_supNorm
    rw [hi, coeff_C_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (P.le_supNorm i) (norm_nonneg c)
  · obtain ⟨i, hi⟩ := P.exists_eq_supNorm
    rw [hi, ← norm_mul, ← coeff_C_mul]
    exact le_supNorm _ i

/-- Reversing the coefficients of a polynomial does not change its naive height: `revAt N` is an
involution of `ℕ`, so it permutes the family the supremum is taken over. -/
theorem supNorm_reflect (N : ℕ) (P : A[X]) : (P.reflect N).supNorm = P.supNorm := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (P.reflect N).exists_eq_supNorm
    rw [hi, coeff_reflect]
    exact P.le_supNorm _
  · obtain ⟨i, hi⟩ := P.exists_eq_supNorm
    have hc : (P.reflect N).coeff (revAt N i) = P.coeff i := by
      rw [coeff_reflect, revAt_invol]
    rw [hi, ← hc]
    exact (P.reflect N).le_supNorm _

end Seminormed

/-! ### Integrality and Northcott -/

section Integer

variable {P : ℤ[X]}

theorem abs_coeff_le_supNorm (P : ℤ[X]) (i : ℕ) : |((P.coeff i : ℤ) : ℝ)| ≤ P.supNorm := by
  simpa [Int.norm_eq_abs] using P.le_supNorm i

/-- **Integrality.** A nonzero integer polynomial has naive height at least `1`, because its
leading coefficient is a nonzero integer. This is what makes the constant in front of
`H(P) ^ (-w)` absorbable in Layer 1.2, and it is false over `ℚ`. -/
theorem one_le_supNorm (hP : P ≠ 0) : 1 ≤ P.supNorm := by
  have hlc : P.coeff P.natDegree ≠ 0 := mt leadingCoeff_eq_zero.1 hP
  have h1 : (1 : ℝ) ≤ ‖P.coeff P.natDegree‖ := by
    rw [Int.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hlc
  exact h1.trans (P.le_supNorm _)

theorem supNorm_pos (hP : P ≠ 0) : 0 < P.supNorm :=
  zero_lt_one.trans_le (one_le_supNorm hP)

theorem coeff_linear_zero {R : Type*} [Semiring R] (a b : R) :
    (C a * X + C b).coeff 0 = b := by
  rw [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, coeff_C_zero, zero_add]

theorem coeff_linear_one {R : Type*} [Semiring R] (a b : R) :
    (C a * X + C b).coeff 1 = a := by
  rw [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_of_ne_zero one_ne_zero, add_zero]

theorem coeff_linear_add_two {R : Type*} [Semiring R] (a b : R) (i : ℕ) :
    (C a * X + C b).coeff (i + 2) = 0 := by
  rw [coeff_add, coeff_C_mul, coeff_X_of_ne_one (by omega), mul_zero,
    coeff_C_of_ne_zero (by omega), add_zero]

/-- The naive height of a linear integer polynomial is the larger of the two coefficients. This
is the naive height of the fraction `-b / a` in the sense of Layer 1.1. -/
theorem supNorm_linear (a b : ℤ) :
    (C a * X + C b).supNorm = max |(a : ℝ)| |(b : ℝ)| := by
  have h0 := coeff_linear_zero a b
  have h1 := coeff_linear_one a b
  have hn := coeff_linear_add_two a b
  refine le_antisymm ?_ (max_le ?_ ?_)
  · obtain ⟨i, hi⟩ := (C a * X + C b : ℤ[X]).exists_eq_supNorm
    rw [hi]
    rcases i with _ | _ | i
    · rw [h0, Int.norm_eq_abs]; exact le_max_right _ _
    · rw [h1, Int.norm_eq_abs]; exact le_max_left _ _
    · rw [hn i, norm_zero]; positivity
  · have h := (C a * X + C b : ℤ[X]).le_supNorm 1
    rwa [h1, Int.norm_eq_abs] at h
  · have h := (C a * X + C b : ℤ[X]).le_supNorm 0
    rwa [h0, Int.norm_eq_abs] at h

/-- **Northcott's theorem for integer polynomials.** Bounded degree and bounded naive height
leave only finitely many polynomials. -/
theorem finite_setOf_natDegree_le_supNorm_le (n : ℕ) (B : ℝ) :
    {P : ℤ[X] | P.natDegree ≤ n ∧ P.supNorm ≤ B}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun P : ℤ[X] ↦ fun i : Fin (n + 1) ↦ P.coeff i) ?_ ?_
  · refine Set.Finite.subset
      (Set.Finite.pi fun _ : Fin (n + 1) ↦ Set.finite_Icc (-⌈B⌉) ⌈B⌉) ?_
    rintro g ⟨Q, ⟨-, hQB⟩, rfl⟩ i -
    have h1 : |((Q.coeff i : ℤ) : ℝ)| ≤ (⌈B⌉ : ℝ) :=
      (Q.abs_coeff_le_supNorm i).trans (hQB.trans (Int.le_ceil B))
    rw [← Int.cast_abs] at h1
    have h2 : |Q.coeff (i : ℕ)| ≤ ⌈B⌉ := by exact_mod_cast h1
    exact ⟨neg_le_of_abs_le h2, le_of_abs_le h2⟩
  · rintro Q ⟨hQ, -⟩ R ⟨hR, -⟩ hQR
    ext i
    rcases le_or_gt i n with hi | hi
    · exact congrFun hQR ⟨i, Nat.lt_succ_of_le hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hi),
        coeff_eq_zero_of_natDegree_lt (hR.trans_lt hi)]

/-- The constant that bounds the naive height of a substitution: the sum of the naive heights of
the powers of the substituted polynomial. It is at least `1`, because the zeroth power
contributes it. -/
theorem one_le_sum_supNorm_pow (q : ℤ[X]) (n : ℕ) :
    1 ≤ ∑ i ∈ Finset.range (n + 1), (q ^ i).supNorm := by
  have h0 : (q ^ 0 : ℤ[X]).supNorm = 1 := by
    rw [pow_zero, ← C_1, supNorm_C, norm_one]
  rw [← h0]
  exact Finset.single_le_sum (fun i _ ↦ supNorm_nonneg (q ^ i))
    (Finset.mem_range.2 (Nat.succ_pos n))

/-- **A substitution multiplies the naive height by at most a constant**, and the constant depends
only on the substituted polynomial and on the degree bound: `P ↦ P.comp q` is a linear map, and
each `X ^ i` has an image of fixed height. -/
theorem supNorm_comp_le {q P : ℤ[X]} {n : ℕ} (hP : P.natDegree ≤ n) :
    (P.comp q).supNorm ≤ (∑ i ∈ Finset.range (n + 1), (q ^ i).supNorm) * P.supNorm := by
  classical
  have hcomp : ∀ (s : Finset ℕ) (g : ℕ → ℤ[X]),
      (∑ i ∈ s, g i).comp q = ∑ i ∈ s, (g i).comp q := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_comp, ih]
  have hPsum : P = ∑ i ∈ Finset.range (n + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (n + 1) (by omega)
  calc (P.comp q).supNorm
      = (∑ i ∈ Finset.range (n + 1), C (P.coeff i) * q ^ i).supNorm := by
        conv_lhs => rw [hPsum]
        rw [hcomp]
        simp only [monomial_comp]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (C (P.coeff i) * q ^ i).supNorm := supNorm_sum_le _ _
    _ = ∑ i ∈ Finset.range (n + 1), |((P.coeff i : ℤ) : ℝ)| * (q ^ i).supNorm :=
        Finset.sum_congr rfl fun i _ ↦ by rw [supNorm_C_mul, Int.norm_eq_abs]
    _ ≤ ∑ i ∈ Finset.range (n + 1), P.supNorm * (q ^ i).supNorm :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_right (abs_coeff_le_supNorm P i) (supNorm_nonneg _)
    _ = (∑ i ∈ Finset.range (n + 1), (q ^ i).supNorm) * P.supNorm := by
        rw [← Finset.mul_sum, mul_comm]

theorem exists_supNorm_le_of_finite {S : Set ℤ[X]} (hS : S.Finite) :
    ∃ B : ℝ, ∀ P ∈ S, P.supNorm ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image Polynomial.supNorm).bddAbove
  exact ⟨B, fun P hP ↦ hB ⟨P, hP, rfl⟩⟩

/-- An infinite set of integer polynomials of bounded degree has **unbounded** naive height, and
in the strong form: above any bound it still has infinitely many members. This is the form Layer
1.2 uses to absorb a constant into the exponent. -/
theorem infinite_sep_lt_supNorm {S : Set ℤ[X]} {n : ℕ} (hS : S.Infinite)
    (hdeg : ∀ P ∈ S, P.natDegree ≤ n) (B : ℝ) : {P ∈ S | B < P.supNorm}.Infinite := by
  have hfin : {P ∈ S | P.supNorm ≤ B}.Finite :=
    (finite_setOf_natDegree_le_supNorm_le n B).subset fun P hP ↦ ⟨hdeg P hP.1, hP.2⟩
  refine Set.Infinite.mono (fun P hP ↦ ?_) (hS.sdiff hfin)
  exact ⟨hP.1, not_le.1 fun h ↦ hP.2 ⟨hP.1, h⟩⟩

/-- **The height gap below a threshold.** For a degree bound `n` and a height bound `B` there is
a positive `δ` such that an integer polynomial of degree at most `n` whose value at `ξ` is nonzero
and smaller than `δ` must have naive height above `B`. The polynomials of degree at most `n` and
height at most `B` are finitely many, and each of those that does not vanish at `ξ` keeps a
positive distance from `0` there. This is how a *root* approximating `ξ` forces its minimal
polynomial to be tall, without any appeal to the arithmetic of the approximation. -/
theorem exists_pos_lt_supNorm_of_abs_aeval_lt (ξ : ℝ) (n : ℕ) (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℤ[X], P.natDegree ≤ n → 0 < |aeval ξ P| → |aeval ξ P| < δ →
      B < P.supNorm := by
  classical
  set F : Set ℤ[X] := {P | (P.natDegree ≤ n ∧ P.supNorm ≤ B) ∧ aeval ξ P ≠ 0} with hF
  have hFfin : F.Finite := (finite_setOf_natDegree_le_supNorm_le n B).subset fun P hP ↦ hP.1
  have key : ∀ P : ℤ[X], P.natDegree ≤ n → 0 < |aeval ξ P| → P ∉ F → B < P.supNorm := by
    intro P hdeg hpos hPF
    by_contra hcon
    exact hPF ⟨⟨hdeg, not_lt.1 hcon⟩, fun h ↦ by rw [h] at hpos; simp at hpos⟩
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · exact ⟨1, one_pos, fun P hdeg hpos _ ↦ key P hdeg hpos (by rw [hFe]; exact fun h ↦ h)⟩
  · obtain ⟨P₀, hP₀F, hmin⟩ := Set.exists_min_image F (fun P ↦ |aeval ξ P|) hFfin hFne
    refine ⟨|aeval ξ P₀|, abs_pos.2 hP₀F.2, fun P hdeg hpos hlt ↦ key P hdeg hpos fun hPF ↦ ?_⟩
    exact absurd (hmin P hPF) (not_le.2 hlt)

/-- **The height gap for roots.** For a degree bound `n` and a height bound `B` there is a
positive `δ` such that an integer polynomial of degree at most `n` with a real root strictly
between `0` and `δ` away from `ξ` must have naive height above `B`. This is the companion of
`Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt` on the Koksma side: only finitely many integer
polynomials have degree at most `n` and height at most `B`, and between them they have only
finitely many real roots, so the ones that are not `ξ` keep a positive distance from it. -/
theorem exists_pos_lt_supNorm_of_abs_sub_root_lt (ξ : ℝ) (n : ℕ) (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Q : ℤ[X]) (α : ℝ), Q.natDegree ≤ n → Q ≠ 0 → aeval α Q = 0 →
      0 < |ξ - α| → |ξ - α| < δ → B < Q.supNorm := by
  classical
  have hroots : ∀ P : ℤ[X], P ≠ 0 → {α : ℝ | aeval α P = 0}.Finite := by
    intro P hP
    have hmap : P.map (algebraMap ℤ ℝ) ≠ 0 :=
      Polynomial.map_ne_zero_iff (algebraMap ℤ ℝ).injective_int |>.2 hP
    have hset : {α : ℝ | aeval α P = 0} = {α : ℝ | (P.map (algebraMap ℤ ℝ)).IsRoot α} := by
      ext α
      simp [Polynomial.IsRoot, aeval_def, eval_map]
    rw [hset]
    exact finite_setOfPred_isRoot hmap
  set G : Set ℝ :=
    {α : ℝ | (∃ P : ℤ[X], P.natDegree ≤ n ∧ P.supNorm ≤ B ∧ P ≠ 0 ∧ aeval α P = 0) ∧ α ≠ ξ}
    with hG
  have hGfin : G.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion
      (finite_setOf_natDegree_le_supNorm_le n B) (t := fun P ↦ {α : ℝ | aeval α P = 0 ∧ P ≠ 0})
      fun P _ ↦ ?_) ?_
    · rcases eq_or_ne P 0 with rfl | hP
      · simp
      · exact (hroots P hP).subset fun _ h ↦ h.1
    · rintro α ⟨⟨P, hdeg, hB, hP0, hval⟩, -⟩
      exact Set.mem_biUnion (⟨hdeg, hB⟩ : P ∈ {P : ℤ[X] | P.natDegree ≤ n ∧ P.supNorm ≤ B})
        ⟨hval, hP0⟩
  have key : ∀ δ : ℝ, (∀ α ∈ G, δ ≤ |ξ - α|) → ∀ (Q : ℤ[X]) (α : ℝ), Q.natDegree ≤ n → Q ≠ 0 →
      aeval α Q = 0 → 0 < |ξ - α| → |ξ - α| < δ → B < Q.supNorm := by
    intro δ hδ Q α hdeg hQ0 hval hpos hlt
    by_contra hcon
    have hαG : α ∈ G := ⟨⟨Q, hdeg, not_lt.1 hcon, hQ0, hval⟩, fun h ↦ by
      rw [h, sub_self, abs_zero] at hpos; exact absurd hpos (lt_irrefl 0)⟩
    exact absurd (hδ α hαG) (not_le.2 hlt)
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · exact ⟨1, one_pos, key 1 fun α hα ↦ absurd hα (by rw [hGe]; exact fun h ↦ h)⟩
  · obtain ⟨α₀, hα₀G, hmin⟩ := Set.exists_min_image G (fun α ↦ |ξ - α|) hGfin hGne
    refine ⟨|ξ - α₀|, ?_, key _ hmin⟩
    exact abs_pos.2 (sub_ne_zero.2 fun h ↦ hα₀G.2 h.symm)

theorem infinite_of_forall_exists_lt_supNorm {S : Set ℤ[X]}
    (h : ∀ B : ℝ, ∃ P ∈ S, B < P.supNorm) : S.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := exists_supNorm_le_of_finite hfin
  obtain ⟨P, hPS, hPB⟩ := h B
  exact absurd (hB P hPS) (not_le.2 hPB)

end Integer

end Polynomial

/-! ### Acceptance criteria -/

section Examples

open Polynomial

/-- The naive height is the largest absolute value of a coefficient. -/
example : (X - C 2 : ℤ[X]).supNorm = 2 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (X - C 2 : ℤ[X]).exists_eq_supNorm
    rw [hi]
    rcases i with _ | _ | i <;> simp [coeff_X, Int.norm_eq_abs]
  · have h0 : ((X - C 2 : ℤ[X]).coeff 0) = -2 := by simp
    have h := (X - C 2 : ℤ[X]).le_supNorm 0
    rw [h0, Int.norm_eq_abs] at h
    norm_num at h
    exact h

/-- Reversing the coefficients permutes them, so it leaves the naive height alone. -/
example (P : ℤ[X]) : (P.reflect 7).supNorm = P.supNorm := supNorm_reflect 7 P

/-- **Rejection test: integrality is what makes `1 ≤ H(P)`.** Over `ℚ` the naive height of a
nonzero polynomial can be as small as one likes, and with it the whole absorption argument of
Layer 1.2 collapses. -/
example : ¬ ∀ P : ℚ[X], P ≠ 0 → 1 ≤ P.supNorm := by
  intro h
  have h1 := h (C (1 / 2 : ℚ)) (by simp)
  rw [supNorm_C, ← Rat.norm_cast_real, Real.norm_eq_abs] at h1
  norm_num at h1

/-- **Rejection test: the degree bound in Northcott is load-bearing.** The powers of `X` all have
naive height `1`, so bounding the height alone leaves an infinite set. -/
example : ¬ {P : ℤ[X] | P.supNorm ≤ 1}.Finite := by
  intro h
  have hsub : Set.range (fun k : ℕ ↦ (X : ℤ[X]) ^ k) ⊆ {P : ℤ[X] | P.supNorm ≤ 1} := by
    rintro P ⟨k, rfl⟩
    change ((X : ℤ[X]) ^ k).supNorm ≤ 1
    rw [← monomial_one_right_eq_X_pow, supNorm_monomial]
    simp
  refine Set.infinite_range_of_injective (fun k l hkl ↦ ?_) (h.subset hsub)
  simpa using congrArg Polynomial.natDegree hkl

end Examples
