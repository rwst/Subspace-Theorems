/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantProduct

/-!
# Resultant forms in generic linear forms

The heights of a multiprojective variety (Rémond, LNM 1752, Ch. 7, §2.3) are those of its
resultant forms of index `(ε_{τ 1}, …, ε_{τ r})`, in generic linear forms `U_l` of the blocks
`τ l` (`MvPolynomial.linIndex`). Only the number of forms in each block matters.

For `n = deg H_I` generic linear forms with `β_i` of them in the block `i`, the iterated
differences `Δ_{ε_{τ 1}} ⋯ Δ_{ε_{τ n}} H_I` are the constant `∏_i β_i! [T^β] H_I`, the
multidegree `d_β(I)` (`MvPolynomial.diffPoly_linIndex_coeff_zero`). So by Prop. 3.4 the degree of
`res_{(δ, ε_{τ 1}, …, ε_{τ n})}(I)` in the coefficients of its first form is `d_β(I)`
(`MvPolynomial.exists_isWeightedHomogeneous_resForm_leftIndex_linIndex`).

## Main definitions

* `MvPolynomial.linIndex`: the index of generic linear forms in the blocks `τ l`.
* `MvPolynomial.formCount`: the number of forms in each block.
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Linear

variable {ι κ : Type*} [DecidableEq ι]

/-- The index `(ε_{τ l})_l` of generic linear forms `U_l` in the blocks `τ l`. -/
def linIndex (τ : κ → ι) : κ → ι → ℕ := fun l ↦ Pi.single (τ l) 1

/-- The number of `l ∈ s` with `τ l = i`, as a multidegree. -/
noncomputable def formCount (τ : κ → ι) (s : Finset κ) : ι →₀ ℕ :=
  ∑ l ∈ s, Finsupp.single (τ l) 1

theorem formCount_apply (τ : κ → ι) (s : Finset κ) (i : ι) :
    formCount τ s i = #{l ∈ s | τ l = i} := by
  classical
  simp [formCount, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole]

omit [DecidableEq ι] in
theorem degree_formCount (τ : κ → ι) (s : Finset κ) : (formCount τ s).degree = #s := by
  simp [formCount, map_sum, Finsupp.degree_single]

/-- **Iterated differences in linear directions**: for `deg P ≤ |β| + #s`,
`β! [T^β] Δ_{ε_{τ l}, l ∈ s} P = (β + γ)! [T^{β + γ}] P`, with `γ = formCount τ s`. -/
theorem prod_factorial_mul_coeff_diffPoly [Fintype ι] (τ : κ → ι) (s : Finset κ)
    (P : MvPolynomial ι ℚ) (β : ι →₀ ℕ) (hP : P.totalDegree ≤ β.degree + #s) :
    (∏ i, ((β i).factorial : ℚ)) * (diffPoly (linIndex τ) s P).coeff β =
      (∏ i, (((β + formCount τ s) i).factorial : ℚ)) * P.coeff (β + formCount τ s) := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty => simp [formCount]
  | insert a s ha ih =>
    rw [diffPoly_insert _ ha]
    set Q := P - shiftPoly (linIndex τ a) P
    have hQ : Q.totalDegree ≤ β.degree + #s := by
      have : Q.totalDegree ≤ P.totalDegree - 1 := totalDegree_sub_shiftPoly_le _ P
      rw [card_insert_of_notMem ha] at hP
      omega
    rw [ih Q hQ]
    have hdeg : P.totalDegree - 1 ≤ (β + formCount τ s).degree := by
      rw [map_add, degree_formCount]
      rw [card_insert_of_notMem ha] at hP
      omega
    have hcoeff : Q.coeff (β + formCount τ s) =
        P.coeff (β + formCount τ s + Finsupp.single (τ a) 1) *
          ((β + formCount τ s) (τ a) + 1) := by
      rw [coeff_sub_shiftPoly _ P hdeg, Finset.sum_eq_single (τ a)]
      · simp [linIndex]
      · intro i _ hi
        simp [linIndex, hi]
      · simp
    have hγ : β + formCount τ (insert a s) = β + formCount τ s + Finsupp.single (τ a) 1 := by
      rw [formCount, sum_insert ha, ← formCount]
      abel
    rw [hcoeff, hγ, prod_factorial_add_single]
    ring

/-- `Δ_{ε_{τ 1}} ⋯ Δ_{ε_{τ n}} H = ∏_i β_i! [T^β] H` for `deg H ≤ n`, with `β` the number of
forms in each block. -/
theorem diffPoly_linIndex_coeff_zero [Fintype ι] [Fintype κ] (τ : κ → ι) (P : MvPolynomial ι ℚ)
    (hP : P.totalDegree ≤ Fintype.card κ) :
    (diffPoly (linIndex τ) univ P).coeff 0 =
      (∏ i, ((formCount τ univ i).factorial : ℚ)) * P.coeff (formCount τ univ) := by
  have := prod_factorial_mul_coeff_diffPoly τ univ P 0 (by simpa using hP)
  simpa using this

end Linear

section Degree

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Fintype κ]

/-- **The degree of a resultant form in its first form** (Rémond, LNM 1752, Ch. 5, Prop. 3.4):
with the other forms linear, `β_i` of them in the block `i` and `|β| = deg H_I`,
`res_{(δ, ε_{τ 1}, …)}(I)` has degree `d_β(I)` in the coefficients of the first form. -/
theorem exists_isWeightedHomogeneous_resForm_leftIndex_linIndex (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) (τ : κ → ι)
    (hdim : (hilbertPoly b I).totalDegree ≤ Fintype.card κ) (δ : ι → ℕ) :
    ∃ D : ℕ, (D : ℚ) = multidegree b I (formCount τ univ) ∧
      IsWeightedHomogeneous (groupWeight b (leftIndex δ (linIndex τ)) none)
        (resForm b K (leftIndex δ (linIndex τ)) I) D := by
  classical
  obtain ⟨D, hD, hhom⟩ := exists_isWeightedHomogeneous_resForm (K := K)
    (d := leftIndex δ (linIndex τ)) hb none hI (by rw [Fintype.card_option]; omega)
  refine ⟨D, ?_, hhom⟩
  rw [hD, diffPoly_erase_none, multidegree]
  exact diffPoly_linIndex_coeff_zero τ _ hdim

end Degree

end MvPolynomial
