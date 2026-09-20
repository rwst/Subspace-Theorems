/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.BombieriVaalerRelative
public import ArithmeticHeights.MonomialIndex

/-!
# The auxiliary polynomial

This is the packaging of Siegel's lemma that transcendence and Diophantine-approximation
arguments import. Fix `r` variables and a degree bound `D`, so that a polynomial of total degree
at most `D` is a vector of

`M = (D + r).choose r`

coefficients; impose `N` linear conditions on those coefficients — typically that the polynomial
vanish to a prescribed order at prescribed algebraic points — as the rows of a matrix `A`. If
there are fewer *independent* conditions than coefficients, there is a nonzero such polynomial
satisfying all of them, of controlled height:

`H(P) ≤ |D_{K/ℚ}| ^ (1 / (2 d)) · (√M · H(A)) ^ (R / (M − R))`,

`H` absolute, `R = rank A`, `H(A)` the height of the entries of `A` and `d = [K : ℚ]`. In the
relative form the conditions have coefficients in a finite extension `F / K` of degree `s` while
the polynomial is required to have coefficients in `K`, and the feasibility hypothesis is
`s · R < M`.

⚠ The feasibility hypothesis is not decoration. One variable, `D = 0` and the single condition
"the constant coefficient vanishes" has `M = 1 = R` and no nonzero solution at all.

## Main results

* `MvPolynomial.exists_ne_zero_mem_ker_mulHeight_rpow_le`: the milestone, with the number of
  conditions entering only through `rank A`.
* `MvPolynomial.exists_ne_zero_mem_ker_mulHeight_rpow_le_of_lt`: the same under the hypothesis
  users actually check, `N < M`, at the cost of the weaker exponent `N / (M − N)`.
* `MvPolynomial.exists_linearIndependent_mem_ker_prod_mulHeight_rpow_le`: the basis form — a
  `K`-linearly independent family of such polynomials with a bound on the product of their
  heights.
* `MvPolynomial.exists_ne_zero_mem_ker_mulHeight_rpow_le_relative` and
  `MvPolynomial.exists_linearIndependent_mem_ker_prod_mulHeight_rpow_le_relative`: the same two
  statements when the conditions have coefficients in `F / K` and the polynomial is required to
  be defined over `K`.

## Implementation notes

⚠ **The count of conditions and the dimension of the coefficient space appear separately**, as
they do in Hindry–Silverman D.4: `N` is the number of rows of `A`, `M` is
`Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}`, and `Finsupp.card_subtype_degree_le` evaluates the
latter to `(D + r).choose r` only when a caller wants it. Downstream users vary the two
independently and a bound that has already combined them is unusable.

⚠ **The height bounded is Layer 2.1's height of the polynomial**, not the height of a coefficient
tuple on a chosen index set: `MvPolynomial.mulHeight P ^ (1/d)` is the absolute height of `P`, and
`MvPolynomial.absMulHeight_coeff_degreeLE` is what identifies it with the absolute height of the
vector Siegel's lemma produces. So `D` occurs in the hypotheses and not in the conclusion's
height.

⚠ **The linear order on the monomials is an artefact of the Plücker indexing** and appears in no
statement. Layers 5.4–5.6 need the columns of the matrix linearly ordered to index the maximal
minors; the monomials carry no canonical order, so the proofs below install an arbitrary
well-order exactly as `ArithmeticHeights/GaussLemma.lean` does. Nothing in the conclusion depends
on the choice, since the heights and the rank do not.

⚠ **`Fintype` on the monomials is noncomputable**, by `Finsupp.instFintypeSubtypeDegreeLE`, so
`Fintype.card` in these statements is the classical cardinality rather than the length of an
enumeration.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 2.9, and Chapter 4 for the auxiliary-polynomial use of Siegel's lemma. M. Hindry and
J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000), Section D.4.

This is Layer 5.7 of the `ArithmeticHeights` roadmap.
-/

public section

open Finsupp Matrix Module MvPolynomial NumberField Real

namespace MvPolynomial

/-!
### The absolute form: conditions and polynomial over the same field
-/

section Absolute

variable {K : Type*} [Field K] [NumberField K] {σ : Type*} [Finite σ] {N D : ℕ}

/-- **Layer 5.7 — the auxiliary polynomial.** `N` linear conditions on the coefficients of a
polynomial in the variables `σ` of total degree at most `D`, of rank `R` less than the number
`M` of such monomials, are satisfied by a nonzero polynomial with coefficients integral over `ℤ`
and

`H(P) ≤ |D| ^ (1 / (2 d)) · (√M · H(A)) ^ (R / (M − R))`,

`H` absolute throughout and `H(A)` the height of the *entries* of the condition matrix. This is
Layer 5.5 read on the coefficient space. -/
theorem exists_ne_zero_mem_ker_mulHeight_rpow_le
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} K)
    (hA : A.rank < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : MvPolynomial σ K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ P.coeff (m : σ →₀ ℕ)) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Real.sqrt (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) *
              A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹) ^
            ((A.rank : ℝ) / (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - A.rank)) := by
  classical
  let _ : LinearOrder {m : σ →₀ ℕ // m.degree ≤ D} := linearOrderOfSTO WellOrderingRel
  obtain ⟨x, hx0, hker, hint, hle⟩ := NumberField.exists_ne_zero_mem_ker_absMulHeight_le A hA
  have hcoeff : ∀ m : {m : σ →₀ ℕ // m.degree ≤ D},
      (ofDegreeLE D x).coeff (m : σ →₀ ℕ) = x m := coeff_ofDegreeLE x
  have hdeg : (ofDegreeLE D x).totalDegree ≤ D := totalDegree_ofDegreeLE_le x
  refine ⟨ofDegreeLE D x, fun h ↦ hx0 (ofDegreeLE_injective (h.trans (map_zero _).symm)), hdeg,
    ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m.degree ≤ D
    · exact hcoeff ⟨m, hm⟩ ▸ hint ⟨m, hm⟩
    · rw [coeff_ofDegreeLE_of_not_le x hm]
      exact isIntegral_zero
  · rw [show (fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ (ofDegreeLE D x).coeff (m : σ →₀ ℕ)) = x from
      funext hcoeff]
    exact hker
  · rw [← absMulHeight_coeff_degreeLE _ hdeg,
      show (fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ (ofDegreeLE D x).coeff (m : σ →₀ ℕ)) = x from
        funext hcoeff]
    exact hle

/-- **Layer 5.7 under the hypothesis users check.** Fewer conditions than coefficients is enough,
`rank A ≤ N` being automatic, and the exponent grows from `R / (M − R)` to `N / (M − N)` because
`x ↦ x / (M − x)` is increasing and the base is at least `1`. -/
theorem exists_ne_zero_mem_ker_mulHeight_rpow_le_of_lt
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} K)
    (hN : N < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : MvPolynomial σ K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ P.coeff (m : σ →₀ ℕ)) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Real.sqrt (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) *
              A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹) ^
            ((N : ℝ) / (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - N)) := by
  have hR : A.rank ≤ N := by simpa using A.rank_le_card_height
  obtain ⟨P, hP0, hPd, hPint, hPker, hPle⟩ :=
    exists_ne_zero_mem_ker_mulHeight_rpow_le A (lt_of_le_of_lt hR hN)
  refine ⟨P, hP0, hPd, hPint, hPker, hPle.trans (mul_le_mul_of_nonneg_left ?_
    (Real.rpow_nonneg (abs_nonneg _) _))⟩
  set M : ℕ := Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} with hM
  have hC : (1 : ℝ) ≤ Real.sqrt M * A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ := by
    have h1 : (1 : ℝ) ≤ Real.sqrt M := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega))
    have h2 : (1 : ℝ) ≤ A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ := by
      rw [show (1 : ℝ) = (1 : ℝ) ^ ((finrank ℚ K : ℝ))⁻¹ from (Real.one_rpow _).symm]
      exact Real.rpow_le_rpow zero_le_one (Matrix.one_le_mulHeight A) (by positivity)
    nlinarith
  refine Real.rpow_le_rpow_of_exponent_le hC ?_
  have hRN : (A.rank : ℝ) ≤ N := by exact_mod_cast hR
  have h1 : (0 : ℝ) < (M : ℝ) - A.rank := by
    have : (A.rank : ℝ) < M := by exact_mod_cast lt_of_le_of_lt hR hN
    linarith
  have h2 : (0 : ℝ) < (M : ℝ) - N := by
    have : (N : ℝ) < M := by exact_mod_cast hN
    linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- **Layer 5.7 — the basis form.** The polynomials of total degree at most `D` satisfying the
conditions form a `K`-space of dimension `k = M − rank A`, and it has a `K`-linearly independent
family of `k` members with integral coefficients and

`∏ₗ H(Pₗ) ≤ |D| ^ (k / (2 d)) · (√M · H(A)) ^ R`.

This is the statement an auxiliary construction that needs several independent polynomials
quotes. -/
theorem exists_linearIndependent_mem_ker_prod_mulHeight_rpow_le
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} K) {k : ℕ}
    (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ P : Fin k → MvPolynomial σ K, LinearIndependent K P ∧
      (∀ l, (P l).totalDegree ≤ D) ∧ (∀ l m, IsIntegral ℤ ((P l).coeff m)) ∧
      (∀ l, A.mulVec (fun m ↦ (P l).coeff (m : σ →₀ ℕ)) = 0) ∧
      ∏ l, (P l).mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) *
          (Real.sqrt (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) *
              A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹) ^ A.rank := by
  classical
  let _ : LinearOrder {m : σ →₀ ℕ // m.degree ≤ D} := linearOrderOfSTO WellOrderingRel
  have : Nonempty {m : σ →₀ ℕ // m.degree ≤ D} := ⟨⟨0, by simp⟩⟩
  obtain ⟨b, hint, hle⟩ := NumberField.exists_basis_ker_prod_absMulHeight_le_entries A hk
  refine ⟨fun l ↦ ofDegreeLE D (fun m ↦ (b l : {m : σ →₀ ℕ // m.degree ≤ D} → K) m), ?_,
    fun l ↦ totalDegree_ofDegreeLE_le _, ?_, ?_, ?_⟩
  · exact (b.linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _)).map' (ofDegreeLE D)
        (LinearMap.ker_eq_bot.2 ofDegreeLE_injective)
  · intro l m
    by_cases hm : m.degree ≤ D
    · rw [coeff_ofDegreeLE _ ⟨m, hm⟩]
      exact hint l ⟨m, hm⟩
    · rw [coeff_ofDegreeLE_of_not_le _ hm]
      exact isIntegral_zero
  · intro l
    rw [funext (coeff_ofDegreeLE (fun m ↦ (b l : {m : σ →₀ ℕ // m.degree ≤ D} → K) m))]
    exact (LinearMap.mem_ker.1 (b l).2)
  · refine le_trans (le_of_eq (Finset.prod_congr rfl fun l _ ↦ ?_)) hle
    rw [← absMulHeight_coeff_degreeLE _ (totalDegree_ofDegreeLE_le _),
      funext (coeff_ofDegreeLE (fun m ↦ (b l : {m : σ →₀ ℕ // m.degree ≤ D} → K) m))]

end Absolute

/-!
### The relative form: conditions over `F`, polynomial over `K`
-/

section Relative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
  {σ : Type*} [Finite σ] {N D : ℕ}

/-- **Layer 5.7 — the relative auxiliary polynomial** (the form transcendence arguments use when
the auxiliary construction and the field of definition differ). The conditions have coefficients
in a finite extension `F / K` of degree `s` and the polynomial is required to be defined over `K`;
the feasibility hypothesis is `s · rank A < M` and the bound is

`H(P) ≤ |D| ^ (1 / (2 d)) · (∏ᵢ H_Ar(Aᵢ) ^ s) ^ (1 / (M − s R))`,

`H_Ar(Aᵢ)` the absolute Arakelov height of the `i`-th condition, a vector over `F`. -/
theorem exists_ne_zero_mem_ker_mulHeight_rpow_le_relative
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} F)
    (hA : finrank K F * A.rank < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : MvPolynomial σ K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ algebraMap K F (P.coeff (m : σ →₀ ℕ))) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (∏ i, (NumberField.arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F) ^
            ((Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - finrank K F * A.rank : ℝ))⁻¹ := by
  classical
  let _ : LinearOrder {m : σ →₀ ℕ // m.degree ≤ D} := linearOrderOfSTO WellOrderingRel
  obtain ⟨x, hx0, hker, hint, hle⟩ :=
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le_relative_rank (K := K) A hA
  have hcoeff : ∀ m : {m : σ →₀ ℕ // m.degree ≤ D},
      (ofDegreeLE D x).coeff (m : σ →₀ ℕ) = x m := coeff_ofDegreeLE x
  have hfun : (fun m : {m : σ →₀ ℕ // m.degree ≤ D} ↦ (ofDegreeLE D x).coeff (m : σ →₀ ℕ)) = x :=
    funext hcoeff
  have hdeg : (ofDegreeLE D x).totalDegree ≤ D := totalDegree_ofDegreeLE_le x
  refine ⟨ofDegreeLE D x, fun h ↦ hx0 (ofDegreeLE_injective (h.trans (map_zero _).symm)), hdeg,
    ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m.degree ≤ D
    · exact hcoeff ⟨m, hm⟩ ▸ hint ⟨m, hm⟩
    · rw [coeff_ofDegreeLE_of_not_le x hm]
      exact isIntegral_zero
  · simpa only [hcoeff] using hker
  · rw [← absMulHeight_coeff_degreeLE _ hdeg, hfun]
    exact hle

/-- **Layer 5.7 — the relative basis form.** `M − s · rank A` polynomials over `K`, linearly
independent, of total degree at most `D`, satisfying all the conditions, with

`∏ₗ H(Pₗ) ≤ |D| ^ ((M − s R) / (2 d)) · ∏ᵢ H_Ar(Aᵢ) ^ s`. -/
theorem exists_linearIndependent_mem_ker_prod_mulHeight_rpow_le_relative
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} F)
    (hA : finrank K F * A.rank < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : Fin (Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - finrank K F * A.rank) →
        MvPolynomial σ K,
      LinearIndependent K P ∧ (∀ l, (P l).totalDegree ≤ D) ∧
      (∀ l m, IsIntegral ℤ ((P l).coeff m)) ∧
      (∀ l, A.mulVec (fun m ↦ algebraMap K F ((P l).coeff (m : σ →₀ ℕ))) = 0) ∧
      ∏ l, (P l).mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^
            ((Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - finrank K F * A.rank : ℝ) /
              (2 * finrank ℚ K)) *
          ∏ i, (NumberField.arakelovMulHeight (A i) ^ ((finrank ℚ F : ℝ))⁻¹) ^ finrank K F := by
  classical
  let _ : LinearOrder {m : σ →₀ ℕ // m.degree ≤ D} := linearOrderOfSTO WellOrderingRel
  obtain ⟨x, hxind, hker, hint, hle⟩ :=
    NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le_rank (K := K) A hA
  refine ⟨fun l ↦ ofDegreeLE D (x l),
    hxind.map' (ofDegreeLE D) (LinearMap.ker_eq_bot.2 ofDegreeLE_injective),
    fun l ↦ totalDegree_ofDegreeLE_le _, ?_, ?_, ?_⟩
  · intro l m
    by_cases hm : m.degree ≤ D
    · rw [coeff_ofDegreeLE _ ⟨m, hm⟩]
      exact hint l ⟨m, hm⟩
    · rw [coeff_ofDegreeLE_of_not_le _ hm]
      exact isIntegral_zero
  · intro l
    simpa only [coeff_ofDegreeLE] using hker l
  · refine le_trans (le_of_eq (Finset.prod_congr rfl fun l _ ↦ ?_)) hle
    rw [← absMulHeight_coeff_degreeLE _ (totalDegree_ofDegreeLE_le _),
      funext (coeff_ofDegreeLE (x l))]

end Relative

end MvPolynomial

/-!
### Examples

The acceptance tests of Layer 5.7: the coefficient space has the dimension stars and bars says it
has, the milestone reads as the roadmap displays it once that dimension is substituted, and the
relative form at `F = K` is the absolute one.
-/

section Examples

open Matrix Module MvPolynomial NumberField

/-- **Acceptance test: the dimension of the coefficient space.** In one variable with `D = 0`
there is exactly one monomial, which is why that is the shape of the counterexample to dropping
the feasibility hypothesis. -/
example : Fintype.card {m : Fin 1 →₀ ℕ // m.degree ≤ 0} = 1 := by
  rw [Finsupp.card_subtype_degree_le_fin]
  rfl

/-- **Acceptance test: the milestone in the roadmap's notation.** With `r` variables and degree
bound `D` the coefficient space has dimension `M = (D + r).choose r`, and the bound reads
`H(P) ≤ |D_K| ^ (1 / (2 d)) · (√M · H(A)) ^ (R / (M − R))`. A development in which the monomials
of degree at most `D` had been miscounted produces a different statement here. -/
example {K : Type*} [Field K] [NumberField K] {r N D : ℕ}
    (A : Matrix (Fin N) {m : Fin r →₀ ℕ // m.degree ≤ D} K)
    (hA : A.rank < (D + r).choose r) :
    ∃ P : MvPolynomial (Fin r) K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ P.coeff (m : Fin r →₀ ℕ)) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Real.sqrt ((D + r).choose r) * A.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹) ^
            ((A.rank : ℝ) / ((D + r).choose r - A.rank)) := by
  rw [← Finsupp.card_subtype_degree_le_fin r D] at hA ⊢
  exact exists_ne_zero_mem_ker_mulHeight_rpow_le A hA

/-- **Conformance: the relative form at `F = K` is the absolute one**, with the Arakelov height
of the rows in place of `√M` times the height of the entries. A miscounted degree `s` produces a
different exponent here. -/
example {K : Type*} [Field K] [NumberField K] {σ : Type*} [Finite σ] {N D : ℕ}
    (A : Matrix (Fin N) {m : σ →₀ ℕ // m.degree ≤ D} K)
    (hA : A.rank < Fintype.card {m : σ →₀ ℕ // m.degree ≤ D}) :
    ∃ P : MvPolynomial σ K, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      (∀ m, IsIntegral ℤ (P.coeff m)) ∧
      A.mulVec (fun m ↦ P.coeff (m : σ →₀ ℕ)) = 0 ∧
      P.mulHeight ^ ((finrank ℚ K : ℝ))⁻¹ ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (∏ i, NumberField.arakelovMulHeight (A i) ^ ((finrank ℚ K : ℝ))⁻¹) ^
            ((Fintype.card {m : σ →₀ ℕ // m.degree ≤ D} - A.rank : ℝ))⁻¹ := by
  have hr : finrank K K = 1 := Module.finrank_self K
  have h := exists_ne_zero_mem_ker_mulHeight_rpow_le_relative (K := K) (F := K) A
    (by rw [hr, one_mul]; exact hA)
  simpa only [hr, Nat.cast_one, one_mul, pow_one, Algebra.algebraMap_self,
    RingHom.id_apply] using h

end Examples

end
