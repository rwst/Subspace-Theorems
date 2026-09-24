/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FormIndex
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Specializing a block of variables to two coordinates

The first half of the proof of the generalized Roth lemma (Bombieri–Gubler, Lemma 7.5.19). A
multihomogeneous polynomial in `m` blocks of `n + 1` variables has to be turned into a
polynomial in `m` variables, so that Layer 2.7 can be applied to it, and this has to be done
**without raising its height** and **without lowering its index** along the forms.

Both are achieved by specializing, in every block, all variables but two to `0` — one at a time,
after dividing out the largest power of the variable being killed. Dividing and specializing is
one operation on coefficients: the result has a subfamily of the coefficients of the original,
so its height cannot go up. The index does not go down because the whole procedure is a
monomial-by-monomial condition in the transformed coordinates, where the forms have become
variables. What is left, a multihomogeneous polynomial in two variables per block, is
dehomogenized to one variable per block by setting the second kept coordinate to `1`.

## Main definitions

* `MvPolynomial.evalZeroAt`: the substitution setting one variable to `0`.
* `MvPolynomial.zeroAt` and `MvPolynomial.zeroOut`: the forms with the coefficients at one
  variable, or at a set of variables, set to `0`.
* `MvPolynomial.deHom`: the dehomogenization `X (h, i₀ h) ↦ X h`, `X (h, i₁ h) ↦ 1`, everything
  else `↦ 0`, and `MvPolynomial.blockProj` the exponent it induces.

## Main results

* `MvPolynomial.coeff_evalZeroAt`: the coefficients of a specialization, and
  `MvPolynomial.evalZeroAt_eq_self_iff`, which says that a polynomial is fixed by it exactly
  when it does not involve the variable.
* `MvPolynomial.evalZeroAt_substFormInv`: **setting a variable to zero commutes with the change
  of coordinates**, after the coefficient of the forms at that variable has been set to zero.
* `MvPolynomial.exists_layer`: one step of the specialization, and
  `MvPolynomial.exists_elimination`: **the specialization to two coordinates in every block**.
* `MvPolynomial.deHom_monomial` and `MvPolynomial.deHom_coeff_correspondence`: the
  dehomogenization is a bijection on the monomials of a multihomogeneous polynomial that
  involves only the two kept coordinates.
* `MvPolynomial.formIndex_eq_index_deHom`: **the index along the forms is the index of Layer 2.3
  after dehomogenization** — Bombieri–Gubler 7.5.18, in the generality Lemma 7.5.19 needs.

## Implementation notes

⚠ **Dividing out and specializing is Mathlib's division by a monomial.** `MvPolynomial.divMonomial`
shifts the coefficients, `MvPolynomial.modMonomial` vanishes exactly when the monomial divides,
and the composite "divide by `X t ^ k`, then set `X t = 0`" reads off the coefficients of the
original at the exponents whose `t`-component is exactly `k`. No polynomial division has to be
written and the height statement is immediate from the coefficient formula.

⚠ **The variables have to be eliminated one at a time.** Taking the componentwise minimum of the
exponents and slicing once does not work: `X 1 + X 2` has no monomial in which both exponents
are minimal, and the slice would be `0`. Killing one variable at a time always leaves something,
because the minimum of a single exponent is attained. The composite of the steps *is* a single
slice, but at an exponent that no direct formula produces.

⚠ **The forms must be truncated as the variables are dropped.** `evalZeroAt_substFormInv` says
`evalZeroAt t ∘ substFormInv i₀ M = substFormInv i₀ (zeroAt t M) ∘ evalZeroAt t`: the
specialization commutes with the change of coordinates only after the coefficient of the form at
`t` has been set to `0` as well. Keeping the untruncated forms gives an inequality in the wrong
direction, and this is the one place in Layer 5.3 where the argument could silently break.

⚠ **Only one half of the book's claim is proved, and it is the half that is needed.**
Bombieri–Gubler assert that the specialization leaves the index unchanged, which is true and
needs the uniqueness of the decomposition of a polynomial in powers of the forms. What
`exists_elimination` gives is that the index does not *decrease*, which is all Lemma 7.5.19
consumes and which needs nothing beyond the monomial-by-monomial description of the ideal.

⚠ **Normalizing `M h (i₀ h)` to `1` removes a scaling of the variables.** Without it,
dehomogenization intertwines the inverse change of coordinates with a translation *composed
with* the diagonal scaling `X h ↦ (M h (i₀ h))⁻¹ X h`; the scaling does not move any support and
so does not move the order, but it has to be written down and carried. The normalization costs
nothing, because `MvPolynomial.formIndex_smul` says the index does not see it and the projective
height of a form does not either.

⚠ **Dehomogenization is injective on multihomogeneous polynomials, and that is the point.** A
monomial of multidegree `r` in two variables per block is determined by the exponent of one of
them, so `blockProj` is injective on the support and the coefficients of the dehomogenization
are the coefficients of the polynomial, not sums of them. Multihomogeneity is not decoration
here: in one block with variables `x₀`, `x₁` and the form `M = x₁`, the polynomial
`x₁ + x₀ ^ 2 - x₀` is not divisible by `M`, so its index along `M` is `0`, while its
dehomogenization at `x₀ = 1` is `t`, whose index at `0` is `1`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.18 and the proof of Lemma 7.5.19.

This is Layer 5.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset

open scoped ENNReal

namespace MvPolynomial

/-! ### Setting one variable to zero -/

section EvalZeroAt

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- The substitution that sets the variable `t` to `0` and leaves every other variable alone. -/
def evalZeroAt (t : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun s ↦ if s = t then 0 else X s

theorem coeff_evalZeroAt (t : σ) (P : MvPolynomial σ R) (ν : σ →₀ ℕ) :
    (evalZeroAt t P).coeff ν = if ν t = 0 then P.coeff ν else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial μ a =>
      by_cases hμ : μ t = 0
      · have hprod : (μ.prod fun s k ↦ (if s = t then (0 : MvPolynomial σ R) else X s) ^ k)
            = μ.prod fun s k ↦ X s ^ k :=
          Finset.prod_congr rfl fun s hs ↦ by
            have hst : s ≠ t := fun hc ↦ (Finsupp.mem_support_iff.mp hs) (hc ▸ hμ)
            simp [hst]
        have hev : evalZeroAt t (monomial μ a) = monomial μ a := by
          rw [evalZeroAt, aeval_monomial, hprod, MvPolynomial.algebraMap_eq, ← monomial_eq]
        rw [hev]
        split_ifs with hν
        · rfl
        · have hne : μ ≠ ν := fun hc ↦ hν (hc ▸ hμ)
          simp [MvPolynomial.coeff_monomial, hne]
      · have hts : t ∈ μ.support := Finsupp.mem_support_iff.mpr hμ
        have hev : evalZeroAt t (monomial μ a) = 0 := by
          rw [evalZeroAt, aeval_monomial]
          have hz : (μ.prod fun s k ↦ (if s = t then (0 : MvPolynomial σ R) else X s) ^ k) = 0 := by
            rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hts]
            simp [hμ]
          rw [hz, mul_zero]
        rw [hev]
        split_ifs with hν
        · have hne : μ ≠ ν := fun hc ↦ hμ (hc ▸ hν)
          simp [MvPolynomial.coeff_monomial, hne]
        · simp
  | add p q hp hq =>
      have hsum : ((evalZeroAt t p + evalZeroAt t q).coeff ν)
          = (evalZeroAt t p).coeff ν + (evalZeroAt t q).coeff ν := by simp
      have hpq : ((p + q).coeff ν) = p.coeff ν + q.coeff ν := by simp
      rw [map_add, hsum, hp, hq, hpq]
      split_ifs <;> simp

theorem coeff_evalZeroAt_ne_zero {t : σ} {P : MvPolynomial σ R} {ν : σ →₀ ℕ}
    (h : (evalZeroAt t P).coeff ν ≠ 0) : ν t = 0 ∧ P.coeff ν ≠ 0 := by
  rw [coeff_evalZeroAt] at h
  by_cases hν : ν t = 0
  · exact ⟨hν, by rwa [ite_eq_left hν] at h⟩
  · exact absurd (ite_eq_right hν) h

theorem weightedOrder_le_weightedOrder_evalZeroAt (w : σ → ℝ≥0∞) (t : σ)
    (P : MvPolynomial σ R) :
    weightedOrder w P ≤ weightedOrder w (evalZeroAt t P) :=
  le_weightedOrder fun _ hν ↦
    weightedOrder_le_of_coeff_ne_zero (coeff_evalZeroAt_ne_zero hν).2

end EvalZeroAt

/-! ### The commutation with the change of coordinates -/

section Commute

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem evalZeroAt_X_self {σ R : Type*} [CommRing R] [DecidableEq σ] (t : σ) :
    evalZeroAt t (X t : MvPolynomial σ R) = 0 := by simp [evalZeroAt]

omit [Fintype ι] [DecidableEq ι] in
theorem evalZeroAt_X_of_ne {σ R : Type*} [CommRing R] [DecidableEq σ] {s t : σ} (h : s ≠ t) :
    evalZeroAt t (X s : MvPolynomial σ R) = X s := by simp [evalZeroAt, h]

/-- The forms `M` with the coefficient at the variable `t` set to zero. -/
def zeroAt (t : κ × ι) (M : κ → ι → K) : κ → ι → K :=
  fun h i ↦ if (h, i) = t then 0 else M h i

omit [Fintype ι] in
theorem zeroAt_apply_of_ne {t : κ × ι} (M : κ → ι → K) {h : κ} {i : ι}
    (hc : ((h, i) : κ × ι) ≠ t) : zeroAt t M h i = M h i := by simp [zeroAt, hc]

/-- **Setting a variable to zero commutes with the inverse change of coordinates**, provided the
form is also truncated at that variable. -/
theorem evalZeroAt_substFormInv {i₀ : κ → ι} (M : κ → ι → K) {t : κ × ι} (ht : t.2 ≠ i₀ t.1)
    (P : MvPolynomial (κ × ι) K) :
    evalZeroAt t (substFormInv i₀ M P) = substFormInv i₀ (zeroAt t M) (evalZeroAt t P) := by
  have key : (evalZeroAt t).comp (substFormInv i₀ M)
      = (substFormInv i₀ (zeroAt t M)).comp (evalZeroAt t) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, i⟩ := p
    have hne : ((h, i₀ h) : κ × ι) ≠ t := fun hc ↦ ht (by rw [← hc])
    simp only [AlgHom.comp_apply]
    by_cases hi : i = i₀ h
    · subst hi
      have hsum : ∑ i' ∈ univ.erase (i₀ h), evalZeroAt t (C (M h i') * X ((h, i') : κ × ι))
          = ∑ i' ∈ univ.erase (i₀ h), C (zeroAt t M h i') * X ((h, i') : κ × ι) := by
        refine Finset.sum_congr rfl fun i' _ ↦ ?_
        rw [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
        by_cases hc : ((h, i') : κ × ι) = t
        · rw [hc, evalZeroAt_X_self, mul_zero, zeroAt]
          simp [← hc]
        · rw [evalZeroAt_X_of_ne hc, zeroAt_apply_of_ne M hc]
      rw [evalZeroAt_X_of_ne hne, substFormInv_X_self, substFormInv_X_self,
        zeroAt_apply_of_ne M hne, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        map_sub, evalZeroAt_X_of_ne hne, map_sum, hsum]
    · rw [substFormInv_X_of_ne i₀ M hi]
      by_cases hc : ((h, i) : κ × ι) = t
      · rw [hc, evalZeroAt_X_self, map_zero]
      · rw [evalZeroAt_X_of_ne hc, substFormInv_X_of_ne i₀ _ hi]
  exact congrArg (fun f ↦ f P) key

end Commute

/-! ### Eliminating one variable -/

section Elim

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **One step of the specialization.** Divide `P` by the largest power of the variable `t`
dividing it and then set `t` to zero. The result is nonzero, its coefficients are coefficients
of `P`, it is multihomogeneous of a smaller multidegree, and its index along the truncated forms
is at least the index of `P`. -/
theorem exists_layer {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {i₀ : κ → ι} {M : κ → ι → K}
    (hM : ∀ h, M h (i₀ h) ≠ 0) {t : κ × ι} (ht : t.2 ≠ i₀ t.1)
    {r : κ → ℕ} {P : MvPolynomial (κ × ι) K} (hP0 : P ≠ 0) (hP : IsMultiHomogeneous r P) :
    ∃ (e : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) K), (∀ s, s ≠ t → e s = 0) ∧ Q ≠ 0 ∧
      (∀ ν, Q.coeff ν ≠ 0 → Q.coeff ν = P.coeff (ν + e)) ∧
      (∀ ν ∈ Q.support, ν t = 0) ∧
      (∃ r' : κ → ℕ, (∀ h, r' h ≤ r h) ∧ IsMultiHomogeneous r' Q) ∧
      formIndex d M P ≤ formIndex d (zeroAt t M) Q := by
  classical
  obtain ⟨t₁, t₂⟩ := t
  have hsupp : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun hc ↦ hP0 (support_eq_empty.mp hc)
  have hSne : (P.support.image fun ν ↦ ν ((t₁, t₂) : κ × ι)).Nonempty := hsupp.image _
  set k := (P.support.image fun ν ↦ ν ((t₁, t₂) : κ × ι)).min' hSne with hkdef
  have hkle : ∀ ν ∈ P.support, k ≤ ν ((t₁, t₂) : κ × ι) := fun ν hν ↦
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hν)
  obtain ⟨ν₀, hν₀, hν₀t⟩ : ∃ ν₀ ∈ P.support, ν₀ ((t₁, t₂) : κ × ι) = k :=
    Finset.mem_image.mp (Finset.min'_mem _ hSne)
  set e : κ × ι →₀ ℕ := Finsupp.single ((t₁, t₂) : κ × ι) k with hedef
  have hezero : ∀ s, s ≠ ((t₁, t₂) : κ × ι) → e s = 0 := fun s hs ↦ by
    rw [hedef, Finsupp.single_apply, ite_eq_right (Ne.symm hs)]
  have hele : ∀ ν ∈ P.support, e ≤ ν := by
    intro ν hν s
    rcases eq_or_ne s ((t₁, t₂) : κ × ι) with rfl | hs
    · rw [hedef, Finsupp.single_eq_same]
      exact hkle ν hν
    · rw [hezero s hs]
      exact Nat.zero_le _
  have hmod : modMonomial P e = 0 := by
    ext ν
    by_cases hle : e ≤ ν
    · rw [coeff_modMonomial_of_le _ hle]
      simp
    · rw [coeff_modMonomial_of_not_le _ hle]
      have hns : ν ∉ P.support := fun hc ↦ hle (hele ν hc)
      simp [notMem_support_iff.mp hns]
  have hPR : monomial e 1 * divMonomial P e = P := by
    have h := divMonomial_add_modMonomial P e
    rwa [hmod, add_zero] at h
  set R := divMonomial P e with hRdef
  have hcoeffR : ∀ ν, R.coeff ν = P.coeff (ν + e) := fun ν ↦ by
    rw [hRdef, coeff_divMonomial, add_comm]
  set Q := evalZeroAt ((t₁, t₂) : κ × ι) R with hQdef
  have hcoeffQ : ∀ ν, Q.coeff ν ≠ 0 → Q.coeff ν = P.coeff (ν + e) := by
    intro ν hν
    rw [hQdef, coeff_evalZeroAt, ite_eq_left (coeff_evalZeroAt_ne_zero (by rwa [← hQdef])).1,
      hcoeffR]
  have hsuppQ : ∀ ν ∈ Q.support, ν ((t₁, t₂) : κ × ι) = 0 := fun ν hν ↦
    (coeff_evalZeroAt_ne_zero (by rw [← hQdef]; exact mem_support_iff.mp hν)).1
  have hQ0 : Q ≠ 0 := by
    have hle0 : e ≤ ν₀ := hele ν₀ hν₀
    refine fun hc ↦ (mem_support_iff.mp hν₀) ?_
    have hcq : Q.coeff (ν₀ - e) = 0 := by rw [hc]; simp
    rw [hQdef, coeff_evalZeroAt] at hcq
    have hz : (ν₀ - e) ((t₁, t₂) : κ × ι) = 0 := by
      have : e ((t₁, t₂) : κ × ι) = k := by rw [hedef, Finsupp.single_eq_same]
      simp [Finsupp.tsub_apply, this, hν₀t]
    rw [ite_eq_left hz, hcoeffR, tsub_add_cancel_of_le hle0] at hcq
    exact hcq
  refine ⟨e, Q, hezero, hQ0, hcoeffQ, hsuppQ,
    ⟨fun h ↦ r h - ∑ i, e (h, i), fun h ↦ Nat.sub_le _ _, ?_⟩, ?_⟩
  · intro ν hν h
    have hPc : P.coeff (ν + e) ≠ 0 := by rw [← hcoeffQ ν hν]; exact hν
    have hr := hP hPc h
    have hsplit : ∑ i, (ν + e) (h, i) = (∑ i, ν (h, i)) + ∑ i, e (h, i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by simp
    change ∑ i, ν (h, i) = r h - ∑ i, e (h, i)
    omega
  · have hne : ((t₁, i₀ t₁) : κ × ι) ≠ (t₁, t₂) := fun hc ↦ ht (congrArg Prod.snd hc).symm
    have hM' : ∀ h, zeroAt ((t₁, t₂) : κ × ι) M h (i₀ h) ≠ 0 := by
      intro h
      rw [zeroAt_apply_of_ne M (fun hc ↦ ht (by rw [← hc]))]
      exact hM h
    have hw : formWeight i₀ d ((t₁, t₂) : κ × ι) = 0 := by simp [formWeight, ht]
    have hXt : substFormInv i₀ M (X ((t₁, t₂) : κ × ι)) = X (t₁, t₂) :=
      substFormInv_X_of_ne i₀ M ht
    have hmone : substFormInv i₀ M (monomial e 1) = monomial e 1 := by
      rw [hedef, ← X_pow_eq_monomial, map_pow, hXt]
    have hsubP : substFormInv i₀ M P = monomial e 1 * substFormInv i₀ M R := by
      rw [← hPR, map_mul, hmone]
    have hweight : Finsupp.weight (formWeight i₀ d) e = 0 := by
      rw [hedef, Finsupp.weight_apply, Finsupp.sum_single_index (by simp), hw, smul_zero]
    rw [formIndex_eq_weightedOrder hd hM, formIndex_eq_weightedOrder hd hM', hsubP,
      weightedOrder_mul (formWeight_ne_top i₀ d), weightedOrder_monomial one_ne_zero, hweight,
      zero_add, hQdef, ← evalZeroAt_substFormInv M ht]
    exact weightedOrder_le_weightedOrder_evalZeroAt _ _ _

end Elim

/-! ### Eliminating a set of variables -/

section ElimSet

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The forms `M` with the coefficients at the variables of `T` set to zero. -/
def zeroOut (T : Finset (κ × ι)) (M : κ → ι → K) : κ → ι → K :=
  fun h i ↦ if (h, i) ∈ T then 0 else M h i

omit [Fintype ι] [Fintype κ] in
@[simp]
theorem zeroOut_empty (M : κ → ι → K) : zeroOut ∅ M = M := by
  funext h i
  simp [zeroOut]

omit [Fintype ι] [Fintype κ] in
theorem zeroOut_zeroAt (t : κ × ι) (T : Finset (κ × ι)) (M : κ → ι → K) :
    zeroOut T (zeroAt t M) = zeroOut (insert t T) M := by
  funext h i
  simp only [zeroOut, zeroAt, Finset.mem_insert]
  split_ifs <;> tauto

omit [Fintype ι] [Fintype κ] in
theorem zeroOut_apply_of_mem {T : Finset (κ × ι)} (M : κ → ι → K) {h : κ} {i : ι}
    (hc : ((h, i) : κ × ι) ∈ T) : zeroOut T M h i = 0 := by simp [zeroOut, hc]

omit [Fintype ι] [Fintype κ] in
theorem zeroOut_apply_of_notMem {T : Finset (κ × ι)} (M : κ → ι → K) {h : κ} {i : ι}
    (hc : ((h, i) : κ × ι) ∉ T) : zeroOut T M h i = M h i := by simp [zeroOut, hc]

/-- **The specialization to two coordinates in every block.** Eliminating the variables of `T`
one at a time produces a nonzero polynomial whose coefficients are coefficients of `P`, which
does not involve any variable of `T`, which is multihomogeneous of a smaller multidegree, and
whose index along the truncated forms is at least the index of `P`. -/
theorem exists_elimination {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {i₀ : κ → ι} (T : Finset (κ × ι)) :
    (∀ t ∈ T, t.2 ≠ i₀ t.1) → ∀ (M : κ → ι → K), (∀ h, M h (i₀ h) ≠ 0) →
      ∀ (r : κ → ℕ) (P : MvPolynomial (κ × ι) K), P ≠ 0 → IsMultiHomogeneous r P →
      ∃ (k : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) K),
        (∀ s, s ∉ T → k s = 0) ∧ Q ≠ 0 ∧
        (∀ ν, Q.coeff ν ≠ 0 → Q.coeff ν = P.coeff (ν + k)) ∧
        (∀ t ∈ T, ∀ ν ∈ Q.support, ν t = 0) ∧
        (∃ r' : κ → ℕ, (∀ h, r' h ≤ r h) ∧ IsMultiHomogeneous r' Q) ∧
        formIndex d M P ≤ formIndex d (zeroOut T M) Q := by
  classical
  induction T using Finset.induction with
  | empty =>
      intro _ M _ r P hP0 hP
      refine ⟨0, P, fun s _ ↦ rfl, hP0, fun ν _ ↦ by simp, fun t ht ↦ absurd ht (by simp),
        ⟨r, fun _ ↦ le_rfl, hP⟩, ?_⟩
      rw [zeroOut_empty]
  | insert t T htT ih =>
      intro hT M hM r P hP0 hP
      have htne : t.2 ≠ i₀ t.1 := hT t (Finset.mem_insert_self t T)
      obtain ⟨e, P₁, hezero, hP₁0, hP₁coeff, hP₁supp, ⟨r₁, hr₁, hP₁⟩, hP₁idx⟩ :=
        exists_layer hd hM htne hP0 hP
      have hM₁ : ∀ h, zeroAt t M h (i₀ h) ≠ 0 := by
        intro h
        rw [zeroAt_apply_of_ne M (fun hc ↦ htne (by rw [← hc]))]
        exact hM h
      obtain ⟨k, Q, hkzero, hQ0, hQcoeff, hQsupp, ⟨r₂, hr₂, hQ⟩, hQidx⟩ :=
        ih (fun t' ht' ↦ hT t' (Finset.mem_insert_of_mem ht')) (zeroAt t M) hM₁ r₁ P₁ hP₁0 hP₁
      have hkt : k t = 0 := hkzero t htT
      have hQt : ∀ ν, Q.coeff ν ≠ 0 → ν t = 0 := by
        intro ν hν
        have h1 : P₁.coeff (ν + k) ≠ 0 := by rw [← hQcoeff ν hν]; exact hν
        have h2 := hP₁supp (ν + k) (mem_support_iff.mpr h1)
        simpa [hkt] using h2
      refine ⟨k + e, Q, ?_, hQ0, ?_, ?_, ⟨r₂, fun h ↦ (hr₂ h).trans (hr₁ h), hQ⟩, ?_⟩
      · intro s hs
        rw [Finset.mem_insert] at hs
        push Not at hs
        simp [hkzero s hs.2, hezero s hs.1]
      · intro ν hν
        have h1 : P₁.coeff (ν + k) ≠ 0 := by rw [← hQcoeff ν hν]; exact hν
        rw [hQcoeff ν hν, hP₁coeff (ν + k) h1, add_assoc]
      · intro t' ht' ν hν
        rw [Finset.mem_insert] at ht'
        rcases ht' with rfl | ht'
        · exact hQt ν (mem_support_iff.mp hν)
        · exact hQsupp t' ht' ν hν
      · rw [← zeroOut_zeroAt]
        exact le_trans hP₁idx hQidx

end ElimSet

/-! ### Dehomogenizing the two remaining coordinates -/

theorem sum_single_apply {α : Type*} [Fintype α] (c : α → ℕ) (a : α) :
    (∑ b, Finsupp.single b (c b)) a = c a := by
  classical
  rw [Finset.sum_apply',
    Finset.sum_eq_single_of_mem (f := fun b ↦ (Finsupp.single b (c b) : α →₀ ℕ) a) a
      (Finset.mem_univ a) (fun b _ hb ↦ by simp [hb])]
  exact Finsupp.single_eq_same

theorem monomial_eq_prod_X_pow {σ K : Type*} [Field K] [Fintype σ] (ν : σ →₀ ℕ) (a : K) :
    monomial ν a = C a * ∏ p : σ, X p ^ ν p := by
  classical
  rw [monomial_eq, Finsupp.prod]
  refine congrArg _ (Finset.prod_subset (Finset.subset_univ _) fun p _ hp ↦ ?_)
  rw [Finsupp.notMem_support_iff.mp hp, pow_zero]

section DeHom

variable {K : Type*} [Field K] {κ ι : Type*} [DecidableEq ι]

/-- The dehomogenization that sends `X (h, i₀ h)` to `X h`, the second kept coordinate to `1`,
and every other variable to `0`. -/
def deHom (i₀ i₁ : κ → ι) : MvPolynomial (κ × ι) K →ₐ[K] MvPolynomial κ K :=
  aeval fun p : κ × ι ↦ if p.2 = i₀ p.1 then X p.1 else if p.2 = i₁ p.1 then 1 else 0

variable (i₀ i₁ : κ → ι)

@[simp]
theorem deHom_X_i₀ (h : κ) : deHom i₀ i₁ (X ((h, i₀ h) : κ × ι)) = (X h : MvPolynomial κ K) := by
  simp [deHom]

theorem deHom_X_i₁ {h : κ} (hne : i₁ h ≠ i₀ h) :
    deHom i₀ i₁ (X ((h, i₁ h) : κ × ι)) = (1 : MvPolynomial κ K) := by
  simp [deHom, hne]

theorem deHom_X_other {h : κ} {i : ι} (h0 : i ≠ i₀ h) (h1 : i ≠ i₁ h) :
    deHom i₀ i₁ (X ((h, i) : κ × ι)) = (0 : MvPolynomial κ K) := by
  simp [deHom, h0, h1]

variable [Finite ι] [Fintype κ]

omit [DecidableEq ι] in
/-- The exponent obtained by keeping only the coordinates `i₀ h`. -/
def blockProj (ν : κ × ι →₀ ℕ) : κ →₀ ℕ :=
  ∑ h, Finsupp.single h (ν (h, i₀ h))

omit [DecidableEq ι] [Finite ι] in
theorem blockProj_apply (ν : κ × ι →₀ ℕ) (h : κ) : blockProj i₀ ν h = ν (h, i₀ h) :=
  sum_single_apply _ h

/-- **The dehomogenization of a monomial that involves only the two kept coordinates.** -/
theorem deHom_monomial (hne : ∀ h, i₁ h ≠ i₀ h) {ν : κ × ι →₀ ℕ}
    (hdrop : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → ν (h, i) = 0) (a : K) :
    deHom i₀ i₁ (monomial ν a) = monomial (blockProj i₀ ν) a := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hblock : ∀ h : κ, ∏ i, deHom i₀ i₁ (X ((h, i) : κ × ι)) ^ ν (h, i)
      = (X h : MvPolynomial κ K) ^ ν (h, i₀ h) := by
    intro h
    rw [Finset.prod_eq_single_of_mem (i₀ h) (Finset.mem_univ _) (fun i _ hi ↦ ?_), deHom_X_i₀]
    by_cases h1 : i = i₁ h
    · rw [h1, deHom_X_i₁ i₀ i₁ (hne h), one_pow]
    · rw [deHom_X_other i₀ i₁ hi h1, hdrop h i hi h1, pow_zero]
  rw [monomial_eq_prod_X_pow, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    map_prod, Fintype.prod_prod_type]
  simp only [map_pow]
  rw [Finset.prod_congr rfl fun h _ ↦ hblock h, blockProj, prod_X_pow_eq_monomial_finset_sum,
    C_mul_monomial, mul_one]

end DeHom

/-! ### The index after dehomogenization -/

section Compare

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (i₀ i₁ : κ → ι) {M : κ → ι → K}

omit [Fintype ι] [Fintype κ] in
theorem evalZeroAt_eq_self_iff {t : κ × ι} {P : MvPolynomial (κ × ι) K} :
    evalZeroAt t P = P ↔ ∀ ν ∈ P.support, ν t = 0 := by
  constructor
  · intro h ν hν
    rw [← h] at hν
    exact (coeff_evalZeroAt_ne_zero (mem_support_iff.mp hν)).1
  · intro h
    ext ν
    rw [coeff_evalZeroAt]
    split_ifs with hν
    · rfl
    · exact (notMem_support_iff.mp fun hc ↦ hν (h ν hc)).symm

omit [Fintype κ] [DecidableEq κ] in
/-- **Dehomogenizing intertwines the inverse change of coordinates with a translation.** -/
theorem deHom_substFormInv (hne : ∀ h, i₁ h ≠ i₀ h) (hM1 : ∀ h, M h (i₀ h) = 1)
    (P : MvPolynomial (κ × ι) K) :
    deHom i₀ i₁ (substFormInv i₀ M P)
      = taylorAt (fun h ↦ -(M h (i₁ h))) (deHom i₀ i₁ P) := by
  have key : (deHom i₀ i₁).comp (substFormInv i₀ M)
      = (taylorAt (fun h ↦ -(M h (i₁ h)))).comp (deHom i₀ i₁) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, i⟩ := p
    simp only [AlgHom.comp_apply]
    by_cases hi : i = i₀ h
    · subst hi
      have hsum : ∑ i ∈ univ.erase (i₀ h), deHom i₀ i₁ (C (M h i) * X ((h, i) : κ × ι))
          = C (M h (i₁ h)) := by
        rw [Finset.sum_eq_single_of_mem (i₁ h)
          (Finset.mem_erase.mpr ⟨hne h, Finset.mem_univ _⟩) (fun i hi hi1 ↦ ?_)]
        · rw [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
            deHom_X_i₁ i₀ i₁ (hne h), mul_one]
        · rw [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
            deHom_X_other i₀ i₁ (Finset.mem_erase.mp hi).1 hi1, mul_zero]
      rw [substFormInv_X_self, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        map_sub, deHom_X_i₀, map_sum, hsum, hM1 h, inv_one, map_one, one_mul,
        taylorAt_X]
      rw [map_neg]
      ring
    · rw [substFormInv_X_of_ne i₀ M hi]
      by_cases h1 : i = i₁ h
      · rw [h1, deHom_X_i₁ i₀ i₁ (hne h), map_one]
      · rw [deHom_X_other i₀ i₁ hi h1, map_zero]
  exact congrArg (fun f ↦ f P) key

omit [Fintype ι] [Fintype κ] in
theorem zeroAt_eq_self {t : κ × ι} (M : κ → ι → K) (ht : M t.1 t.2 = 0) : zeroAt t M = M := by
  obtain ⟨t₁, t₂⟩ := t
  funext h i
  simp only [zeroAt]
  split_ifs with hc
  · have h1 : h = t₁ := congrArg Prod.fst hc
    have h2 : i = t₂ := congrArg Prod.snd hc
    subst h1
    subst h2
    exact ht.symm
  · rfl

omit [DecidableEq κ] in
/-- **The coefficients of the dehomogenization are the coefficients of the polynomial.** For a
multihomogeneous polynomial that involves only the two kept coordinates in each block, the
projection `MvPolynomial.blockProj` is a bijection from its monomials to those of its
dehomogenization. -/
theorem deHom_coeff_correspondence (hne : ∀ h, i₁ h ≠ i₀ h) {r : κ → ℕ}
    {S : MvPolynomial (κ × ι) K} (hS : IsMultiHomogeneous r S)
    (hSdrop : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → ∀ ν ∈ S.support, ν (h, i) = 0) :
    (∀ ν ∈ S.support, (deHom i₀ i₁ S).coeff (blockProj i₀ ν) = S.coeff ν) ∧
      ∀ l : κ →₀ ℕ, (deHom i₀ i₁ S).coeff l ≠ 0 → ∃ ν ∈ S.support, blockProj i₀ ν = l := by
  classical
  have hdeHom : deHom i₀ i₁ S
      = ∑ ν ∈ S.support, monomial (blockProj i₀ ν) (S.coeff ν) := by
    conv_lhs => rw [S.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun ν hν ↦
      deHom_monomial i₀ i₁ hne (fun h i hi0 hi1 ↦ hSdrop h i hi0 hi1 ν hν) _
  have hpair : ∀ ν ∈ S.support, ∀ h, ν (h, i₀ h) + ν (h, i₁ h) = r h := by
    intro ν hν h
    rw [← hS (mem_support_iff.mp hν) h,
      ← Finset.sum_subset (Finset.subset_univ ({i₀ h, i₁ h} : Finset ι))
        (fun i _ hi ↦ hSdrop h i (fun hc ↦ hi (by simp [hc])) (fun hc ↦ hi (by simp [hc])) ν hν),
      Finset.sum_pair (Ne.symm (hne h))]
  have hinj : ∀ ν ∈ S.support, ∀ ν' ∈ S.support, blockProj i₀ ν = blockProj i₀ ν' → ν = ν' := by
    intro ν hν ν' hν' hbp
    ext p
    obtain ⟨h, i⟩ := p
    have h0 : ν (h, i₀ h) = ν' (h, i₀ h) := by
      rw [← blockProj_apply i₀ ν h, ← blockProj_apply i₀ ν' h, hbp]
    by_cases hi0 : i = i₀ h
    · rw [hi0]; exact h0
    · by_cases hi1 : i = i₁ h
      · have e1 := hpair ν hν h
        have e2 := hpair ν' hν' h
        rw [hi1]
        omega
      · rw [hSdrop h i hi0 hi1 ν hν, hSdrop h i hi0 hi1 ν' hν']
  refine ⟨fun ν hν ↦ ?_, fun l hl ↦ ?_⟩
  · rw [hdeHom, coeff_sum, Finset.sum_eq_single_of_mem ν hν (fun ν' hν' hne' ↦ ?_)]
    · simp [coeff_monomial]
    · rw [coeff_monomial]
      exact ite_eq_right (fun hc ↦ hne' (hinj ν' hν' ν hν hc))
  · by_contra hc
    push Not at hc
    rw [hdeHom, coeff_sum] at hl
    exact hl (Finset.sum_eq_zero fun ν hν ↦ by
      rw [coeff_monomial]
      exact ite_eq_right (hc ν hν))

omit [DecidableEq κ] in
/-- **The index along the forms is the index of Layer 2.3 after dehomogenization.** This is
Bombieri–Gubler 7.5.18, in the generality the generalized Roth lemma needs it. -/
theorem formIndex_eq_index_deHom {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) (hne : ∀ h, i₁ h ≠ i₀ h)
    (hM1 : ∀ h, M h (i₀ h) = 1) (hMdrop : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → M h i = 0)
    {r : κ → ℕ} {Q : MvPolynomial (κ × ι) K} (hQ : IsMultiHomogeneous r Q)
    (hQdrop : ∀ h i, i ≠ i₀ h → i ≠ i₁ h → ∀ ν ∈ Q.support, ν (h, i) = 0) :
    formIndex d M Q = index d (fun h ↦ -(M h (i₁ h))) (deHom i₀ i₁ Q) := by
  classical
  have hM0 : ∀ h, M h (i₀ h) ≠ 0 := fun h ↦ by rw [hM1 h]; exact one_ne_zero
  have hRdrop : ∀ (h : κ) (i : ι), i ≠ i₀ h → i ≠ i₁ h →
      ∀ ν ∈ (substFormInv i₀ M Q).support, ν (h, i) = 0 := by
    intro h i hi0 hi1
    have hQt : evalZeroAt ((h, i) : κ × ι) Q = Q :=
      evalZeroAt_eq_self_iff.mpr (fun ν hν ↦ hQdrop h i hi0 hi1 ν hν)
    have hcomm := evalZeroAt_substFormInv (t := ((h, i) : κ × ι)) M hi0 Q
    rw [hQt, zeroAt_eq_self M (hMdrop h i hi0 hi1)] at hcomm
    exact evalZeroAt_eq_self_iff.mp hcomm
  obtain ⟨hcoeff, hsurj⟩ :=
    deHom_coeff_correspondence i₀ i₁ hne (hQ.substFormInv i₀ M) hRdrop
  have hwt : ∀ ν : κ × ι →₀ ℕ,
      Finsupp.weight (fun h ↦ ENNReal.ofReal (d h)⁻¹) (blockProj i₀ ν)
        = Finsupp.weight (formWeight i₀ d) ν := by
    intro ν
    rw [weight_formWeight hd, Finsupp.weight_ofReal_inv d hd,
      Finsupp.sum_fintype _ _ (by simp)]
    exact congrArg _ (Finset.sum_congr rfl fun h _ ↦ by rw [blockProj_apply])
  have hord : weightedOrder (formWeight i₀ d) (substFormInv i₀ M Q)
      = weightedOrder (fun h ↦ ENNReal.ofReal (d h)⁻¹)
          (deHom i₀ i₁ (substFormInv i₀ M Q)) := by
    refine le_antisymm (le_weightedOrder fun l hl ↦ ?_) (le_weightedOrder fun ν hν ↦ ?_)
    · obtain ⟨ν, hν, rfl⟩ := hsurj l hl
      rw [hwt]
      exact weightedOrder_le_of_coeff_ne_zero (mem_support_iff.mp hν)
    · rw [← hwt ν]
      exact weightedOrder_le_of_coeff_ne_zero
        (by rw [hcoeff ν (mem_support_iff.mpr hν)]; exact hν)
  rw [formIndex_eq_weightedOrder hd hM0, index_eq_weightedOrder d hd,
    ← deHom_substFormInv i₀ i₁ hne hM1]
  exact hord

end Compare

end MvPolynomial
