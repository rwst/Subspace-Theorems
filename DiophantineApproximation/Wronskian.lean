/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Wronskian

-- Used only by the acceptance criteria.
import Mathlib.Data.ZMod.Basic

/-!
# The Wronskian of several polynomials

The **Wronskian** of `n` polynomials in one variable is the determinant of the matrix whose
`i`-th row is the `i`-th derivative of each of them. Mathlib has the case `n = 2` as
`Polynomial.wronskian`; this file has the determinant for every `n`, in the two normalisations
that differ by the factor `∏ i, i !` — ordinary derivatives and Hasse derivatives — and the
criterion they exist for: over a field of characteristic zero the Wronskian is nonzero **exactly**
when the polynomials are linearly independent over the field.

The proof of the hard half is by leading coefficients, not by the classical argument that
differentiates a relation with coefficients in the field of rational functions. Every term of the
Leibniz expansion of the Wronskian has the same degree, namely `∑ j, deg ψ j - ∑ i, i`, because
differentiating `i` times lowers the degree by `i` whichever column it happens in. So the top
coefficient of the Wronskian is a determinant of *numbers*: replace the family by one with
pairwise distinct degrees `d j`, which spans the same space, and that determinant is the matrix
of binomial coefficients `(d j).choose i`. It is nonzero because a polynomial with `n` terms
cannot vanish to order `n` at `1` — apply the Euler operator `p ↦ X p'`, which lowers the order of
vanishing at `1` by at most one and acts on `X ^ d` by the scalar `d`, and read off a Vandermonde
determinant in the exponents.

## Main results

* `Polynomial.wronskianDet` and `Polynomial.hasseWronskianDet`: the two determinants, and
  `Polynomial.wronskianDet_eq_C_mul` between them.
* `Polynomial.wronskianDet_fin_two`: Mathlib's `Polynomial.wronskian` is the case `n = 2`.
* `Polynomial.linearIndependent_iff_wronskianDet_ne_zero` and its Hasse form: **the criterion**,
  over a field of characteristic zero.
* `Polynomial.det_choose_ne_zero`: the binomial determinant of `n` distinct exponents is nonzero
  — the arithmetic content of the milestone.
* `Polynomial.exists_natDegree_injective`: a linearly independent family spans the same space as
  one with pairwise distinct degrees.
* `Polynomial.coeff_mul_of_natDegree_le` and `Polynomial.coeff_prod_of_natDegree_le'`: the
  coefficient of a product at the sum of individual degree bounds. Mathlib's
  `Polynomial.coeff_prod_of_natDegree_le` is the case of one bound shared by all the factors,
  which is not the case that arises here.

## Implementation notes

⚠ **Characteristic zero is essential, and the rejection test is one line.** Over `ZMod 2` the
polynomials `1` and `X ^ 2` are linearly independent and both Wronskians vanish; the same happens
over `ZMod p` with `1` and `X ^ p`. Characteristic zero enters twice, in the binomial determinant
and in the passage between the two normalisations, and both uses are essential.

⚠ **The easy half needs no hypothesis on the characteristic and no derivative property.** A
linear relation over the field is a relation between the *columns* of the matrix, which is enough
to kill the determinant over the integral domain `K[X]`; the proof never differentiates anything.

⚠ **The Hasse normalisation is the one that generalises.** Layer 2.4's several-variable statement
differentiates with `MvPolynomial.hasseDeriv`, because that is the derivative that survives in
positive characteristic and the one Layer 2.1 builds; the ordinary determinant is `∏ i, i !` times
it, so in characteristic zero the two criteria are the same statement. The `n = 2` compatibility
with Mathlib is in the ordinary normalisation, where `hasseDeriv 1 = derivative` makes it an
identity.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 6.3.10, of which this is the one-variable case that the Kronecker substitution reduces
the several-variable statement to.

This is Layer 2.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

namespace Polynomial

/-! ### The coefficient of a product at the sum of the degree bounds -/

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- If `p` has degree at most `a` and `q` degree at most `b`, the coefficient of `p * q` at
`a + b` is the product of the two coefficients there. -/
theorem coeff_mul_of_natDegree_le {p q : R[X]} {a b : ℕ} (hp : p.natDegree ≤ a)
    (hq : q.natDegree ≤ b) : (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_single (a, b) (fun x hx hne ↦ ?_) fun h ↦ ?_
  · rcases le_or_gt x.1 a with h1 | h1
    · have hx' := Finset.mem_antidiagonal.mp hx
      have hne' : ¬(x.1 = a ∧ x.2 = b) := fun h ↦ hne (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
      rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega)), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h1), zero_mul]
  · exact absurd (by simp : ((a, b) : ℕ × ℕ) ∈ Finset.antidiagonal (a + b)) h

/-- The coefficient of a product at the sum of individual degree bounds is the product of the
coefficients there. Mathlib's `Polynomial.coeff_prod_of_natDegree_le` is the case of one bound
shared by every factor. -/
theorem coeff_prod_of_natDegree_le' (s : Finset ι) (f : ι → R[X]) (m : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ m i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, m i) = ∏ i ∈ s, (f i).coeff (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        coeff_mul_of_natDegree_le (h a (Finset.mem_insert_self a s))
          ((Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum fun i hi ↦
            h i (Finset.mem_insert_of_mem hi))),
        ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

/-! ### The two Wronskian determinants -/

variable {S : Type*} [CommRing S] {n : ℕ}

/-- The **Wronskian matrix** of a family of polynomials: the entry `(i, j)` is the `i`-th
derivative of `ψ j`. -/
def wronskianMatrix (ψ : Fin n → S[X]) : Matrix (Fin n) (Fin n) S[X] :=
  .of fun i j ↦ derivative^[i] (ψ j)

/-- The **Wronskian** of a family of polynomials, the determinant of `wronskianMatrix`. -/
def wronskianDet (ψ : Fin n → S[X]) : S[X] := (wronskianMatrix ψ).det

/-- The **Hasse–Wronskian matrix**: the entry `(i, j)` is the `i`-th Hasse derivative of `ψ j`. -/
def hasseWronskianMatrix (ψ : Fin n → S[X]) : Matrix (Fin n) (Fin n) S[X] :=
  .of fun i j ↦ hasseDeriv i (ψ j)

/-- The **Hasse–Wronskian** of a family of polynomials, the determinant of
`hasseWronskianMatrix`. It differs from `wronskianDet` by the factor `∏ i, i !`. -/
def hasseWronskianDet (ψ : Fin n → S[X]) : S[X] := (hasseWronskianMatrix ψ).det

@[simp]
theorem wronskianMatrix_apply (ψ : Fin n → S[X]) (i j : Fin n) :
    wronskianMatrix ψ i j = derivative^[i] (ψ j) := rfl

@[simp]
theorem hasseWronskianMatrix_apply (ψ : Fin n → S[X]) (i j : Fin n) :
    hasseWronskianMatrix ψ i j = hasseDeriv i (ψ j) := rfl

/-- **Mathlib's Wronskian is the case `n = 2`.** -/
theorem wronskianDet_fin_two (a b : S[X]) : wronskianDet ![a, b] = wronskian a b := by
  simp [wronskianDet, wronskianMatrix, Matrix.det_fin_two, wronskian]
  ring

/-- The two normalisations differ by the factor `∏ i, i !`. -/
theorem wronskianDet_eq_C_mul (ψ : Fin n → S[X]) :
    wronskianDet ψ = C (∏ i : Fin n, (Nat.factorial (i : ℕ) : S)) * hasseWronskianDet ψ := by
  have hrow : wronskianMatrix ψ
      = Matrix.diagonal (fun i : Fin n ↦ (C (Nat.factorial (i : ℕ) : S) : S[X]))
        * hasseWronskianMatrix ψ := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.diagonal_mul, wronskianMatrix_apply, hasseWronskianMatrix_apply,
      ← factorial_smul_hasseDeriv (k := (i : ℕ))]
    simp [nsmul_eq_mul]
  rw [wronskianDet, hrow, Matrix.det_mul, Matrix.det_diagonal, hasseWronskianDet, map_prod]

/-! ### The binomial determinant -/

variable {K : Type*} [Field K]

/-- If `(X - a) ^ (m + 1)` divides `p`, then `(X - a) ^ m` divides its derivative. -/
theorem dvd_derivative_of_pow_succ_dvd {a : K} {m : ℕ} {p : K[X]}
    (h : ((X : K[X]) - C a) ^ (m + 1) ∣ p) : ((X : K[X]) - C a) ^ m ∣ derivative p := by
  obtain ⟨q, rfl⟩ := h
  rw [derivative_mul, derivative_pow, derivative_X_sub_C, mul_one, Nat.add_sub_cancel]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left _ _) q)
    (dvd_mul_of_dvd_left (pow_dvd_pow _ (Nat.le_succ m)) _)

/-- **A polynomial with `n` terms does not vanish to order `n` at `1`.** The Euler operator
`p ↦ X p'` lowers the order of vanishing at `1` by at most one and multiplies `X ^ d` by `d`, so
`n` applications of it turn the hypothesis into a Vandermonde system in the exponents. -/
theorem eq_zero_of_pow_dvd_sum [CharZero K] {n : ℕ} {c : Fin n → K} {d : Fin n → ℕ}
    (hd : Function.Injective d)
    (hdvd : ((X : K[X]) - C 1) ^ n ∣ ∑ j, C (c j) * X ^ d j) : c = 0 := by
  classical
  set f : K[X] := ∑ j, C (c j) * X ^ d j with hf
  have hterm : ∀ (u : K) (k : ℕ),
      (X : K[X]) * derivative (C u * X ^ k) = C (u * (k : K)) * X ^ k := by
    intro u k
    cases k with
    | zero => simp
    | succ k => rw [derivative_C_mul, derivative_X_pow, C_mul, Nat.add_sub_cancel]; ring
  have hstep : ∀ b : Fin n → K, (X : K[X]) * derivative (∑ j, C (b j) * X ^ d j)
      = ∑ j, C (b j * (d j : K)) * X ^ d j := fun b ↦ by
    rw [derivative_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ hterm (b j) (d j)
  have hiter : ∀ i : ℕ, (fun p ↦ (X : K[X]) * derivative p)^[i] f
      = ∑ j, C (c j * (d j : K) ^ i) * X ^ d j := by
    intro i
    induction i with
    | zero => simp [hf]
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih, hstep]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [pow_succ, mul_assoc]
  have hdvd' : ∀ i, i ≤ n → ((X : K[X]) - C 1) ^ (n - i)
      ∣ (fun p ↦ (X : K[X]) * derivative p)^[i] f := by
    intro i
    induction i with
    | zero => simpa using hdvd
    | succ i ih =>
        intro hi
        have h2 := ih (by omega)
        rw [show n - i = (n - (i + 1)) + 1 by omega] at h2
        rw [Function.iterate_succ_apply']
        exact (dvd_derivative_of_pow_succ_dvd h2).mul_left X
  have hroot : ∀ i : Fin n, ∑ j, c j * (d j : K) ^ (i : ℕ) = 0 := by
    intro i
    have h1 : ((X : K[X]) - C 1) ∣ (fun p ↦ (X : K[X]) * derivative p)^[(i : ℕ)] f :=
      dvd_trans (dvd_pow_self _ (by have := i.isLt; omega)) (hdvd' i i.isLt.le)
    obtain ⟨q, hq⟩ := h1
    have h2 : ((fun p ↦ (X : K[X]) * derivative p)^[(i : ℕ)] f).eval 1 = 0 := by
      rw [hq]; simp
    rw [hiter, eval_finsetSum] at h2
    simpa using h2
  have hvan : (Matrix.vandermonde fun j ↦ (d j : K)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr fun x y h ↦ hd (Nat.cast_injective h)
  have hker : (Matrix.vandermonde fun j ↦ (d j : K)).transpose.mulVec c = 0 := by
    funext i
    have h := hroot i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  exact Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hker

/-- **The binomial determinant.** For `n` pairwise distinct exponents `d j`, the matrix of
binomial coefficients `(d j).choose i` with `i < n` is invertible over a field of characteristic
zero. Its columns are the first `n` coefficients of `(X + 1) ^ d j`, so a kernel vector is a
polynomial with `n` terms vanishing to order `n` at `1`. -/
theorem det_choose_ne_zero [CharZero K] {n : ℕ} {d : Fin n → ℕ} (hd : Function.Injective d) :
    (Matrix.of fun (i j : Fin n) ↦ (((d j).choose (i : ℕ) : ℕ) : K)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine hc0 (eq_zero_of_pow_dvd_sum hd ?_)
  have htaylor : taylor (1 : K) (∑ j, C (c j) * X ^ d j)
      = ∑ j, C (c j) * (X + C 1) ^ d j := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [taylor_apply, mul_comp, C_comp, X_pow_comp]
  have hcoeff : ∀ i < n, (taylor (1 : K) (∑ j, C (c j) * X ^ d j)).coeff i = 0 := by
    intro i hi
    have h := congrFun hc ⟨i, hi⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    rw [htaylor, finsetSum_coeff]
    simp only [coeff_C_mul, C_1, coeff_X_add_one_pow]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  obtain ⟨g, hg⟩ := (X_pow_dvd_iff (n := n)).mpr hcoeff
  refine ⟨g.comp ((X : K[X]) - C 1), ?_⟩
  have h := congrArg (fun p ↦ p.comp ((X : K[X]) - C 1)) hg
  simp only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X,
    mul_comp, pow_comp] at h
  exact h

/-! ### A family with pairwise distinct degrees -/

/-- **Echelon basis.** A linearly independent family of polynomials over a field spans the same
space as a family with pairwise distinct degrees: one element of each degree occurring in the span
already spans it, so there are at least `n` such degrees. -/
theorem exists_natDegree_injective {n : ℕ} {ψ : Fin n → K[X]} (hψ : LinearIndependent K ψ) :
    ∃ g : Fin n → K[X], (∀ i, g i ∈ Submodule.span K (Set.range ψ)) ∧ (∀ i, g i ≠ 0) ∧
      Function.Injective fun i ↦ (g i).natDegree := by
  classical
  set V : Submodule K K[X] := Submodule.span K (Set.range ψ) with hV
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ f ∈ V, f.natDegree ≤ B := by
    refine ⟨Finset.univ.sup fun j ↦ (ψ j).natDegree, fun f hf ↦ ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
    rw [smul_eq_C_mul]
    exact (natDegree_C_mul_le _ _).trans
      (Finset.le_sup (f := fun j ↦ (ψ j).natDegree) (Finset.mem_univ j))
  set D : Finset ℕ := (Finset.range (B + 1)).filter
    (fun m ↦ ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = m) with hD
  have hex : ∀ m : ℕ, ∃ f : K[X], m ∈ D → (f ∈ V ∧ f ≠ 0 ∧ f.natDegree = m) := by
    intro m
    by_cases hm : m ∈ D
    · obtain ⟨f, hf1, hf2, hf3⟩ := (Finset.mem_filter.mp hm).2
      exact ⟨f, fun _ ↦ ⟨hf1, hf2, hf3⟩⟩
    · exact ⟨0, fun h ↦ absurd h hm⟩
  choose g hg using hex
  have hmemD : ∀ f ∈ V, f ≠ 0 → f.natDegree ∈ D := fun f hf hf0 ↦
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB f hf)), f, hf, hf0, rfl⟩
  have hspan : ∀ m : ℕ, ∀ f ∈ V, f.natDegree = m → f ∈ Submodule.span K (g '' ↑D) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro f hf hfdeg
      rcases eq_or_ne f 0 with rfl | hf0
      · exact Submodule.zero_mem _
      have hmD : m ∈ D := hfdeg ▸ hmemD f hf hf0
      obtain ⟨hgV, hg0, hgdeg⟩ := hg m hmD
      set c : K := f.leadingCoeff / (g m).leadingCoeff with hc
      have hcne : c ≠ 0 :=
        div_ne_zero (leadingCoeff_ne_zero.mpr hf0) (leadingCoeff_ne_zero.mpr hg0)
      have hmem : C c * g m ∈ Submodule.span K (g '' ↑D) := by
        rw [← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hmD, rfl⟩)
      have hCmemV : C c * g m ∈ V := by
        rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ hgV
      have hdeg : (f - C c * g m).degree < f.degree := by
        refine degree_sub_lt_left ?_ hf0 ?_
        · rw [degree_C_mul hcne, degree_eq_natDegree hf0, degree_eq_natDegree hg0, hfdeg, hgdeg]
        · rw [leadingCoeff_mul, leadingCoeff_C, hc,
            div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hg0)]
      rcases eq_or_ne (f - C c * g m) 0 with h0 | h0
      · rw [sub_eq_zero] at h0
        exact h0 ▸ hmem
      · have hlt : (f - C c * g m).natDegree < m := by
          have h := natDegree_lt_natDegree h0 hdeg
          rwa [hfdeg] at h
        have hsub := ih _ hlt (f - C c * g m) (Submodule.sub_mem _ hf hCmemV) rfl
        have hfeq : f = (f - C c * g m) + C c * g m := by ring
        rw [hfeq]
        exact Submodule.add_mem _ hsub hmem
  have hcard : n ≤ D.card := by
    have h1 : Module.finrank K V = n := by
      rw [hV, finrank_span_eq_card hψ, Fintype.card_fin]
    have : FiniteDimensional K (Submodule.span K ((D.image g : Finset K[X]) : Set K[X])) :=
      FiniteDimensional.span_of_finite _ (Finset.finite_toSet _)
    have h2 : V ≤ Submodule.span K ((D.image g : Finset K[X]) : Set K[X]) := by
      intro f hf
      refine Submodule.span_mono ?_ (hspan _ f hf rfl)
      rintro x ⟨m, hm, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    calc n = Module.finrank K V := h1.symm
      _ ≤ Module.finrank K (Submodule.span K ((D.image g : Finset K[X]) : Set K[X])) :=
          Submodule.finrank_mono h2
      _ ≤ (D.image g).card := finrank_span_finset_le_card _
      _ ≤ D.card := Finset.card_image_le
  obtain ⟨t, htD, htcard⟩ := Finset.exists_subset_card_eq hcard
  have hmem : ∀ i : Fin n, ((t.orderIsoOfFin htcard i : ℕ)) ∈ D :=
    fun i ↦ htD (t.orderIsoOfFin htcard i).2
  refine ⟨fun i ↦ g (t.orderIsoOfFin htcard i), fun i ↦ (hg _ (hmem i)).1,
    fun i ↦ (hg _ (hmem i)).2.1, fun i₁ i₂ h ↦ ?_⟩
  have h1 := (hg _ (hmem i₁)).2.2
  have h2 := (hg _ (hmem i₂)).2.2
  exact (t.orderIsoOfFin htcard).injective (Subtype.ext (by rw [← h1, ← h2]; exact h))

/-! ### The top coefficient of the Wronskian -/

/-- Every term of the Leibniz expansion of the Hasse–Wronskian sits in the same degree, and its
coefficient there is a product of binomial coefficients: differentiating `i` times lowers a degree
by `i`, whichever column it is done in. -/
theorem coeff_prod_hasseDeriv {n : ℕ} (g : Fin n → K[X]) (τ : Equiv.Perm (Fin n)) :
    (∏ i, hasseDeriv (τ i : ℕ) (g i)).coeff ((∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ))
      = (∏ i, (g i).leadingCoeff) * ∏ i, (((g i).natDegree.choose (τ i : ℕ) : ℕ) : K) := by
  classical
  by_cases hgood : ∀ i, (τ i : ℕ) ≤ (g i).natDegree
  · have hsum : ∑ i, ((g i).natDegree - (τ i : ℕ))
        = (∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ) := by
      have h1 : (∑ i, ((g i).natDegree - (τ i : ℕ))) + ∑ i, ((τ i : ℕ))
          = ∑ i, (g i).natDegree := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hgood i)
      have h2 : ∑ i, ((τ i : ℕ)) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ fun i ↦ (i : ℕ)
      omega
    rw [← hsum, coeff_prod_of_natDegree_le' _ _ _ fun i _ ↦ natDegree_hasseDeriv_le _ _,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [hasseDeriv_coeff, Nat.sub_add_cancel (hgood i), coeff_natDegree, mul_comm]
  · simp only [not_forall, not_le] at hgood
    obtain ⟨i₀, hi₀⟩ := hgood
    have h1 : hasseDeriv (τ i₀ : ℕ) (g i₀) = 0 := hasseDeriv_eq_zero_of_lt_natDegree _ _ hi₀
    have h2 : (((g i₀).natDegree.choose (τ i₀ : ℕ) : ℕ) : K) = 0 := by
      rw [Nat.choose_eq_zero_of_lt hi₀, Nat.cast_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) h1, coeff_zero,
      show (∏ i, (((g i).natDegree.choose (τ i : ℕ) : ℕ) : K)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ i₀) h2, mul_zero]

/-- **The top coefficient of the Hasse–Wronskian is a binomial determinant.** -/
theorem coeff_hasseWronskianDet {n : ℕ} (g : Fin n → K[X]) :
    (hasseWronskianDet g).coeff ((∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ))
      = (∏ i, (g i).leadingCoeff)
        * (Matrix.of fun (i j : Fin n) ↦ (((g j).natDegree.choose (i : ℕ) : ℕ) : K)).det := by
  classical
  rw [hasseWronskianDet, Matrix.det_apply', finsetSum_coeff, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  have hc : ((Equiv.Perm.sign τ : ℤ) : K[X]) = C ((Equiv.Perm.sign τ : ℤ) : K) := by simp
  simp only [hasseWronskianMatrix, Matrix.of_apply]
  rw [hc, coeff_C_mul, coeff_prod_hasseDeriv]
  ring

/-! ### The criterion -/

/-- **The hard half.** Over a field of characteristic zero the Hasse–Wronskian of a linearly
independent family is not the zero polynomial: pass to a family with pairwise distinct degrees,
whose Wronskian has a nonzero top coefficient. -/
theorem hasseWronskianDet_ne_zero [CharZero K] {n : ℕ} {ψ : Fin n → K[X]}
    (hψ : LinearIndependent K ψ) : hasseWronskianDet ψ ≠ 0 := by
  classical
  obtain ⟨g, hgV, hg0, hginj⟩ := exists_natDegree_injective hψ
  have hgdet : hasseWronskianDet g ≠ 0 := by
    intro h
    have hco := coeff_hasseWronskianDet g
    rw [h, coeff_zero] at hco
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ leadingCoeff_ne_zero.mpr (hg0 i))
      (det_choose_ne_zero hginj) hco.symm
  choose M hM using fun i ↦ (Submodule.mem_span_range_iff_exists_fun K).mp (hgV i)
  have hmat : hasseWronskianMatrix g
      = hasseWronskianMatrix ψ * Matrix.of fun k i ↦ C (M i k) := by
    refine Matrix.ext fun i j ↦ ?_
    rw [hasseWronskianMatrix_apply, ← hM j, map_sum, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [hasseWronskianMatrix_apply, Matrix.of_apply, map_smul, smul_eq_C_mul, mul_comm]
  intro h
  refine hgdet ?_
  rw [hasseWronskianDet, hmat, Matrix.det_mul, ← hasseWronskianDet, h, zero_mul]

/-- **The easy half**, in any characteristic: a linear relation between the polynomials is a
linear relation between the columns of the matrix, which kills the determinant over the integral
domain `K[X]`. No derivative property is used. -/
theorem hasseWronskianDet_eq_zero_of_not_linearIndependent {n : ℕ} {ψ : Fin n → K[X]}
    (hψ : ¬ LinearIndependent K ψ) : hasseWronskianDet ψ = 0 := by
  classical
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hψ
  have hker : (hasseWronskianMatrix ψ).mulVec (fun j ↦ C (c j)) = 0 := by
    funext i
    have hz : (hasseDeriv (i : ℕ)) (∑ j, c j • ψ j) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hz
    simp only [Matrix.mulVec, dotProduct, hasseWronskianMatrix_apply, Pi.zero_apply]
    rw [← hz]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_C_mul, mul_comm]
  exact Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun j ↦ C (c j), fun h ↦ hi₀ (by simpa using congrFun h i₀), hker⟩

/-- **The Wronskian criterion, Hasse normalisation.** -/
theorem linearIndependent_iff_hasseWronskianDet_ne_zero [CharZero K] {n : ℕ} (ψ : Fin n → K[X]) :
    LinearIndependent K ψ ↔ hasseWronskianDet ψ ≠ 0 :=
  ⟨hasseWronskianDet_ne_zero, fun h ↦ by
    by_contra hn
    exact h (hasseWronskianDet_eq_zero_of_not_linearIndependent hn)⟩

/-- **The Wronskian criterion** (Bombieri–Gubler, Proposition 6.3.10 in one variable): `n`
polynomials over a field of characteristic zero are linearly independent exactly when the
determinant of their first `n` derivatives is not the zero polynomial. -/
theorem linearIndependent_iff_wronskianDet_ne_zero [CharZero K] {n : ℕ} (ψ : Fin n → K[X]) :
    LinearIndependent K ψ ↔ wronskianDet ψ ≠ 0 := by
  have hfac : (C (∏ i : Fin n, (Nat.factorial (i : ℕ) : K)) : K[X]) ≠ 0 := by
    rw [Ne, C_eq_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [linearIndependent_iff_hasseWronskianDet_ne_zero, wronskianDet_eq_C_mul]
  exact ⟨fun h ↦ mul_ne_zero hfac h, fun h hz ↦ h (by rw [hz, mul_zero])⟩

/-! ### Acceptance criteria -/

/-- **Acceptance test: Mathlib's two-polynomial Wronskian is the case `n = 2`.** -/
example (a b : ℚ[X]) : wronskianDet ![a, b] = wronskian a b := wronskianDet_fin_two a b

/-- **Acceptance test: the Wronskian of `1, X, X ^ 2` is `2`.** -/
example : wronskianDet ![(1 : ℚ[X]), X, X ^ 2] = 2 := by
  simp [wronskianDet, wronskianMatrix, Matrix.det_fin_three, Function.iterate_succ_apply']
  ring

/-- **Rejection test: characteristic zero is not decoration.** Over `ZMod 2` the polynomials `1`
and `X ^ 2` are linearly independent and every Wronskian of them vanishes, in either
normalisation; over `ZMod p` the same happens with `1` and `X ^ p`. -/
example : LinearIndependent (ZMod 2) ![(1 : (ZMod 2)[X]), X ^ 2] ∧
    wronskianDet ![(1 : (ZMod 2)[X]), X ^ 2] = 0 ∧
    hasseWronskianDet ![(1 : (ZMod 2)[X]), X ^ 2] = 0 := by
  have hd : derivative (X ^ 2 : (ZMod 2)[X]) = 0 := by
    rw [derivative_X_pow, show ((2 : ℕ) : ZMod 2) = 0 by decide, map_zero, zero_mul]
  refine ⟨LinearIndependent.pair_iff.mpr fun s t h ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [Polynomial.coeff_one] using congrArg (fun p ↦ Polynomial.coeff p 0) h
  · simpa [Polynomial.coeff_one] using congrArg (fun p ↦ Polynomial.coeff p 2) h
  · rw [wronskianDet_fin_two, wronskian, hd]
    simp
  · simp only [hasseWronskianDet, hasseWronskianMatrix, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.val_zero,
      Fin.val_one, hasseDeriv_zero', hasseDeriv_one', derivative_one, hd, mul_zero, sub_zero]

end Polynomial

end

end
