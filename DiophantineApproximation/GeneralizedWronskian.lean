/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDerivTaylor
public import DiophantineApproximation.PolynomialIndex
public import DiophantineApproximation.Wronskian
public import Mathlib.Algebra.Polynomial.Roots

-- Used only by the acceptance criteria.
import Mathlib.Data.ZMod.Basic

/-!
# Generalized Wronskians

A **generalized Wronskian** of `φ 1, …, φ n : MvPolynomial σ K` is a determinant
`det (∂_(μ i) (φ j))` of Hasse derivatives in which the `i`-th row differentiates at total order
at most `i`. Bombieri–Gubler's Proposition 6.3.10 says that over a field of characteristic zero
some generalized Wronskian is nonzero **exactly** when the `φ j` are linearly independent over
the field. It is what Roth's lemma differentiates with: the bound on the orders is what keeps the
degrees of the Wronskian under control, so it is part of the statement and not an afterthought.

The proof of the hard half is the Kronecker substitution, and the chain rule it needs is the
Taylor formula of Layer 2.1 rather than a Faà di Bruno formula. Substituting `X s ↦ T ^ e s` for
weights `e` that separate the finitely many exponent vectors occurring in the `φ j` — a choice
that exists because the weights `e t = x ^ ι t` fail only when `x` is a root of one of finitely
many nonzero integer polynomials — is injective on their span, so the images are linearly
independent in `K[T]` and the one-variable criterion of
`DiophantineApproximation/Wronskian.lean` applies to them. Evaluating that one-variable Wronskian
at a point `a` where it survives, and writing `T` as `a + U`, turns the substitution into
`X s ↦ (a + U) ^ e s - a ^ e s`, a family of polynomials **with zero constant term**; so the
coefficient of `U ^ i` in the image of a monomial `X ^ ν` vanishes as soon as `i < |ν|`. Reading
the `i`-th row of the one-variable Wronskian matrix through the Taylor expansion of `φ j` at the
point `a ^ e` therefore expresses it as a `K`-linear combination of the vectors
`(∂_ν φ j)(a ^ e)` with `|ν| ≤ i`, and expanding the determinant multilinearly in its rows
produces a nonzero generalized Wronskian of admissible orders.

## Main results

* `MvPolynomial.genWronskianMatrix` and `MvPolynomial.genWronskian`: the definitions.
* `MvPolynomial.linearIndependent_iff_exists_genWronskian_ne_zero`: **the criterion**
  (Bombieri–Gubler, Proposition 6.3.10), with the two halves
  `MvPolynomial.exists_genWronskian_ne_zero` and
  `MvPolynomial.genWronskian_eq_zero_of_not_linearIndependent` separately.
* `Finsupp.exists_weight_injOn`: **Kronecker's choice of weights**, for an arbitrary finite set
  of exponent vectors in an arbitrary number of variables.
* `MvPolynomial.kroneckerHom` and `MvPolynomial.eq_zero_of_kroneckerHom_eq_zero`: the
  substitution and its injectivity, and `MvPolynomial.linearIndependent_kroneckerHom` with it.
* `MvPolynomial.kroneckerShift` and `MvPolynomial.eval_hasseDeriv_kroneckerHom`: **the chain
  rule** for the substitution, as a finite sum over orders of total degree at most the order of
  differentiation.

## Implementation notes

⚠ **Nothing is assumed about `σ`.** The variables are not finite in number, not ordered and not
well-ordered. The Kronecker weights only have to separate the finitely many exponent vectors that
actually occur, and they are produced by avoiding the roots of finitely many nonzero polynomials
over `ℤ` — an argument that never mentions the variable type. The usual base-`B` digit
construction would be no shorter and would need the variables enumerated.

⚠ **The order bound `|μ i| ≤ i` is not imposed, it falls out.** It is the statement that the
translated substitution has zero constant term in every variable, so that the coefficient of
`T ^ i` cannot see a derivative of order higher than `i`. This is the only place the *shape* of
the Kronecker substitution matters; any substitution by polynomials vanishing at the point would
do as well.

⚠ **Characteristic zero is used once**, in the one-variable criterion. The easy half holds over
any field, at every family of orders, and uses no property of the derivative at all — only that
`MvPolynomial σ K` is an integral domain. The rejection test is `1` and `X ^ 2` over `ZMod 2`:
independent, and every admissible generalized Wronskian vanishes.

⚠ **Hasse derivatives, not iterated `pderiv`.** In characteristic zero the two differ by the
factor `∏ j, (μ j)!` and the criterion is the same; the Hasse form is the one Layer 2.1 builds
and the one whose coefficient formula the chain rule above is a statement about.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 6.3.10, used in the proof of Roth's lemma (Lemma 6.3.7).

This is Layer 2.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

namespace Finsupp

/-- **Kronecker's choice of weights.** Any finite set of exponent vectors is separated by a single
`ℕ`-valued weight. The weights `e t = x ^ ι t`, for an `ι` injective on the variables that occur,
separate `μ` from `ν` unless `x` is a root of `∑ t, (μ t - ν t) X ^ ι t`, which is not the zero
polynomial; finitely many nonzero polynomials have finitely many roots between them. -/
theorem exists_weight_injOn {σ : Type*} (T : Finset (σ →₀ ℕ)) :
    ∃ e : σ → ℕ, ∀ μ ∈ T, ∀ ν ∈ T, weight e μ = weight e ν → μ = ν := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Finset σ, V = T.biUnion fun μ ↦ μ.support := ⟨_, rfl⟩
  have hsupp : ∀ μ ∈ T, ∀ t : σ, t ∉ V → μ t = 0 := by
    intro μ hμ t ht
    by_contra hc
    exact ht (hV ▸ Finset.mem_biUnion.mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hc⟩)
  obtain ⟨ι, hι⟩ : ∃ ι : σ → ℕ,
      ∀ t₁ ∈ V, ∀ t₂ ∈ V, ι t₁ = ι t₂ → t₁ = t₂ := by
    refine ⟨fun t ↦ if h : t ∈ V then ((Fintype.equivFin V) ⟨t, h⟩ : ℕ) else 0,
      fun t₁ h₁ t₂ h₂ h ↦ ?_⟩
    simp only [h₁, h₂, dite_true] at h
    exact congrArg Subtype.val ((Fintype.equivFin V).injective (Fin.val_injective h))
  obtain ⟨P, hP⟩ : ∃ P : (σ →₀ ℕ) → (σ →₀ ℕ) → Polynomial ℤ, P = fun μ ν ↦
      ∑ t ∈ V, Polynomial.C ((μ t : ℤ) - (ν t : ℤ)) * Polynomial.X ^ ι t := ⟨_, rfl⟩
  have hcoeff : ∀ μ ν : σ →₀ ℕ, ∀ t ∈ V, (P μ ν).coeff (ι t) = (μ t : ℤ) - (ν t : ℤ) := by
    intro μ ν t ht
    rw [hP]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single t (fun b hb hbt ↦ ?_) fun h ↦ absurd ht h]
    · simp
    · have hne : ι t ≠ ι b := fun h ↦ hbt (hι b hb t ht h.symm)
      simp [hne]
  have hPne : ∀ μ ∈ T, ∀ ν ∈ T, μ ≠ ν → P μ ν ≠ 0 := by
    intro μ hμ ν hν hne h
    refine hne (Finsupp.ext fun t ↦ ?_)
    by_cases ht : t ∈ V
    · have hc := hcoeff μ ν t ht
      rw [h, Polynomial.coeff_zero] at hc
      omega
    · rw [hsupp μ hμ t ht, hsupp ν hν t ht]
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℤ,
      Q = ∏ p ∈ (T ×ˢ T).filter fun p ↦ p.1 ≠ p.2, P p.1 p.2 := ⟨_, rfl⟩
  have hQne : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
    obtain ⟨hmem, hne⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    exact hPne _ h1 _ h2 hne
  obtain ⟨x, hx⟩ : ∃ x : ℕ, ¬ Q.IsRoot (x : ℤ) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hQne (Polynomial.eq_zero_of_infinite_isRoot Q ?_)
    exact Set.Infinite.mono (fun y hy ↦ by obtain ⟨m, rfl⟩ := hy; exact hcon m)
      (Set.infinite_range_of_injective fun a b h ↦ Nat.cast_injective h)
  have hw : ∀ μ ∈ T, ((weight (fun t ↦ x ^ ι t) μ : ℕ) : ℤ)
      = ∑ t ∈ V, (μ t : ℤ) * (x : ℤ) ^ ι t := by
    intro μ hμ
    rw [Finsupp.weight_apply, Finsupp.sum]
    push_cast
    refine Finset.sum_subset (fun t ht ↦ hV ▸ Finset.mem_biUnion.mpr ⟨μ, hμ, ht⟩) fun t _ ht ↦ ?_
    rw [Finsupp.notMem_support_iff.mp ht]
    simp
  refine ⟨fun t ↦ x ^ ι t, fun μ hμ ν hν h ↦ ?_⟩
  by_contra hne
  have hdvd : P μ ν ∣ Q :=
    hQ ▸ Finset.dvd_prod_of_mem (fun p ↦ P p.1 p.2)
      (show ((μ, ν) : (σ →₀ ℕ) × (σ →₀ ℕ)) ∈ _ from
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hμ, hν⟩, hne⟩)
  refine hx (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd ?_)
  have hev : (P μ ν).eval (x : ℤ) = ∑ t ∈ V, ((μ t : ℤ) - (ν t : ℤ)) * (x : ℤ) ^ ι t := by
    rw [hP]
    simp [Polynomial.eval_finsetSum]
  rw [hev]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, ← hw μ hμ, ← hw ν hν, h, sub_self]

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {n : ℕ}

/-! ### The Kronecker substitution -/

/-- The **Kronecker substitution** `X s ↦ T ^ e s`, which turns several variables into one. -/
def kroneckerHom (e : σ → ℕ) : MvPolynomial σ R →ₐ[R] Polynomial R :=
  aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s

/-- The **translated Kronecker substitution** `X s ↦ (T + a) ^ e s - a ^ e s`. Each image has zero
constant term, which is what bounds the orders of differentiation that can appear. -/
def kroneckerShift (e : σ → ℕ) (a : R) : MvPolynomial σ R →ₐ[R] Polynomial R :=
  aeval fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s)

@[simp]
theorem kroneckerHom_X (e : σ → ℕ) (s : σ) :
    kroneckerHom (R := R) e (X s) = Polynomial.X ^ e s := aeval_X _ _

-- Not a `simp` lemma: `simp` proves it from `algHom_C` and `Polynomial.algebraMap_eq`.
theorem kroneckerShift_C (e : σ → ℕ) (a r : R) :
    kroneckerShift e a (C r) = Polynomial.C r := by
  rw [kroneckerShift, aeval_C, Polynomial.algebraMap_eq]

/-- A monomial goes to a single power of `T`, with exponent the weight of its exponent vector. -/
theorem kroneckerHom_monomial (e : σ → ℕ) (μ : σ →₀ ℕ) (a : R) :
    kroneckerHom e (monomial μ a)
      = Polynomial.C a * Polynomial.X ^ Finsupp.weight e μ := by
  rw [kroneckerHom, aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod, Finsupp.weight_apply,
    Finsupp.sum]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun s _ ↦ by rw [← pow_mul, smul_eq_mul, mul_comm]

/-- **The Kronecker substitution is injective** on polynomials supported in a set of exponent
vectors whose weights it separates. -/
theorem eq_zero_of_kroneckerHom_eq_zero {e : σ → ℕ} {T : Finset (σ →₀ ℕ)}
    (hT : ∀ μ ∈ T, ∀ ν ∈ T, Finsupp.weight e μ = Finsupp.weight e ν → μ = ν)
    {f : MvPolynomial σ R} (hf : f.support ⊆ T) (h : kroneckerHom e f = 0) : f = 0 := by
  classical
  by_contra h0
  obtain ⟨ν, hν⟩ := support_nonempty.mpr h0
  have hcoeff : (kroneckerHom e f).coeff (Finsupp.weight e ν) = f.coeff ν := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single ν (fun μ hμ hne ↦ ?_) fun h ↦ absurd hν h]
    · rw [kroneckerHom_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp
    · have hw : Finsupp.weight e ν ≠ Finsupp.weight e μ := fun hw ↦
        hne (hT μ (hf hμ) ν (hf hν) hw.symm)
      rw [kroneckerHom_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hw]
  rw [h, Polynomial.coeff_zero] at hcoeff
  exact mem_support_iff.mp hν hcoeff.symm

/-- The Kronecker substitution preserves linear independence of a family it separates. -/
theorem linearIndependent_kroneckerHom {K : Type*} [Field K] {e : σ → ℕ} {T : Finset (σ →₀ ℕ)}
    (hT : ∀ μ ∈ T, ∀ ν ∈ T, Finsupp.weight e μ = Finsupp.weight e ν → μ = ν)
    {φ : Fin n → MvPolynomial σ K} (hsupp : ∀ j, (φ j).support ⊆ T)
    (hφ : LinearIndependent K φ) : LinearIndependent K fun j ↦ kroneckerHom e (φ j) := by
  classical
  rw [Fintype.linearIndependent_iff] at hφ ⊢
  intro c hc
  refine hφ c (eq_zero_of_kroneckerHom_eq_zero hT (fun μ hμ ↦ ?_) ?_)
  · by_contra hnot
    refine mem_support_iff.mp hμ ?_
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [smul_eq_C_mul, coeff_C_mul, notMem_support_iff.mp fun h ↦ hnot (hsupp j h), mul_zero]
  · rw [map_sum]
    simpa using hc

/-! ### The chain rule through the Kronecker substitution -/

/-- Substituting `T ^ e s` and then translating `T` is the same as translating the variables and
then substituting `(T + a) ^ e s - a ^ e s`. -/
theorem kroneckerShift_taylorAt (e : σ → ℕ) (a : R) (f : MvPolynomial σ R) :
    kroneckerShift e a (taylorAt (fun s ↦ a ^ e s) f)
      = Polynomial.taylor a (kroneckerHom e f) := by
  have h : (kroneckerShift e a).comp (taylorAt fun s ↦ a ^ e s)
      = (Polynomial.aeval (Polynomial.X + Polynomial.C a)).comp (kroneckerHom (R := R) e) := by
    refine algHom_ext fun s ↦ ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, taylorAt_X, map_add, kroneckerShift_C,
      kroneckerShift, aeval_X, sub_add_cancel, kroneckerHom_X, map_pow, Polynomial.aeval_X]
  rw [Polynomial.taylor_apply, Polynomial.comp_eq_aeval, ← AlgHom.comp_apply, h,
    AlgHom.comp_apply]

/-- The image of a monomial under the translated substitution is divisible by `T ^ degree`, so it
has no coefficient below that degree: differentiating `i` times in one variable can only see
derivatives of total order at most `i` in several. -/
theorem coeff_kroneckerShift_monomial_eq_zero (e : σ → ℕ) (a : R) (ν : σ →₀ ℕ) {i : ℕ}
    (hi : i < ν.degree) : (kroneckerShift e a (monomial ν (1 : R))).coeff i = 0 := by
  refine Polynomial.X_pow_dvd_iff.mp ?_ i hi
  rw [kroneckerShift, aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun s _ ↦ pow_dvd_pow_of_dvd ?_ _
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- **The chain rule.** A one-variable Hasse derivative of the Kronecker substitution, evaluated at
`a`, is a fixed linear combination of the several-variable Hasse derivatives of total order at
most `i`, evaluated at the point `a ^ e`. -/
theorem eval_hasseDeriv_kroneckerHom (e : σ → ℕ) (a : R) (f : MvPolynomial σ R)
    (s : Finset (σ →₀ ℕ)) (hs : (taylorAt (fun t ↦ a ^ e t) f).support ⊆ s) (i : ℕ) :
    Polynomial.eval a (Polynomial.hasseDeriv i (kroneckerHom e f))
      = ∑ ν ∈ s.filter fun ν ↦ ν.degree ≤ i,
          (kroneckerShift e a (monomial ν (1 : R))).coeff i
            * eval (fun t ↦ a ^ e t) (hasseDeriv ν f) := by
  classical
  rw [Finset.sum_filter_of_ne fun ν _ hne ↦ ?_]
  · rw [← Polynomial.taylor_coeff, ← kroneckerShift_taylorAt]
    conv_lhs => rw [show taylorAt (fun t ↦ a ^ e t) f
      = ∑ ν ∈ s, monomial ν ((taylorAt (fun t ↦ a ^ e t) f).coeff ν) from
        ((taylorAt (fun t ↦ a ^ e t) f).as_sum).trans
          (Finset.sum_subset hs fun ν _ hν ↦ by
            rw [notMem_support_iff.mp hν, monomial_zero])]
    rw [map_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [← coeff_taylorAt, show (monomial ν ((taylorAt (fun t ↦ a ^ e t) f).coeff ν) :
        MvPolynomial σ R) = C ((taylorAt (fun t ↦ a ^ e t) f).coeff ν) * monomial ν 1 from by
      rw [C_mul_monomial, mul_one], map_mul, kroneckerShift_C, Polynomial.coeff_C_mul, mul_comm]
  · by_contra hdeg
    exact hne (by rw [coeff_kroneckerShift_monomial_eq_zero e a ν (by omega), zero_mul])

/-! ### The generalized Wronskian -/

/-- The **generalized Wronskian matrix** (Bombieri–Gubler, Proposition 6.3.10): the entry
`(i, j)` is the `μ i`-th Hasse derivative of `φ j`. -/
def genWronskianMatrix (μ : Fin n → (σ →₀ ℕ)) (φ : Fin n → MvPolynomial σ R) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ R) := .of fun i j ↦ hasseDeriv (μ i) (φ j)

/-- The **generalized Wronskian** of a family of polynomials at a family of orders. -/
def genWronskian (μ : Fin n → (σ →₀ ℕ)) (φ : Fin n → MvPolynomial σ R) : MvPolynomial σ R :=
  (genWronskianMatrix μ φ).det

@[simp]
theorem genWronskianMatrix_apply (μ : Fin n → (σ →₀ ℕ)) (φ : Fin n → MvPolynomial σ R)
    (i j : Fin n) : genWronskianMatrix μ φ i j = hasseDeriv (μ i) (φ j) := rfl

/-- **The easy half**, in any characteristic and at every family of orders: a linear relation
between the polynomials is a linear relation between the columns of the matrix, which kills the
determinant over the integral domain `MvPolynomial σ K`. -/
theorem genWronskian_eq_zero_of_not_linearIndependent {K : Type*} [Field K]
    {φ : Fin n → MvPolynomial σ K} (hφ : ¬ LinearIndependent K φ) (μ : Fin n → (σ →₀ ℕ)) :
    genWronskian μ φ = 0 := by
  classical
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hφ
  have hker : (genWronskianMatrix μ φ).mulVec (fun j ↦ C (c j)) = 0 := by
    funext i
    have hz : (hasseDeriv (μ i)) (∑ j, c j • φ j) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hz
    simp only [Matrix.mulVec, dotProduct, genWronskianMatrix_apply, Pi.zero_apply]
    rw [← hz]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_C_mul, mul_comm]
  exact Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun j ↦ C (c j), fun h ↦ hi₀ (by simpa using congrFun h i₀), hker⟩

/-- **The hard half.** A linearly independent family over a field of characteristic zero has a
nonzero generalized Wronskian of admissible orders: substitute `X s ↦ T ^ e s` for weights that
separate the exponents occurring, apply the one-variable criterion to the images, evaluate at a
point where that Wronskian survives, and expand each row in the several-variable Hasse derivatives
the chain rule produces — all of total order at most the row index. -/
theorem exists_genWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {φ : Fin n → MvPolynomial σ K} (hφ : LinearIndependent K φ) :
    ∃ μ : Fin n → (σ →₀ ℕ), (∀ i, (μ i).degree ≤ (i : ℕ)) ∧ genWronskian μ φ ≠ 0 := by
  classical
  obtain ⟨e, he⟩ := Finsupp.exists_weight_injOn (Finset.univ.biUnion fun j ↦ (φ j).support)
  have hsupp : ∀ j, (φ j).support ⊆ Finset.univ.biUnion fun j ↦ (φ j).support :=
    fun j μ hμ ↦ Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hμ⟩
  have hW := Polynomial.hasseWronskianDet_ne_zero (linearIndependent_kroneckerHom he hsupp hφ)
  obtain ⟨a, ha⟩ : ∃ a : K, Polynomial.eval a
      (Polynomial.hasseWronskianDet fun j ↦ kroneckerHom e (φ j)) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    refine hW (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    have huniv : {x : K | (Polynomial.hasseWronskianDet fun j ↦ kroneckerHom e (φ j)).IsRoot x}
        = Set.univ := Set.eq_univ_of_forall fun x ↦ hcon x
    rw [huniv]
    exact Set.infinite_univ
  obtain ⟨S, hS⟩ : ∃ S : Finset (σ →₀ ℕ),
      S = Finset.univ.biUnion fun j ↦ (taylorAt (fun t ↦ a ^ e t) (φ j)).support := ⟨_, rfl⟩
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Fin n → Finset (σ →₀ ℕ),
      Sf = fun (i : Fin n) ↦ S.filter fun ν ↦ ν.degree ≤ (i : ℕ) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → (σ →₀ ℕ) → K,
      lam = fun (i : Fin n) ν ↦ (kroneckerShift e a (monomial ν (1 : K))).coeff (i : ℕ) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : (σ →₀ ℕ) → (Fin n → K),
      v = fun ν j ↦ eval (fun t ↦ a ^ e t) (hasseDeriv ν (φ j)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) K, A = (Polynomial.hasseWronskianMatrix
      fun j ↦ kroneckerHom e (φ j)).map (Polynomial.evalRingHom a) := ⟨_, rfl⟩
  have hAdet : A.det ≠ 0 := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ha
  have hrows : (fun i ↦ A i) = fun i ↦ ∑ ν ∈ Sf i, lam i ν • v ν := by
    funext i
    funext j
    rw [hA]
    simp only [Matrix.map_apply, Polynomial.hasseWronskianMatrix_apply,
      Polynomial.coe_evalRingHom]
    rw [eval_hasseDeriv_kroneckerHom e a (φ j) S (hS ▸ fun ν hν ↦
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hν⟩) (i : ℕ)]
    rw [hSf, hlam, hv, Finset.sum_apply]
    rfl
  have hexp : A.det = ∑ p ∈ Fintype.piFinset Sf,
      (∏ i, lam i (p i)) * (Matrix.of fun i j ↦ v (p i) j).det := by
    calc A.det
        = Matrix.detRowAlternating.toMultilinearMap (fun i ↦ ∑ ν ∈ Sf i, lam i ν • v ν) := by
          rw [← hrows]; rfl
      _ = ∑ p ∈ Fintype.piFinset Sf,
            Matrix.detRowAlternating.toMultilinearMap (fun i ↦ lam i (p i) • v (p i)) :=
          MultilinearMap.map_sum_finset _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [MultilinearMap.map_smul_univ]
          rfl
  rw [hexp] at hAdet
  obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hAdet
  refine ⟨p, fun i ↦ ?_, fun hz ↦ right_ne_zero_of_mul hpne ?_⟩
  · rw [hSf] at hp
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  · have hmat : (Matrix.of fun i j ↦ v (p i) j)
        = (genWronskianMatrix p φ).map (eval fun t ↦ a ^ e t) := by
      refine Matrix.ext fun i j ↦ ?_
      rw [hv]
      rfl
    rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← genWronskian, hz, map_zero]

/-- **The generalized Wronskian criterion** (Bombieri–Gubler, Proposition 6.3.10). Over a field of
characteristic zero, polynomials in any number of variables are linearly independent over the
field exactly when some generalized Wronskian, the `i`-th row differentiating at total order at
most `i`, is not the zero polynomial. -/
theorem linearIndependent_iff_exists_genWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    (φ : Fin n → MvPolynomial σ K) :
    LinearIndependent K φ ↔
      ∃ μ : Fin n → (σ →₀ ℕ), (∀ i, (μ i).degree ≤ (i : ℕ)) ∧ genWronskian μ φ ≠ 0 := by
  refine ⟨exists_genWronskian_ne_zero, fun ⟨μ, _, hμ⟩ ↦ ?_⟩
  by_contra hn
  exact hμ (genWronskian_eq_zero_of_not_linearIndependent hn μ)

/-! ### Acceptance criteria -/

/-- **Acceptance test (the roadmap's): `1, X, Y` have a nonzero generalized Wronskian**, namely
the determinant of `id, ∂_X, ∂_Y`, which is `1`. -/
example : genWronskian ![0, Finsupp.single 0 1, Finsupp.single 1 1]
      (![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) ℚ) = 1 ∧
    ∀ i, ((![0, Finsupp.single 0 1, Finsupp.single 1 1] : Fin 3 → (Fin 2 →₀ ℕ)) i).degree
      ≤ (i : ℕ) := by
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [genWronskian, Matrix.det_fin_three]
    simp [genWronskianMatrix, hasseDeriv_single_one, pderiv_X]
  · fin_cases i <;> simp [Finsupp.degree_single]

/-- **Acceptance test (the roadmap's): every generalized Wronskian of `X, Y, X + Y` vanishes**,
at every family of orders, because the three are linearly dependent. -/
example (μ : Fin 3 → (Fin 2 →₀ ℕ)) :
    genWronskian μ (![X 0, X 1, X 0 + X 1] : Fin 3 → MvPolynomial (Fin 2) ℚ) = 0 := by
  refine genWronskian_eq_zero_of_not_linearIndependent (Fintype.not_linearIndependent_iff.mpr
    ⟨![1, 1, -1], ?_, 0, by norm_num⟩) μ
  simp [Fin.sum_univ_three]
  ring

/-- **Rejection test (the roadmap's): characteristic zero is not decoration.** Over `ZMod 2` the
polynomials `1` and `X ^ 2` are linearly independent, and every generalized Wronskian of them
with admissible orders vanishes — the second row is either a repeat of the first or zero. -/
example : LinearIndependent (ZMod 2) (![1, X () ^ 2] : Fin 2 → MvPolynomial Unit (ZMod 2)) ∧
    ∀ μ : Fin 2 → (Unit →₀ ℕ), (∀ i, (μ i).degree ≤ (i : ℕ)) →
      genWronskian μ (![1, X () ^ 2] : Fin 2 → MvPolynomial Unit (ZMod 2)) = 0 := by
  have hX : (X () ^ 2 : MvPolynomial Unit (ZMod 2)) = monomial (Finsupp.single () 2) 1 := by
    rw [X_pow_eq_monomial]
  have hpd : pderiv () (X () ^ 2 : MvPolynomial Unit (ZMod 2)) = 0 := by
    have h2 : (X () + X () : MvPolynomial Unit (ZMod 2)) = 0 := by
      calc (X () + X () : MvPolynomial Unit (ZMod 2))
          = C (1 + 1) * X () := by rw [C_add, add_mul, C_1, one_mul]
        _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from by decide, C_0, zero_mul]
    rw [pow_two, pderiv_mul, pderiv_X_self, one_mul, mul_one, h2]
  refine ⟨LinearIndependent.pair_iff.mpr fun s t h ↦ ⟨?_, ?_⟩, fun μ hμ ↦ ?_⟩
  · have := congrArg (fun p ↦ p.coeff 0) h
    simpa [hX, smul_eq_C_mul, coeff_monomial, Finsupp.single_eq_zero] using this
  · have hne : ¬ (0 : Unit →₀ ℕ) = Finsupp.single () 2 := fun hc ↦ by
      simpa using Finsupp.single_eq_zero.mp hc.symm
    have := congrArg (fun p ↦ p.coeff (Finsupp.single () 2)) h
    simpa [hX, smul_eq_C_mul, coeff_monomial, coeff_C, hne] using this
  · have h0 : μ 0 = 0 := by
      have := hμ 0
      simp only [Fin.isValue, Fin.val_zero, Nat.le_zero] at this
      exact (Finsupp.degree_eq_zero_iff (μ 0)).mp this
    rw [genWronskian, Matrix.det_fin_two]
    rcases eq_or_ne (μ 1) 0 with h1 | h1
    · simp [genWronskianMatrix, h0, h1, mul_comm]
    · have hval : μ 1 = Finsupp.single () 1 := by
        have hu := Finsupp.unique_single (μ 1)
        have hle : (μ 1) default ≤ 1 := by
          have := hμ 1
          rwa [hu, Finsupp.degree_single, Fin.val_one] at this
        have hne : (μ 1) default ≠ 0 := fun h ↦ h1 (by rw [hu, h, Finsupp.single_zero])
        rw [hu, show (μ 1) default = 1 by omega]
      simp [genWronskianMatrix, h0, hval, hasseDeriv_single_one, hpd]

end MvPolynomial

end

end
