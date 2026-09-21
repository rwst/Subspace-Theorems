/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GeneralizedWronskian
public import DiophantineApproximation.IndexRename
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The separation of the last variable, and the two Wronskians

Roth's lemma is an induction on the number of variables, and the inductive step splits off one
variable. The split is a *tensor decomposition*: a nonzero `P` in `Fin (m + 1)` variables is
`∑ l, f l * g l` with `f l` in the first `m` variables, `g l` in the last, and **both** families
linearly independent over `K`. The number `p` of terms is the rank of the space spanned by the
coefficients of `P` read as a polynomial in the separated variable, so `p ≤ degreeOf 0 P + 1`.

The matrix of Hasse derivatives `∂_(μ i + ν j) P` then factors as a product of two matrices, one
carrying only the `f`'s and one only the `g`'s, so its determinant is the product of a
generalized Wronskian of the `f`'s and one of the `g`'s. That is the whole of Bombieri–Gubler's
proof of Lemma 6.3.7 that is not an estimate.

## Main results

* `MvPolynomial.exists_tensor_decomposition`: the decomposition, with both families independent.
* `MvPolynomial.det_hasseDeriv_eq_mul`: the determinant of the matrix of Hasse derivatives is the
  product of the two generalized Wronskians.

## Implementation notes

⚠ **The separated variable is `0` and not the last one.** Mathlib's `MvPolynomial.finSuccEquiv`
splits off `X 0`, and Roth's lemma separates the variable of *smallest* degree; so the induction
runs with the degrees **increasing**, `d j ≤ σ * d (j + 1)`, and the book's decreasing statement
is obtained once at the end by renaming along `Fin.rev`.

⚠ **The independence of the second family is not an extra construction but a consequence of
choosing the first one to be a basis.** If `∑ l, λ l * g l = 0` then the functional
`∑ l, λ l * (b.coord l)` kills every coefficient of `P`, hence the whole span, hence each basis
vector, so `λ = 0`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Finsupp Function

/-! ### A finite family, its independent core and the coefficients that express it -/

namespace Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- **A finite family is expressed by a linearly independent one of no greater size, and the
coefficients that do it are jointly nondegenerate.** The last clause is what makes the second
family of Roth's decomposition linearly independent: a linear relation among the coefficient
*columns* is a linear functional killing every member of the family, hence the span, hence every
basis vector. -/
theorem exists_basis_repr {n : ℕ} (c : Fin n → M) :
    ∃ (p : ℕ) (f : Fin p → M) (a : Fin n → Fin p → K),
      p ≤ n ∧ LinearIndependent K f ∧ (∀ k, c k = ∑ l, a k l • f l) ∧
      ∀ lam : Fin p → K, (∀ k, ∑ l, lam l * a k l = 0) → lam = 0 := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  have : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range c)
  set p := Module.finrank K W with hp
  set b : Module.Basis (Fin p) K W := Module.finBasis K W with hb
  set c' : Fin n → W := fun k ↦ ⟨c k, Submodule.subset_span ⟨k, rfl⟩⟩ with hc'
  have hspan : Submodule.span K (Set.range c') = ⊤ := by
    refine Submodule.map_injective_of_injective W.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_subtype_top]
    congr 1
    rw [← Set.range_comp]
    rfl
  refine ⟨p, fun l ↦ (b l : M), fun k l ↦ b.repr (c' k) l,
    le_of_le_of_eq (finrank_range_le_card c) (Fintype.card_fin n),
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), fun k ↦ ?_, fun lam hlam ↦ ?_⟩
  · have := congrArg (W.subtype) (b.sum_repr (c' k))
    rw [map_sum] at this
    simpa using this.symm
  · set ψ : W →ₗ[K] K := (Finsupp.linearCombination K lam).comp b.repr.toLinearMap with hψ
    have hker : ∀ k, c' k ∈ LinearMap.ker ψ := by
      intro k
      simp only [LinearMap.mem_ker, hψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype _ _ (fun i ↦ zero_smul K (lam i))]
      simp only [smul_eq_mul]
      simpa [mul_comm] using hlam k
    have htop : LinearMap.ker ψ = ⊤ :=
      top_le_iff.mp (hspan ▸ Submodule.span_le.mpr (Set.range_subset_iff.mpr hker))
    funext l
    have hbl : ψ (b l) = lam l := by
      simp [hψ, Module.Basis.repr_self, Finsupp.linearCombination_single]
    rw [← hbl]
    exact LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top)

end Module

namespace MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- The embedding of the separated variable: `Fin 1` onto the index `0`. -/
def lastVar (m : ℕ) : Fin 1 → Fin (m + 1) := fun _ ↦ 0

theorem lastVar_injective (m : ℕ) : Injective (lastVar m) :=
  fun a b _ ↦ Subsingleton.elim a b

@[simp]
theorem lastVar_apply (m : ℕ) (i : Fin 1) : lastVar m i = 0 := rfl

theorem range_lastVar (m : ℕ) : Set.range (lastVar m) = {0} := by
  ext j
  exact ⟨fun ⟨_, h⟩ ↦ h ▸ rfl, fun h ↦ ⟨0, h ▸ rfl⟩⟩

theorem notMem_range_lastVar {j : Fin (m + 1)} (hj : j ≠ 0) : j ∉ Set.range (lastVar m) := by
  rw [range_lastVar]
  simpa using hj

theorem zero_notMem_range_succ : (0 : Fin (m + 1)) ∉ Set.range (Fin.succ : Fin m → Fin (m + 1)) :=
  fun ⟨i, hi⟩ ↦ absurd hi (Fin.succ_ne_zero i)

/-! ### The tensor decomposition -/

section Decomposition

/-- The image of a polynomial in the first `m` variables under `MvPolynomial.finSuccEquiv` is a
constant. -/
theorem finSuccEquiv_rename_succ (q : MvPolynomial (Fin m) K) :
    finSuccEquiv K m (rename Fin.succ q) = Polynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C r => rw [rename_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
      Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | mul_X a j ha => rw [map_mul, rename_X, map_mul, ha, finSuccEquiv_X_succ, ← map_mul]

/-- `P` is the sum of its coefficients along the separated variable. -/
theorem eq_sum_rename_succ_mul_pow (P : MvPolynomial (Fin (m + 1)) K) (N : ℕ)
    (hN : (finSuccEquiv K m P).natDegree < N + 1) :
    P = ∑ k ∈ Finset.range (N + 1),
      rename Fin.succ ((finSuccEquiv K m P).coeff k)
        * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ k := by
  refine (finSuccEquiv K m).injective ?_
  rw [map_sum]
  simp only [map_mul, map_pow, finSuccEquiv_rename_succ, finSuccEquiv_X_zero]
  simp only [Polynomial.C_mul_X_pow_eq_monomial]
  exact Polynomial.as_sum_range' _ _ hN

/-- A monomial in the separated variable, renamed into the big polynomial ring. -/
theorem rename_lastVar_monomial (k : ℕ) (x : K) :
    rename (lastVar m) (monomial (Finsupp.single 0 k) x : MvPolynomial (Fin 1) K)
      = C x * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ k := by
  rw [rename_monomial, Finsupp.mapDomain_single, lastVar_apply, monomial_eq,
    Finsupp.prod_single_index (by rw [pow_zero])]

/-- The coefficients of a polynomial in one variable written as a sum of monomials. -/
theorem coeff_sum_monomial_single {n : ℕ} (u : Fin n → K) (k : Fin n) :
    (∑ j : Fin n, monomial (Finsupp.single (0 : Fin 1) (j : ℕ)) (u j)).coeff
        (Finsupp.single 0 (k : ℕ)) = u k := by
  classical
  rw [coeff_sum, Finset.sum_eq_single k]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro j _ hj
    refine (coeff_monomial _ _ _).trans (ite_eq_right fun h ↦ hj ?_)
    exact Fin.val_injective (Finsupp.single_injective 0 h)
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **The tensor decomposition of a polynomial along the variable `X 0`.** -/
theorem exists_tensor_decomposition {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0) :
    ∃ (p : ℕ) (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K),
      0 < p ∧ p ≤ P.degreeOf 0 + 1 ∧ LinearIndependent K f ∧ LinearIndependent K g ∧
      P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l) := by
  classical
  obtain ⟨p, f, a, hple, hf, hrepr, hnd⟩ := Module.exists_basis_repr (K := K)
    (fun k : Fin (P.degreeOf 0 + 1) ↦ (finSuccEquiv K m P).coeff (k : ℕ))
  set g : Fin p → MvPolynomial (Fin 1) K :=
    fun l ↦ ∑ k : Fin (P.degreeOf 0 + 1), monomial (Finsupp.single 0 (k : ℕ)) (a k l) with hg
  have hgrename : ∀ l, rename (lastVar m) (g l)
      = ∑ k : Fin (P.degreeOf 0 + 1),
        C (a k l) * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ (k : ℕ) := by
    intro l
    rw [hg, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ rename_lastVar_monomial _ _
  have hdecomp : P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l) := by
    rw [eq_sum_rename_succ_mul_pow P (P.degreeOf 0) (by rw [natDegree_finSuccEquiv]; omega),
      ← Fin.sum_univ_eq_sum_range (fun k ↦ rename Fin.succ ((finSuccEquiv K m P).coeff k)
        * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ k)]
    simp only [hgrename, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hrepr k, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    ring
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h
      exact absurd (by simpa using hdecomp) hP
    · exact h
  refine ⟨p, f, g, hp0, hple, hf, ?_, hdecomp⟩
  refine Fintype.linearIndependent_iff.mpr fun lam hlam ↦ ?_
  have hcoeff : ∀ k : Fin (P.degreeOf 0 + 1), ∑ l, lam l * a k l = 0 := by
    intro k
    have := congrArg (fun Q : MvPolynomial (Fin 1) K ↦ Q.coeff (Finsupp.single 0 (k : ℕ))) hlam
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at this
    have h2 : ∑ l, lam l * (g l).coeff (Finsupp.single 0 (k : ℕ)) = 0 := by simpa using this
    rw [← h2]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [hg, coeff_sum_monomial_single]
  exact congrFun (hnd lam hcoeff)

end Decomposition

/-! ### The determinant of the matrix of Hasse derivatives -/

section Determinant

/-- A renamed order does not reach the variables outside the range of the renaming. -/
theorem mapDomain_succ_apply_zero (ρ : Fin m →₀ ℕ) :
    (ρ.mapDomain (Fin.succ : Fin m → Fin (m + 1))) 0 = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ zero_notMem_range_succ

theorem mapDomain_lastVar_apply_ne (τ : Fin 1 →₀ ℕ) {j : Fin (m + 1)} (hj : j ≠ 0) :
    (τ.mapDomain (lastVar m)) j = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (notMem_range_lastVar hj)

/-- Every term of the Leibniz expansion other than the split one vanishes: its order reaches
into the wrong variable set. -/
theorem hasseDeriv_rename_mul_eq_zero_of_ne {ρ : Fin m →₀ ℕ} {τ : Fin 1 →₀ ℕ}
    (u : MvPolynomial (Fin m) K) (w : MvPolynomial (Fin 1) K) {x y : Fin (m + 1) →₀ ℕ}
    (hxy : x + y = ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m))
    (hne : (x, y) ≠ (ρ.mapDomain Fin.succ, τ.mapDomain (lastVar m))) :
    hasseDeriv x (rename Fin.succ u) * hasseDeriv y (rename (lastVar m) w) = 0 := by
  by_cases hx0 : x 0 = 0
  swap
  · rw [hasseDeriv_rename_eq_zero hx0 zero_notMem_range_succ, zero_mul]
  by_cases hy : ∃ j, j ≠ 0 ∧ y j ≠ 0
  · obtain ⟨j, hj, hyj⟩ := hy
    rw [hasseDeriv_rename_eq_zero hyj (notMem_range_lastVar hj), mul_zero]
  · refine absurd ?_ hne
    push Not at hy
    have hyt : y = τ.mapDomain (lastVar m) := by
      refine Finsupp.ext fun j ↦ ?_
      rcases eq_or_ne j 0 with rfl | hj
      · have h0 : x 0 + y 0 = (ρ.mapDomain Fin.succ) 0 + (τ.mapDomain (lastVar m)) 0 := by
          rw [← Finsupp.add_apply, ← Finsupp.add_apply, hxy]
        rw [hx0, mapDomain_succ_apply_zero] at h0
        omega
      · rw [hy j hj, mapDomain_lastVar_apply_ne τ hj]
    exact Prod.ext (add_right_cancel (hxy.trans (by rw [hyt]))) hyt

/-- **A Hasse derivative of an order split between two disjoint variable sets acts factor by
factor.** -/
theorem hasseDeriv_add_rename_mul (ρ : Fin m →₀ ℕ) (τ : Fin 1 →₀ ℕ)
    (u : MvPolynomial (Fin m) K) (w : MvPolynomial (Fin 1) K) :
    hasseDeriv (ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m))
        (rename Fin.succ u * rename (lastVar m) w)
      = rename Fin.succ (hasseDeriv ρ u) * rename (lastVar m) (hasseDeriv τ w) := by
  rw [hasseDeriv_mul]
  have hmem : (ρ.mapDomain Fin.succ, τ.mapDomain (lastVar m))
      ∈ Finset.antidiagonal (ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m)) :=
    Finset.mem_antidiagonal.mpr rfl
  refine (Finset.sum_eq_single_of_mem _ hmem ?_).trans ?_
  · rintro ⟨x, y⟩ hxy hne
    exact hasseDeriv_rename_mul_eq_zero_of_ne u w (Finset.mem_antidiagonal.mp hxy) hne
  · rw [hasseDeriv_rename (Fin.succ_injective m), hasseDeriv_rename (lastVar_injective m)]

/-- The matrix of Hasse derivatives of `P` at the orders `μ i` in the first `m` variables and
`ν j` in the last. -/
def hasseDerivMatrix {p : ℕ} (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ))
    (P : MvPolynomial (Fin (m + 1)) K) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin (m + 1)) K) :=
  .of fun i j ↦ hasseDeriv ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar m)) P

@[simp]
theorem hasseDerivMatrix_apply {p : ℕ} (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ))
    (P : MvPolynomial (Fin (m + 1)) K) (i j : Fin p) :
    hasseDerivMatrix μ ν P i j
      = hasseDeriv ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar m)) P := rfl

/-- **The determinant of the matrix of Hasse derivatives is the product of the two generalized
Wronskians.** This is Cauchy's formula for the determinant of a product: the matrix is the
product of the Wronskian matrix of the `f` family and the transpose of the one of the `g`
family. -/
theorem det_hasseDerivMatrix {p : ℕ} {P : MvPolynomial (Fin (m + 1)) K}
    (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K)
    (hP : P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l))
    (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ)) :
    (hasseDerivMatrix μ ν P).det
      = rename Fin.succ (genWronskian μ f) * rename (lastVar m) (genWronskian ν g) := by
  have hmat : hasseDerivMatrix μ ν P
      = (genWronskianMatrix μ f).map (rename Fin.succ)
        * Matrix.transpose ((genWronskianMatrix ν g).map (rename (lastVar m))) := by
    ext i j
    have hij : hasseDerivMatrix μ ν P i j
        = ∑ l, rename Fin.succ (hasseDeriv (μ i) (f l))
            * rename (lastVar m) (hasseDeriv (ν j) (g l)) := by
      rw [hasseDerivMatrix_apply, hP, map_sum]
      exact Finset.sum_congr rfl fun l _ ↦ hasseDeriv_add_rename_mul _ _ _ _
    rw [hij, Matrix.mul_apply]
    rfl
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, genWronskian, genWronskian,
    AlgHom.map_det, AlgHom.map_det]
  rfl

end Determinant

end MvPolynomial

