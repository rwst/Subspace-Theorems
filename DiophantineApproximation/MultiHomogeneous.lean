/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDeriv
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Multihomogeneous polynomials and the substitution by linear forms

The Subspace Theorem's auxiliary polynomial lives on a product of projective spaces: it is
multihomogeneous of degree `d h` in each of `m` blocks `X h : ι → K` of `n + 1` variables, and
what is read off it is its expansion in the monomials

`∏ h, ∏ i, (L v i (X h)) ^ (J h i)`

in a system of independent linear forms `L v` attached to a place `v`. This file builds that
machinery over an arbitrary commutative ring: the multidegree, the block substitution, and the
one fact about Hasse derivatives that the vanishing statement of Layer 5.2 needs.

The block substitution is `X (h, j) ↦ ∑ i, A j i • X (h, i)`, the same change of coordinates in
every block, and the expansion coefficients `a(L; J; I)` of Bombieri–Gubler 7.5.14 are the
coefficients of `blockSubst A⁻¹ (hasseDeriv I P)`, with `A` the matrix of the forms.

## Main definitions

* `MvPolynomial.IsMultiHomogeneous`: multihomogeneity of multidegree `d : κ → ℕ` for a polynomial
  in the variables `κ × ι`.
* `MvPolynomial.blockSubst`: the block-wise linear substitution, as an algebra map.
* `MvPolynomial.multiMons`: the monomials of multidegree `d`, the coefficient space of `P(d)`.
* `MvPolynomial.ofMulti`: the polynomial named by a coefficient vector on `multiMons d`.

## Main results

* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`: **the key vanishing statement** — a
  coefficient of the expansion of `∂_I P` vanishes as soon as the coefficients of `P` vanish at
  all the orders `J + I'` with `I'` of the same block degrees as `I`.
* `MvPolynomial.pderiv_blockSubst`: the chain rule for the block substitution, which is what that
  statement is proved from.
* `MvPolynomial.IsMultiHomogeneous.blockSubst`: a linear change of coordinates inside the blocks
  preserves the multidegree.
* `MvPolynomial.IsMultiHomogeneous.hasseDeriv`: a Hasse derivative of order `I` is
  multihomogeneous of multidegree `d h - ∑ i, I (h, i)` — the block degrees drop separately, which
  is what the upper half of Lemma 7.5.15 is read off.
* `MvPolynomial.IsWeightedHomogeneous.aeval`: the general statement behind it — a substitution
  that respects the weights preserves weighted homogeneity.
* `MvPolynomial.card_multiMons`, `MvPolynomial.card_multiMons_le` and
  `MvPolynomial.multiMons_nonempty`: the count of the monomials of multidegree `d`, exactly as a
  product over the blocks and crudely as `∏ t : κ × ι, (d t.1 + 1)`.
* `MvPolynomial.coeff_blockSubst_ofMulti`: the coefficient of a substituted auxiliary polynomial
  as a linear form in the unknowns, which is the row of the condition matrix of Layer 5.2.

## Implementation notes

⚠ **Multihomogeneity is Mathlib's weighted homogeneity for the weight `Pi.single h 1`**, and
`MvPolynomial.isMultiHomogeneous_iff` is the dictionary. The predicate is stated separately
because every user reads it as "degree `d h` in the `h`-th block", which is a `Finset.sum` over
`ι` rather than a `Finsupp.weight`; the closure properties are imported through the dictionary.

⚠ **The chain rule is what makes the vanishing statement true, and it is not the trivial one.**
Bombieri–Gubler differentiate in the *original* coordinates and expand in the *transformed* ones,
so `a(L; J; I)` is not `binom(J + I, I) · a(L; J + I; 0)`: it is a combination of those
coefficients over all orders `I'` with the same block degrees as `I`, because `∂ / ∂x (h, k)` is
the combination `∑ i, A i k ∂ / ∂y (h, i)`. The proof below is an induction on the order of the
derivative that never names the combination: one derivative is peeled off with
`MvPolynomial.hasseDeriv_comp`, the chain rule turns it into a sum over the block, and the
inductive hypothesis is applied to each summand. The constant `hasseDeriv_comp` produces is a
positive natural number, which is why the field has to have characteristic zero.

⚠ **The monomials of multidegree `d` are indexed by a `Finset`, not a subtype**, so that they
carry a `Fintype` instance without a decidability argument and so that
`MvPolynomial.card_multiMons` hands the counting of Layer 5.2 straight to
`Fintype.piFinset`, which is where the deviation estimate of
`DiophantineApproximation/MonomialDeviation.lean` counts.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.14.

This is part of Layer 5.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {κ ι R : Type*} [CommRing R] [Fintype ι]

/-- A polynomial in the blocks of variables `κ × ι` is **multihomogeneous of multidegree `d`**
when every monomial has degree `d h` in the `h`-th block of variables. -/
def IsMultiHomogeneous (d : κ → ℕ) (P : MvPolynomial (κ × ι) R) : Prop :=
  ∀ ⦃ν : κ × ι →₀ ℕ⦄, P.coeff ν ≠ 0 → ∀ h, ∑ i, ν (h, i) = d h

section Weight

variable [Finite κ] [DecidableEq κ]

/-- The weight that reads off the degree in each block of variables. -/
def blockWeight (κ ι : Type*) [DecidableEq κ] : κ × ι → (κ → ℕ) := fun p ↦ Pi.single p.1 1

theorem weight_blockWeight (ν : κ × ι →₀ ℕ) (h : κ) :
    Finsupp.weight (blockWeight κ ι) ν h = ∑ i, ν (h, i) := by
  have : Fintype κ := Fintype.ofFinite κ
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (g := fun h' ↦ if h' = h then ∑ i, ν (h', i) else 0)
    (fun h' _ ↦ ?_), Finset.sum_ite_eq' Finset.univ h]
  · simp
  · by_cases hh : h' = h
    · subst hh
      simp [blockWeight]
    · simp [blockWeight, hh]

theorem isMultiHomogeneous_iff {d : κ → ℕ} {P : MvPolynomial (κ × ι) R} :
    IsMultiHomogeneous d P ↔ IsWeightedHomogeneous (blockWeight κ ι) P d := by
  constructor
  · intro hP ν hν
    funext h
    rw [weight_blockWeight]
    exact hP hν h
  · intro hP ν hν h
    rw [← weight_blockWeight ν h, hP hν]

end Weight

/-! ### Weighted homogeneity under a substitution -/

section Aeval

variable {σ M : Type*} [AddCommMonoid M] {w : σ → M}

theorem IsWeightedHomogeneous.finset_prod {α : Type*} {s : Finset α}
    {f : α → MvPolynomial σ R} {m : α → M}
    (h : ∀ a ∈ s, IsWeightedHomogeneous w (f a) (m a)) :
    IsWeightedHomogeneous w (∏ a ∈ s, f a) (∑ a ∈ s, m a) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isWeightedHomogeneous_one (R := R) (σ := σ) w
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb))

theorem IsWeightedHomogeneous.finset_sum {α : Type*} {s : Finset α}
    {f : α → MvPolynomial σ R} {m : M}
    (h : ∀ a ∈ s, IsWeightedHomogeneous w (f a) m) :
    IsWeightedHomogeneous w (∑ a ∈ s, f a) m := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isWeightedHomogeneous_zero (R := R) (σ := σ) w m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb))

/-- **A substitution that respects the weights preserves weighted homogeneity.** The substituted
variables may live in another type, carrying their own weights: what is asked of the substitution
is that the polynomial put in place of `X s` be homogeneous of the weight of `s`. -/
theorem IsWeightedHomogeneous.aeval {τ : Type*} {w' : τ → M} {g : σ → MvPolynomial τ R}
    (hg : ∀ s, IsWeightedHomogeneous w' (g s) (w s)) {P : MvPolynomial σ R} {m : M}
    (hP : IsWeightedHomogeneous w P m) :
    IsWeightedHomogeneous w' (MvPolynomial.aeval g P) m := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.finset_sum fun ν hν ↦ ?_
  rw [aeval_monomial]
  have hprod : IsWeightedHomogeneous w' (ν.prod fun s k ↦ g s ^ k) m := by
    rw [Finsupp.prod]
    have := IsWeightedHomogeneous.finset_prod (w := w') (s := ν.support)
      (f := fun s ↦ g s ^ ν s) (m := fun s ↦ ν s • w s)
      (fun s _ ↦ (hg s).pow (ν s))
    have hw : ∑ a ∈ ν.support, ν a • w a = Finsupp.weight w ν := by
      rw [Finsupp.weight_apply, Finsupp.sum]
    rwa [hw, hP (mem_support_iff.mp hν)] at this
  simpa using hprod.C_mul _

end Aeval

/-! ### The block substitution -/

section BlockSubst

/-- The **block-wise linear substitution** `X (h, j) ↦ ∑ i, A j i • X (h, i)`: the same change of
coordinates in every block. -/
noncomputable def blockSubst (A : Matrix ι ι R) :
    MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ι) R :=
  aeval fun p : κ × ι ↦ ∑ i, C (A p.2 i) * X (p.1, i)

@[simp]
theorem blockSubst_X (A : Matrix ι ι R) (h : κ) (j : ι) :
    blockSubst A (X (h, j)) = ∑ i, C (A j i) * X ((h, i) : κ × ι) := by
  simp [blockSubst]

theorem blockSubst_comp (A B : Matrix ι ι R) (P : MvPolynomial (κ × ι) R) :
    blockSubst A (blockSubst B P) = blockSubst (B * A) P := by
  have : (blockSubst A).comp (blockSubst B)
      = (blockSubst (B * A) : MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ι) R) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, j⟩ := p
    rw [AlgHom.comp_apply, blockSubst_X, map_sum, blockSubst_X (B * A) h j]
    calc ∑ i, blockSubst A (C (B j i) * X ((h, i) : κ × ι))
        = ∑ i, ∑ l, C (B j i * A i l) * X ((h, l) : κ × ι) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_mul, MvPolynomial.algHom_C, blockSubst_X, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ ↦ by
            simp only [MvPolynomial.algebraMap_eq, map_mul]; ring
      _ = ∑ l, ∑ i, C (B j i * A i l) * X ((h, l) : κ × ι) := Finset.sum_comm
      _ = ∑ l, C ((B * A) j l) * X ((h, l) : κ × ι) := by
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [Matrix.mul_apply, ← Finset.sum_mul, ← map_sum]
  exact congrArg (fun f ↦ f P) this

variable [DecidableEq ι]

theorem blockSubst_one (P : MvPolynomial (κ × ι) R) :
    blockSubst (1 : Matrix ι ι R) P = P := by
  have : (blockSubst (1 : Matrix ι ι R)
      : MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ι) R) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, j⟩ := p
    rw [blockSubst_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  exact congrArg (fun f ↦ f P) this

theorem blockSubst_blockSubst {A M : Matrix ι ι R} (hMA : M * A = 1)
    (P : MvPolynomial (κ × ι) R) : blockSubst A (blockSubst M P) = P := by
  rw [blockSubst_comp, hMA, blockSubst_one]

omit [DecidableEq ι] in
variable [Finite κ] [DecidableEq κ] in
omit [DecidableEq κ] in
theorem IsMultiHomogeneous.blockSubst {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (A : Matrix ι ι R) :
    IsMultiHomogeneous d (MvPolynomial.blockSubst A P) := by
  classical
  rw [isMultiHomogeneous_iff] at hP ⊢
  refine IsWeightedHomogeneous.aeval (fun p ↦ ?_) hP
  obtain ⟨h, j⟩ := p
  refine IsWeightedHomogeneous.finset_sum fun i _ ↦ ?_
  have hX : IsWeightedHomogeneous (blockWeight κ ι)
      (X ((h, i) : κ × ι) : MvPolynomial (κ × ι) R) (blockWeight κ ι (h, i)) :=
    isWeightedHomogeneous_X R (blockWeight κ ι) (h, i)
  simpa [blockWeight] using hX.C_mul (A j i)

end BlockSubst

/-! ### The chain rule -/

section ChainRule

theorem pderiv_blockSubst (A : Matrix ι ι R) (h₀ : κ) (k : ι) (Q : MvPolynomial (κ × ι) R) :
    pderiv ((h₀, k) : κ × ι) (blockSubst A Q)
      = ∑ j, A j k • blockSubst A (pderiv ((h₀, j) : κ × ι) Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_add]
  | mul_X p s hp =>
      obtain ⟨h₁, j₁⟩ := s
      have hbX : blockSubst A (X ((h₁, j₁) : κ × ι)) = ∑ i, C (A j₁ i) * X ((h₁, i) : κ × ι) :=
        blockSubst_X A h₁ j₁
      have hd : pderiv ((h₀, k) : κ × ι) (∑ i, C (A j₁ i) * X ((h₁, i) : κ × ι))
          = if h₁ = h₀ then C (A j₁ k) else 0 := by
        rw [map_sum]
        by_cases hh : h₁ = h₀
        · subst hh
          rw [Finset.sum_eq_single k]
          · simp
          · intro i _ hik
            rw [pderiv_C_mul, pderiv_X_of_ne (by simp [hik]), mul_zero]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        · rw [ite_eq_right hh, Finset.sum_eq_zero]
          intro i _
          rw [pderiv_C_mul, pderiv_X_of_ne (by simp [hh]), mul_zero]
      rw [map_mul, pderiv_mul, hp, hbX, hd]
      have hrhs : ∀ j : ι,
          A j k • blockSubst A (pderiv ((h₀, j) : κ × ι) (p * X ((h₁, j₁) : κ × ι)))
          = A j k • (blockSubst A (pderiv ((h₀, j) : κ × ι) p)
              * ∑ i, C (A j₁ i) * X ((h₁, i) : κ × ι))
            + A j k • (blockSubst A p * (if (h₁, j₁) = ((h₀, j) : κ × ι) then 1 else 0)) := by
        intro j
        rw [pderiv_mul, map_add, map_mul, map_mul, hbX, smul_add]
        congr 2
        classical
        rw [pderiv_X]
        by_cases hij : (h₁, j₁) = ((h₀, j) : κ × ι) <;> simp [hij]
      rw [Finset.sum_congr rfl fun j _ ↦ hrhs j, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ smul_mul_assoc _ _ _
      · by_cases hh : h₁ = h₀
        · subst hh
          rw [Finset.sum_eq_single j₁]
          · simp [MvPolynomial.smul_eq_C_mul, mul_comm]
          · intro j _ hj
            simp [Ne.symm hj]
          · intro hj; exact absurd (Finset.mem_univ j₁) hj
        · rw [ite_eq_right hh, mul_zero, Finset.sum_eq_zero]
          intro j _
          simp [hh]

end ChainRule

/-! ### Vanishing of the expansion coefficients -/

section Vanishing

variable [DecidableEq κ]

theorem sum_single_block (h₀ : κ) (j : ι) (h : κ) :
    ∑ i, (Finsupp.single ((h₀, j) : κ × ι) 1) (h, i) = if h = h₀ then 1 else 0 := by
  by_cases hh : h = h₀
  · subst hh
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · rw [ite_eq_right hh, Finset.sum_eq_zero]
    intro i _
    have hne : ((h₀, j) : κ × ι) ≠ (h, i) := fun hc ↦ hh (congrArg Prod.fst hc).symm
    simp [hne]

variable {K : Type*} [Field K] [CharZero K] [DecidableEq ι] [Fintype κ]

omit [DecidableEq κ] in
/-- **The expansion coefficients of a Hasse derivative vanish where those of the polynomial do.**
The order of a derivative changes the block degrees by its own block degrees and nothing else, so
a coefficient of `∂_I P` in the `L`-monomials is a combination of the coefficients of `P` at the
orders `J + I'` with `I'` of the same block degrees as `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero {A M : Matrix ι ι K} (hAM : A * M = 1) :
    ∀ (N : ℕ) (I : κ × ι →₀ ℕ), ∑ t, I t = N →
      ∀ (Q : MvPolynomial (κ × ι) K) (J : κ × ι →₀ ℕ),
        (∀ I' : κ × ι →₀ ℕ, (∀ h, ∑ i, I' (h, i) = ∑ i, I (h, i)) → Q.coeff (J + I') = 0) →
        (blockSubst M (hasseDeriv I (blockSubst A Q))).coeff J = 0 := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro I hIN Q J hQ
    rcases eq_or_ne I 0 with rfl | hI0
    · rw [hasseDeriv_zero_apply, blockSubst_blockSubst hAM]
      simpa using hQ 0 (fun h ↦ rfl)
    · obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hI0
      obtain ⟨h₀, k⟩ := s
      set I'' : κ × ι →₀ ℕ := I - Finsupp.single ((h₀, k) : κ × ι) 1 with hI''def
      have hIs : 1 ≤ I (h₀, k) := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have hIeq : I'' + Finsupp.single ((h₀, k) : κ × ι) 1 = I := by
        ext t
        rcases eq_or_ne t ((h₀, k) : κ × ι) with rfl | ht
        · simp only [hI''def, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hI''def, Ne.symm ht]
      have hblk : ∀ h : κ, ∑ i, I (h, i) = ∑ i, I'' (h, i) + (if h = h₀ then 1 else 0) := by
        intro h
        rw [← hIeq]
        simp only [Finsupp.add_apply]
        rw [Finset.sum_add_distrib, sum_single_block]
      have hsingle : ∑ t : κ × ι, (Finsupp.single ((h₀, k) : κ × ι) 1) t = 1 := by
        rw [Finset.sum_eq_single ((h₀, k) : κ × ι)]
        · simp
        · intro t _ ht
          simp [Ne.symm ht]
        · intro ht; exact absurd (Finset.mem_univ ((h₀, k) : κ × ι)) ht
      have hdeg : ∑ t, I'' t < N := by
        have hsum := congrArg (fun f : κ × ι →₀ ℕ ↦ ∑ t, f t) hIeq
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hsingle] at hsum
        omega
      set c : ℕ := I''.prod fun j k' ↦ (k' + (Finsupp.single ((h₀, k) : κ × ι) 1) j).choose k'
        with hcdef
      have hc : 0 < c := by
        rw [hcdef, Finsupp.prod]
        exact Finset.prod_pos fun j _ ↦ Nat.choose_pos (Nat.le_add_right _ _)
      have hcomp : hasseDeriv I'' (hasseDeriv (Finsupp.single ((h₀, k) : κ × ι) 1)
          (blockSubst A Q)) = (c : ℕ) • hasseDeriv I (blockSubst A Q) := by
        rw [hasseDeriv_comp, hIeq]
      have hzero : (blockSubst M (hasseDeriv I'' (hasseDeriv (Finsupp.single
          ((h₀, k) : κ × ι) 1) (blockSubst A Q)))).coeff J = 0 := by
        rw [hasseDeriv_single_one, pderiv_blockSubst]
        rw [map_sum, map_sum, coeff_sum]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [map_smul, map_smul, coeff_smul, smul_eq_mul]
        have hzz := ih (∑ t, I'' t) hdeg I'' rfl (pderiv ((h₀, j) : κ × ι) Q) J ?_
        · rw [hzz, mul_zero]
        · intro I''' hI'''
          rw [← hasseDeriv_single_one, hasseDeriv_coeff]
          have : Q.coeff (J + I''' + Finsupp.single ((h₀, j) : κ × ι) 1) = 0 := by
            rw [add_assoc]
            refine hQ _ fun h ↦ ?_
            simp only [Finsupp.add_apply]
            rw [Finset.sum_add_distrib, sum_single_block, hI''' h, hblk h]
          rw [this, mul_zero]
      rw [hcomp, map_nsmul, coeff_smul, nsmul_eq_mul] at hzero
      have hcK : (c : K) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
      exact (mul_eq_zero.mp hzero).resolve_left hcK

end Vanishing

/-! ### The monomials of a fixed multidegree -/

section Monomials

theorem IsMultiHomogeneous.coeff_hasseDeriv {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) {I ν : κ × ι →₀ ℕ} (hν : (hasseDeriv I P).coeff ν ≠ 0) (h : κ) :
    ∑ i, ν (h, i) + ∑ i, I (h, i) = d h := by
  rw [hasseDeriv_coeff] at hν
  have hc : P.coeff (ν + I) ≠ 0 := fun hc ↦ hν (by rw [hc, mul_zero])
  rw [← hP hc h, ← Finset.sum_add_distrib]
  rfl

/-- **A Hasse derivative of a multihomogeneous polynomial is multihomogeneous**, of the
multidegree reduced in each block by the order of differentiation in that block. -/
theorem IsMultiHomogeneous.hasseDeriv {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (I : κ × ι →₀ ℕ) :
    IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) (hasseDeriv I P) := by
  intro ν hν h
  have h1 := hP.coeff_hasseDeriv hν h
  change ∑ i, ν (h, i) = d h - ∑ i, I (h, i)
  omega

section TotalDegree

variable [Fintype κ]

/-- Every monomial of a multihomogeneous polynomial has total degree `∑ h, d h`. -/
theorem IsMultiHomogeneous.sum_eq {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) {ν : κ × ι →₀ ℕ} (hν : P.coeff ν ≠ 0) :
    ∑ t, ν t = ∑ h, d h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun h _ ↦ hP hν h

end TotalDegree

variable [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Splitting a monomial into its blocks.** -/
noncomputable def blockSplit : (κ × ι →₀ ℕ) ≃ (κ → ι →₀ ℕ) :=
  Finsupp.equivFunOnFinite.trans <| (Equiv.curry κ ι ℕ).trans <|
    Equiv.piCongrRight fun _ ↦ Finsupp.equivFunOnFinite.symm

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem blockSplit_apply (ν : κ × ι →₀ ℕ) (h : κ) (i : ι) : blockSplit ν h i = ν (h, i) := rfl

/-- **The monomials of multidegree `d`**: the coefficient space of the multihomogeneous
polynomials of multidegree `d`. -/
noncomputable def multiMons (d : κ → ℕ) : Finset (κ × ι →₀ ℕ) :=
  (Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h)).map
    (blockSplit (κ := κ) (ι := ι)).symm.toEmbedding

@[simp]
theorem mem_multiMons {d : κ → ℕ} {ν : κ × ι →₀ ℕ} :
    ν ∈ multiMons d ↔ ∀ h, ∑ i, ν (h, i) = d h := by
  rw [multiMons, Finset.mem_map_equiv]
  simp only [Fintype.mem_piFinset, Finset.mem_finsuppAntidiag, Equiv.symm_symm]
  have hsum : ∀ (μ : κ × ι →₀ ℕ) (h : κ),
      (Finset.univ : Finset ι).sum ⇑(blockSplit μ h) = ∑ i, μ (h, i) :=
    fun μ h ↦ Finset.sum_congr rfl fun i _ ↦ blockSplit_apply μ h i
  constructor
  · intro hν h
    rw [← hsum ν h]
    exact (hν h).1
  · intro hν h
    exact ⟨by rw [hsum ν h]; exact hν h, Finset.subset_univ _⟩

theorem card_multiMons (d : κ → ℕ) :
    #(multiMons (ι := ι) d)
      = #(Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h)) :=
  Finset.card_map _

/-- Membership in `multiMons` read on the split monomial, which is the form the counting of
Layer 5.2 consumes. -/
theorem mem_multiMons_iff_blockSplit_mem {d : κ → ℕ} {ν : κ × ι →₀ ℕ} :
    ν ∈ multiMons d ↔ blockSplit ν
      ∈ Fintype.piFinset fun h ↦ Finset.finsuppAntidiag (Finset.univ : Finset ι) (d h) := by
  rw [multiMons, Finset.mem_map_equiv, Equiv.symm_symm]

/-- Each exponent of a monomial of multidegree `d` is at most the degree of its block. -/
theorem le_of_mem_multiMons {d : κ → ℕ} {ν : κ × ι →₀ ℕ} (hν : ν ∈ multiMons d) (t : κ × ι) :
    ν t ≤ d t.1 := by
  obtain ⟨h, i⟩ := t
  rw [← mem_multiMons.mp hν h]
  exact Finset.single_le_sum (f := fun i ↦ ν (h, i)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- The monomials of a given multidegree are never exhausted: putting the whole degree of each
block on one variable gives one. -/
theorem multiMons_nonempty [Nonempty ι] (d : κ → ℕ) : (multiMons (ι := ι) d).Nonempty := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨blockSplit.symm fun h ↦ Finsupp.single i₀ (d h), mem_multiMons.mpr fun h ↦ ?_⟩
  have hval : ∀ i, (blockSplit.symm fun h ↦ Finsupp.single i₀ (d h) : κ × ι →₀ ℕ) (h, i)
      = Finsupp.single i₀ (d h) i := by
    intro i
    rw [← blockSplit_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hval i, Finset.sum_eq_single i₀]
  · exact Finsupp.single_eq_same
  · exact fun i _ hi ↦ Finsupp.single_eq_of_ne hi
  · exact fun hi ↦ absurd (Finset.mem_univ i₀) hi

/-- **A crude count of the monomials of multidegree `d`**, enough to make `log #multiMons d` a
constant times `∑ h, d h`. -/
theorem card_multiMons_le (d : κ → ℕ) :
    #(multiMons (ι := ι) d) ≤ ∏ _t : κ × ι, (d _t.1 + 1) := by
  classical
  have hcard : ∏ t : κ × ι, (d t.1 + 1)
      = #(Fintype.piFinset fun t : κ × ι ↦ Finset.range (d t.1 + 1)) := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun t _ ↦ (Finset.card_range _).symm
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun ν ↦ (⇑ν : κ × ι → ℕ)) (fun ν hν ↦ ?_)
    (fun a _ b _ hab ↦ DFunLike.coe_injective hab)
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun t ↦ Finset.mem_range.mpr
    (Nat.lt_succ_of_le (le_of_mem_multiMons (Finset.mem_coe.mp hν) t))

end Monomials

/-! ### The coefficient vector of a multihomogeneous polynomial -/

section OfMulti

variable {K : Type*} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {d : κ → ℕ}

/-- **The polynomial named by a coefficient vector on the monomials of multidegree `d`.** -/
noncomputable def ofMulti (d : κ → ℕ) :
    ((multiMons (ι := ι) d) → K) →ₗ[K] MvPolynomial (κ × ι) K :=
  ∑ ν : (multiMons (ι := ι) d), (monomial (ν : κ × ι →₀ ℕ)).comp (LinearMap.proj ν)

theorem ofMulti_apply (x : (multiMons (ι := ι) d) → K) :
    ofMulti d x = ∑ ν : (multiMons (ι := ι) d), monomial (ν : κ × ι →₀ ℕ) (x ν) := by
  simp [ofMulti, LinearMap.sum_apply]

@[simp]
theorem coeff_ofMulti (x : (multiMons (ι := ι) d) → K) (ν : (multiMons (ι := ι) d)) :
    (ofMulti d x).coeff (ν : κ × ι →₀ ℕ) = x ν := by
  rw [ofMulti_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single ν ?_ (by simp)]
  · simp [coeff_monomial]
  · intro μ _ hμ
    rw [coeff_monomial]
    exact ite_eq_right fun h ↦ absurd (Subtype.ext h) hμ

theorem coeff_ofMulti_of_notMem (x : (multiMons (ι := ι) d) → K) {ν : κ × ι →₀ ℕ}
    (hν : ν ∉ multiMons (ι := ι) d) : (ofMulti d x).coeff ν = 0 := by
  rw [ofMulti_apply, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun μ _ ↦ ?_
  have hne : (μ : κ × ι →₀ ℕ) ≠ ν := fun h ↦ hν (h ▸ μ.2)
  simp [coeff_monomial, hne]

theorem isMultiHomogeneous_ofMulti (x : (multiMons (ι := ι) d) → K) :
    IsMultiHomogeneous d (ofMulti d x) := by
  intro ν hν h
  by_contra hc
  exact hν (coeff_ofMulti_of_notMem x (fun hm ↦ hc (mem_multiMons.mp hm h)))

theorem ofMulti_injective : Function.Injective (ofMulti (K := K) (ι := ι) d) := by
  intro x y h
  funext ν
  rw [← coeff_ofMulti x ν, h, coeff_ofMulti]

/-- **The expansion of a substituted auxiliary polynomial**: each coefficient is the linear
form in the unknowns whose vanishing Siegel's lemma imposes. -/
theorem coeff_blockSubst_ofMulti (M : Matrix ι ι K) (x : (multiMons (ι := ι) d) → K)
    (N : κ × ι →₀ ℕ) :
    (blockSubst M (ofMulti d x)).coeff N
      = ∑ ν : (multiMons (ι := ι) d),
          x ν * (blockSubst M (monomial (ν : κ × ι →₀ ℕ) (1 : K))).coeff N := by
  rw [ofMulti_apply, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [show (monomial (ν : κ × ι →₀ ℕ) (x ν) : MvPolynomial (κ × ι) K)
      = C (x ν) * monomial (ν : κ × ι →₀ ℕ) 1 by rw [C_mul_monomial, mul_one],
    map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, coeff_C_mul]

theorem ofMulti_eq_zero_iff (x : (multiMons (ι := ι) d) → K) :
    ofMulti d x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext ν
    rw [← coeff_ofMulti x ν, h]
    simp
  · rintro rfl
    simp

end OfMulti

end MvPolynomial
