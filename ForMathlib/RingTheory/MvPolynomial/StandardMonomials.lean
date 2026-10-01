/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Weighted homogeneous ideals and their standard monomials

Let `w : σ → M` be a weight on the variables. An ideal `I` of `K[X]` is *`w`-homogeneous* if it
contains the `w`-homogeneous components of its elements. Fix a monomial order. The *leading
monomials* of `I` are the degrees, for that order, of the nonzero elements of `I`. They form an
upper set of exponents.

The main result counts dimensions by leading monomials. If the monomials of weight `d` form a
finite set `S`, then the degree-`d` part of `I` has dimension the number of members of `S` that are
leading monomials of `I`. The remaining members of `S`, the *standard monomials*, therefore count
the dimension of the degree-`d` part of `K[X]/I`. This is the linear algebra behind Hilbert
functions computed through Gröbner bases, and it needs no Gröbner basis.

## Main definitions

* `Ideal.IsWeightedHomogeneous w I`: `I` contains the `w`-homogeneous components of its elements.
* `MvPolynomial.leadingMonomials m I`: the degrees of the nonzero elements of `I` for the monomial
  order `m`.

## Main statements

* `MvPolynomial.linearIndependent_of_injective_degree`: polynomials with pairwise distinct
  leading monomials are linearly independent.
* `MvPolynomial.finrank_weightedHomogeneousSubmodule`: the weight-`d` part of `K[X]` has
  dimension the number of monomials of weight `d`.
* `MvPolynomial.finrank_inf_weightedHomogeneousSubmodule`: the weight-`d` part of a homogeneous
  ideal has dimension the number of its leading monomials of weight `d`.
-/

@[expose] public section

open Module
open scoped MonomialOrder

variable {σ M R K : Type*} [AddCommMonoid M]

/-- An ideal of `R[X]` is `w`-homogeneous if it contains the `w`-homogeneous components of its
elements. -/
def Ideal.IsWeightedHomogeneous [CommSemiring R] (w : σ → M) (I : Ideal (MvPolynomial σ R)) :
    Prop :=
  ∀ ⦃p⦄, p ∈ I → ∀ d, MvPolynomial.weightedHomogeneousComponent w d p ∈ I

namespace MvPolynomial

section Semiring

variable [CommSemiring R]

theorem isWeightedHomogeneous_top (w : σ → M) :
    (⊤ : Ideal (MvPolynomial σ R)).IsWeightedHomogeneous w :=
  fun _ _ _ ↦ Submodule.mem_top

theorem isWeightedHomogeneous_bot (w : σ → M) :
    (⊥ : Ideal (MvPolynomial σ R)).IsWeightedHomogeneous w := by
  intro p hp d
  rw [Ideal.mem_bot] at hp ⊢
  simp [hp]

end Semiring

variable [Field K]

section LeadingMonomials

variable (m : MonomialOrder σ)

/-- The *leading monomials* of an ideal: the degrees, for the monomial order `m`, of its nonzero
elements. -/
def leadingMonomials (I : Ideal (MvPolynomial σ K)) : Set (σ →₀ ℕ) :=
  {c | ∃ f ∈ I, f ≠ 0 ∧ m.degree f = c}

variable {m}

theorem add_mem_leadingMonomials {I : Ideal (MvPolynomial σ K)} {c : σ →₀ ℕ}
    (hc : c ∈ leadingMonomials m I) (e : σ →₀ ℕ) : e + c ∈ leadingMonomials m I := by
  classical
  obtain ⟨f, hfI, hf0, rfl⟩ := hc
  have hmono : (monomial e (1 : K)) ≠ 0 := by simp
  refine ⟨monomial e 1 * f, I.mul_mem_left _ hfI, mul_ne_zero hmono hf0, ?_⟩
  rw [m.degree_mul hmono hf0, m.degree_monomial]
  simp

/-- The leading monomials of an ideal form an upper set. -/
theorem isUpperSet_leadingMonomials (I : Ideal (MvPolynomial σ K)) :
    IsUpperSet (leadingMonomials m I) := by
  intro c e hce hc
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hce
  simpa [add_comm] using add_mem_leadingMonomials hc k

/-- Polynomials with pairwise distinct leading monomials are linearly independent. -/
theorem linearIndependent_of_injective_degree {ι : Type*} {f : ι → MvPolynomial σ K}
    (hf : ∀ i, f i ≠ 0) (hinj : Function.Injective fun i ↦ m.degree (f i)) :
    LinearIndependent K f := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra! h
  obtain ⟨j, hjs, hj⟩ := h
  set t := s.filter fun i ↦ g i ≠ 0 with ht
  have hjt : j ∈ t := by simp [ht, hjs, hj]
  obtain ⟨i₀, hi₀t, hmax⟩ :=
    Finset.exists_max_image t (fun i ↦ m.toSyn (m.degree (f i))) ⟨j, hjt⟩
  have hi₀ : i₀ ∈ s ∧ g i₀ ≠ 0 := by simpa [ht] using hi₀t
  have hcoeff := congrArg (fun p : MvPolynomial σ K ↦ p.coeff (m.degree (f i₀))) hsum
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul, Finsupp.coe_finsetSum,
    Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoeff
  rw [Finset.sum_eq_single_of_mem i₀ hi₀.1] at hcoeff
  · simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    exact mul_ne_zero hi₀.2 (m.coeff_degree_ne_zero_iff.mpr (hf i₀)) hcoeff
  · intro i his hne
    by_cases hgi : g i = 0
    · simp [hgi]
    have hle := hmax i (by simp [ht, his, hgi])
    have hlt : m.degree (f i) ≺[m] m.degree (f i₀) := by
      refine lt_of_le_of_ne hle fun heq ↦ hne (hinj ?_)
      exact m.toSyn.injective heq
    simp [m.coeff_eq_zero_of_lt hlt]

end LeadingMonomials

section Finrank

variable {w : σ → M}

/-- The weight-`d` part of `K[X]` has dimension the number of monomials of weight `d`. -/
theorem finrank_weightedHomogeneousSubmodule {d : M} {S : Finset (σ →₀ ℕ)}
    (hS : ∀ c, c ∈ S ↔ Finsupp.weight w c = d) :
    finrank K (weightedHomogeneousSubmodule K w d) = S.card := by
  have hset : {c | Finsupp.weight w c = d} = (S : Set (σ →₀ ℕ)) := by
    ext c
    simp [hS]
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, hset,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) (S : Set (σ →₀ ℕ))).finrank_eq]
  simp

theorem finiteDimensional_weightedHomogeneousSubmodule {d : M} {S : Finset (σ →₀ ℕ)}
    (hS : ∀ c, c ∈ S ↔ Finsupp.weight w c = d) :
    FiniteDimensional K (weightedHomogeneousSubmodule K w d) := by
  have hset : {c | Finsupp.weight w c = d} = (S : Set (σ →₀ ℕ)) := by
    ext c
    simp [hS]
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, hset]
  exact LinearEquiv.finiteDimensional
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) (S : Set (σ →₀ ℕ))).symm

variable (m : MonomialOrder σ)

/-- The `w`-homogeneous component of the weight of the leading monomial keeps that monomial. -/
theorem degree_weightedHomogeneousComponent_degree {f : MvPolynomial σ K} (hf : f ≠ 0) :
    weightedHomogeneousComponent w (Finsupp.weight w (m.degree f)) f ≠ 0 ∧
      m.degree (weightedHomogeneousComponent w (Finsupp.weight w (m.degree f)) f) =
        m.degree f := by
  classical
  set g := weightedHomogeneousComponent w (Finsupp.weight w (m.degree f)) f
  have hcoeff : g.coeff (m.degree f) = f.coeff (m.degree f) := by
    simp [g, coeff_weightedHomogeneousComponent]
  have hg : g ≠ 0 := by
    intro h
    rw [h] at hcoeff
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    exact m.coeff_degree_ne_zero_iff.mpr hf hcoeff.symm
  refine ⟨hg, ?_⟩
  apply m.toSyn.injective
  apply le_antisymm
  · refine m.degree_le_iff.mpr fun c hc ↦ m.le_degree ?_
    rw [mem_support_iff] at hc ⊢
    intro hfc
    simp [g, coeff_weightedHomogeneousComponent, hfc] at hc
  · apply m.le_degree
    rw [mem_support_iff, hcoeff]
    exact m.coeff_degree_ne_zero_iff.mpr hf

/-- In a homogeneous ideal, every leading monomial is the leading monomial of a homogeneous
element of the same weight. -/
theorem exists_mem_weightedHomogeneousSubmodule {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous w) {c : σ →₀ ℕ} (hc : c ∈ leadingMonomials m I) :
    ∃ f ∈ I, f ∈ weightedHomogeneousSubmodule K w (Finsupp.weight w c) ∧ f ≠ 0 ∧
      m.degree f = c := by
  obtain ⟨f, hfI, hf0, rfl⟩ := hc
  obtain ⟨hg0, hgdeg⟩ := degree_weightedHomogeneousComponent_degree (w := w) m hf0
  exact ⟨_, hI hfI _, weightedHomogeneousComponent_isWeightedHomogeneous _ _, hg0, hgdeg⟩

/-- **Counting by leading monomials.** The weight-`d` part of a homogeneous ideal has dimension
the number of its leading monomials of weight `d`. -/
theorem finrank_inf_weightedHomogeneousSubmodule {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous w) {d : M} {S : Finset (σ →₀ ℕ)}
    (hS : ∀ c, c ∈ S ↔ Finsupp.weight w c = d) [DecidablePred (· ∈ leadingMonomials m I)] :
    finrank K ↥(I.restrictScalars K ⊓ weightedHomogeneousSubmodule K w d) =
      (S.filter (· ∈ leadingMonomials m I)).card := by
  classical
  set Γ := weightedHomogeneousSubmodule K w d
  set V := I.restrictScalars K ⊓ Γ
  set T := S.filter (· ∈ leadingMonomials m I)
  have : FiniteDimensional K Γ := finiteDimensional_weightedHomogeneousSubmodule hS
  have : FiniteDimensional K V := Submodule.finiteDimensional_of_le inf_le_right
  apply le_antisymm
  · -- The standard monomials of weight `d` span a complement of `V` inside `Γ`.
    set W : Submodule K (MvPolynomial σ K) :=
      AddMonoidAlgebra.supported K K (↑(S \ T) : Set (σ →₀ ℕ))
    have hWΓ : W ≤ Γ := by
      change W ≤ weightedHomogeneousSubmodule K w d
      rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
      refine AddMonoidAlgebra.supported_mono fun c hc ↦ ?_
      have : c ∈ S := (Finset.mem_sdiff.mp hc).1
      exact (hS c).mp this
    have : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWΓ
    have hdisj : V ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      intro p ⟨⟨hpI, hpΓ⟩, hpW⟩
      rw [Submodule.mem_bot]
      by_contra hp0
      have hmem : m.degree p ∈ p.support := m.degree_mem_support hp0
      have hSdiff : m.degree p ∈ S \ T := by
        by_contra hnot
        exact (mem_support_iff.mp hmem) (AddMonoidAlgebra.mem_supported'.mp hpW _ hnot)
      have hw : Finsupp.weight w (m.degree p) = d :=
        (mem_weightedHomogeneousSubmodule K w d p).mp hpΓ (mem_support_iff.mp hmem)
      have hST := Finset.mem_sdiff.mp hSdiff
      exact hST.2 (Finset.mem_filter.mpr ⟨hST.1, p, hpI, hp0, rfl⟩)
    have hfinW : finrank K W = (S \ T).card := by
      rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
        (↑(S \ T) : Set (σ →₀ ℕ))).finrank_eq]
      simp
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hdisj, finrank_bot, add_zero] at hsum
    have hle : finrank K ↥(V ⊔ W) ≤ finrank K Γ :=
      Submodule.finrank_mono (sup_le inf_le_right hWΓ)
    rw [finrank_weightedHomogeneousSubmodule hS] at hle
    have hcard : (S \ T).card + T.card = S.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    omega
  · -- A leading monomial of weight `d` comes from a homogeneous element of `I`.
    have hchoose : ∀ c : T, ∃ f ∈ I, f ∈ Γ ∧ f ≠ 0 ∧ m.degree f = c := by
      intro c
      have hc := Finset.mem_filter.mp c.2
      have := exists_mem_weightedHomogeneousSubmodule m hI hc.2
      rwa [(hS c).mp hc.1] at this
    choose f hfI hfΓ hf0 hfdeg using hchoose
    let g : T → V := fun c ↦ ⟨f c, hfI c, hfΓ c⟩
    have hli : LinearIndependent K g := by
      apply LinearIndependent.of_comp V.subtype
      refine linearIndependent_of_injective_degree (m := m) (f := fun c ↦ f c) hf0 ?_
      intro c c' h
      exact Subtype.ext (by simpa [hfdeg] using h)
    simpa using hli.fintype_card_le_finrank

end Finrank

end MvPolynomial
