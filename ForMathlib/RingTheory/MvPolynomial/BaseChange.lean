/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.HilbertPolynomial

-- Used only inside proofs.
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Multigraded ideals under extension of the coefficients

Extension of the coefficients `R → L` for multigraded ideals of `R[X]`, `X` in blocks.

* The homogeneous components of the elements of the extension `I L[X]` are spanned by the images
  of the homogeneous elements of `I`
  (`MvPolynomial.weightedHomogeneousComponent_mem_span_homogImage`).
* For a field extension `K → L` and a multihomogeneous ideal `I` of `K[X]`, the extension keeps
  the leading monomials and the dimensions `dim (I L[X])_d = dim_K I_d`, so it keeps the Hilbert
  function and the Hilbert polynomial (`MvPolynomial.hilbertFunction_map`,
  `MvPolynomial.hilbertPoly_map`). Rémond uses this for `L[X]/𝔭 L[X] ≅ (K[X]/𝔭) ⊗_K L` in the
  proof of Lemma 2.12 (G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon
  (eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001)).
-/

@[expose] public section

open Finset Module

namespace MvPolynomial

section Components

variable {σ M R S : Type*} [AddCommMonoid M] [CommSemiring R] [CommSemiring S] {w : σ → M}

/-- A polynomial is the sum of its homogeneous components, as a `Finset` sum. -/
theorem sum_weightedHomogeneousComponent_image [DecidableEq M] (p : MvPolynomial σ R) :
    ∑ e ∈ p.support.image (Finsupp.weight w), weightedHomogeneousComponent w e p = p := by
  ext c
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight w c)]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · intro hc
    simp only [mem_image, mem_support_iff, not_exists, not_and] at hc
    by_contra h
    exact hc c (by simpa using h) rfl

/-- Homogeneous components commute with maps of coefficients. -/
theorem weightedHomogeneousComponent_map (f : R →+* S) (e : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w e (map f p) = map f (weightedHomogeneousComponent w e p) := by
  classical
  ext c
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- The extension of a homogeneous ideal along a map of coefficients is homogeneous. -/
theorem _root_.Ideal.IsWeightedHomogeneous.map {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsWeightedHomogeneous w) (f : R →+* S) :
    (I.map (MvPolynomial.map f)).IsWeightedHomogeneous w := by
  classical
  have heq : I.map (MvPolynomial.map f) = Ideal.span
      (MvPolynomial.map f '' {p | p ∈ I ∧ ∃ e, IsWeightedHomogeneous w p e}) := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_)
      (Ideal.span_le.mpr ?_)
    · rw [Ideal.mem_comap, ← sum_weightedHomogeneousComponent_image (w := w) p, map_sum]
      exact Ideal.sum_mem _ fun e _ ↦ Ideal.subset_span
        ⟨_, ⟨hI hp e, e, weightedHomogeneousComponent_isWeightedHomogeneous e p⟩, rfl⟩
    · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
      exact Ideal.mem_map_of_mem _ hp
  rw [heq]
  refine isWeightedHomogeneous_span fun g hg ↦ ?_
  obtain ⟨p, ⟨-, e, he⟩, rfl⟩ := hg
  refine ⟨e, fun c hc ↦ he fun h0 ↦ hc ?_⟩
  rw [coeff_map, h0, map_zero]


end Components

variable {σ ι : Type*} [DecidableEq ι] {b : σ → ι}

section Span

variable {A L : Type*} [CommRing A] [CommRing L] (ρ : A →+* L) (I' : Ideal (MvPolynomial σ A))

/-- The images under `ρ` of the elements of `I'` homogeneous of multidegree `k`. -/
def homogImage (k : ι → ℕ) : Set (MvPolynomial σ L) :=
  MvPolynomial.map ρ '' {Q | Q ∈ I' ∧ IsWeightedHomogeneous (multiWeight b) Q k}

theorem monomial_mul_mem_span_homogImage {k : ι → ℕ} {y : MvPolynomial σ L}
    (hy : y ∈ Submodule.span L (homogImage (b := b) ρ I' k)) (c : σ →₀ ℕ) (a : L) :
    monomial c a * y ∈ Submodule.span L
      (homogImage (b := b) ρ I' (k + Finsupp.weight (multiWeight b) c)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨Q, ⟨hQ, hQk⟩, rfl⟩ := hy
    have : monomial c a * MvPolynomial.map ρ Q =
        a • MvPolynomial.map ρ (monomial c 1 * Q) := by
      rw [map_mul, map_monomial, map_one, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨I'.mul_mem_left _ hQ, ?_⟩, rfl⟩)
    rw [add_comm]
    exact (isWeightedHomogeneous_monomial _ _ _ rfl).mul hQk
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem weightedHomogeneousComponent_monomial_mul [Fintype ι] (c : σ →₀ ℕ) (a : L)
    (x : MvPolynomial σ L) (k : ι → ℕ) :
    weightedHomogeneousComponent (multiWeight b) k (monomial c a * x) =
      if Finsupp.weight (multiWeight b) c ≤ k then
        monomial c a * weightedHomogeneousComponent (multiWeight b) (k - Finsupp.weight
          (multiWeight b) c) x
      else 0 := by
  split_ifs with h
  · conv_lhs => rw [← tsub_add_cancel_of_le h, mul_comm]
    rw [(isWeightedHomogeneous_monomial _ c a rfl).weightedHomogeneousComponent_add_mul,
      mul_comm]
  · refine weightedHomogeneousComponent_eq_zero' _ _ fun e he hek ↦ h ?_
    rw [mem_support_iff, mul_comm, coeff_mul_monomial'] at he
    split_ifs at he with hce
    · obtain ⟨e', rfl⟩ := le_iff_exists_add.mp hce
      rw [← hek, map_add]
      exact le_self_add
    · exact absurd rfl he

/-- The homogeneous components of the elements of the extension `I' L[X]` are spanned by the
images of the homogeneous elements of `I'`. -/
theorem weightedHomogeneousComponent_mem_span_homogImage [Finite ι]
    (hI' : I'.IsWeightedHomogeneous (multiWeight b)) {x : MvPolynomial σ L}
    (hx : x ∈ I'.map (MvPolynomial.map ρ)) (k : ι → ℕ) :
    weightedHomogeneousComponent (multiWeight b) k x ∈
      Submodule.span L (homogImage (b := b) ρ I' k) := by
  have := Fintype.ofFinite ι
  induction hx using Submodule.span_induction generalizing k with
  | mem x hx =>
    obtain ⟨P, hP, rfl⟩ := hx
    rw [weightedHomogeneousComponent_map]
    exact Submodule.subset_span ⟨_, ⟨hI' hP k, weightedHomogeneousComponent_isWeightedHomogeneous
      _ _⟩, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ (hx k) (hy k)
  | smul a x _ hx =>
    rw [smul_eq_mul]
    induction a using MvPolynomial.induction_on' generalizing k with
    | monomial c a =>
      rw [weightedHomogeneousComponent_monomial_mul]
      split_ifs with h
      · have := monomial_mul_mem_span_homogImage ρ I' (hx (k - Finsupp.weight (multiWeight b) c))
          c a
        rwa [tsub_add_cancel_of_le h] at this
      · exact Submodule.zero_mem _
    | add p q hp hq => rw [add_mul, map_add]; exact Submodule.add_mem _ (hp k) (hq k)

end Span

section Field

variable {K L : Type*} [Field K] [Field L] (ρ : K →+* L)

/-- A map of coefficient fields keeps leading monomials. -/
theorem degree_map (m : MonomialOrder σ) (f : MvPolynomial σ K) :
    m.degree (MvPolynomial.map ρ f) = m.degree f := by
  rw [MonomialOrder.degree, MonomialOrder.degree, support_map_of_injective _ ρ.injective]

/-- The leading monomials of `I` are leading monomials of its extension `I L[X]`. -/
theorem leadingMonomials_subset_map (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    leadingMonomials m I ⊆ leadingMonomials m (I.map (MvPolynomial.map ρ)) := by
  rintro c ⟨f, hf, hf0, rfl⟩
  refine ⟨MvPolynomial.map ρ f, Ideal.mem_map_of_mem _ hf, fun h ↦ hf0 ?_, degree_map ρ m f⟩
  exact map_injective ρ ρ.injective (h.trans (map_zero _).symm)

variable [Finite σ] [Finite ι]

/-- **The homogeneous parts of an ideal keep their dimension under extension of the field of
coefficients.** The extension `(I L[X])_d` is spanned by the image of `I_d`, so its dimension is at
most `dim_K I_d`; leading monomials give the other inequality. -/
theorem finrank_map_inf_weightedHomogeneousSubmodule {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b)) (d : ι → ℕ) :
    finrank L ↥((I.map (MvPolynomial.map ρ)).restrictScalars L ⊓
      weightedHomogeneousSubmodule L (multiWeight b) d) =
      finrank K ↥(I.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b) d) := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  set m := MonomialOrder.lex (σ := σ)
  refine le_antisymm ?_ ?_
  · set V := I.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b) d
    have : FiniteDimensional K V := Submodule.finiteDimensional_of_le inf_le_right
    let v := Module.finBasis K V
    have hle : (I.map (MvPolynomial.map ρ)).restrictScalars L ⊓
        weightedHomogeneousSubmodule L (multiWeight b) d ≤
        Submodule.span L (Set.range fun i ↦ MvPolynomial.map ρ (v i : MvPolynomial σ K)) := by
      rintro x ⟨hxI, hxd⟩
      have hx := weightedHomogeneousComponent_mem_span_homogImage ρ I hI hxI d
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hxd] at hx
      refine Submodule.span_le.mpr ?_ hx
      rintro _ ⟨Q, ⟨hQI, hQd⟩, rfl⟩
      have hQ := congrArg (fun y : V ↦ MvPolynomial.map ρ (y : MvPolynomial σ K))
        (v.sum_repr ⟨Q, hQI, hQd⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul,
        map_C] at hQ
      rw [← hQ]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have : FiniteDimensional L (Submodule.span L
        (Set.range fun i ↦ MvPolynomial.map ρ (v i : MvPolynomial σ K))) :=
      FiniteDimensional.span_of_finite L (Set.finite_range _)
    refine (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans ?_)
    simp
  · rw [finrank_inf_weightedHomogeneousSubmodule m hI fun _ ↦ mem_blockMonomials,
      finrank_inf_weightedHomogeneousSubmodule m (hI.map _) fun _ ↦ mem_blockMonomials]
    exact Finset.card_le_card (Finset.monotone_filter_right _
      fun c _ hc ↦ leadingMonomials_subset_map ρ m I hc)

/-- **The Hilbert function does not change under extension of the field of coefficients.** -/
theorem hilbertFunction_map {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    hilbertFunction b (I.map (MvPolynomial.map ρ)) = hilbertFunction b I := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  funext d
  rw [hilbertFunction, hilbertFunction, finrank_multiWeight, finrank_multiWeight,
    finrank_map_inf_weightedHomogeneousSubmodule ρ hI]

/-- **The Hilbert polynomial does not change under extension of the field of coefficients.** -/
theorem hilbertPoly_map {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    hilbertPoly b (I.map (MvPolynomial.map ρ)) = hilbertPoly b I := by
  rw [hilbertPoly, hilbertPoly, hilbertFunction_map ρ hI]

end Field

end MvPolynomial

end
