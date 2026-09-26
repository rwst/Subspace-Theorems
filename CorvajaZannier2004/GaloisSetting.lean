/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Galois setting of Corvaja–Zannier

Corvaja and Zannier work in a number field `K`, Galois over `ℚ` and embedded in `ℂ`, which
contains all the algebraic numbers in play, and they read every archimedean absolute value of `K`
as `|ρ⁻¹ x|` for an automorphism `ρ` of `K` (§2, formula (2.2)). This file provides both.

## Main results

* `NumberField.exists_isGalois_ringHom_mem_range`: finitely many algebraic complex numbers lie in
  the image of one embedding `K → ℂ` of a number field `K`, Galois over `ℚ`.
* `NumberField.ComplexEmbedding.exists_algEquiv_apply_eq`: over a Galois `K`, every embedding
  `ψ : K → ℂ` is `φ ∘ τ` for a fixed `φ` and an automorphism `τ`.
* `NumberField.InfinitePlace.exists_algEquiv_apply_eq_norm`: every infinite place of a Galois `K`
  is `x ↦ ‖φ (τ x)‖` for an automorphism `τ`.

## Implementation notes

⚠ **Each place chooses its own automorphism, and nothing is made of the choice.** The paper
partitions the archimedean places by the cosets of `Gal(K/k)` (the sets `S_i` of p. 4) to know
which conjugate of `u` a place sees. Here a place `v` with `v x = ‖φ (τ x)‖` sees the conjugate
`τ⁻¹ u` through `φ`, and the form at `v` is written with `τ` directly; no partition is needed.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, §2.
-/

@[expose] public section

open Polynomial

namespace NumberField

/-- An embedding of a field in which the minimal polynomial of `x` splits reaches `x`. -/
theorem mem_range_of_splits {K : Type*} [Field K] [Algebra ℚ K] {x : ℂ} (hx : IsAlgebraic ℚ x)
    (φ : K →+* ℂ)
    (hs : ((minpoly ℚ x).map (algebraMap ℚ K)).Splits) : x ∈ φ.range := by
  have hroot : x ∈ (minpoly ℚ x).aroots ℂ := by
    rw [mem_aroots]
    exact ⟨minpoly.ne_zero hx.isIntegral, minpoly.aeval ℚ x⟩
  have hmap : (minpoly ℚ x).aroots ℂ = ((minpoly ℚ x).aroots K).map φ := by
    unfold aroots
    rw [← hs.roots_map φ, Polynomial.map_map]
    congr 2
    exact RingHom.ext_rat _ _
  rw [hmap] at hroot
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hroot
  exact ⟨y, rfl⟩

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Over a Galois number field, two complex embeddings differ by an automorphism.** -/
theorem ComplexEmbedding.exists_algEquiv_apply_eq (φ ψ : K →+* ℂ) :
    ∃ τ : K ≃ₐ[ℚ] K, ∀ x, ψ x = φ (τ x) := by
  obtain ⟨σ, hσ⟩ := InfinitePlace.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ
    (RingHom.ext_rat _ _)
  exact ⟨σ.symm, fun x ↦ by rw [← hσ]; rfl⟩

/-- **Every infinite place of a Galois number field is a twist of a fixed embedding**:
`v x = ‖φ (τ x)‖`. This is formula (2.2) of Corvaja–Zannier, `τ` being their `ρ⁻¹`, without the
normalizing exponent `d(ρ)/[K:ℚ]`, which Mathlib carries in `InfinitePlace.mult`. -/
theorem InfinitePlace.exists_algEquiv_apply_eq_norm (φ : K →+* ℂ) (v : InfinitePlace K) :
    ∃ τ : K ≃ₐ[ℚ] K, ∀ x, v x = ‖φ (τ x)‖ := by
  obtain ⟨τ, hτ⟩ := ComplexEmbedding.exists_algEquiv_apply_eq φ v.embedding
  exact ⟨τ, fun x ↦ by rw [← v.norm_embedding_eq x, hτ]⟩

/-- **The field of the paper.** Finitely many algebraic complex numbers lie in the image of one
embedding `φ : K → ℂ` of a number field `K`, Galois over `ℚ`: the splitting field of the product
of their minimal polynomials. -/
theorem exists_isGalois_ringHom_mem_range (s : Finset ℂ) (hs : ∀ x ∈ s, IsAlgebraic ℚ x) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsGalois ℚ K) (φ : K →+* ℂ),
      ∀ x ∈ s, x ∈ φ.range := by
  classical
  set p : ℚ[X] := ∏ x ∈ s, minpoly ℚ x with hp
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦ minpoly.ne_zero (hs x hx).isIntegral
  let L := SplittingField p
  have : NumberField L := ⟨⟩
  have : IsGalois ℚ L := ⟨⟩
  let φ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  exact ⟨L, inferInstance, inferInstance, inferInstance, φ,
    fun x hx ↦ mem_range_of_splits (hs x hx) φ <|
      (SplittingField.splits p).of_dvd ((Polynomial.map_ne_zero_iff
    (algebraMap ℚ L).injective).mpr hp0) (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ hx))⟩

end NumberField
