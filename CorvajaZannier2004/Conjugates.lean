/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PseudoPisot
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic

-- Used only inside proofs.
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# The conjugates of an element of a real subfield

In the proof of Lemma 3, Corvaja and Zannier index the conjugates of `u ∈ k` by coset
representatives `σ₁ = id, σ₂, …, σ_d` of `Gal(K/k)` in `Gal(K/ℚ)`. Here they are indexed by the
embeddings `e : k →ₐ[ℚ] K` themselves, the identity being `k.val`, which removes the choice of
representatives. This file collects what the proof needs about them.

## Main results

* `NumberField.exists_algEquiv_apply_eq_of_algHom`: an embedding of `k` extends to an
  automorphism of `K`.
* `NumberField.algHomCompEquiv`: composing with an automorphism permutes the embeddings.
* `NumberField.mem_of_forall_algEquiv_apply_eq`: an element fixed by `Gal(K/k)` lies in `k`.
* `NumberField.exists_ne_val_apply_eq_or_adjoin_eq`: either a second embedding fixes `y`, or `y`
  generates `k`.
* `NumberField.exists_algEquiv_apply_eq_of_mem_aroots`: every complex conjugate of `y` is
  `φ (τ y)` for an automorphism `τ`.
* `NumberField.exists_ne_val_one_le_norm`: the claim in the first case of the proof of Lemma 3 —
  if `y ∈ k` has integral trace `∑ₑ e y`, `|y| > 1`, and is not pseudo-Pisot, then some conjugate
  `e y` with `e ≠ id` has modulus at least `1`.

## Implementation notes

⚠ **"`qλu` has an integral trace" is ambiguous, and the ambiguity matters.** The paper knows
`Tr_{k/ℚ}(qλu) = p ∈ ℤ`, while the pseudo-Pisot condition is about `Tr_{ℚ(qλu)/ℚ}`, and the first
is `[k : ℚ(qλu)]` times the second. The gap closes by a case split: if `qλu` does not generate `k`,
a second embedding of `k` fixes it (`exists_ne_val_apply_eq_or_adjoin_eq`, the Galois
correspondence), and that conjugate has modulus `|qλu| > 1` outright; if it does generate `k`, the
two traces agree.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, proof of Lemma 3.
-/

@[expose] public section

open Polynomial IntermediateField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **An embedding of a subfield extends to an automorphism**, `K` being normal over `ℚ`. -/
theorem exists_algEquiv_apply_eq_of_algHom {k : IntermediateField ℚ K} (e : k →ₐ[ℚ] K) :
    ∃ τ : K ≃ₐ[ℚ] K, ∀ x : k, e x = τ x := by
  refine ⟨AlgEquiv.ofBijective (e.liftNormal K) ((e.liftNormal K).normal_bijective ℚ K K),
    fun x ↦ ?_⟩
  simpa using (e.liftNormal_commutes K x).symm

omit [IsGalois ℚ K] in
/-- **Composing with an automorphism permutes the embeddings of `k`.** -/
noncomputable def algHomCompEquiv (k : IntermediateField ℚ K) (τ : K ≃ₐ[ℚ] K) :
    (k →ₐ[ℚ] K) ≃ (k →ₐ[ℚ] K) where
  toFun e := (τ : K →ₐ[ℚ] K).comp e
  invFun e := (τ.symm : K →ₐ[ℚ] K).comp e
  left_inv e := by ext; simp
  right_inv e := by ext; simp

omit [IsGalois ℚ K] in
@[simp]
theorem algHomCompEquiv_apply (k : IntermediateField ℚ K) (τ : K ≃ₐ[ℚ] K) (e : k →ₐ[ℚ] K)
    (x : k) : algHomCompEquiv k τ e x = τ (e x) := rfl

/-- **The Galois correspondence, as used in the Claim of Lemma 3**: an element of `K` fixed by
every automorphism fixing `k` lies in `k`. -/
theorem mem_of_forall_algEquiv_apply_eq {k : IntermediateField ℚ K} {x : K}
    (h : ∀ τ : K ≃ₐ[ℚ] K, (∀ y ∈ k, τ y = y) → τ x = x) : x ∈ k := by
  rw [← IsGalois.fixedField_fixingSubgroup k, mem_fixedField_iff]
  exact fun τ hτ ↦ h τ ((IntermediateField.mem_fixingSubgroup_iff k τ).mp hτ)

/-- **Either a second embedding of `k` fixes `y`, or `y` generates `k`.** If `ℚ(y) < k`, the
Galois group of `K` over `ℚ(y)` is strictly larger than that over `k`; an automorphism in the
difference restricts to an embedding of `k` other than the identity which fixes `y`. -/
theorem exists_ne_val_apply_eq_or_adjoin_eq {k : IntermediateField ℚ K} {y : K} (hy : y ∈ k) :
    (∃ e : k →ₐ[ℚ] K, e ≠ k.val ∧ e ⟨y, hy⟩ = y) ∨ ℚ⟮y⟯ = k := by
  by_cases h : ℚ⟮y⟯ = k
  · exact Or.inr h
  left
  have hle : ℚ⟮y⟯ ≤ k := adjoin_simple_le_iff.mpr hy
  have hne : fixingSubgroup k ≠ fixingSubgroup ℚ⟮y⟯ := fun hfix ↦ h <| by
    rw [← IsGalois.fixedField_fixingSubgroup k, ← IsGalois.fixedField_fixingSubgroup ℚ⟮y⟯, hfix]
  obtain ⟨τ, hτy, hτk⟩ : ∃ τ ∈ fixingSubgroup ℚ⟮y⟯, τ ∉ fixingSubgroup k := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (fixingSubgroup_le hle) hcon)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτy hτk
  push Not at hτk
  obtain ⟨x, hxk, hx⟩ := hτk
  refine ⟨(τ : K →ₐ[ℚ] K).comp k.val, fun he ↦ hx ?_, hτy y (mem_adjoin_simple_self ℚ y)⟩
  simpa using DFunLike.congr_fun he ⟨x, hxk⟩

/-- The complex roots of the minimal polynomial of `y` are the images under `φ` of its roots in
`K`, since the minimal polynomial splits in the normal field `K`. -/
theorem aroots_minpoly_eq_map (φ : K →+* ℂ) (y : K) :
    (minpoly ℚ y).aroots ℂ = ((minpoly ℚ y).aroots K).map φ := by
  unfold aroots
  rw [← (Normal.splits (IsGalois.to_normal) y).roots_map φ, Polynomial.map_map]
  congr 2
  exact RingHom.ext_rat _ _

/-- **Every complex conjugate of `y ∈ K` is `φ (τ y)` for an automorphism `τ`.** -/
theorem exists_algEquiv_apply_eq_of_mem_aroots (φ : K →+* ℂ) {y : K} {z : ℂ}
    (hz : z ∈ (minpoly ℚ y).aroots ℂ) : ∃ τ : K ≃ₐ[ℚ] K, φ (τ y) = z := by
  rw [aroots_minpoly_eq_map φ y] at hz
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hz
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hmin : minpoly ℚ y' = minpoly ℚ y := by
    rw [mem_aroots] at hy'
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy'.2
      (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp hmin
  exact ⟨τ, by rw [← hτ]; rfl⟩

omit [IsGalois ℚ K] in
/-- The minimal polynomial of a real number `r` with `(r : ℂ) = φ y` is that of `y`. -/
theorem minpoly_re_eq (φ : K →+* ℂ) {y : K} (hy : (φ y).im = 0) :
    minpoly ℚ (φ y).re = minpoly ℚ y := by
  have hre : (((φ y).re : ℝ) : ℂ) = φ y := Complex.ext (by simp) (by simp [hy])
  have h1 : minpoly ℚ (((φ y).re : ℝ) : ℂ) = minpoly ℚ (φ y).re :=
    minpoly.algHom_eq ((Algebra.ofId ℝ ℂ).restrictScalars ℚ) Complex.ofReal_injective _
  rw [← h1, hre]
  exact minpoly.algHom_eq φ.toRatAlgHom φ.injective y

/-- **The trace, when `y` generates `k`**: the sum of the complex conjugates of `y` is the image
of `∑ₑ e y` over the embeddings `e` of `k`. -/
theorem sum_aroots_minpoly_eq (φ : K →+* ℂ) {k : IntermediateField ℚ K} {y : K} (hy : y ∈ k)
    (hgen : ℚ⟮y⟯ = k) :
    ((minpoly ℚ y).aroots ℂ).sum = φ (∑ e : k →ₐ[ℚ] K, e ⟨y, hy⟩) := by
  classical
  set x : k := ⟨y, hy⟩
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hminx : minpoly ℚ x = minpoly ℚ y := (minpoly.algHom_eq k.val Subtype.val_injective x).symm
  -- `x` generates `k`, by counting degrees
  have hrank : Module.finrank ℚ⟮x⟯ k = 1 := by
    have h1 : Module.finrank ℚ ℚ⟮x⟯ = (minpoly ℚ y).natDegree := by
      rw [adjoin.finrank hint, hminx]
    have h2 : Module.finrank ℚ k = (minpoly ℚ y).natDegree := by
      rw [← adjoin.finrank (Algebra.IsIntegral.isIntegral y), hgen]
    have h3 := Module.finrank_mul_finrank ℚ ℚ⟮x⟯ k
    rw [h1, h2] at h3
    have hpos : 0 < (minpoly ℚ y).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)
    exact Nat.eq_of_mul_eq_mul_left hpos (h3.trans (mul_one _).symm)
  have htr := trace_eq_trace_adjoin ℚ x
  rw [hrank, one_smul] at htr
  have hroots := IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots (K := ℚ) (F := ℂ) x
    (IsAlgClosed.splits _)
  have hemb := trace_eq_sum_embeddings (K := ℚ) (L := k) (E := ℂ) (x := x)
  rw [← hminx, ← hroots, ← htr, hemb, map_sum]
  symm
  refine Fintype.sum_bijective (fun e ↦ φ.toRatAlgHom.comp e) ?_ _ _ fun e ↦ rfl
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun e₁ e₂ h ↦ AlgHom.ext fun z ↦ φ.injective (DFunLike.congr_fun h z), ?_⟩
  rw [AlgHom.card_of_splits ℚ k K fun z ↦ by
      rw [← minpoly.algHom_eq k.val Subtype.val_injective z]
      exact Normal.splits IsGalois.to_normal (z : K), AlgHom.card]

/-- **The Claim in the first case of Lemma 3.** Let `y ∈ k`, real under `φ`, with `|y| > 1`,
`∑ₑ e y ∈ ℤ` over the embeddings `e` of `k`, and not pseudo-Pisot. Then a conjugate `e y` with
`e` not the identity has modulus at least `1`. -/
theorem exists_ne_val_one_le_norm (φ : K →+* ℂ) {k : IntermediateField ℚ K} {y : K}
    (hy : y ∈ k) (hreal : (φ y).im = 0) (h1 : 1 < ‖φ y‖) (hPP : ¬ IsPseudoPisot (φ y).re)
    {m : ℤ} (htr : ∑ e : k →ₐ[ℚ] K, e ⟨y, hy⟩ = m) :
    ∃ e : k →ₐ[ℚ] K, e ≠ k.val ∧ 1 ≤ ‖φ (e ⟨y, hy⟩)‖ := by
  rcases exists_ne_val_apply_eq_or_adjoin_eq hy with ⟨e, he, hey⟩ | hgen
  · exact ⟨e, he, by rw [hey]; exact h1.le⟩
  by_contra hcon
  push Not at hcon
  have hre : (((φ y).re : ℝ) : ℂ) = φ y := Complex.ext (by simp) (by simp [hreal])
  have hmin := minpoly_re_eq φ hreal
  refine hPP ⟨?_, ?_, fun z hz hzne ↦ ?_, m, ?_⟩
  · rwa [← Real.norm_eq_abs, ← Complex.norm_real, hre]
  · have : IsAlgebraic ℚ (((φ y).re : ℝ) : ℂ) := by
      rw [hre]
      exact (Algebra.IsIntegral.isIntegral y).isAlgebraic.algHom φ.toRatAlgHom
    exact (isAlgebraic_algHom_iff ((Algebra.ofId ℝ ℂ).restrictScalars ℚ)
      Complex.ofReal_injective).mp this
  · rw [hmin] at hz
    obtain ⟨τ, rfl⟩ := exists_algEquiv_apply_eq_of_mem_aroots φ hz
    have hne : (τ : K →ₐ[ℚ] K).comp k.val ≠ k.val := fun h ↦ hzne <| by
      rw [hre]
      congr 1
      simpa using DFunLike.congr_fun h ⟨y, hy⟩
    simpa using hcon _ hne
  · rw [hmin, sum_aroots_minpoly_eq φ hy hgen, htr]
    simp

end NumberField
