/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneity under substitution

If `φ` is weighted homogeneous of degree `m` for the weights `w`, and every `g i` is weighted
homogeneous of degree `w i` for the weights `w'`, then `φ(g)` is weighted homogeneous of degree
`m` for `w'` (`MvPolynomial.IsWeightedHomogeneous.aeval_of_algebra`, for any `R`-algebra `S`).
Special cases: `map`, `rename`.
-/

@[expose] public section

namespace MvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]

theorem IsWeightedHomogeneous.aeval_of_algebra [Algebra R S] {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ R} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) :
    IsWeightedHomogeneous w' (MvPolynomial.aeval g φ) m := by
  rw [aeval_def, eval₂_eq]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ ?_
  rw [← zero_add m]
  refine (isWeightedHomogeneous_C w' _).mul ?_
  have hw : ∑ i ∈ d.support, d i * w i = m := by
    rw [← hφ (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.sum]
    simp [mul_comm]
  rw [← hw]
  exact IsWeightedHomogeneous.prod _ _ _ fun i _ ↦ by
    simpa [smul_eq_mul] using (hg i).pow (d i)

theorem IsWeightedHomogeneous.map {w : σ → ℕ} {φ : MvPolynomial σ R} {m : ℕ}
    (hφ : IsWeightedHomogeneous w φ m) (f : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map f φ) m := fun d hd ↦
  hφ fun h0 ↦ hd (by rw [coeff_map, h0, map_zero])

theorem IsWeightedHomogeneous.rename {w : σ → ℕ} {w' : τ → ℕ} {f : σ → τ}
    (hf : ∀ i, w' (f i) = w i) {φ : MvPolynomial σ R} {m : ℕ}
    (hφ : IsWeightedHomogeneous w φ m) :
    IsWeightedHomogeneous w' (MvPolynomial.rename f φ) m := by
  rw [rename_eq_aeval]
  exact hφ.aeval_of_algebra _ fun i ↦ hf i ▸ isWeightedHomogeneous_X R w' (f i)

end MvPolynomial
