/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Multigraded
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Block multinomial coefficients

For blocks `b : σ → ι` and a monomial `m` of multidegree `δ`, the block multinomial coefficient
is `C(δ, m) = ∏_i δ_i! / ∏_{b s = i} m_s!`. The **block multinomial theorem** is
`∑_{|m| = δ} C(δ, m) x^m = ∏_i (∑_{b s = i} x_s)^{δ_i}`. With `x_s = |z_s|²` it says that the
`ℓ²` norm of `(√C(δ, m) z^m)_m` is `∏_i ‖z^{(i)}‖^{δ_i}` (Rémond's remodeled Veronese
embedding, LNM 1752, Ch. 7, §2.2).
-/

@[expose] public section

open Finset

namespace Finset

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- The **multinomial theorem** over `finsuppAntidiag`. -/
theorem sum_pow_eq_sum_finsuppAntidiag (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n =
      ∑ k ∈ finsuppAntidiag s n, Nat.multinomial s k * ∏ i ∈ s, f i ^ k i := by
  rw [sum_pow_eq_sum_piAntidiag, finsuppAntidiag, sum_map, ← sum_attach (piAntidiag s n)]
  rfl

end Finset

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]

/-- The multinomial coefficient `C(δ, m) = ∏_i δ_i! / ∏_{b s = i} m_s!` of a monomial `m`, where
`δ_i` is its degree in block `i`. -/
noncomputable def blockMultinomial (b : σ → ι) (m : σ →₀ ℕ) : ℕ :=
  ∏ i, Nat.multinomial {s | b s = i} m

theorem blockMultinomial_pos (b : σ → ι) (m : σ →₀ ℕ) : 0 < blockMultinomial b m :=
  Finset.prod_pos fun _ _ ↦ Nat.multinomial_pos _ _

/-- The **block multinomial theorem**:
`∑_{m ∈ M_δ} C(δ, m) x^m = ∏_i (∑_{b s = i} x_s)^{δ_i}`. -/
theorem sum_blockMultinomial_mul_prod_pow {R : Type*} [CommSemiring R] (b : σ → ι)
    (δ : ι → ℕ) (x : σ → R) :
    ∑ m ∈ blockMonomials b δ, (blockMultinomial b m : R) * ∏ s, x s ^ m s =
      ∏ i, (∑ s ∈ ({s | b s = i} : Finset σ), x s) ^ δ i := by
  classical
  simp_rw [sum_pow_eq_sum_finsuppAntidiag, prod_univ_sum, sum_blockMonomials]
  refine sum_congr rfl fun f hf ↦ ?_
  rw [Fintype.mem_piFinset] at hf
  have hsupp : ∀ j, (f j).support ⊆ ({s | b s = j} : Finset σ) :=
    fun j ↦ (mem_finsuppAntidiag.mp (hf j)).2
  have happ := sum_apply_of_support_subset b hsupp
  have hmult : ∀ i, Nat.multinomial {s | b s = i} ⇑(∑ j, f j) =
      Nat.multinomial {s | b s = i} ⇑(f i) := fun i ↦
    Nat.multinomial_congr fun s hs ↦ by
      rw [happ s]
      simp only [mem_filter, mem_univ, true_and] at hs
      rw [hs]
  have hpow : ∏ s, x s ^ (∑ j, f j) s = ∏ i, ∏ s ∈ ({s | b s = i} : Finset σ), x s ^ f i s := by
    rw [← prod_fiberwise univ b]
    refine prod_congr rfl fun i _ ↦ prod_congr rfl fun s hs ↦ ?_
    simp only [mem_filter, mem_univ, true_and] at hs
    rw [happ s, hs]
  rw [blockMultinomial, Nat.cast_prod, hpow, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ ↦ by rw [hmult]

end MvPolynomial
