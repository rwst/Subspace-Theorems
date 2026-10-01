/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Fintype.BigOperators

-- Used only inside proofs.
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Small natural combinations avoiding finitely many subspaces

Over a field of characteristic `0`, let `v_r` (`r ∈ R`) be vectors and `W_t` (`t ∈ T`) subspaces,
none of which contains all the `v_r`. Then some combination `∑ a_r v_r` with natural coefficients
of total size `∑ a_r ≤ |T|` lies in none of the `W_t`
(`Submodule.exists_sum_nsmul_forall_notMem`).

This is G. Rémond, *Sur le théorème du produit*, J. Théor. Nombres Bordeaux **13** (2001),
Lemma 5.1, which chooses the polynomials of the excess Bézout inequality with small integer
coefficients, so that their heights are controlled. The proof here differs from Rémond's
induction on the dimension: for each `t` a linear form `λ_t` on `K^R` vanishes on the
combinations in `W_t` but not on all of `K^R`, and the Combinatorial Nullstellensatz
(`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`) finds a point of the simplex
`{a ∈ ℕ^R : ∑ a_r ≤ |T|}` where `∏_t λ_t`, of degree `|T|`, does not vanish.
-/

@[expose] public section

open Finset MvPolynomial

variable {K V R T : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace Submodule

/-- **Rémond's Lemma 5.1.** Over a field of characteristic `0`, if no subspace `W t` contains all
the vectors `v r`, then a natural combination `∑ a_r v_r` with `∑ a_r ≤ |T|` lies in none of
them. -/
theorem exists_sum_nsmul_forall_notMem [CharZero K] [Fintype R] [Fintype T] (v : R → V)
    (W : T → Submodule K V) (h : ∀ t, ∃ r, v r ∉ W t) :
    ∃ a : R → ℕ, ∑ r, a r ≤ Fintype.card T ∧ ∀ t, ∑ r, a r • v r ∉ W t := by
  classical
  -- A linear form on `V ⧸ W t` that does not vanish at some `v r`.
  have hφ : ∀ t, ∃ φ : Module.Dual K (V ⧸ W t), ∃ r, φ ((W t).mkQ (v r)) ≠ 0 := by
    intro t
    obtain ⟨r, hr⟩ := h t
    have hne : (W t).mkQ (v r) ≠ 0 := by
      rwa [Ne, mkQ_apply, Quotient.mk_eq_zero]
    obtain ⟨φ, hφ⟩ := not_forall.mp ((Module.forall_dual_apply_eq_zero_iff K _).not.mpr hne)
    exact ⟨φ, r, hφ⟩
  choose φ r₀ hr₀ using hφ
  -- The linear polynomial `λ_t = ∑_r φ_t(v_r) X_r`, and its value at a point.
  set lam : T → MvPolynomial R K := fun t ↦ ∑ r, φ t ((W t).mkQ (v r)) • X r
  have heval : ∀ (x : R → K) t, eval x (lam t) = φ t ((W t).mkQ (∑ r, x r • v r)) := by
    intro x t
    simp [lam, map_sum, smul_eval, mul_comm]
  have hlam0 : ∀ t, lam t ≠ 0 := by
    intro t h0
    have := congrArg (fun p : MvPolynomial R K ↦ p.coeff (Finsupp.single (r₀ t) 1)) h0
    simp only [mkQ_apply, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul,
      Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, coeff_X,
      Finsupp.single_left_inj one_ne_zero, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq',
      mem_univ, ↓reduceIte, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      lam] at this
    exact hr₀ t this
  have hdeg : ∀ t, (lam t).totalDegree ≤ 1 := by
    intro t
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ ↦ ?_)
    exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le
  set F : MvPolynomial R K := ∏ t, lam t
  have hF0 : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ ↦ hlam0 t
  have hFdeg : F.totalDegree ≤ Fintype.card T := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ t, (lam t).totalDegree ≤ ∑ _t : T, 1 := sum_le_sum fun t _ ↦ hdeg t
      _ = Fintype.card T := by simp
  -- A monomial of top degree, and the Combinatorial Nullstellensatz on the box below it.
  obtain ⟨m, hm, hmdeg⟩ : ∃ m, F.coeff m ≠ 0 ∧ m.degree = F.totalDegree := by
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF0)
      (fun s ↦ s.sum fun _ e ↦ e)
    exact ⟨m, mem_support_iff.mp hm, hmeq.symm⟩
  set S : R → Finset K := fun r ↦ (range (m r + 1)).image (fun k : ℕ ↦ (k : K))
  have hS : ∀ r, m r < #(S r) := by
    intro r
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
    exact Nat.lt_succ_self _
  obtain ⟨x, hxS, hx⟩ :=
    combinatorial_nullstellensatz_exists_eval_nonzero F m hm hmdeg.symm S hS
  have hxa : ∀ r, ∃ k ≤ m r, x r = k := by
    intro r
    obtain ⟨k, hk, hkx⟩ := mem_image.mp (hxS r)
    exact ⟨k, Nat.lt_succ_iff.mp (mem_range.mp hk), hkx.symm⟩
  choose a ha hax using hxa
  refine ⟨a, ?_, fun t ht ↦ ?_⟩
  · calc ∑ r, a r ≤ ∑ r, m r := sum_le_sum fun r _ ↦ ha r
      _ = m.degree := by rw [Finsupp.degree_eq_sum]
      _ ≤ Fintype.card T := hmdeg ▸ hFdeg
  · apply hx
    rw [eval_prod]
    refine Finset.prod_eq_zero (mem_univ t) ?_
    rw [heval]
    have : ∑ r, x r • v r = ∑ r, a r • v r := by
      refine sum_congr rfl fun r _ ↦ ?_
      rw [hax r, Nat.cast_smul_eq_nsmul]
    rw [this, mkQ_apply, (Quotient.mk_eq_zero _).mpr ht, map_zero]

end Submodule
