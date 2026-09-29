/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.Recurrences

-- Used only inside proofs.
import DiophantineApproximation.UnitEquation
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Complex.Norm

/-!
# Evertse's Corollary 4 for one characteristic root

**Corollary 4** (Evertse 1984, p. 229). A non-degenerate linear recurrence `u` has only finitely
many pairs `r > s` with `u_r = u_s`, unless it is of the form `u_k = c α ^ k` with `α` a root of
unity.

With at least two characteristic roots this follows from Theorem 3; the full statement is
`NumberField.finite_setOf_powerSum_eq` in `Evertse1984.GeneralRoots`. This file treats one root,
`u_k = f(k) α ^ k`, with `f` split over `K`:

* if `α` is not a root of unity, `α ^ (r - s) = f(s) / f(r)` gives `H(α) ^ (r - s) ≤ (C r ^ N) ^ 2`,
  so `r - s = O(log r)`, and Lemma 2 applies to `f` (nonconstant, or else `α ^ (r - s) = 1`);
* if `α` is a root of unity and `f` is nonconstant, `|f(r)|_w = |f(s)|_w` at an infinite place
  `w`; writing `f = c ∏ (X - a)`, each factor `|r - a|_w` increases strictly with `r` once
  `r > Re a`, so each `s` has at most one partner `r` beyond that point.

## Main results

* `NumberField.finite_setOf_eval_mul_pow_eq_of_splits`: the one-root case, `f` split.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, Corollary 4.
-/

@[expose] public section

open IsDedekindDomain Height Module Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **One root, not a root of unity**: for `α ≠ 0` not a root of unity and `f ≠ 0` split, only
finitely many `r > s` have `f(r) α ^ r = f(s) α ^ s`. -/
theorem finite_setOf_eval_mul_pow_eq_of_not_root {α : K} (hα0 : α ≠ 0)
    (hα : ∀ n : ℕ, 0 < n → α ^ n ≠ 1) {f : K[X]} (hf0 : f ≠ 0) (hfs : f.Splits) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2}.Finite := by
  classical
  -- the pairs with `f(r) = 0` (then also `f(s) = 0`)
  have hR : {r : ℕ | f.eval (r : K) = 0}.Finite :=
    (f.roots.toFinset.finite_toSet.preimage (Nat.cast_injective (R := K)).injOn).subset
      fun r hr ↦ Multiset.mem_toFinset.mpr ((mem_roots hf0).mpr hr)
  suffices hmain : {p : ℕ × ℕ | (p.2 < p.1 ∧
      f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2) ∧ f.eval (p.1 : K) ≠ 0}.Finite by
    refine ((hR.prod hR).union hmain).subset fun p hp ↦ ?_
    by_cases h : f.eval (p.1 : K) = 0
    · refine Or.inl ⟨h, ?_⟩
      have := hp.2
      rw [h, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right (pow_ne_zero _ hα0)
    · exact Or.inr ⟨hp, h⟩
  have hsub : ∀ {p : ℕ × ℕ}, p.2 < p.1 → f.eval (p.1 : K) ≠ 0 →
      f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2 →
      f.eval (p.2 : K) ≠ 0 ∧ α ^ (p.1 - p.2) = f.eval (p.2 : K) / f.eval (p.1 : K) := by
    intro p hsr hr h
    have hs : f.eval (p.2 : K) ≠ 0 := fun h0 ↦ by
      rw [h0, zero_mul] at h
      exact mul_ne_zero hr (pow_ne_zero _ hα0) h
    refine ⟨hs, ?_⟩
    rw [eq_div_iff hr]
    apply mul_left_cancel₀ (pow_ne_zero p.2 hα0)
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsr.le, mul_comm, h, mul_comm]
  by_cases hdeg : f.natDegree = 0
  · -- `f` constant: `α ^ (r - s) = 1`
    refine Set.finite_empty.subset fun p ⟨⟨hsr, h⟩, hr⟩ ↦ ?_
    obtain ⟨-, hpow⟩ := hsub hsr hr h
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C, eval_C, div_self (by
      rwa [eq_C_of_natDegree_eq_zero hdeg, eval_C] at hr)] at hpow
    exact hα (p.1 - p.2) (Nat.sub_pos_of_lt hsr) hpow
  obtain ⟨T, hT⟩ := exists_finset_mem_unit (Units.mk0 α hα0)
  obtain ⟨C, hC1, N, hCN⟩ := exists_forall_mulHeight₁_eval_le (K := K) fun _ : Unit ↦ f
  set γ : ℝ := 1 / (2 * f.natDegree + 3) with hγ
  have hγ0 : 0 < γ := by positivity
  obtain ⟨β, hβ0, hβ⟩ := exists_forall_sub_le_mul_rpow (one_lt_mulHeight₁ hα0 hα) hC1 N hγ0
  have hγd : γ < 1 / (f.natDegree + f.natDegree + 2) := by
    rw [hγ]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hL2 := finite_setOf_eval_div_eval_mem_unit_of_splits T hfs hfs
    (fun h hh ↦ Polynomial.not_comp_X_add_C_dvd (Nat.pos_of_ne_zero hdeg)
      (Int.cast_ne_zero.mpr hh)) hβ0 hγ0.le hγd
  refine (hL2.preimage (f := fun p : ℕ × ℕ ↦ ((p.1 : ℤ), (p.2 : ℤ))) fun p _ q _ h ↦ ?_).subset
    fun p ⟨⟨hsr, h⟩, hr⟩ ↦ ?_
  · simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  obtain ⟨hs, hpow⟩ := hsub hsr hr h
  have hr1 : 1 ≤ p.1 := Nat.one_le_of_lt hsr
  have hCr : 1 ≤ C * (p.1 : ℝ) ^ N :=
    one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ (by exact_mod_cast hr1))
  have hup : mulHeight₁ α ^ (p.1 - p.2) ≤ (C * (p.1 : ℝ) ^ N) ^ 4 := by
    rw [← mulHeight₁_pow, hpow]
    calc _ ≤ mulHeight₁ (f.eval (p.2 : K)) * mulHeight₁ (f.eval (p.1 : K)) :=
          mulHeight₁_div_le _ _
      _ ≤ (C * (p.1 : ℝ) ^ N) * (C * (p.1 : ℝ) ^ N) :=
          mul_le_mul (hCN () _ _ hsr.le hr1) (hCN () _ _ le_rfl hr1) (mulHeight₁_pos _).le
            (by positivity)
      _ ≤ (C * (p.1 : ℝ) ^ N) ^ 4 := by
          rw [← pow_two]; exact pow_le_pow_right₀ hCr (by norm_num)
  have hrs := hβ p.1 p.2 hsr hup
  refine ⟨?_, ?_, ?_⟩
  · change (p.1 : ℤ) ≠ (p.2 : ℤ)
    exact_mod_cast hsr.ne'
  · simp only [Int.cast_natCast]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hsr.le : (p.2 : ℝ) ≤ p.1)),
      abs_of_nonneg (Nat.cast_nonneg _), ← Nat.cast_sub hsr.le]
    exact hrs
  · refine ⟨(Units.mk0 α hα0 ^ (p.1 - p.2))⁻¹, inv_mem (pow_mem hT _), ?_⟩
    simp only [Int.cast_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_mk0, hpow, inv_div]

/-- **One root, a root of unity**: for `α` a root of unity and `f` nonconstant split, only
finitely many `r > s` have `f(r) α ^ r = f(s) α ^ s`. -/
theorem finite_setOf_eval_mul_pow_eq_of_root {α : K} {n : ℕ} (hn : 0 < n) (hαn : α ^ n = 1)
    {f : K[X]} (hdeg : 0 < f.natDegree) (hfs : f.Splits) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2}.Finite := by
  have hf0 : f ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  set φ := w.embedding
  have hwα : w α = 1 := by
    have h := congrArg w hαn
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (apply_nonneg w α) hn.ne').mp h
  -- `x ↦ |f(x)|_w` on `ℕ`
  set g : ℕ → ℝ := fun x ↦ w (f.eval (x : K)) with hg
  have hgprod : ∀ x : ℕ, g x = w f.leadingCoeff *
      (f.roots.map fun a ↦ ‖(x : ℂ) - φ a‖).prod := fun x ↦ by
    simp only [hg, hfs.eval_eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map,
      Function.comp_def]
    congr 2
    refine Multiset.map_congr rfl fun a _ ↦ ?_
    rw [← w.norm_embedding_eq, map_sub, map_natCast]
  obtain ⟨B, hB⟩ := (f.roots.map fun a ↦ (φ a).re).toFinset.finite_toSet.bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt B
  have hre : ∀ a ∈ f.roots, (φ a).re < M := fun a ha ↦
    (hB (Multiset.mem_toFinset.mpr (Multiset.mem_map_of_mem _ ha))).trans_lt hM
  -- `g` is strictly increasing on `[M, ∞)`
  have hmono : ∀ s r : ℕ, M ≤ s → s < r → g s < g r := by
    intro s r hMs hsr
    have hlc : 0 < w f.leadingCoeff := InfinitePlace.pos_iff.mpr (leadingCoeff_ne_zero.mpr hf0)
    have hsq : ∀ (a : K) (x y : ℕ), (φ a).re < x → x < y → ‖(x : ℂ) - φ a‖ < ‖(y : ℂ) - φ a‖ ∧
        0 < ‖(x : ℂ) - φ a‖ := by
      intro a x y hx hxy
      have hxy' : (x : ℝ) < y := by exact_mod_cast hxy
      have hsq : ‖(x : ℂ) - φ a‖ ^ 2 < ‖(y : ℂ) - φ a‖ ^ 2 := by
        simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.natCast_re, Complex.natCast_im]
        nlinarith
      refine ⟨pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp hsq,
        norm_pos_iff.mpr fun h ↦ ?_⟩
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at this
      linarith
    rw [hgprod, hgprod]
    refine mul_lt_mul_of_pos_left (Multiset.prod_map_lt_prod_map ?_ _ _ ?_ ?_) hlc
    · intro h0
      rw [hfs.natDegree_eq_card_roots, h0, Multiset.card_zero] at hdeg
      exact lt_irrefl 0 hdeg
    · intro a ha
      exact (hsq a s r (by exact_mod_cast (hre a ha).trans_le (by exact_mod_cast hMs)) hsr).2
    · intro a ha
      exact (hsq a s r (by exact_mod_cast (hre a ha).trans_le (by exact_mod_cast hMs)) hsr).1
  have hinj : Set.InjOn g (Set.Ici M) := fun x hx y hy hxy ↦ by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hmono x y hx h).ne hxy
    · exact (hmono y x hy h).ne hxy.symm
  -- each `s < M` has at most one partner `r ≥ M`
  refine (((Set.finite_Iio M).prod (Set.finite_Iio M)).union (Set.finite_iUnion (ι := Fin M)
    fun s ↦ ((Set.Subsingleton.finite (s := {r | M ≤ r ∧ g r = g s}) fun x hx y hy ↦
      hinj hx.1 hy.1 (hx.2.trans hy.2.symm)).image fun r ↦ (r, (s : ℕ))))).subset
    fun p ⟨hsr, h⟩ ↦ ?_
  have hgeq : g p.1 = g p.2 := by
    have := congrArg w h
    simp only [map_mul, map_pow, hwα, one_pow, mul_one] at this
    exact this
  by_cases hs : M ≤ p.2
  · exact absurd hgeq (hmono p.2 p.1 hs hsr).ne'
  push Not at hs
  by_cases hr : p.1 < M
  · exact Or.inl ⟨hr, hs⟩
  push Not at hr
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨p.2, hs⟩, p.1, ⟨hr, hgeq⟩, rfl⟩)

/-- **Corollary 4, one characteristic root**: `u_k = f(k) α ^ k` with `α ≠ 0`, `f ≠ 0` split,
and not both `f` constant and `α` a root of unity, has only finitely many pairs `r > s` with
`u_r = u_s`. -/
theorem finite_setOf_eval_mul_pow_eq_of_splits {α : K} (hα0 : α ≠ 0) {f : K[X]} (hf0 : f ≠ 0)
    (hfs : f.Splits) (h : 0 < f.natDegree ∨ ∀ n : ℕ, 0 < n → α ^ n ≠ 1) :
    {p : ℕ × ℕ | p.2 < p.1 ∧ f.eval (p.1 : K) * α ^ p.1 = f.eval (p.2 : K) * α ^ p.2}.Finite := by
  by_cases hα : ∀ n : ℕ, 0 < n → α ^ n ≠ 1
  · exact finite_setOf_eval_mul_pow_eq_of_not_root hα0 hα hf0 hfs
  push Not at hα
  obtain ⟨n, hn, hαn⟩ := hα
  exact finite_setOf_eval_mul_pow_eq_of_root hn hαn
    (h.resolve_right fun h' ↦ h' n hn hαn) hfs

end NumberField
