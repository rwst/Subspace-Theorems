/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Kronecker

import ArithmeticHeights.NorthcottTheorem

/-!
# Lower bounds for the height away from one

**An algebraic number that is neither zero nor a root of unity has absolute height greater than
one, and for each bound on the degree the gap is uniform.** Kronecker's theorem of Layer 1.4 says
that the height is `1` exactly on the degenerate cases; this file says that everything else stays
away from `1`, which is the shape in which Diophantine arguments consume the layer.

The strict bound is Kronecker's theorem read contrapositively. The uniform bound needs Northcott's
theorem of Layer 1.3 as well: the algebraic numbers of logarithmic height at most `1` and degree at
most `D` are finitely many, each of them has positive height unless it is zero or a root of unity,
and the least of those finitely many positive values — or `1`, for everything above the cut — is
the constant.

## Main results

* `NumberField.one_lt_absMulHeight₁` and `NumberField.absLogHeight₁_pos`, over any field of
  characteristic zero.
* `NumberField.exists_pos_forall_le_absLogHeight₁`: for each degree bound `D` a constant `c > 0`
  below the logarithmic height of every algebraic number of degree at most `D` that is neither
  zero nor a root of unity. `NumberField.exists_one_lt_forall_le_absMulHeight₁` is the
  multiplicative form, with a constant `c > 1`.

## Implementation notes

⚠ The constant is **not effective**. It is the minimum of a finite set that Northcott's theorem
only asserts to be finite, and nothing here describes it. Bombieri–Gubler note in the same breath
the effective partial bound `h(α) ≥ (log 2)/d` for an `α` of degree `d` that is not an algebraic
unit, and Dobrowolski's theorem is the effective statement in the general case; neither is part of
this milestone.

⚠ The dependence of `c` on the degree is **essential**, and saying so is not Lehmer's conjecture.
The number `2 ^ (1/N)` is neither zero nor a root of unity and has logarithmic height
`(log 2)/N`, which tends to zero, so no single `c > 0` serves every degree; this is refuted among
the examples below. What Lehmer's conjecture asks is whether `[ℚ(x) : ℚ] · h(x)` — the logarithm
of the Mahler measure, by Layer 1.2 — is bounded below by a positive constant, and that is open.
The family above keeps that product equal to `log 2`, so it does not bear on the question; the
example records the bound it does satisfy.

⚠ The hypotheses `x ≠ 0` and `IsIntegral ℚ x` are needed for the junk-value reasons of Layer 1.4:
`absMulHeight₁` is `1` at `0` and `1` at every transcendental element. Dropping either makes the
strict bound false, and both are refuted in `ArithmeticHeights/Kronecker.lean`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
1.6.15, where this statement is derived exactly as here — from the finiteness of a set of bounded
height and degree together with Kronecker's theorem — and where Lehmer's conjecture is stated.
M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Theorem B.2.3 and Corollary B.2.3.1 are the two inputs in their numbering.

This is Layer 1.5 of the `ArithmeticHeights` roadmap.
-/

public section

open IntermediateField Module NumberField Polynomial

namespace NumberField

variable {K : Type*} [Field K] [CharZero K]

/-- **An algebraic number that is neither zero nor a root of unity has height greater than one.**
This is Kronecker's theorem of Layer 1.4 read contrapositively, the height being at least `1`
always. -/
theorem one_lt_absMulHeight₁ {x : K} (hx : IsIntegral ℚ x) (hx0 : x ≠ 0)
    (hxu : ¬ ∃ n, 0 < n ∧ x ^ n = 1) : 1 < absMulHeight₁ x :=
  (one_le_absMulHeight₁ x).lt_of_ne fun h ↦
    ((absMulHeight₁_eq_one_iff hx).mp h.symm).elim hx0 hxu

/-- The logarithmic form of `NumberField.one_lt_absMulHeight₁`. -/
theorem absLogHeight₁_pos {x : K} (hx : IsIntegral ℚ x) (hx0 : x ≠ 0)
    (hxu : ¬ ∃ n, 0 < n ∧ x ^ n = 1) : 0 < absLogHeight₁ x := by
  rw [absLogHeight₁]
  exact Real.log_pos (one_lt_absMulHeight₁ hx hx0 hxu)

/-- **The gap is uniform in each degree** (Bombieri–Gubler, 1.6.15). For every bound `D` on the
degree there is a `c > 0` below the logarithmic height of every algebraic number of degree at most
`D` that is neither zero nor a root of unity.

⚠ `c` depends on `D`, and must: `2 ^ (1/N)` has logarithmic height `(log 2)/N`. See the examples
at the end of the file. Whether `D · c` can be taken independent of `D` is Lehmer's conjecture. -/
theorem exists_pos_forall_le_absLogHeight₁ (D : ℕ) :
    ∃ c > 0, ∀ x : K, IsIntegral ℚ x → x ≠ 0 → finrank ℚ ℚ⟮x⟯ ≤ D →
      (¬ ∃ n, 0 < n ∧ x ^ n = 1) → c ≤ absLogHeight₁ x := by
  classical
  have hS : {x : K | IsIntegral ℚ x ∧ x ≠ 0 ∧ (¬ ∃ n, 0 < n ∧ x ^ n = 1) ∧
      absLogHeight₁ x ≤ 1 ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.Finite :=
    (finite_setOfPred_absLogHeight₁_le_of_finrank_le 1 D).subset
      fun _ hx ↦ ⟨hx.1, hx.2.2.2.1, hx.2.2.2.2⟩
  set G : Finset ℝ := insert 1 (hS.toFinset.image absLogHeight₁) with hG
  have hne : G.Nonempty := ⟨1, hG ▸ Finset.mem_insert_self _ _⟩
  have hGpos : ∀ r ∈ G, 0 < r := by
    intro r hr
    rw [hG] at hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact one_pos
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨h1, h2, h3, -, -⟩ := hS.mem_toFinset.mp hy
      exact absLogHeight₁_pos h1 h2 h3
  refine ⟨G.min' hne, hGpos _ (G.min'_mem hne), fun x hx hx0 hxD hxu ↦ ?_⟩
  rcases le_or_gt (absLogHeight₁ x) 1 with h | h
  · exact G.min'_le _ (hG ▸ Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (hS.mem_toFinset.mpr ⟨hx, hx0, hxu, h, hxD⟩)))
  · exact (G.min'_le 1 (hG ▸ Finset.mem_insert_self _ _)).trans h.le

/-- The multiplicative form of `NumberField.exists_pos_forall_le_absLogHeight₁`. -/
theorem exists_one_lt_forall_le_absMulHeight₁ (D : ℕ) :
    ∃ c > 1, ∀ x : K, IsIntegral ℚ x → x ≠ 0 → finrank ℚ ℚ⟮x⟯ ≤ D →
      (¬ ∃ n, 0 < n ∧ x ^ n = 1) → c ≤ absMulHeight₁ x := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_forall_le_absLogHeight₁ (K := K) D
  refine ⟨Real.exp c, Real.one_lt_exp_iff.mpr hc, fun x hx hx0 hxD hxu ↦ ?_⟩
  rw [← Real.exp_log (zero_lt_one.trans_le (one_le_absMulHeight₁ x))]
  exact Real.exp_le_exp.mpr (hbound x hx hx0 hxD hxu)

end NumberField

/-!
### Worked examples

The acceptance criteria the roadmap attaches to this layer: that the strict bound is not vacuous,
that the root-of-unity hypothesis is what rules out the equality case, and — the substantive one —
that the constant of the uniform bound must depend on the degree, without thereby saying anything
about Lehmer's conjecture.
-/

section Examples

/-- **Acceptance test.** The strict bound is not vacuous: `2` is neither zero nor a root of unity,
so its absolute height exceeds `1`. -/
example : 1 < absMulHeight₁ (2 : ℚ) :=
  one_lt_absMulHeight₁ (IsIntegral.of_finite ℚ _) two_ne_zero
    fun ⟨_, hn, hn1⟩ ↦ absurd hn1 (one_lt_pow₀ one_lt_two hn.ne').ne'

/-- **Rejection test: the root-of-unity hypothesis cannot be dropped.** A root of unity has height
exactly `1`, by Kronecker's theorem. -/
example {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x) {n : ℕ} (hn : 0 < n)
    (hxn : x ^ n = 1) : absMulHeight₁ x = 1 :=
  (absMulHeight₁_eq_one_iff hx).mpr (Or.inr ⟨n, hn, hxn⟩)

/-- **Rejection test: the constant must depend on the degree.** For every `c > 0` there is an
algebraic number, neither zero nor a root of unity, of logarithmic height below `c`: the `N`-th
root of `2`, whose height is `(log 2)/N` because its `N`-th power is `2` and `H(2) = 2`.

The second conclusion is what keeps this away from Lehmer's conjecture. The degree of `2 ^ (1/N)`
is at most `N` — it is exactly `N`, `X ^ N - 2` being irreducible, but the inequality is what is
needed and it is free — so the product of the degree and the height stays at most `log 2`. The
conjecture asks for a positive lower bound on that product, which this family does not disturb;
and `(log 2)/N` is exactly the bound Bombieri–Gubler record for numbers that are not algebraic
units, which `2 ^ (1/N)` is not, its norm being `±2`. -/
example {c : ℝ} (hc : 0 < c) : ∃ x : ℝ, IsIntegral ℚ x ∧ x ≠ 0 ∧
    (¬ ∃ n, 0 < n ∧ x ^ n = 1) ∧ absLogHeight₁ x < c ∧
    (finrank ℚ ℚ⟮x⟯ : ℝ) * absLogHeight₁ x ≤ Real.log 2 := by
  have h2 : absLogHeight₁ (2 : ℝ) = Real.log 2 := by
    rw [absLogHeight₁, ← absMulHeight_eq_absMulHeight₁,
      show ![(2 : ℝ), 1] = ⇑(Algebra.ofId ℚ ℝ) ∘ ![(2 : ℚ), 1] from by
        funext i; fin_cases i <;> simp,
      absMulHeight_comp, absMulHeight_eq, Module.finrank_self, Nat.cast_one, inv_one,
      Real.rpow_one, ← Height.mulHeight₁_eq_mulHeight, Rat.mulHeight₁_eq_max]
    norm_num
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, N ≠ 0 ∧ Real.log 2 / c < N := by
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log 2 / c)
    exact ⟨n + 1, n.succ_ne_zero, hn.trans (by push_cast; linarith)⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hx1 : (1 : ℝ) < (2 : ℝ) ^ ((N : ℝ)⁻¹) :=
    (Real.one_lt_rpow_iff_of_pos two_pos).mpr (Or.inl ⟨one_lt_two, by positivity⟩)
  have hxN : ((2 : ℝ) ^ ((N : ℝ)⁻¹)) ^ N = 2 := Real.rpow_inv_natCast_pow (by norm_num) hN0
  have hp0 : (X ^ N - C (2 : ℚ)) ≠ 0 := (monic_X_pow_sub_C 2 hN0).ne_zero
  have haeval : aeval ((2 : ℝ) ^ ((N : ℝ)⁻¹)) (X ^ N - C (2 : ℚ)) = 0 := by simp [hxN]
  have hxint : IsIntegral ℚ ((2 : ℝ) ^ ((N : ℝ)⁻¹)) :=
    ⟨X ^ N - C 2, monic_X_pow_sub_C 2 hN0, haeval⟩
  have hlog : Real.log 2 = N * absLogHeight₁ ((2 : ℝ) ^ ((N : ℝ)⁻¹)) := by
    rw [← h2]
    conv_lhs => rw [← hxN]
    exact absLogHeight₁_pow hxint N
  have hdeg : finrank ℚ ℚ⟮(2 : ℝ) ^ ((N : ℝ)⁻¹)⟯ ≤ N := by
    rw [adjoin.finrank hxint]
    exact (natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero ℚ _ hp0 haeval)).trans_eq natDegree_X_pow_sub_C
  refine ⟨_, hxint, (zero_lt_one.trans hx1).ne', fun ⟨m, hm, hm1⟩ ↦
    absurd hm1 (one_lt_pow₀ hx1 hm.ne').ne', ?_, ?_⟩
  · refine lt_of_mul_lt_mul_left (a := (N : ℝ)) ?_ hNpos.le
    rw [← hlog]
    exact (div_lt_iff₀ hc).mp hN
  · rw [hlog]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hdeg) (absLogHeight₁_nonneg _)

/-- **Conformance.** The roadmap pins the statement over `ℂ`; it is the special case of the
above. -/
example (D : ℕ) :
    ∃ c > 0, ∀ x : ℂ, IsIntegral ℚ x → x ≠ 0 → finrank ℚ ℚ⟮x⟯ ≤ D →
      (¬ ∃ n, 0 < n ∧ x ^ n = 1) → c ≤ NumberField.absLogHeight₁ x :=
  NumberField.exists_pos_forall_le_absLogHeight₁ D

end Examples

end
