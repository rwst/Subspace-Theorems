/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.BombieriVaalerMaxNorm
public import ArithmeticHeights.RowEntryHeight

/-!
# Siegel's lemma in terms of the entries: the corollaries applications quote

Layer 5.4 bounds a basis of the solution space of `A x = 0` by the Arakelov height of the *row
space* of `A`. That is what Bombieri and Vaaler prove, and it is not what an application has in
hand: an application knows the entries of `A`. This file makes the exchange, by Layer 5.5's
inequality `H_Ar^row(A) ≤ ∏ᵢ H_Ar(Aᵢ) ≤ (√N · H(A)) ^ R`, and states the two corollaries the
literature quotes — Bombieri–Gubler Corollary 2.9.9 and its single-solution form.

With `N` columns, `R = N − dim ker A` independent rows, `d = [K : ℚ]` and `D` the discriminant:

`∏ₗ H(xₗ) ≤ |D| ^ ((N − R) / (2 d)) · (√N · H(A)) ^ R`,

and hence a single nonzero integral solution with

`H(x) ≤ |D| ^ (1 / (2 d)) · (√N · H(A)) ^ (R / (N − R))`.

All heights here are absolute, `NumberField.absMulHeight`; `H(A)` is `Matrix.mulHeight` in the
absolute normalization, the sup-norm height of the tuple of *entries*.

## Main results

* `NumberField.exists_basis_ker_prod_absMulHeight_le_entries`: the product bound in terms of the
  entries, Bombieri–Gubler Corollary 2.9.9.
* `NumberField.exists_ne_zero_mem_ker_absMulHeight_le`: the single-solution form, the statement
  transcendence and Diophantine-approximation arguments import, and
  `NumberField.exists_ne_zero_mem_ker_absMulHeight_le_of_linearIndependent_row` for a matrix whose
  rank is read off its rows.
* `Matrix.finrank_ker_mulVecLin`: the rank–nullity bookkeeping that makes `N − R` the dimension of
  the kernel.

## Implementation notes

⚠ **Over `ℚ` this replaces the `N` of the classical Siegel lemma by `√N`, and that is the
acceptance test for the whole of Layer 5.** Layer 5.1's
`Matrix.exists_ne_zero_mulVec_eq_zero_mulHeight_le` produces a solution of height at most
`(N · B) ^ (R / (N − R))` with `B` a bound on the entries; with `discr ℚ = 1` and `[ℚ : ℚ] = 1`
the bound here reads `(√N · H(A)) ^ (R / (N − R))`, and `H(A) ≤ B`. The example at the end of
this file is that specialization. The `√N` is not an artefact of the route: it is
`‖·‖₂ ≤ √N ‖·‖_∞` at each archimedean place, applied once per row, and it is the only place a
cardinality is paid at all.

⚠ **No rank hypothesis is needed, and the exponent is the rank and not the number of rows.**
Bombieri–Gubler's Corollary 2.9.7 obtains the non-maximal-rank case "by restricting to `R`
independent rows", and that restriction is done once, inside
`Matrix.exists_submatrix_row_linearIndependent`, rather than being imposed on the user: a maximal
independent family of rows spans the same row space, so the row-space height is paid `rank A`
times. Layer 5.4 already carries no hypothesis on `A`, its bound being in terms of the row-space
height, which is defined for every matrix; what would need a hypothesis is only the identification
of that height with the tuple of `m × m` minors, and that identification is not used here.
`NumberField.exists_ne_zero_mem_ker_absMulHeight_le_of_linearIndependent_row` is the special case
in which the rank is read off the rows, which is the shape the roadmap states.

⚠ **The single-solution form is extraction from the product, and it needs `H ≥ 1`.** From
`∏ₗ H(xₗ) ≤ C` with `k` factors, the smallest factor satisfies `H(x)ᵏ ≤ ∏ₗ H(xₗ) ≤ C`; this is
where `NumberField.one_le_absMulHeight` is used, and it is why the exponent of the bound is
`R / (N − R)` and not `R`. It also needs `k > 0`, which is `m < N`: with `m = N` and `A`
of full rank the only solution is `0` and the statement is false as stated.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.9.8, Corollary 2.9.7 and Corollary 2.9.9. E. Bombieri and J. Vaaler, "On Siegel's lemma",
*Inventiones Mathematicae* **73** (1983), 11–32, Theorem 9 and its corollaries.
M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Lemma D.4.1, the `K = ℚ` case with the classical constant.

This is Layer 5.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Matrix Module NumberField Real

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ}

/-- **Rank–nullity, in the form Layer 5.5 needs it.** The solution space of `A x = 0` has
dimension `N − rank A`, with `N` the number of columns. `Matrix.rank` is by definition the rank of
`A.mulVecLin`, so nothing but Mathlib's rank–nullity theorem is used. -/
theorem finrank_ker_mulVecLin {μ : Type*} (A : Matrix μ ι K) :
    finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, ← Matrix.rank] at h
  omega

end Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The Arakelov height of the row space, in the absolute normalization, against the absolute
sup-norm height of the entries: `H_Ar^row(A) ^ (1/d) ≤ (√N · H(A) ^ (1/d)) ^ m`. This is the one
step of Layer 5.5 that produces the `√N`. -/
theorem arakelovMulHeight_span_range_row_rpow_le [Nonempty ι] (A : Matrix (Fin m) ι K) :
    (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹
      ≤ (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^ A.rank := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hH : (0 : ℝ) < A.mulHeight := Matrix.mulHeight_pos A
  set X : ℝ := (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) * A.mulHeight with hXdef
  have hX0 : 0 < X := by rw [hXdef]; positivity
  have hXrpow : X ^ (finrank ℚ K : ℝ)⁻¹
      = Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
    rw [hXdef, Real.mul_rpow (by positivity) hH.le, ← Real.rpow_mul hcard.le,
      totalWeight_eq_finrank, Real.sqrt_eq_rpow]
    congr 2
    have : ((finrank ℚ K : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    field_simp
  have hpow : (X ^ A.rank) ^ (finrank ℚ K : ℝ)⁻¹ = (X ^ (finrank ℚ K : ℝ)⁻¹) ^ A.rank := by
    rw [← Real.rpow_natCast X A.rank, ← Real.rpow_natCast (X ^ (finrank ℚ K : ℝ)⁻¹) A.rank,
      ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, mul_comm]
  calc (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹
      ≤ (X ^ A.rank) ^ (finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow (Submodule.arakelovMulHeight_pos _).le
          (Matrix.arakelovMulHeight_span_range_row_le_pow A) (by positivity)
    _ = _ := by rw [hpow, hXrpow]

open scoped Classical in
/-- **Layer 5.5 — the entry-height corollary** (Bombieri–Gubler, Corollary 2.9.9). A basis of the
solution space of `A x = 0` with coordinates integral over `ℤ` and

`∏ₗ H(xₗ) ≤ |D| ^ (k / (2 d)) · (√N · H(A)) ^ m`,

all heights absolute, `H(A)` the height of the *entries* of `A` and `k = dim ker A = N − m`. -/
theorem exists_basis_ker_prod_absMulHeight_le_entries [Nonempty ι] (A : Matrix (Fin m) ι K)
    {k : ℕ} (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight fun j ↦ (b l : ι → K) j) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^ A.rank := by
  obtain ⟨b, hint, hle⟩ := exists_basis_ker_prod_absMulHeight_le A hk
  refine ⟨b, hint, hle.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (arakelovMulHeight_span_range_row_rpow_le A)
    (Real.rpow_nonneg (abs_nonneg _) _)

open scoped Classical in
/-- **Layer 5.5 — a single small solution** (Bombieri–Gubler, Corollary 2.9.9). With `N` columns,
`m < N` independent rows and `d = [K : ℚ]`, the system `A x = 0` has a nonzero solution with
coordinates integral over `ℤ` and

`H(x) ≤ |D| ^ (1 / (2 d)) · (√N · H(A)) ^ (m / (N − m))`,

absolute heights throughout. Over `ℚ` this is the classical Siegel lemma with `√N` in place of
`N`. -/
theorem exists_ne_zero_mem_ker_absMulHeight_le (A : Matrix (Fin m) ι K)
    (hm : A.rank < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^
              ((A.rank : ℝ) / (Fintype.card ι - A.rank)) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (Nat.zero_le A.rank |>.trans_lt hm)
  set k : ℕ := Fintype.card ι - A.rank with hkdef
  have hk : finrank K (LinearMap.ker A.mulVecLin) = k := Matrix.finrank_ker_mulVecLin A
  have hk0 : 0 < k := by omega
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  obtain ⟨b, hint, hle⟩ := exists_basis_ker_prod_absMulHeight_le_entries A hk
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 hk0
  obtain ⟨l₀, hl₀⟩ := Finite.exists_min fun l : Fin k ↦ absMulHeight fun j ↦ (b l : ι → K) j
  set C : ℝ := Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹ with hCdef
  have hC0 : 0 < C := by
    rw [hCdef]
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hH : (0 : ℝ) < A.mulHeight := Matrix.mulHeight_pos A
    positivity
  set H : ℝ := absMulHeight fun j ↦ (b l₀ : ι → K) j with hHdef
  have hH1 : 1 ≤ H := one_le_absMulHeight _
  have hpow : H ^ k ≤ |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) * C ^ A.rank
      := by
    refine le_trans ?_ hle
    calc H ^ k = ∏ _l : Fin k, H := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ l, absMulHeight fun j ↦ (b l : ι → K) j :=
          Finset.prod_le_prod₀ (fun l _ ↦ by positivity) fun l _ ↦ hl₀ l
  have hfinal : H ≤ |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
      * C ^ ((A.rank : ℝ) / (Fintype.card ι - A.rank)) := by
    have hstep := Real.rpow_le_rpow (by positivity) hpow
      (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by linarith) hk0.ne'] at hstep
    refine hstep.trans (le_of_eq ?_)
    have hD : (|(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))) ^ ((k : ℝ)⁻¹)
        = |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp
    have hCk : (C ^ A.rank) ^ ((k : ℝ)⁻¹)
        = C ^ ((A.rank : ℝ) / (Fintype.card ι - A.rank)) := by
      rw [← Real.rpow_natCast C A.rank, ← Real.rpow_mul hC0.le]
      congr 1
      rw [hkdef, Nat.cast_sub hm.le]
      field_simp
    rw [Real.mul_rpow (by positivity) (by positivity), hD, hCk]
  refine ⟨fun j ↦ (b l₀ : ι → K) j, ?_, ?_, hint l₀, hfinal⟩
  · intro h0
    refine b.ne_zero l₀ ?_
    ext j
    exact congrFun h0 j
  · have hmem := (b l₀).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
    exact hmem

open scoped Classical in
/-- **Layer 5.5 with the rank read off the rows**, the shape the roadmap states: `m` independent
rows and `m < N` give a nonzero integral solution of height at most
`|D| ^ (1 / (2 d)) · (√N · H(A)) ^ (m / (N − m))`. -/
theorem exists_ne_zero_mem_ker_absMulHeight_le_of_linearIndependent_row (A : Matrix (Fin m) ι K)
    (hA : LinearIndependent K A.row) (hm : m < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
      absMulHeight x ≤
        |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
          * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^
              ((m : ℝ) / (Fintype.card ι - m)) := by
  have hr : A.rank = m := (Matrix.linearIndependent_row_iff_rank_eq A).1 hA
  have h := exists_ne_zero_mem_ker_absMulHeight_le A (by rw [hr]; exact hm)
  rwa [hr] at h

end NumberField

/-!
### Examples

The acceptance test the roadmap states for the whole of Layer 5: over `ℚ` the classical `N` of
Siegel's lemma becomes `√N`.
-/

section Examples

open Matrix Module NumberField Real

/-- **Acceptance test: over `ℚ` the bound is `(√N · H(A)) ^ (m / (N − m))`.** The discriminant is
`1` and the degree is `1`, so both exponents collapse and what is left is the classical shape of
Siegel's lemma with `√N` in place of `N` — which is Bombieri and Vaaler's improvement, and the
whole point of Layers 5.2–5.5. A development in which the two normalizations of Layer 0 have been
interchanged produces `N` here and is refuted. -/
example {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι ℚ)
    (hA : LinearIndependent ℚ A.row) (hm : m < Fintype.card ι) :
    ∃ x : ι → ℚ, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
      NumberField.absMulHeight x ≤
        (Real.sqrt (Fintype.card ι) * A.mulHeight) ^ ((m : ℝ) / (Fintype.card ι - m)) := by
  obtain ⟨x, hx0, hker, hint, hle⟩ :=
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le_of_linearIndependent_row A hA hm
  refine ⟨x, hx0, hker, hint, hle.trans (le_of_eq ?_)⟩
  rw [NumberField.discr_rat, CommSemiring.finrank_self]
  norm_num

/-- **Conformance.** The two statements of the milestone: the product bound over a basis of the
solution space, and the single small solution extracted from it. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {m : ℕ} (A : Matrix (Fin m) ι K) {k : ℕ} (hk : finrank K (LinearMap.ker A.mulVecLin) = k)
    (hm : A.rank < Fintype.card ι) :
    (∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
        (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
        (∏ l, NumberField.absMulHeight fun j ↦ (b l : ι → K) j) ≤
          |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
            * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^ A.rank) ∧
      ∃ x : ι → K, x ≠ 0 ∧ A.mulVec x = 0 ∧ (∀ j, IsIntegral ℤ (x j)) ∧
        NumberField.absMulHeight x ≤
          |(NumberField.discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹
            * (Real.sqrt (Fintype.card ι) * A.mulHeight ^ (finrank ℚ K : ℝ)⁻¹) ^
                ((A.rank : ℝ) / (Fintype.card ι - A.rank)) :=
  ⟨NumberField.exists_basis_ker_prod_absMulHeight_le_entries A hk,
    NumberField.exists_ne_zero_mem_ker_absMulHeight_le A hm⟩

end Examples

end
