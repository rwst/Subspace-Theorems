/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MahlerExponent
public import DiophantineApproximation.PolynomialEval
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Mahler's exponent of an algebraic number is at most `d - 1`

The upper bound of Layer 1.3: if `ξ` is real algebraic of degree `d` over `ℚ` then
`mahlerExponent n ξ ≤ d - 1` for every `n`. It is Liouville's inequality, read for the value of a
polynomial rather than for the distance to a fraction: for `P` of degree at most `n` with
`P ξ ≠ 0`,

```text
|P ξ| ≥ c * H(P) ^ (-(d-1)),
```

with `c` depending only on `ξ` and `n`. Since a solution counted by `mahlerExponent n ξ` has
`|P ξ| ≤ H(P) ^ (-w)` and solutions of unbounded height, `w ≤ d - 1` follows.

## Main results

* `Real.exists_pos_le_abs_aeval`: **Liouville's inequality for the value of an integer
  polynomial** at a real algebraic number.
* `Real.mahlerExponent_le_of_isAlgebraic`: **`w_n(ξ) ≤ d - 1`** for `ξ` algebraic of degree `d`.

## Implementation notes

⚠ **The exponent `d - 1` needs the norm, not the height.** Layer 0.4's fundamental inequality
gives `|γ| ≥ (H_K γ)⁻¹` at a single place, and `H_K (P ξ) ≍ H(P) ^ d`, so it proves only
`w_n ≤ d`. The missing factor is the distinguished place itself: what is bounded below by `1` is
the *norm* `∏ w, w γ ^ mult w` of an algebraic **integer**, and only the `d - 1` other places are
then estimated by `H(P)`. So this file uses `NumberField.InfinitePlace.prod_eq_abs_norm` and
integrality, not `NumberField.inv_mulHeight₁_le_prod_apply`.

⚠ **Integrality is bought with `Polynomial.scaleRoots`, not by changing `ξ`.** The natural move —
replace `ξ` by an algebraic integer `t ξ` and quote the Möbius invariance of Layer 1.2 — needs
`ℚ⟮t ξ⟯ = ℚ⟮ξ⟯` to keep the degree. Multiplying the *value* instead costs nothing:
`t ^ deg P * P ξ` is `(P.scaleRoots t) (t ξ)`, an integer polynomial evaluated at an algebraic
integer, so it lies in the ring of integers, and the factor `t ^ deg P ≤ t ^ n` is absorbed by
the constant.

⚠ **The real place is the one that is not estimated, and it has multiplicity one.** `ξ` is real,
so the embedding `ℚ⟮ξ⟯ → ℂ` through `ℝ` is `ComplexEmbedding.IsReal` and its place has
`mult = 1`; that is what makes `∑ w ≠ w₀, mult w = d - 1` rather than `d - 2`.

⚠ **The bound is not sharp and Layer 7.3 is what sharpens it.** Schmidt's theorem gives
`w_n α = min n (d - 1)`; Layer 1.3 supplies the upper bound `d - 1` and the lower bound `n` (for
`ξ` not algebraic of degree at most `n`), and the two meet only after Layer 7.1.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Theorem A.1
and §3.4. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University
Press (2006), Theorem 1.5.21.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open IntermediateField Polynomial NumberField
open scoped ENNReal NNReal

namespace Real

/-! ### The value of a polynomial at an infinite place -/

/-- The triangle inequality for an evaluation, read at an infinite place of a number field: the
same statement as `Polynomial.abs_aeval_le`, with the archimedean absolute value replaced by an
arbitrary one. -/
theorem infinitePlace_aeval_le {K : Type*} [Field K] (w : InfinitePlace K) (x : K) {P : ℤ[X]}
    {n : ℕ} (hP : P.natDegree ≤ n) :
    w (aeval x P) ≤ ((n : ℝ) + 1) * (P.supNorm * max 1 (w x) ^ n) := by
  have hM1 : (1 : ℝ) ≤ max 1 (w x) := le_max_left _ _
  have hlt : P.natDegree < n + 1 := by omega
  have hsum : w (∑ i ∈ Finset.range (n + 1), (P.coeff i) • x ^ i)
      ≤ ∑ i ∈ Finset.range (n + 1), w ((P.coeff i) • x ^ i) := by
    simpa only [← InfinitePlace.coe_apply] using
      AbsoluteValue.sum_le w.1 (Finset.range (n + 1)) fun i ↦ (P.coeff i) • x ^ i
  rw [aeval_eq_sum_range' hlt]
  refine le_trans hsum ?_
  have hbound : ∀ i ∈ Finset.range (n + 1),
      w ((P.coeff i) • x ^ i) ≤ P.supNorm * max 1 (w x) ^ n := by
    intro i hi
    have hcast : w ((P.coeff i : K)) = |((P.coeff i : ℤ) : ℝ)| := by
      rw [← InfinitePlace.norm_embedding_eq, map_intCast, Complex.norm_intCast]
    rw [zsmul_eq_mul, map_mul, map_pow, hcast]
    have h1 : |((P.coeff i : ℤ) : ℝ)| ≤ P.supNorm := P.abs_coeff_le_supNorm i
    have h2 : w x ^ i ≤ max 1 (w x) ^ n :=
      (pow_le_pow_left₀ (apply_nonneg w x) (le_max_right 1 (w x)) i).trans
        (pow_le_pow_right₀ hM1 (Finset.mem_range_succ_iff.1 hi))
    exact mul_le_mul h1 h2 (by positivity) P.supNorm_nonneg
  calc ∑ i ∈ Finset.range (n + 1), w ((P.coeff i) • x ^ i)
      ≤ ∑ _i ∈ Finset.range (n + 1), P.supNorm * max 1 (w x) ^ n := Finset.sum_le_sum hbound
    _ = ((n : ℝ) + 1) * (P.supNorm * max 1 (w x) ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Liouville's inequality for a polynomial value -/

/-- **Liouville's inequality for the value of an integer polynomial.** If `ξ` is real algebraic of
degree `d` then no integer polynomial of degree at most `n` takes at `ξ` a nonzero value smaller
than `c * H(P) ^ (-(d-1))`, for a constant `c` depending only on `ξ` and `n`. -/
theorem exists_pos_le_abs_aeval {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℤ[X], P.natDegree ≤ n → aeval ξ P ≠ 0 →
      c * P.supNorm ^ (-(((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ)) ≤ |aeval ξ P| := by
  classical
  have hintQ : IsIntegral ℚ ξ := hξ.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮ξ⟯ := IntermediateField.adjoin.finiteDimensional hintQ
  have hnf : NumberField ℚ⟮ξ⟯ := {}
  set K := ℚ⟮ξ⟯
  set g : K := IntermediateField.AdjoinSimple.gen ℚ ξ with hgdef
  have hgmap : algebraMap K ℝ g = ξ := IntermediateField.AdjoinSimple.algebraMap_gen ℚ ξ
  have hinj : Function.Injective (algebraMap K ℝ) := (algebraMap K ℝ).injective
  -- transfer of integrality from `ℝ` to `K`
  have hpull : ∀ x : K, IsIntegral ℤ (algebraMap K ℝ x) → IsIntegral ℤ x := by
    intro x hx
    obtain ⟨m, hmonic, hm⟩ := hx
    refine ⟨m, hmonic, hinj ?_⟩
    rw [map_zero, hom_eval₂]
    have : (algebraMap K ℝ).comp (algebraMap ℤ K) = algebraMap ℤ ℝ := by
      ext k
      simp
    rw [this]
    exact hm
  -- an integer `t` with `t * ξ` an algebraic integer
  have hξZ : IsAlgebraic ℤ ξ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 hξ
  obtain ⟨t, ht0, htint⟩ := hξZ.exists_integral_multiple
  have htR : (t : ℝ) * ξ = t • ξ := (zsmul_eq_mul _ _).symm
  have hhmap : algebraMap K ℝ ((t : K) * g) = t • ξ := by
    rw [map_mul, map_intCast, hgmap, ← htR]
  have hhint : IsIntegral ℤ ((t : K) * g) := hpull _ (by rw [hhmap]; exact htint)
  have hT1 : (1 : ℝ) ≤ |(t : ℝ)| := by
    have : (1 : ℤ) ≤ |t| := Int.one_le_abs (by omega)
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|t| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h2
  -- the distinguished real place
  set φ₀ : K →+* ℂ := Complex.ofRealHom.comp (algebraMap K ℝ) with hφ₀
  set w₀ : InfinitePlace K := InfinitePlace.mk φ₀ with hw₀def
  have hw₀apply : ∀ x : K, w₀ x = |algebraMap K ℝ x| := by
    intro x
    rw [hw₀def, InfinitePlace.apply, hφ₀]
    simp [Complex.norm_real]
  have hw₀real : w₀.IsReal := by
    rw [hw₀def, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp [hφ₀, ComplexEmbedding.conjugate]
  have hw₀mult : w₀.mult = 1 := hw₀real.mult_eq_one
  -- the degree
  set d : ℕ := Module.finrank ℚ K with hddef
  have hdeg : d = (minpoly ℚ ξ).natDegree := IntermediateField.adjoin.finrank hintQ
  have hd1 : 1 ≤ d := Module.finrank_pos
  set D : ℕ := d - 1 with hDdef
  have hDeq : ((minpoly ℚ ξ).natDegree - 1 : ℕ) = D := by omega
  have hsum : ∑ w ∈ Finset.univ.erase w₀, w.mult = D := by
    have h := InfinitePlace.sum_mult_eq (K := K)
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ w₀), hw₀mult] at h
    omega
  -- the uniform bound on the conjugates
  set M : ℝ := Finset.univ.sup' ⟨w₀, Finset.mem_univ w₀⟩ (fun w : InfinitePlace K ↦ max 1 (w g))
    with hMdef
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left 1 (w₀ g))
      (Finset.le_sup' (fun w : InfinitePlace K ↦ max 1 (w g)) (Finset.mem_univ w₀))
  have hMle : ∀ w : InfinitePlace K, max 1 (w g) ≤ M :=
    fun w ↦ Finset.le_sup' (fun w : InfinitePlace K ↦ max 1 (w g)) (Finset.mem_univ w)
  set C : ℝ := ((n : ℝ) + 1) * M ^ n with hCdef
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]
    have h1 : (1 : ℝ) ≤ M ^ n := one_le_pow₀ hM1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  set B : ℝ := |(t : ℝ)| ^ n * C with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hBdef]
    nlinarith [one_le_pow₀ hT1 (n := n)]
  refine ⟨(|(t : ℝ)| ^ n * B ^ D)⁻¹, by positivity, fun P hPdeg hPne ↦ ?_⟩
  rw [hDeq]
  -- the polynomial and its value
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hPne
  have hH1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  set γ : K := aeval g P with hγdef
  have hγmap : algebraMap K ℝ γ = aeval ξ P := by
    rw [hγdef, aeval_def, hom_eval₂]
    have : (algebraMap K ℝ).comp (algebraMap ℤ K) = algebraMap ℤ ℝ := by
      ext k
      simp
    rw [this, hgmap, ← aeval_def]
  set γ' : K := aeval ((t : K) * g) (P.scaleRoots t) with hγ'def
  have hγ'eq : γ' = (t : K) ^ P.natDegree * γ := by
    rw [hγ'def, hγdef, aeval_def, aeval_def]
    have h := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ K) g t
    simpa using h
  have hγ'int : IsIntegral ℤ γ' := by
    have hsub : Algebra.adjoin ℤ ({(t : K) * g} : Set K) ≤ integralClosure ℤ K :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hhint)
    exact hsub (Polynomial.aeval_mem_adjoin_singleton (p := P.scaleRoots t) ℤ ((t : K) * g))
  have hγ0 : γ ≠ 0 := fun h ↦ hPne (by rw [← hγmap, h, map_zero])
  have hγ'0 : γ' ≠ 0 := by
    rw [hγ'eq]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht0)) hγ0
  -- the norm of an algebraic integer is at least one in absolute value
  have hnorm : (1 : ℝ) ≤ |(Algebra.norm ℚ) γ'| := by
    have hint : IsIntegral ℤ ((Algebra.norm ℚ) γ') := Algebra.isIntegral_norm ℚ hγ'int
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      exact hγ'0 (Algebra.norm_eq_zero_iff.1 hz.symm)
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    have h2 : |(Algebra.norm ℚ) γ'| = |(z : ℚ)| := by rw [← hz]; simp
    rw [h2]
    exact_mod_cast (by exact_mod_cast this : (1 : ℚ) ≤ |(z : ℚ)|)
  -- every place is bounded by `B * H(P)`
  have hplace : ∀ w : InfinitePlace K, w γ' ≤ B * P.supNorm := by
    intro w
    have h1 : w γ' = |(t : ℝ)| ^ P.natDegree * w γ := by
      rw [hγ'eq, map_mul, map_pow]
      congr 2
      rw [← InfinitePlace.norm_embedding_eq, map_intCast, Complex.norm_intCast]
    have h2 : w γ ≤ C * P.supNorm := by
      refine le_trans (infinitePlace_aeval_le w g hPdeg) ?_
      have h3 : max 1 (w g) ^ n ≤ M ^ n := pow_le_pow_left₀ (by positivity) (hMle w) n
      rw [hCdef]
      have h4 : P.supNorm * max 1 (w g) ^ n ≤ P.supNorm * M ^ n := by
        exact mul_le_mul_of_nonneg_left h3 P.supNorm_nonneg
      nlinarith [Nat.cast_nonneg (α := ℝ) n, P.supNorm_nonneg]
    have h5 : |(t : ℝ)| ^ P.natDegree ≤ |(t : ℝ)| ^ n := pow_le_pow_right₀ hT1 hPdeg
    rw [h1, hBdef]
    calc |(t : ℝ)| ^ P.natDegree * w γ ≤ |(t : ℝ)| ^ n * (C * P.supNorm) := by
          exact mul_le_mul h5 h2 (apply_nonneg w _) (by positivity)
      _ = |(t : ℝ)| ^ n * C * P.supNorm := by ring
  -- the product formula
  have hprod : (1 : ℝ) ≤ w₀ γ' * (B * P.supNorm) ^ D := by
    have hkey : ∏ w : InfinitePlace K, w γ' ^ w.mult = |(Algebra.norm ℚ) γ'| :=
      InfinitePlace.prod_eq_abs_norm γ'
    have hsplit : ∏ w : InfinitePlace K, w γ' ^ w.mult
        = (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) * w₀ γ' ^ w₀.mult :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)).symm
    have hle : (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) ≤ (B * P.supNorm) ^ D := by
      have h1 : (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult)
          ≤ ∏ w ∈ Finset.univ.erase w₀, (B * P.supNorm) ^ w.mult := by
        apply Finset.prod_le_prod₀
        · intro w _
          positivity
        · intro w _
          exact pow_le_pow_left₀ (apply_nonneg w _) (hplace w) _
      rwa [Finset.prod_pow_eq_pow_sum, hsum] at h1
    have h1 : (1 : ℝ) ≤ (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) * w₀ γ' := by
      have h2 : (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) * w₀ γ' ^ w₀.mult
          = (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) * w₀ γ' := by
        rw [hw₀mult, pow_one]
      rw [← h2, ← hsplit, hkey]
      exact hnorm
    calc (1 : ℝ) ≤ (∏ w ∈ Finset.univ.erase w₀, w γ' ^ w.mult) * w₀ γ' := h1
      _ ≤ (B * P.supNorm) ^ D * w₀ γ' :=
          mul_le_mul_of_nonneg_right hle (apply_nonneg w₀ _)
      _ = w₀ γ' * (B * P.supNorm) ^ D := by ring
  -- unwinding
  have hw₀γ' : w₀ γ' ≤ |(t : ℝ)| ^ n * |aeval ξ P| := by
    rw [hγ'eq, hw₀apply, map_mul, map_pow, map_intCast, hγmap, abs_mul, abs_pow]
    have : |(t : ℝ)| ^ P.natDegree ≤ |(t : ℝ)| ^ n := pow_le_pow_right₀ hT1 hPdeg
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hfinal : (1 : ℝ) ≤ |(t : ℝ)| ^ n * |aeval ξ P| * (B ^ D * P.supNorm ^ D) := by
    calc (1 : ℝ) ≤ w₀ γ' * (B * P.supNorm) ^ D := hprod
      _ ≤ (|(t : ℝ)| ^ n * |aeval ξ P|) * (B * P.supNorm) ^ D :=
          mul_le_mul_of_nonneg_right hw₀γ' (by positivity)
      _ = |(t : ℝ)| ^ n * |aeval ξ P| * (B ^ D * P.supNorm ^ D) := by rw [mul_pow]
  have hrpow : P.supNorm ^ (-(D : ℝ)) = (P.supNorm ^ D)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [hrpow, ← mul_inv]
  have hden : (0 : ℝ) < |(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D := by positivity
  have hkey2 : (1 : ℝ) ≤ |aeval ξ P| * (|(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D) := by
    calc (1 : ℝ) ≤ |(t : ℝ)| ^ n * |aeval ξ P| * (B ^ D * P.supNorm ^ D) := hfinal
      _ = |aeval ξ P| * (|(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D) := by ring
  calc (|(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D)⁻¹
      ≤ |aeval ξ P| * (|(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D)
          * (|(t : ℝ)| ^ n * B ^ D * P.supNorm ^ D)⁻¹ :=
        le_mul_of_one_le_left (le_of_lt (inv_pos.2 hden)) hkey2
    _ = |aeval ξ P| := by field_simp

/-! ### The upper bound on Mahler's exponent -/

/-- **Mahler's exponent of a real algebraic number of degree `d` is at most `d - 1`**, at every
degree bound `n`. -/
theorem mahlerExponent_le_of_isAlgebraic {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    mahlerExponent n ξ ≤ (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞) := by
  set D : ℕ := (minpoly ℚ ξ).natDegree - 1 with hDdef
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_abs_aeval hξ n
  rw [mahlerExponent_le_iff]
  intro w hinf
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : (D : ℝ) < (w : ℝ) := by exact_mod_cast hlt
  set B : ℝ := max 1 ((2 / c) ^ (1 / ((w : ℝ) - D))) with hBdef
  obtain ⟨P, hPmem⟩ :=
    (Polynomial.infinite_sep_lt_supNorm hinf (fun P hP ↦ hP.1) B).nonempty
  obtain ⟨⟨hdeg, hpos, hle⟩, hB⟩ := hPmem
  have hP0 : P ≠ 0 := ne_zero_of_mem_mahlerSet ⟨hdeg, hpos, hle⟩
  have hH1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  have hHB : B < P.supNorm := hB
  have hH0 : (0 : ℝ) < P.supNorm := by linarith
  have hlow := hc P hdeg (fun h ↦ by rw [h] at hpos; simp at hpos)
  -- `c ≤ H ^ (D - w)`
  have hsplit : P.supNorm ^ (-(w : ℝ)) = P.supNorm ^ (-(D : ℝ)) * P.supNorm ^ ((D : ℝ) - w) := by
    rw [← Real.rpow_add hH0]
    ring_nf
  have hpow0 : (0 : ℝ) < P.supNorm ^ (-(D : ℝ)) := Real.rpow_pos_of_pos hH0 _
  have hcle : c ≤ P.supNorm ^ ((D : ℝ) - w) := by
    have h1 : c * P.supNorm ^ (-(D : ℝ)) ≤ P.supNorm ^ (-(D : ℝ)) * P.supNorm ^ ((D : ℝ) - w) := by
      rw [← hsplit]
      exact hlow.trans hle
    exact le_of_mul_le_mul_right (by linarith [h1]) hpow0
  -- but `H ^ (w - D) ≥ 2 / c`
  have hexp : (0 : ℝ) < (w : ℝ) - D := by linarith
  have hBle : (2 / c) ^ (1 / ((w : ℝ) - D)) ≤ B := le_max_right _ _
  have hBpow : 2 / c ≤ P.supNorm ^ ((w : ℝ) - D) := by
    calc 2 / c = ((2 / c) ^ (1 / ((w : ℝ) - D))) ^ ((w : ℝ) - D) := by
          rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (by linarith),
            Real.rpow_one]
      _ ≤ P.supNorm ^ ((w : ℝ) - D) :=
          Real.rpow_le_rpow (by positivity) (le_of_lt (lt_of_le_of_lt hBle hHB)) (le_of_lt hexp)
  have hneg : P.supNorm ^ ((D : ℝ) - w) = (P.supNorm ^ ((w : ℝ) - D))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt hH0)]
    ring_nf
  rw [hneg] at hcle
  have hpos2 : (0 : ℝ) < P.supNorm ^ ((w : ℝ) - D) := Real.rpow_pos_of_pos hH0 _
  have hcontra : (P.supNorm ^ ((w : ℝ) - D))⁻¹ ≤ c / 2 := by
    rw [inv_le_comm₀ hpos2 (by positivity), inv_div]
    exact hBpow
  linarith

/-! ### Acceptance criteria -/

/-- **Acceptance test: Liouville's inequality for a polynomial value.** -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℤ[X], P.natDegree ≤ n → aeval ξ P ≠ 0 →
      c * P.supNorm ^ (-(((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ)) ≤ |aeval ξ P| :=
  exists_pos_le_abs_aeval hξ n

/-- **Acceptance test: `w_n ≤ d - 1`.** -/
example {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    mahlerExponent n ξ ≤ (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞) :=
  mahlerExponent_le_of_isAlgebraic hξ n

/-- **Acceptance test: a rational number has Mahler exponent `0` at every degree.** Its minimal
polynomial has degree one, so the bound reads `w_n ≤ 0`; at `n = 1` this recovers Layer 1.2's
`Real.mahlerExponent_one_ratCast` from the general upper bound. -/
example (q : ℚ) (n : ℕ) : mahlerExponent n (q : ℝ) = 0 := by
  have halg : IsAlgebraic ℚ ((q : ℝ)) := ⟨X - C q, X_sub_C_ne_zero q, by simp⟩
  have hmin : (minpoly ℚ ((q : ℝ))).natDegree = 1 := by
    rw [show ((q : ℝ)) = algebraMap ℚ ℝ q from rfl, minpoly.eq_X_sub_C ℝ q, natDegree_X_sub_C]
  have := mahlerExponent_le_of_isAlgebraic halg n
  rw [hmin] at this
  simpa using this

end Real
