/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.BetaApproximation
public import DiophantineApproximation.StammeringWords
public import ForMathlib.Analysis.Real.BetaExpansion
public import ForMathlib.NumberTheory.PisotNumber
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

-- Used only inside proofs.
import AdamczewskiBugeaud2007.PisotSubspace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.LinearCombination

/-!
# K. Schmidt's theorem: `β`-expansions of the elements of `ℚ(β)`

**K. Schmidt (1980).** For a Pisot number `β`, the `β`-expansion of every element of
`ℚ(β) ∩ [0, 1)` is eventually periodic. Adamczewski–Bugeaud use it to derive Theorem 5A from
Theorem 5.

The proof is Schmidt's. The orbit `T ^ n x` of `x` under the `β`-transformation is
`β ^ n x - P_n (β)`, with `P_n` the digit polynomial, so it stays in `ℚ(β)`, and a fixed integer
multiple `q T ^ n x` is an algebraic integer. At the real place `0 ≤ T ^ n x < 1`, and at every
other complex embedding `σ` the conjugate `|σ β| < 1` makes `σ (T ^ n x)` at most
`|σ x| + ⌊β⌋ / (1 - |σ β|)`, uniformly in `n`. There are only finitely many algebraic integers of
`ℚ(β)` with all conjugates bounded (`NumberField.Embeddings.finite_of_norm_le`), so the orbit is
finite, it returns, and the digits `⌊β T ^ n x⌋` repeat.

## Main results

* `Real.iterate_betaTransform_eq`: `T ^ n x = β ^ n x - P_n (β)`.
* `Real.isEventuallyPeriodic_betaDigits_of_mem_adjoin`: **K. Schmidt's theorem**.

## Implementation notes

⚠ **Only the Pisot case.** For a Salem number the conjugates on the unit circle give no uniform
bound, and whether every element of `ℚ(β) ∩ [0, 1)` has an eventually periodic `β`-expansion is
open (Adamczewski–Bugeaud 2007, after Theorem 5A).

## References

K. Schmidt, *On periodic expansions of Pisot numbers and Salem numbers*, Bull. London Math. Soc.
**12** (1980), 269–278; B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I.
Expansions in integer bases*, Annals of Mathematics **165** (2007), 547–565, §4.
-/

@[expose] public section

open IntermediateField Polynomial Finset

namespace Real

variable {β x : ℝ}

/-- **The orbit of the `β`-transformation**: `T ^ n x = β ^ n x - P_n (β)`, with `P_n` the digit
polynomial of the first `n` `β`-digits. -/
theorem iterate_betaTransform_eq (hβ : 0 < β) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    (betaTransform β)^[n] x
      = β ^ n * x - aeval β (digitPoly (fun k ↦ (betaDigits β x k : ℤ)) n) := by
  have h := eq_sum_betaDigits_add hβ hx n
  have hβn : β ^ n ≠ 0 := pow_ne_zero _ hβ.ne'
  rw [← pow_mul_sum_div_pow hβ.ne']
  simp only [Int.cast_natCast]
  have h' : (betaTransform β)^[n] x / β ^ n
      = x - ∑ k ∈ range n, (betaDigits β x k : ℝ) / β ^ (k + 1) := by linarith
  have h'' := (div_eq_iff hβn).mp h'
  linear_combination h''

/-- **K. Schmidt's theorem.** For a Pisot number `β`, the `β`-expansion of every element of
`ℚ(β) ∩ [0, 1)` is eventually periodic. -/
theorem isEventuallyPeriodic_betaDigits_of_mem_adjoin (hβ : IsPisot β)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hxK : x ∈ ℚ⟮β⟯) :
    Function.IsEventuallyPeriodic (betaDigits β x) := by
  classical
  obtain ⟨hβ1, hint, hconj⟩ := hβ
  have hβ0 : 0 < β := by linarith
  have hintQ : IsIntegral ℚ β := hint.tower_top
  have : FiniteDimensional ℚ ℚ⟮β⟯ := adjoin.finiteDimensional hintQ
  have : NumberField ℚ⟮β⟯ := {}
  set K := ℚ⟮β⟯ with hKdef
  set b : K := AdjoinSimple.gen ℚ β with hbdef
  have hb : algebraMap K ℝ b = β := AdjoinSimple.algebraMap_gen ℚ β
  have hbint : IsIntegral ℤ b :=
    (isIntegral_algHom_iff (algebraMap K ℝ).toIntAlgHom (algebraMap K ℝ).injective).mp
      (by rw [RingHom.toIntAlgHom_apply, hb]; exact hint)
  set xK : K := ⟨x, hxK⟩ with hxKdef
  have hxK' : algebraMap K ℝ xK = x := rfl
  set d : ℕ → ℤ := fun k ↦ (betaDigits β x k : ℤ) with hddef
  have hd : ∀ k, |(d k : ℝ)| ≤ ⌊β⌋₊ := fun k ↦ by
    simp only [hddef, Int.cast_natCast, Nat.abs_cast]
    exact_mod_cast betaDigits_le_floor hβ0 hx k
  -- the orbit in `ℚ(β)`
  set t : ℕ → K := fun n ↦ b ^ n * xK - aeval b (digitPoly d n) with htdef
  have ht : ∀ n, algebraMap K ℝ (t n) = (betaTransform β)^[n] x := by
    intro n
    rw [iterate_betaTransform_eq hβ0 hx n]
    simp only [htdef, map_sub, map_mul, map_pow, hb, hxK', ← aeval_algebraMap_apply]
    rfl
  -- a fixed integer multiple of the orbit is integral
  obtain ⟨q, hq0, hqint⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic xK))
  have hPint : ∀ P : ℤ[X], aeval b P ∈ integralClosure ℤ K := fun P ↦
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hbint) (aeval_mem_adjoin_singleton ℤ b)
  have htint : ∀ n, IsIntegral ℤ (q • t n) := by
    intro n
    have e : q • t n = b ^ n * (q • xK) - algebraMap ℤ K q * aeval b (digitPoly d n) := by
      rw [Algebra.smul_def, Algebra.smul_def, htdef]
      ring
    rw [e]
    exact ((hbint.pow n).mul hqint).sub (isIntegral_algebraMap.mul (hPint _))
  -- the conjugates of the orbit are bounded
  set B : (K →+* ℂ) → ℝ := fun φ ↦ ‖φ xK‖ + ⌊β⌋₊ / |1 - ‖φ b‖| with hBdef
  set R : ℝ := |(q : ℝ)| * (1 + ∑ φ, B φ) with hRdef
  have hB0 : ∀ φ, 0 ≤ B φ := fun φ ↦ by positivity
  have hbound : ∀ n, ∀ φ : K →+* ℂ, ‖φ (q • t n)‖ ≤ R := by
    intro n φ
    rw [map_zsmul, zsmul_eq_mul, norm_mul, Complex.norm_intCast, hRdef]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases hφ : φ = Complex.ofRealHom.comp (algebraMap K ℝ)
    · rw [hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs,
        ht, abs_of_nonneg (iterate_betaTransform_mem_Ico hx n).1]
      have := (iterate_betaTransform_mem_Ico (β := β) hx n).2
      linarith [sum_nonneg fun φ (_ : φ ∈ univ) ↦ hB0 φ]
    · have hne : φ b ≠ (β : ℂ) := fun h ↦ hφ (ringHom_eq_of_apply_gen_eq h)
      have hlt : ‖φ b‖ < 1 := hconj _ (apply_gen_mem_aroots hintQ φ) hne
      have e : φ (t n) = φ b ^ n * φ xK - aeval (φ b) (digitPoly d n) := by
        rw [htdef]
        simp only [map_sub, map_mul, map_pow]
        congr 1
        exact (aeval_algHom_apply φ.toIntAlgHom b _).symm
      have h1 : ‖φ (t n)‖ ≤ B φ := by
        rw [e]
        change _ ≤ ‖φ xK‖ + ⌊β⌋₊ / |1 - ‖φ b‖|
        rw [abs_of_pos (sub_pos.mpr hlt)]
        refine (norm_sub_le _ _).trans (add_le_add ?_
          (Complex.norm_aeval_digitPoly_le_of_lt_one hd hlt n))
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hlt.le)
      have h2 : B φ ≤ ∑ φ, B φ := single_le_sum (fun φ _ ↦ hB0 φ) (mem_univ φ)
      linarith
  -- the orbit is finite, so it returns
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ R
  have hmaps : ∀ n, q • t n ∈ {y : K | IsIntegral ℤ y ∧ ∀ φ : K →+* ℂ, ‖φ y‖ ≤ R} :=
    fun n ↦ ⟨htint n, hbound n⟩
  have := hfin.to_subtype
  obtain ⟨m, n, hmn, hmn'⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (⟨q • t n, hmaps n⟩ : {y // y ∈ {y : K | IsIntegral ℤ y ∧
      ∀ φ : K →+* ℂ, ‖φ y‖ ≤ R}}))
  have heq : t m = t n := smul_right_injective K hq0 (congrArg Subtype.val hmn')
  have hT : (betaTransform β)^[m] x = (betaTransform β)^[n] x := by rw [← ht, ← ht, heq]
  have hper : ∀ {m n : ℕ}, m < n → (betaTransform β)^[m] x = (betaTransform β)^[n] x →
      Function.IsEventuallyPeriodic (betaDigits β x) := by
    intro m n hlt hT
    refine ⟨m, n - m, by omega, fun k hk ↦ ?_⟩
    simp only [betaDigits]
    rw [show k + (n - m) = k - m + n by omega, Function.iterate_add_apply, ← hT,
      ← Function.iterate_add_apply, show k - m + m = k by omega]
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hper h hT
  · exact hper h hT.symm

end Real
