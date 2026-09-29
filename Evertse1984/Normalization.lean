/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.PlaceProd

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import DiophantineApproximation.UnitNormalization

/-!
# Normalizing a tuple of `S`-integers by an `S`-unit

For the proof of Theorem 1, Evertse (1984, §3) chooses, by an argument of Schmidt, homogeneous
coordinates that are algebraic integers whose conjugates are at most a constant times
`H(X) ^ (1 / [K : ℚ])`. Here the same normalization is done with an `S`-unit `u`: for a nonzero
tuple `x` of `S`-integers, `u • x` is a tuple of algebraic integers with

```text
‖u x_i‖ ≤ C · (∏_{v ∈ S∞ ∪ S} max_i ‖x_i‖_v) ^ (1 / [K : ℚ]).
```

Scaling by an `S`-unit changes neither `∏_i ∏_{v ∈ S∞ ∪ S} ‖x_i‖_v` nor the product on the right
(the `S`-product formula), so this is all the proof of Theorem 1 needs. The unit is found by
approximating a trace-zero target vector by the logarithms of an `S`-unit
(`NumberField.SUnit.exists_forall_abs_log_sub_le` of `DiophantineApproximation`, from the
`S`-unit lattice of `ArithmeticHeights` 6.5): at the places of `S` the target makes `u x`
integral, at the infinite places it balances the sizes.

## Main results

* `NumberField.exists_pos_forall_exists_unit_house_le`: **the normalization**.
* `NumberField.mulHeight_le_placeProd_univ`: the height of a tuple of `S`-integers is at most its
  product over `S∞ ∪ S`.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §3; W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Math. **785** (1980),
p. 63.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- **The height of a tuple of `S`-integers is at most its product over `S∞ ∪ S`.** -/
theorem mulHeight_le_placeProd_univ {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight x ≤ placeProd S Set.univ (fun v ↦ ⨆ i, v (x i)) := by
  refine (mulHeight_le_prod_of_forall_mem_integer S hx hxS).trans_eq ?_
  simp only [placeProd, Set.mulIndicator_univ]
  rfl

/-- **The `S`-product formula** in the notation of `NumberField.placeProd`. -/
theorem placeProd_univ_eq_one_of_mem_unit {u : Kˣ}
    (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    placeProd S Set.univ (fun v ↦ v (u : K)) = 1 := by
  refine Eq.trans ?_ (prod_apply_eq_one_of_mem_unit S hu)
  simp only [placeProd, Set.mulIndicator_univ]
  rfl

/-- The house is at most any bound on the infinite places. -/
theorem house_le_of_forall_infinitePlace_le {α : K} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ w : InfinitePlace K, w α ≤ B) : house α ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun φ ↦ ?_
  rw [canonicalEmbedding.apply_at, ← InfinitePlace.apply]
  exact h _

/-- **Normalization by an `S`-unit** (Schmidt's normalization, as Evertse uses it in §3). There is
`C > 0` such that every nonzero tuple `x` of `S`-integers has an `S`-unit multiple `u • x` that is
a tuple of algebraic integers with `‖u x_i‖ ≤ C · (∏_{v ∈ S∞ ∪ S} max_i ‖x_i‖_v) ^ (1 / [K : ℚ])`.
-/
theorem exists_pos_forall_exists_unit_house_le (ι : Type*) [Finite ι] :
    ∃ C > 0, ∀ x : ι → K, x ≠ 0 → (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      ∃ u : Kˣ, u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
        (∀ i, IsIntegral ℤ ((u : K) * x i)) ∧
        ∀ i, house ((u : K) * x i) ≤
          C * placeProd S Set.univ (fun v ↦ ⨆ i, v (x i)) ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨R, hR0, hR⟩ := SUnit.exists_forall_abs_log_sub_le S
  set D : ℝ := ((finrank ℚ K : ℕ) : ℝ) with hD
  have hDpos : 0 < D := Nat.cast_pos.mpr finrank_pos
  set A : ℝ := S.card * R with hA
  refine ⟨Real.exp (A / D + R), Real.exp_pos _, fun x hx hxS ↦ ?_⟩
  set M : AbsoluteValue K ℝ → ℝ := fun v ↦ ⨆ i, v (x i) with hMdef
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hle : ∀ (v : AbsoluteValue K ℝ) i, v (x i) ≤ M v :=
    fun v i ↦ le_ciSup (f := fun i ↦ v (x i)) (Finite.bddAbove_range _) i
  have hMpos : ∀ v, 0 < M v := fun v ↦ (v.pos hi₀).trans_le (hle v i₀)
  set Linf : ℝ := ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (M w.1) with hLinf
  set Lfin : ℝ := ∑ P ∈ S, Real.log (M (FinitePlace.mk P).1) with hLfin
  set L : ℝ := Real.log (placeProd S Set.univ M) with hLdef
  have hL : L = Linf + Lfin := by
    have hP : placeProd S Set.univ M =
        (∏ w : InfinitePlace K, M w.1 ^ w.mult) * ∏ P ∈ S, M (FinitePlace.mk P).1 := by
      simp only [placeProd, Set.mulIndicator_univ]
    rw [hLdef, hP, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ ↦ (pow_pos (hMpos _) _).ne')
      (Finset.prod_ne_zero_iff.mpr fun P _ ↦ (hMpos _).ne'),
      Real.log_prod (fun w _ ↦ (pow_pos (hMpos _) _).ne'),
      Real.log_prod (fun P _ ↦ (hMpos _).ne')]
    simp only [Real.log_pow, hLinf, hLfin]
  set ℓ : ℝ := (L + A) / D with hℓ
  -- the target: `ℓ - log M_w` at the infinite places, `-R - log M_P` at the places of `S`
  obtain ⟨y, hyinf, hyfin⟩ := hR (fun w ↦ (w.mult : ℝ) * (ℓ - Real.log (M w.1)))
    (fun P ↦ -R - Real.log (M (FinitePlace.mk P.1).1)) (by
      have hmult : ∑ w : InfinitePlace K, (w.mult : ℝ) * (ℓ - Real.log (M w.1)) =
          D * ℓ - Linf := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hLinf, hD]
        rw [← Nat.cast_sum, InfinitePlace.sum_mult_eq]
      rw [hmult, Finset.sum_coe_sort S (fun P ↦ -R - Real.log (M (FinitePlace.mk P).1)),
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hLfin, hℓ, hA]
      field_simp
      linarith)
  have hy0 : ((y : Kˣ) : K) ≠ 0 := Units.ne_zero _
  -- At a place of `S`, `|u|_P · M_P ≤ 1`.
  have hfin : ∀ P ∈ S, FinitePlace.mk P ((y : Kˣ) : K) * M (FinitePlace.mk P).1 ≤ 1 := by
    intro P hP
    have h := (abs_le.mp (hyfin ⟨P, hP⟩)).2
    have hpos : 0 < FinitePlace.mk P ((y : Kˣ) : K) := FinitePlace.pos_iff.mpr hy0
    rw [← Real.log_le_log_iff (mul_pos hpos (hMpos _)) one_pos, Real.log_mul hpos.ne'
      (hMpos _).ne', Real.log_one]
    linarith
  -- At an infinite place, `log (|u|_w · M_w) ≤ ℓ + R`.
  have hinf : ∀ w : InfinitePlace K,
      Real.log (w ((y : Kˣ) : K)) + Real.log (M w.1) ≤ ℓ + R := by
    intro w
    have hmult1 : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
    have h := (abs_le.mp (hyinf w)).2
    have hbound : Real.log (w ((y : Kˣ) : K)) + Real.log (M w.1) - ℓ ≤ R := by
      by_contra hcon
      push Not at hcon
      have : R < w.mult * (Real.log (w ((y : Kˣ) : K)) + Real.log (M w.1) - ℓ) :=
        lt_of_lt_of_le hcon (le_mul_of_one_le_left (hR0.trans hcon.le) hmult1)
      linarith
    linarith
  refine ⟨(y : Kˣ), y.2, fun i ↦ ?_, fun i ↦ ?_⟩
  · -- integrality: every finite place is at most `1`
    have hmem : ((y : Kˣ) : K) * x i ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).integer K := by
      rw [Set.mem_integer_iff_finitePlace]
      intro P _
      rw [map_mul]
      by_cases hP : P ∈ S
      · exact (mul_le_mul_of_nonneg_left (hle _ i) (apply_nonneg _ _)).trans (hfin P hP)
      · rw [(Set.mem_unit_iff_finitePlace _ _).mp y.2 P (by simpa using hP), one_mul]
        exact (Set.mem_integer_iff_finitePlace _ _).mp (hxS i) P (by simpa using hP)
    obtain ⟨a, ha⟩ := Set.mem_integer_empty_iff.mp hmem
    rw [← ha]
    exact a.isIntegral_coe
  · have hB : 0 ≤ Real.exp (A / D + R) * placeProd S Set.univ M ^ D⁻¹ :=
      mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (placeProd_nonneg S _ fun v _ ↦ (hMpos v).le) _)
    refine house_le_of_forall_infinitePlace_le hB fun w ↦ ?_
    have hw0 : 0 < w ((y : Kˣ) : K) := InfinitePlace.pos_iff.mpr hy0
    have hPpos : 0 < placeProd S Set.univ M := placeProd_pos S _ fun v _ ↦ hMpos v
    calc w (((y : Kˣ) : K) * x i) ≤ w ((y : Kˣ) : K) * M w.1 := by
          rw [map_mul]; exact mul_le_mul_of_nonneg_left (hle _ i) hw0.le
      _ = Real.exp (Real.log (w ((y : Kˣ) : K)) + Real.log (M w.1)) := by
          rw [Real.exp_add, Real.exp_log hw0, Real.exp_log (hMpos _)]
      _ ≤ Real.exp (ℓ + R) := Real.exp_le_exp.mpr (hinf w)
      _ = Real.exp (A / D + R) * placeProd S Set.univ M ^ D⁻¹ := by
          rw [Real.rpow_def_of_pos hPpos, ← Real.exp_add, ← hLdef, hℓ]
          congr 1
          field_simp
          ring

end NumberField
