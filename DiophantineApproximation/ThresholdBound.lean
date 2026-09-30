/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ThresholdHeights

/-!
# The threshold of the parametric Subspace Theorem is linear in the heights

The threshold `NumberField.parametricThreshold` of the interval form of Layer 6.1 lives on the
scale of `log Q`. This file shows that it is at most `a Λ`, where

`Λ = formLogHeight + log |D_K| + ∑_{v ∈ Sfin} log N(v) + 1`

(`NumberField.thresholdScale`) and `a` is an explicit formula in `#ι`, `[K : ℚ]`, the number of
infinite places, `#Sfin`, `ε` and `A`. The local bounds of `ThresholdHeights.lean` are put in
the form `X ≤ exp (c Λ)`, whose coefficients add up under products and multiply under powers.

## Main results

* `NumberField.parametricThreshold_le`: `parametricThreshold ≤ parametricCoeff · Λ`.
* `NumberField.thresholdScale`: the scale `Λ`.
* `NumberField.evertseConst_le`: the constant of Evertse's lemma is at most
  `(4 m ^ 2 max A 1) ^ m`.
* `NumberField.log_minimaThreshold_le`, `NumberField.log_rankThreshold_le`,
  `NumberField.log_pluckerConst_le` and `NumberField.log_wedgeWeightConst_le`: the thresholds
  of Layers 4 and 6.1 that do not involve the wedge forms.
* `NumberField.penultimateThreshold_le`: the threshold of Layer 5.6, for any forms.
* `NumberField.thresholdScale_wedgeForms_le`: the scale of the wedge forms is at most
  `wedgeScaleCoeff` times that of the forms.
* `NumberField.parametricStepThreshold_le`: the threshold along one size of subsets.

This is part of Q0.2e of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Exponential bounds -/

theorem add_one_le_exp_log_mul {a Λ : ℝ} (ha : 0 ≤ a) (hΛ : 1 ≤ Λ) :
    a + 1 ≤ Real.exp (Real.log (a + 1) * Λ) := by
  have h0 : 0 ≤ Real.log (a + 1) := Real.log_nonneg (by linarith)
  calc a + 1 = Real.exp (Real.log (a + 1)) := (Real.exp_log (by linarith)).symm
    _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right h0 hΛ)

theorem le_exp_log_add_one_mul {a Λ : ℝ} (ha : 0 ≤ a) (hΛ : 1 ≤ Λ) :
    a ≤ Real.exp (Real.log (a + 1) * Λ) :=
  (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp_log_mul ha hΛ)

theorem one_le_exp_mul {c Λ : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ) : 1 ≤ Real.exp (c * Λ) :=
  Real.one_le_exp (mul_nonneg hc hΛ)

theorem log_le_of_le_exp {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ Real.exp c) :
    Real.log x ≤ c := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hc
  · exact (Real.log_le_iff_le_exp hx).2 h

theorem exp_mul_le_exp_mul {c c' Λ : ℝ} (hc : c ≤ c') (hΛ : 0 ≤ Λ) :
    Real.exp (c * Λ) ≤ Real.exp (c' * Λ) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hc hΛ)

theorem log_abs_discr_nonneg : 0 ≤ Real.log |(discr K : ℝ)| := by
  refine Real.log_nonneg ?_
  have h : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
  exact_mod_cast h

/-- The constant of Evertse's lemma grows at most like `(4 m ^ 2 max A 1) ^ m`. -/
theorem evertseConst_le (A : ℝ) (m : ℕ) : evertseConst A m ≤ (4 * m ^ 2 * max A 1) ^ m := by
  induction m with
  | zero => simp [evertseConst]
  | succ m ih =>
    set A' := max A 1 with hA'
    set E := evertseConst A m with hE
    have hA1 : 1 ≤ A' := le_max_right _ _
    have hAA : A ≤ A' := le_max_left _ _
    have hE1 : 1 ≤ E := one_le_evertseConst A m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    set c : ℝ := 4 * ((m + 1 : ℕ) : ℝ) ^ 2 * A' with hc
    have hc' : c = 4 * ((m : ℝ) + 1) ^ 2 * A' := by rw [hc]; push_cast; ring
    have hmA : (m : ℝ) * A * E ≤ m * A' * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAA hm) (by linarith)
    have hAE : 1 ≤ A' * E := one_le_mul_of_one_le_of_one_le hA1 hE1
    have hstep : evertseConst A (m + 1) ≤ c * E := by
      change max E (max (m * E) (max (m * A * E) (2 * max 1 (m * (2 * max (m * A * E) 1)))))
        ≤ c * E
      have h1 : max ((m : ℝ) * A * E) 1 ≤ (m + 1) * A' * E :=
        max_le (by nlinarith) (by nlinarith)
      have h2 : (m : ℝ) * (2 * max ((m : ℝ) * A * E) 1) ≤ 2 * (m + 1) ^ 2 * A' * E := by
        nlinarith
      have h3 : max 1 ((m : ℝ) * (2 * max ((m : ℝ) * A * E) 1)) ≤ 2 * (m + 1) ^ 2 * A' * E :=
        max_le (by nlinarith) h2
      have hmc : (m : ℝ) ≤ 4 * (m + 1) ^ 2 * A' := by nlinarith
      have hmE : (m : ℝ) * E ≤ 4 * (m + 1) ^ 2 * A' * E :=
        mul_le_mul_of_nonneg_right hmc (by linarith)
      rw [hc']
      refine max_le (by nlinarith) (max_le hmE (max_le (by nlinarith) (by linarith)))
    have hmono : (4 * (m : ℝ) ^ 2 * A') ^ m ≤ c ^ m :=
      pow_le_pow_left₀ (by positivity) (by rw [hc']; nlinarith) m
    calc evertseConst A (m + 1) ≤ c * E := hstep
      _ ≤ c * c ^ m := mul_le_mul_of_nonneg_left (ih.trans hmono) (by positivity)
      _ = c ^ (m + 1) := by ring

section Scale

open NumberField.InfinitePlace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))

/-- **The scale of the threshold**: `formLogHeight + log |D_K| + ∑_{v ∈ Sfin} log N(v) + 1`. -/
noncomputable def thresholdScale : ℝ :=
  formLogHeight Sfin L + Real.log |(discr K : ℝ)|
    + ∑ v ∈ Sfin, Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) + 1

theorem sum_log_absNorm_nonneg :
    0 ≤ ∑ v ∈ Sfin, Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) :=
  Finset.sum_nonneg fun _ _ ↦ Real.log_natCast_nonneg _

theorem one_le_thresholdScale : 1 ≤ thresholdScale Sfin L := by
  have := formLogHeight_nonneg Sfin L
  have := log_abs_discr_nonneg (K := K)
  have := sum_log_absNorm_nonneg Sfin
  rw [thresholdScale]; linarith

theorem thresholdScale_nonneg : 0 ≤ thresholdScale Sfin L :=
  zero_le_one.trans (one_le_thresholdScale Sfin L)

theorem formLogHeight_le_thresholdScale : formLogHeight Sfin L ≤ thresholdScale Sfin L := by
  have := log_abs_discr_nonneg (K := K)
  have := sum_log_absNorm_nonneg Sfin
  rw [thresholdScale]; linarith

theorem log_abs_discr_le_thresholdScale :
    Real.log |(discr K : ℝ)| ≤ thresholdScale Sfin L := by
  have := formLogHeight_nonneg Sfin L
  have := sum_log_absNorm_nonneg Sfin
  rw [thresholdScale]; linarith

theorem sum_log_absNorm_le_thresholdScale :
    ∑ v ∈ Sfin, Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ≤ thresholdScale Sfin L := by
  have := formLogHeight_nonneg Sfin L
  have := log_abs_discr_nonneg (K := K)
  rw [thresholdScale]; linarith

/-- The coefficient of `detLogBound`: `d log N! + N! N`. -/
noncomputable def detCoeff (d N : ℕ) : ℝ := d * Real.log N.factorial + N.factorial * N

theorem detCoeff_nonneg (d N : ℕ) : 0 ≤ detCoeff d N :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (Nat.one_le_cast.2 (Nat.factorial_pos N)))) (by positivity)

theorem detLogBound_le_mul (N : ℕ) {h Λ : ℝ} (hh : h ≤ Λ) (hΛ : 1 ≤ Λ) :
    detLogBound K N h ≤ detCoeff (finrank ℚ K) N * Λ := by
  have hl : 0 ≤ Real.log N.factorial := Real.log_nonneg (Nat.one_le_cast.2 (Nat.factorial_pos N))
  have h1 : (finrank ℚ K : ℝ) * Real.log N.factorial
      ≤ (finrank ℚ K : ℝ) * Real.log N.factorial * Λ :=
    le_mul_of_one_le_right (by positivity) hΛ
  have h2 : (N.factorial : ℝ) * (N * h) ≤ N.factorial * N * Λ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hh (by positivity)
  rw [detLogBound, totalWeight_eq_finrank, detCoeff, add_mul]
  linarith

variable {Sfin L}

theorem detLogBound_formLogHeight_le (N : ℕ) :
    detLogBound K N (formLogHeight Sfin L) ≤ detCoeff (finrank ℚ K) N * thresholdScale Sfin L :=
  detLogBound_le_mul N (formLogHeight_le_thresholdScale Sfin L)
    (one_le_thresholdScale Sfin L)

theorem exp_detLogBound_le (N : ℕ) :
    Real.exp (detLogBound K N (formLogHeight Sfin L))
      ≤ Real.exp (detCoeff (finrank ℚ K) N * thresholdScale Sfin L) :=
  Real.exp_le_exp.2 (detLogBound_formLogHeight_le N)

/-- The coefficient of `invSizeBound`: `log (N + 1) + log (N ^ 2 + 1) + 2 detCoeff`. -/
noncomputable def invCoeff (d N : ℕ) : ℝ :=
  Real.log (N + 1) + Real.log (N ^ 2 + 1) + 2 * detCoeff d N

theorem invCoeff_nonneg (d N : ℕ) : 0 ≤ invCoeff d N := by
  have := detCoeff_nonneg d N
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)] :
    (1 : ℝ) ≤ N + 1)
  have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ (N : ℝ) ^ 2 + 1)
  rw [invCoeff]; linarith

theorem invSizeBound_le (N : ℕ) :
    invSizeBound K N (formLogHeight Sfin L)
      ≤ Real.exp (invCoeff (finrank ℚ K) N * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set D := detLogBound K N (formLogHeight Sfin L)
  have hD : 0 ≤ D := detLogBound_nonneg N (formLogHeight_nonneg Sfin L)
  have hE : 1 ≤ Real.exp (2 * D) := Real.one_le_exp (by linarith)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  calc invSizeBound K N (formLogHeight Sfin L) = N * (1 + N ^ 2 * Real.exp (2 * D)) := rfl
    _ ≤ N * ((N ^ 2 + 1) * Real.exp (2 * D)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hN
    _ ≤ Real.exp (Real.log (N + 1) * Λ) * (Real.exp (Real.log (N ^ 2 + 1) * Λ)
          * Real.exp (2 * (detCoeff (finrank ℚ K) N * Λ))) := by
        gcongr
        · exact le_exp_log_add_one_mul hN hΛ
        · exact add_one_le_exp_log_mul hN2 hΛ
        · exact detLogBound_formLogHeight_le N
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, invCoeff]; ring_nf

/-- The coefficient of `pointHeightConst`: `(d + t) (log (r + 1) + log (t + 1) + 2 invCoeff)`. -/
noncomputable def pointCoeff (d N r t : ℕ) : ℝ :=
  (d + t) * (Real.log (r + 1) + Real.log (t + 1) + 2 * invCoeff d N)

theorem pointCoeff_nonneg (d N r t : ℕ) : 0 ≤ pointCoeff d N r t := by
  have := invCoeff_nonneg d N
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : (1 : ℝ) ≤ r + 1)
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)] : (1 : ℝ) ≤ t + 1)
  rw [pointCoeff]; positivity

theorem pointFactor_le_exp :
    ((1 + Fintype.card (InfinitePlace K) * invSizeBound K (Fintype.card ι) (formLogHeight Sfin L))
        * (1 + #Sfin * invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)))
          ^ (finrank ℚ K + #Sfin) ≤ Real.exp (pointCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set B := invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)
  set E := Real.exp (invCoeff (finrank ℚ K) (Fintype.card ι) * Λ)
  have hBE : B ≤ E := invSizeBound_le _
  have hE1 : 1 ≤ E := one_le_exp_mul (invCoeff_nonneg _ _) (by linarith)
  have hB0 : 0 ≤ B := invSizeBound_nonneg _ _
  have hfac : ∀ a : ℕ, 1 + (a : ℝ) * B ≤ Real.exp (Real.log (a + 1) * Λ) * E := fun a ↦ by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have h1 := add_one_le_exp_log_mul ha hΛ
    nlinarith [mul_le_mul_of_nonneg_left hBE ha]
  calc ((1 + Fintype.card (InfinitePlace K) * B) * (1 + #Sfin * B)) ^ (finrank ℚ K + #Sfin)
      ≤ ((Real.exp (Real.log ((Fintype.card (InfinitePlace K) : ℕ) + 1) * Λ) * E)
          * (Real.exp (Real.log ((#Sfin : ℕ) + 1) * Λ) * E)) ^ (finrank ℚ K + #Sfin) := by
        gcongr
        · exact hfac _
        · exact hfac _
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, pointCoeff,
          invCoeff]
        push_cast; ring_nf

/-- The coefficient of the second argument of `minimaThreshold`:
`d N log 2 + 2 N + (d + t) detCoeff`. -/
noncomputable def normCoeff (d N t : ℕ) : ℝ :=
  d * N * Real.log 2 + 2 * N + (d + t) * detCoeff d N

theorem normCoeff_nonneg (d N t : ℕ) : 0 ≤ normCoeff d N t := by
  have := detCoeff_nonneg d N
  have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  rw [normCoeff]; positivity

theorem sqrt_abs_discr_le_exp :
    √|(discr K : ℝ)| ≤ Real.exp (Real.log |(discr K : ℝ)|) := by
  have h : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
  have h1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast h
  rw [Real.exp_log (by linarith)]
  exact Real.sqrt_le_self_iff.2 (Or.inr h1)

theorem pow_le_exp_mul_log (x N : ℕ) : (x : ℝ) ^ N ≤ Real.exp (N * Real.log x) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · simp [zero_pow hN.ne']
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hx)]

theorem normFactor_le_exp :
    2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) *
          (√|(discr K : ℝ)| ^ Fintype.card ι *
            Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
              ^ (finrank ℚ K + #Sfin))
      ≤ Real.exp (normCoeff (finrank ℚ K) (Fintype.card ι) #Sfin * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h2 : (2 : ℝ) ^ (d * N) ≤ Real.exp ((d * N * Real.log 2) * Λ) := by
    calc (2 : ℝ) ^ (d * N) = Real.exp ((d * N : ℕ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ _ := Real.exp_le_exp.2 (by push_cast; exact le_mul_of_one_le_right (by positivity) hΛ)
  have hprod : ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N
      ≤ Real.exp (N * Λ) := by
    calc ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N
        ≤ ∏ v ∈ Sfin, Real.exp (N * Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ pow_le_exp_mul_log _ _
      _ = Real.exp (N * ∑ v ∈ Sfin, Real.log (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          (sum_log_absNorm_le_thresholdScale Sfin L) hN)
  have hsqrt : √|(discr K : ℝ)| ^ N ≤ Real.exp (N * Λ) := by
    calc √|(discr K : ℝ)| ^ N ≤ Real.exp (Real.log |(discr K : ℝ)|) ^ N :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) sqrt_abs_discr_le_exp N
      _ = Real.exp (N * Real.log |(discr K : ℝ)|) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          (log_abs_discr_le_thresholdScale Sfin L) hN)
  have hdet : Real.exp (detLogBound K N (formLogHeight Sfin L)) ^ (d + #Sfin)
      ≤ Real.exp (((d + #Sfin : ℕ) : ℝ) * (detCoeff d N * Λ)) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (detLogBound_formLogHeight_le N)
      (Nat.cast_nonneg _))
  calc _ ≤ Real.exp ((d * N * Real.log 2) * Λ) * Real.exp (N * Λ) *
        (Real.exp (N * Λ) * Real.exp (((d + #Sfin : ℕ) : ℝ) * (detCoeff d N * Λ))) := by
        gcongr
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, normCoeff]; push_cast; ring_nf

/-- The coefficient of `log minimaThreshold`: `pointCoeff + normCoeff`. -/
noncomputable def minimaCoeff (d N r t : ℕ) : ℝ := pointCoeff d N r t + normCoeff d N t

open scoped Classical in
/-- **The level of the minima bounds is at most `exp (minimaCoeff Λ)`.** -/
theorem log_minimaThreshold_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    Real.log (minimaThreshold Sfin L) ≤ minimaCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 0 ≤ Λ := thresholdScale_nonneg Sfin L
  have hp := pointCoeff_nonneg (finrank ℚ K) (Fintype.card ι) (Fintype.card (InfinitePlace K))
    #Sfin
  have hn := normCoeff_nonneg (finrank ℚ K) (Fintype.card ι) #Sfin
  have hpm := exp_mul_le_exp_mul (Λ := Λ) (c' := minimaCoeff (finrank ℚ K) (Fintype.card ι)
    (Fintype.card (InfinitePlace K)) #Sfin) (le_add_of_nonneg_right hn) hΛ
  have hnm := exp_mul_le_exp_mul (Λ := Λ) (c' := minimaCoeff (finrank ℚ K) (Fintype.card ι)
    (Fintype.card (InfinitePlace K)) #Sfin) (le_add_of_nonneg_left hp) hΛ
  have h1 : (1 : ℝ) ≤ Real.exp (minimaCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * Λ) := one_le_exp_mul (add_nonneg hp hn) hΛ
  refine log_le_of_le_exp (zero_le_one.trans (le_max_left _ _ |>.trans' (le_max_left _ _)))
    (mul_nonneg (add_nonneg hp hn) hΛ) ((minimaThreshold_le hLInf hLFin).trans ?_)
  refine max_le (max_le h1 ?_) (max_le ?_ h1)
  · exact pointFactor_le_exp.trans hpm
  · exact normFactor_le_exp.trans hnm

/-- The coefficient of `reducedBasisBound`: `log (d + 1) + d log 2 + 1`. -/
noncomputable def basisCoeff (d : ℕ) : ℝ := Real.log (d + 1) + d * Real.log 2 + 1

theorem basisCoeff_nonneg (d : ℕ) : 0 ≤ basisCoeff d := by
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)] : (1 : ℝ) ≤ d + 1)
  have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  rw [basisCoeff]; positivity

theorem reducedBasisBound_nonneg : 0 ≤ reducedBasisBound K := by
  rw [reducedBasisBound]; positivity

theorem reducedBasisBound_le_exp :
    reducedBasisBound K ≤ Real.exp (basisCoeff (finrank ℚ K) * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set d := finrank ℚ K
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h2 : (2 : ℝ) ^ d ≤ Real.exp ((d * Real.log 2) * Λ) := by
    calc (2 : ℝ) ^ d = Real.exp (d * Real.log 2) := by rw [Real.exp_nat_mul, Real.exp_log two_pos]
      _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right (by positivity) hΛ)
  have hD : √|(discr K : ℝ)| ≤ Real.exp (1 * Λ) :=
    sqrt_abs_discr_le_exp.trans (Real.exp_le_exp.2 (by
      have := log_abs_discr_le_thresholdScale Sfin L; linarith))
  calc reducedBasisBound K = d * 2 ^ d * √|(discr K : ℝ)| := rfl
    _ ≤ Real.exp (Real.log (d + 1) * Λ) * Real.exp ((d * Real.log 2) * Λ) * Real.exp (1 * Λ) := by
        gcongr
        exact le_exp_log_add_one_mul (Nat.cast_nonneg d) hΛ
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, basisCoeff]; ring_nf

/-- The coefficient of the numerator of the rank threshold:
`log ((d N)! + 1) + d N (basisCoeff + log (2 π)) + (d + t) detCoeff`. -/
noncomputable def rankNumCoeff (d N t : ℕ) : ℝ :=
  Real.log ((d * N).factorial + 1) + d * N * (basisCoeff d + Real.log (2 * Real.pi))
    + (d + t) * detCoeff d N

theorem one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]

theorem rankNumCoeff_nonneg (d N t : ℕ) : 0 ≤ rankNumCoeff d N t := by
  have := detCoeff_nonneg d N
  have := basisCoeff_nonneg d
  have := Real.log_nonneg one_le_two_pi
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg (d * N).factorial : (0 : ℝ) ≤ _)] :
    (1 : ℝ) ≤ ((d * N).factorial : ℕ) + 1)
  rw [rankNumCoeff]; positivity

theorem rankNum_le_exp :
    (finrank ℚ K * Fintype.card ι).factorial *
      reducedBasisBound K ^ (finrank ℚ K * Fintype.card ι) *
        ((2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
          Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
            ^ (finrank ℚ K + #Sfin))
      ≤ Real.exp (rankNumCoeff (finrank ℚ K) (Fintype.card ι) #Sfin * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  have hpi : (2 * Real.pi) ^ (d * N) ≤ Real.exp ((d * N : ℕ) * (Real.log (2 * Real.pi) * Λ)) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by linarith [one_le_two_pi]) ?_ _
    calc 2 * Real.pi = Real.exp (Real.log (2 * Real.pi)) :=
          (Real.exp_log (by linarith [one_le_two_pi])).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right (Real.log_nonneg one_le_two_pi) hΛ)
  have hRB : reducedBasisBound K ^ (d * N)
      ≤ Real.exp ((d * N : ℕ) * (basisCoeff d * Λ)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ reducedBasisBound_nonneg (reducedBasisBound_le_exp (L := L)) _
  have hdet : Real.exp (detLogBound K N (formLogHeight Sfin L)) ^ (d + #Sfin)
      ≤ Real.exp (((d + #Sfin : ℕ) : ℝ) * (detCoeff d N * Λ)) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (detLogBound_formLogHeight_le N)
      (Nat.cast_nonneg _))
  have hfac : ((d * N).factorial : ℝ) ≤ Real.exp (Real.log (((d * N).factorial : ℕ) + 1) * Λ) :=
    le_exp_log_add_one_mul (Nat.cast_nonneg _) hΛ
  calc _ ≤ Real.exp (Real.log (((d * N).factorial : ℕ) + 1) * Λ)
        * Real.exp ((d * N : ℕ) * (basisCoeff d * Λ))
        * (Real.exp ((d * N : ℕ) * (Real.log (2 * Real.pi) * Λ))
          * Real.exp (((d + #Sfin : ℕ) : ℝ) * (detCoeff d N * Λ))) := by
        gcongr
        exact pow_nonneg reducedBasisBound_nonneg _
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, rankNumCoeff]; push_cast; ring_nf

/-- The coefficient of `log rankThreshold`: `log 2 + η⁻¹ rankNumCoeff`. -/
noncomputable def rankCoeff (d N t : ℕ) (η : ℝ) : ℝ := Real.log 2 + η⁻¹ * rankNumCoeff d N t

theorem rankCoeff_nonneg (d N t : ℕ) {η : ℝ} (hη : 0 ≤ η) : 0 ≤ rankCoeff d N t η := by
  have := rankNumCoeff_nonneg d N t
  have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  rw [rankCoeff]; positivity

open scoped Classical in
/-- **The rank threshold is at most `exp (rankCoeff Λ)`.** -/
theorem log_rankThreshold_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {η : ℝ} (hη : 0 < η) :
    Real.log (rankThreshold Sfin L η) ≤ rankCoeff (finrank ℚ K) (Fintype.card ι) #Sfin η
      * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set c := rankNumCoeff (finrank ℚ K) (Fintype.card ι) #Sfin with hcdef
  have hc : 0 ≤ c := rankNumCoeff_nonneg _ _ _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  set F := (finrank ℚ K * Fintype.card ι).factorial *
      reducedBasisBound K ^ (finrank ℚ K * Fintype.card ι) *
        ((2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
          Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
            ^ (finrank ℚ K + #Sfin))
  have hF0 : 0 ≤ F := by
    have := reducedBasisBound_nonneg (K := K)
    have := Real.pi_pos
    positivity
  have hF : F / 2 ^ (finrank ℚ K * Fintype.card ι) ≤ Real.exp (c * Λ) :=
    (div_le_self hF0 (one_le_pow₀ one_le_two)).trans rankNum_le_exp
  have hpow : (F / 2 ^ (finrank ℚ K * Fintype.card ι)) ^ η⁻¹ ≤ Real.exp (η⁻¹ * c * Λ) := by
    calc (F / 2 ^ (finrank ℚ K * Fintype.card ι)) ^ η⁻¹ ≤ Real.exp (c * Λ) ^ η⁻¹ :=
          Real.rpow_le_rpow (by positivity) hF (inv_nonneg.2 hη.le)
      _ = _ := by rw [← Real.exp_mul]; ring_nf
  have hmax : max 1 ((F / 2 ^ (finrank ℚ K * Fintype.card ι)) ^ η⁻¹)
      ≤ Real.exp (η⁻¹ * c * Λ) :=
    max_le (Real.one_le_exp (by have := inv_nonneg.2 hη.le; positivity)) hpow
  have hpos : 0 < rankThreshold Sfin L η := by
    rw [rankThreshold]; exact mul_pos two_pos (zero_lt_one.trans_le (le_max_left _ _))
  rw [Real.log_le_iff_le_exp hpos]
  calc rankThreshold Sfin L η ≤ 2 * max 1 ((F / 2 ^ (finrank ℚ K * Fintype.card ι)) ^ η⁻¹) :=
        rankThreshold_le hLInf hLFin hη
    _ ≤ Real.exp (Real.log 2 * Λ) * Real.exp (η⁻¹ * c * Λ) := by
        gcongr
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
          _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right hlog2 hΛ)
    _ = _ := by rw [← Real.exp_add, rankCoeff, hcdef]; ring_nf

/-- The coefficient of `pluckerConst`:
`log (N! + 1) + N ^ 2 (log (4 N ^ 2 + 1) + log (d + 1) + basisCoeff)`. -/
noncomputable def pluckerCoeff (d N : ℕ) : ℝ :=
  Real.log (N.factorial + 1)
    + N ^ 2 * (Real.log (4 * N ^ 2 + 1) + Real.log (d + 1) + basisCoeff d)

theorem pluckerCoeff_nonneg (d N : ℕ) : 0 ≤ pluckerCoeff d N := by
  have := basisCoeff_nonneg d
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)] : (1 : ℝ) ≤ d + 1)
  have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 4 * (N : ℝ) ^ 2 + 1)
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg N.factorial : (0 : ℝ) ≤ _)] :
    (1 : ℝ) ≤ (N.factorial : ℕ) + 1)
  rw [pluckerCoeff]; positivity

/-- **The Plücker constant is at most `exp (pluckerCoeff Λ)`.** -/
theorem pluckerConst_le_exp (N : ℕ) :
    pluckerConst K N ≤ Real.exp (pluckerCoeff (finrank ℚ K) N * thresholdScale Sfin L) := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set d := finrank ℚ K
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hb := basisCoeff_nonneg d
  have hld := Real.log_nonneg (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)] :
    (1 : ℝ) ≤ d + 1)
  set E := evertseConst ((d : ℝ) * reducedBasisBound K) N
  have hE1 : 1 ≤ E := one_le_evertseConst _ _
  have hA : max ((d : ℝ) * reducedBasisBound K) 1
      ≤ Real.exp (Real.log (d + 1) * Λ) * Real.exp (basisCoeff d * Λ) := by
    refine max_le (mul_le_mul (le_exp_log_add_one_mul (Nat.cast_nonneg d) hΛ)
      (reducedBasisBound_le_exp (L := L)) reducedBasisBound_nonneg (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]; exact Real.one_le_exp (by positivity)
  have h4 : 4 * (N : ℝ) ^ 2 ≤ Real.exp (Real.log (4 * N ^ 2 + 1) * Λ) :=
    le_exp_log_add_one_mul (by positivity) hΛ
  have hbase : 4 * (N : ℝ) ^ 2 * max ((d : ℝ) * reducedBasisBound K) 1
      ≤ Real.exp ((Real.log (4 * N ^ 2 + 1) + Real.log (d + 1) + basisCoeff d) * Λ) := by
    calc _ ≤ Real.exp (Real.log (4 * N ^ 2 + 1) * Λ)
          * (Real.exp (Real.log (d + 1) * Λ) * Real.exp (basisCoeff d * Λ)) :=
          mul_le_mul h4 hA (zero_le_one.trans (le_max_right _ _)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hEb : E ^ N ≤ Real.exp (((N * N : ℕ) : ℝ) *
      ((Real.log (4 * N ^ 2 + 1) + Real.log (d + 1) + basisCoeff d) * Λ)) := by
    rw [Real.exp_nat_mul, pow_mul]
    exact pow_le_pow_left₀ (by linarith) ((evertseConst_le _ N).trans
      (pow_le_pow_left₀ (by positivity) hbase N)) N
  calc pluckerConst K N = N.factorial * max 1 E ^ N := rfl
    _ = N.factorial * E ^ N := by rw [max_eq_right hE1]
    _ ≤ Real.exp (Real.log ((N.factorial : ℕ) + 1) * Λ) * Real.exp (((N * N : ℕ) : ℝ) *
        ((Real.log (4 * N ^ 2 + 1) + Real.log (d + 1) + basisCoeff d) * Λ)) :=
        mul_le_mul (le_exp_log_add_one_mul (Nat.cast_nonneg _) hΛ) hEb (by positivity)
          (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, pluckerCoeff]; push_cast; ring_nf

theorem one_le_pluckerConst (N : ℕ) : 1 ≤ pluckerConst K N := by
  rw [pluckerConst]
  exact one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 (Nat.factorial_pos N))
    (one_le_pow₀ (le_max_left _ _))

theorem log_pluckerConst_le (N : ℕ) :
    Real.log (pluckerConst K N) ≤ pluckerCoeff (finrank ℚ K) N * thresholdScale Sfin L :=
  log_le_of_le_exp (zero_le_one.trans (one_le_pluckerConst N))
    (mul_nonneg (pluckerCoeff_nonneg _ _) (thresholdScale_nonneg Sfin L)) (pluckerConst_le_exp N)

/-- The coefficient of `wedgeWeightConst` at the Plücker constant:
`N ^ 2 (binom(N, p) d pluckerCoeff + binom(N - 1, p - 1) normCoeff) + rankNumCoeff`. -/
noncomputable def wedgeWeightCoeff (d N t p : ℕ) : ℝ :=
  N ^ 2 * (N.choose p * d * pluckerCoeff d N + (N - 1).choose (p - 1) * normCoeff d N t)
    + rankNumCoeff d N t

theorem wedgeWeightCoeff_nonneg (d N t p : ℕ) : 0 ≤ wedgeWeightCoeff d N t p := by
  have := pluckerCoeff_nonneg d N
  have := normCoeff_nonneg d N t
  have := rankNumCoeff_nonneg d N t
  rw [wedgeWeightCoeff]; positivity

open scoped Classical in
/-- **The constant of the wedge weight is at most `exp (wedgeWeightCoeff Λ)`.** -/
theorem log_wedgeWeightConst_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (p : ℕ) :
    Real.log (wedgeWeightConst Sfin L (pluckerConst K (Fintype.card ι)) p)
      ≤ wedgeWeightCoeff (finrank ℚ K) (Fintype.card ι) #Sfin p * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set C := pluckerConst K N
  have hC1 : 1 ≤ C := one_le_pluckerConst N
  have hpc := pluckerCoeff_nonneg d N
  have hnc := normCoeff_nonneg d N #Sfin
  have hrc := rankNumCoeff_nonneg d N #Sfin
  have hM : Fintype.card (Set.powersetCard ι p) = N.choose p := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  set G := 2 ^ (d * N) * (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ N) *
    (√|(discr K : ℝ)| ^ N * Real.exp (detLogBound K N (formLogHeight Sfin L)) ^ (d + #Sfin))
  set b := (N - 1).choose (p - 1) with hbdef
  have hG0 : 0 ≤ G := by positivity
  have hF0 : 0 ≤ (d * N).factorial * reducedBasisBound K ^ (d * N) *
      ((2 * Real.pi) ^ (d * N)
        * Real.exp (detLogBound K N (formLogHeight Sfin L)) ^ (d + #Sfin)) := by
    have := reducedBasisBound_nonneg (K := K)
    have := Real.pi_pos
    positivity
  have hF : (d * N).factorial * reducedBasisBound K ^ (d * N) *
      ((2 * Real.pi) ^ (d * N) * Real.exp (detLogBound K N (formLogHeight Sfin L)) ^ (d + #Sfin))
        / 2 ^ (d * N) ≤ Real.exp (rankNumCoeff d N #Sfin * Λ) :=
    (div_le_self hF0 (one_le_pow₀ one_le_two)).trans rankNum_le_exp
  have hCp : C ^ (N.choose p * d)
      ≤ Real.exp (((N.choose p * d : ℕ) : ℝ) * (pluckerCoeff d N * Λ)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) (pluckerConst_le_exp N) _
  have hGp : G ^ b ≤ Real.exp ((b : ℝ) * (normCoeff d N #Sfin * Λ)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ hG0 normFactor_le_exp _
  have hinner : max (C ^ (N.choose p * d) * G ^ b) 1
      ≤ Real.exp (((N.choose p * d : ℕ) : ℝ) * (pluckerCoeff d N * Λ)
        + (b : ℝ) * (normCoeff d N #Sfin * Λ)) := by
    refine max_le ?_ (Real.one_le_exp (by positivity))
    rw [Real.exp_add]
    exact mul_le_mul hCp hGp (by positivity) (Real.exp_pos _).le
  have hpowN := pow_le_pow_left₀ (zero_le_one.trans (le_max_right _ _)) hinner (N ^ 2)
  refine log_le_of_le_exp (zero_le_one.trans (le_max_right _ _))
    (mul_nonneg (wedgeWeightCoeff_nonneg _ _ _ _) (by linarith))
    ((wedgeWeightConst_le hLInf hLFin (by linarith) p).trans ?_)
  rw [hM]
  refine max_le ((mul_le_mul hpowN hF (div_nonneg hF0 (by positivity)) (by positivity)).trans
    (le_of_eq ?_)) (one_le_exp_mul (wedgeWeightCoeff_nonneg _ _ _ _) (by linarith))
  rw [← Real.exp_nat_mul, ← Real.exp_add, wedgeWeightCoeff, hbdef]
  push_cast; ring_nf

/-- The coefficient of the constant of the auxiliary polynomial:
`1 / 2 + d N / 2 + d log N + 2 (r + t) N ^ 2 detCoeff`. -/
noncomputable def auxCoeff (d N r t : ℕ) : ℝ :=
  2⁻¹ + ((d : ℝ) / 2 * N + d * Real.log N + 2 * ((r : ℝ) + t) * N ^ 2 * detCoeff d N)

theorem auxCoeff_nonneg (d N r t : ℕ) : 0 ≤ auxCoeff d N r t := by
  have := detCoeff_nonneg d N
  have := Real.log_natCast_nonneg N
  rw [auxCoeff]; positivity

/-- The constant of the auxiliary polynomial is at most `auxCoeff Λ`. -/
theorem max_auxHeightConst_le :
    max (auxHeightConst Sfin L) 0 ≤ auxCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  have hdc := detCoeff_nonneg d N
  have hlN := Real.log_natCast_nonneg N
  have hlam := log_abs_discr_le_thresholdScale Sfin L
  have hD := detLogBound_formLogHeight_le (Sfin := Sfin) (L := L) N
  have h1 : (d : ℝ) / 2 * N ≤ (d : ℝ) / 2 * N * Λ := le_mul_of_one_le_right (by positivity) hΛ
  have h2 : (d : ℝ) * Real.log N ≤ (d : ℝ) * Real.log N * Λ :=
    le_mul_of_one_le_right (by positivity) hΛ
  have h3 : ((r : ℝ) + #Sfin) * N ^ 2 * (2 * detLogBound K N (formLogHeight Sfin L))
      ≤ ((r : ℝ) + #Sfin) * N ^ 2 * (2 * (detCoeff d N * Λ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine max_le ((auxHeightConst_le).trans ?_) (mul_nonneg (auxCoeff_nonneg _ _ _ _) (by linarith))
  rw [totalWeight_eq_finrank, auxCoeff]
  nlinarith

/-- The coefficient of the heights of the reference family:
`2 (r + t) N ^ 2 detCoeff + (2 B + 1) d log B`. -/
noncomputable def refCoeff (d N r t B : ℕ) : ℝ :=
  2 * ((r : ℝ) + t) * N ^ 2 * detCoeff d N + (2 * B + 1) * (d * Real.log B)

theorem refCoeff_nonneg (d N r t B : ℕ) : 0 ≤ refCoeff d N r t B := by
  have := detCoeff_nonneg d N
  have := Real.log_natCast_nonneg B
  rw [refCoeff]; positivity

/-- The heights of the reference family are at most `refCoeff Λ`. -/
theorem sum_log_mulHeight₁_refFamily_le_mul (B : ℕ) :
    ∑ θ, Real.log (mulHeight₁ (refFamily L Sfin B θ)) ≤ refCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin B * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  have hD := detLogBound_formLogHeight_le (Sfin := Sfin) (L := L) N
  have h1 : ((r : ℝ) + #Sfin) * N ^ 2 * (2 * detLogBound K N (formLogHeight Sfin L))
      ≤ ((r : ℝ) + #Sfin) * N ^ 2 * (2 * (detCoeff d N * Λ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (2 * (B : ℝ) + 1) * (d * Real.log B) ≤ (2 * (B : ℝ) + 1) * (d * Real.log B) * Λ :=
    le_mul_of_one_le_right (by have := Real.log_natCast_nonneg B; positivity) hΛ
  refine (sum_log_mulHeight₁_refFamily_le B).trans ?_
  rw [totalWeight_eq_finrank, refCoeff]
  nlinarith

/-- The coefficient of the patterns constant: `log (N + 1) + log (r + t + 1) + invCoeff`. -/
noncomputable def patternConstCoeff (d N r t : ℕ) : ℝ :=
  Real.log (N + 1) + Real.log ((r : ℝ) + t + 1) + invCoeff d N

theorem patternConstCoeff_nonneg (d N r t : ℕ) : 0 ≤ patternConstCoeff d N r t := by
  have := invCoeff_nonneg d N
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)] : (1 : ℝ) ≤ N + 1)
  have := Real.log_nonneg (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r),
    (Nat.cast_nonneg t : (0 : ℝ) ≤ t)] : (1 : ℝ) ≤ r + t + 1)
  rw [patternConstCoeff]; positivity

/-- The constant of the pattern vectors is at most `exp (patternConstCoeff Λ)`. -/
theorem log_patternConst_le :
    Real.log (patternConst Sfin L) ≤ patternConstCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  set B := invSizeBound K N (formLogHeight Sfin L)
  set E := Real.exp (invCoeff d N * Λ)
  have hBE : B ≤ E := invSizeBound_le _
  have hE1 : 1 ≤ E := one_le_exp_mul (invCoeff_nonneg _ _) (by linarith)
  have hs : (0 : ℝ) ≤ r + #Sfin := by positivity
  have hfac : 1 + ((r : ℝ) + #Sfin) * B ≤ Real.exp (Real.log ((r : ℝ) + #Sfin + 1) * Λ) * E := by
    have h1 := add_one_le_exp_log_mul hs hΛ
    nlinarith [mul_le_mul_of_nonneg_left hBE hs]
  have h0 : 0 ≤ patternConst Sfin L := by
    rw [patternConst]
    have h1 := Finset.sum_nonneg fun w (_ : w ∈ Finset.univ) ↦ invFormBound_nonneg (ι := ι)
      (w : InfinitePlace K).1 (L w.1)
    have h2 := Finset.sum_nonneg fun v (_ : v ∈ (Finset.univ : Finset {v // v ∈ Sfin})) ↦
      invFormBound_nonneg (ι := ι) v.1.1 (L v.1.1)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  refine log_le_of_le_exp h0 (mul_nonneg (patternConstCoeff_nonneg _ _ _ _) (by linarith))
    ((patternConst_le).trans ?_)
  calc (N : ℝ) * (1 + ((r : ℝ) + #Sfin) * B)
      ≤ Real.exp (Real.log (N + 1) * Λ) * (Real.exp (Real.log ((r : ℝ) + #Sfin + 1) * Λ) * E) :=
        mul_le_mul (le_exp_log_add_one_mul (Nat.cast_nonneg N) hΛ) hfac
          (add_nonneg zero_le_one (mul_nonneg hs (invSizeBound_nonneg _ _))) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, patternConstCoeff]; ring_nf

/-- The coefficient of the pattern heights:
`log 2 + N (r + t) log 2 + 1 / 2 + N (d log N / 2 + 2 (r + t) N ^ 2 detCoeff)`. -/
noncomputable def patternHeightCoeff (d N r t : ℕ) : ℝ :=
  Real.log 2 + N * ((r : ℝ) + t) * Real.log 2
    + (2⁻¹ + N * ((d : ℝ) / 2 * Real.log N + 2 * ((r : ℝ) + t) * N ^ 2 * detCoeff d N))

theorem patternHeightCoeff_nonneg (d N r t : ℕ) : 0 ≤ patternHeightCoeff d N r t := by
  have := detCoeff_nonneg d N
  have := Real.log_natCast_nonneg N
  have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  rw [patternHeightCoeff]; positivity

/-- The coefficient of `C₅ = |s log κ⁻¹ + d log n!|`, with `M = binom(N, n)`:
`s (s M ((d + M) detCoeff d n + d log M)) + d log n!`. -/
noncomputable def kappaCoeff (d M n s : ℕ) : ℝ :=
  s * (s * M * ((d + M) * detCoeff d n + d * Real.log M)) + d * Real.log n.factorial

theorem kappaCoeff_nonneg (d M n s : ℕ) : 0 ≤ kappaCoeff d M n s := by
  have := detCoeff_nonneg d n
  have := Real.log_natCast_nonneg M
  have := Real.log_natCast_nonneg n.factorial
  rw [kappaCoeff]; positivity


end Scale

section Penultimate

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

theorem patternLogBound_le :
    patternLogBound Sfin L ≤ (2⁻¹ + Fintype.card ι * ((finrank ℚ K : ℝ) / 2 *
      Real.log (Fintype.card ι) + 2 * ((Fintype.card (InfinitePlace K) : ℝ) + #Sfin)
        * Fintype.card ι ^ 2 * detCoeff (finrank ℚ K) (Fintype.card ι)))
      * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  have hlam := log_abs_discr_le_thresholdScale Sfin L
  have hD := detLogBound_formLogHeight_le (Sfin := Sfin) (L := L) N
  have hlN := Real.log_natCast_nonneg N
  have h1 : (d : ℝ) / 2 * Real.log N ≤ (d : ℝ) / 2 * Real.log N * Λ :=
    le_mul_of_one_le_right (by positivity) hΛ
  have h2 : ((r : ℝ) + #Sfin) * N ^ 2 * (2 * detLogBound K N (formLogHeight Sfin L))
      ≤ ((r : ℝ) + #Sfin) * N ^ 2 * (2 * (detCoeff d N * Λ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : (N : ℝ) * ((d : ℝ) / 2 * Real.log N
        + ((r : ℝ) + #Sfin) * N ^ 2 * (2 * detLogBound K N (formLogHeight Sfin L)))
      ≤ (N : ℝ) * ((d : ℝ) / 2 * Real.log N * Λ
        + ((r : ℝ) + #Sfin) * N ^ 2 * (2 * (detCoeff d N * Λ))) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  rw [patternLogBound]
  nlinarith

open scoped Classical in
/-- Twice the bound on the pattern heights is at most `exp (patternHeightCoeff Λ)`. -/
theorem log_two_mul_patternHeightBound_le [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    Real.log (2 * patternHeightBound Sfin L) ≤ patternHeightCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set r := Fintype.card (InfinitePlace K)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hcard : (Fintype.card ((InfinitePlace K → Finset ι) ×
      ({w : FinitePlace K // w ∈ Sfin} → Finset ι)) : ℝ)
        = Real.exp ((N * ((r : ℝ) + #Sfin)) * Real.log 2) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_finset,
      Fintype.card_coe, ← pow_add, ← pow_mul]
    rw [show ((N : ℝ) * ((r : ℝ) + #Sfin)) = ((N * (r + #Sfin) : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log two_pos]
    push_cast; ring
  have h0 : 0 ≤ patternHeightBound Sfin L := by
    rw [patternHeightBound]
    exact Finset.sum_nonneg fun _ _ ↦ zero_le_one.trans (le_max_left _ _)
  have hmain : 2 * patternHeightBound Sfin L ≤ Real.exp (Real.log 2 +
      (N * ((r : ℝ) + #Sfin)) * Real.log 2 + patternLogBound Sfin L) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log two_pos, ← hcard, mul_assoc]
    exact mul_le_mul_of_nonneg_left (patternHeightBound_le hLInf hLFin) zero_le_two
  refine log_le_of_le_exp (by positivity)
    (mul_nonneg (patternHeightCoeff_nonneg _ _ _ _) (by linarith)) (hmain.trans ?_)
  refine Real.exp_le_exp.2 ?_
  have h1 := patternLogBound_le (Sfin := Sfin) (L := L)
  have h2 : Real.log 2 ≤ Real.log 2 * Λ := le_mul_of_one_le_right hlog2 hΛ
  have h3 : (N * ((r : ℝ) + #Sfin)) * Real.log 2 ≤ (N * ((r : ℝ) + #Sfin)) * Real.log 2 * Λ :=
    le_mul_of_one_le_right (by positivity) hΛ
  rw [patternHeightCoeff]
  nlinarith

theorem normalKappa_le_one (n : ℕ) : normalKappa n Sfin L ≤ 1 := by
  rw [normalKappa]
  refine (min_le_left _ _).trans (Finset.prod_le_one₀ (fun p _ ↦ le_min zero_le_one ?_)
    fun _ _ ↦ min_le_left _ _)
  have := one_le_mulHeight (exteriorPower.wedgeFormCoeff (L p.1.1) n p.2)
  exact div_nonneg (pow_nonneg (Real.iSup_nonneg fun t ↦ apply_nonneg _ _) _) (by positivity)

theorem exp_neg_le_kappaFactor {M : ℕ} (hM : 0 < M) {E : ℝ} (hE : 0 ≤ E) :
    Real.exp (-(E * totalWeight K + totalWeight K * Real.log M + E * M)) ≤ kappaFactor K M E := by
  have hx : Real.exp (-E) ^ totalWeight K / ((M : ℝ) ^ totalWeight K * Real.exp E ^ M)
      = Real.exp (-(E * totalWeight K + totalWeight K * Real.log M + E * M)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_log (by exact_mod_cast hM : (0 : ℝ) < M), ← Real.exp_nat_mul, Real.log_exp,
      ← Real.exp_add, ← Real.exp_sub]
    ring_nf
  have := Real.log_natCast_nonneg M
  have : (0 : ℝ) ≤ totalWeight K := Nat.cast_nonneg _
  rw [kappaFactor, hx]
  exact le_min (Real.exp_le_one_iff.2 (by nlinarith)) le_rfl

/-- **`C₅ = |s log κ⁻¹ + d log n!|` is at most `kappaCoeff Λ`**, with `M = binom(N, n)`. -/
theorem abs_log_normalKappa_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {n : ℕ} (hn : n ≤ Fintype.card ι) :
    |((Fintype.card (InfinitePlace K) + #Sfin : ℕ) : ℝ) * Real.log (normalKappa n Sfin L)⁻¹
        + (totalWeight K : ℝ) * Real.log n.factorial|
      ≤ kappaCoeff (finrank ℚ K) ((Fintype.card ι).choose n) n
          (Fintype.card (InfinitePlace K) + #Sfin) * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set d := finrank ℚ K
  set s := Fintype.card (InfinitePlace K) + #Sfin
  set M := Fintype.card (Set.powersetCard ι n) with hMdef
  have hMch : M = (Fintype.card ι).choose n := by
    rw [hMdef, Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hM : 0 < M := by rw [hMch]; exact Nat.choose_pos hn
  set E := detLogBound K n (formLogHeight Sfin L)
  have hE0 : 0 ≤ E := detLogBound_nonneg n (formLogHeight_nonneg Sfin L)
  have hEle : E ≤ detCoeff d n * Λ := detLogBound_formLogHeight_le n
  have hkf := exp_neg_le_kappaFactor (K := K) hM hE0
  rw [totalWeight_eq_finrank] at hkf ⊢
  set Q := E * d + d * Real.log M + E * M with hQ
  set κ := normalKappa n Sfin L
  have hκ : Real.exp (-Q) ^ (s * M) ≤ κ :=
    (pow_le_pow_left₀ (Real.exp_pos _).le hkf _).trans
      (kappaFactor_pow_le_normalKappa n hLInf hLFin)
  have hκpos : 0 < κ := lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) hκ
  have hκ1 : κ ≤ 1 := normalKappa_le_one n
  have hlogκ : ((s * M : ℕ) : ℝ) * -Q ≤ Real.log κ := by
    rw [Real.le_log_iff_exp_le hκpos, Real.exp_nat_mul]; exact hκ
  have hlogκ1 : Real.log κ ≤ 0 := Real.log_nonpos hκpos.le hκ1
  have hlf : 0 ≤ Real.log n.factorial := Real.log_natCast_nonneg _
  have hlM : 0 ≤ Real.log M := Real.log_natCast_nonneg _
  have hs : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  rw [Real.log_inv, abs_of_nonneg (by nlinarith)]
  have hQle : Q ≤ (((d : ℝ) + M) * detCoeff d n + d * Real.log M) * Λ := by
    have h1 : E * ((d : ℝ) + M) ≤ detCoeff d n * Λ * ((d : ℝ) + M) :=
      mul_le_mul_of_nonneg_right hEle (by positivity)
    have h2 : (d : ℝ) * Real.log M ≤ d * Real.log M * Λ := le_mul_of_one_le_right (by positivity) hΛ
    rw [hQ]; nlinarith
  have h3 : -Real.log κ ≤ (s : ℝ) * M * ((((d : ℝ) + M) * detCoeff d n + d * Real.log M) * Λ) := by
    have : ((s * M : ℕ) : ℝ) * Q ≤ ((s * M : ℕ) : ℝ) * ((((d : ℝ) + M) * detCoeff d n
        + d * Real.log M) * Λ) := mul_le_mul_of_nonneg_left hQle (Nat.cast_nonneg _)
    push_cast at this hlogκ; nlinarith
  have h4 : (d : ℝ) * Real.log n.factorial ≤ d * Real.log n.factorial * Λ :=
    le_mul_of_one_le_right (by positivity) hΛ
  have h5 := mul_le_mul_of_nonneg_left h3 hs
  rw [kappaCoeff, ← hMch]
  nlinarith

/-- **The coefficient of the threshold of Layer 5.6** for forms in `N` variables, `d = [K : ℚ]`,
`r` infinite places, `t` finite places of `S`, the dimension `n`, the margin `ε` and the weight
bound `A`: `1 + c₁ + c₂ + c₃`, one term for each argument of `penultimateThreshold`. -/
noncomputable def penultimateCoeff (d N r t n : ℕ) (ε A : ℝ) : ℝ :=
  1 + 8 * ((n : ℝ) + 1) * (d * Real.log (2 * ((n : ℝ) + 1) * n) + auxCoeff d N r t
      + 2 * refCoeff d N r t ⌈2 * (n : ℝ) / subspaceEta n ε A + 1⌉₊) / ε
    + 8 * ((r + t : ℕ) : ℝ) * ((n : ℝ) * (subspaceRatio n (r + t) ε A)⁻¹
        * ((subspaceChainLength n (r + t) ε A : ℝ) + 1) * (auxCoeff d N r t + 4 * d)
      + kappaCoeff d (N.choose n) n (r + t)) / ε
    + (4 * ((d + t) * patternConstCoeff d N r t + patternHeightCoeff d N r t) + 1) / ε

theorem log_two_mul_add_one_mul_nonneg (n : ℕ) : 0 ≤ Real.log (2 * ((n : ℝ) + 1) * n) := by
  have : (2 * ((n : ℝ) + 1) * n) = ((2 * (n + 1) * n : ℕ) : ℝ) := by push_cast; ring
  rw [this]; exact Real.log_natCast_nonneg _

theorem penultimateCoeff_nonneg (d N r t n : ℕ) {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    0 ≤ penultimateCoeff d N r t n ε A := by
  have := auxCoeff_nonneg d N r t
  have := refCoeff_nonneg d N r t ⌈2 * (n : ℝ) / subspaceEta n ε A + 1⌉₊
  have := kappaCoeff_nonneg d (N.choose n) n (r + t)
  have := patternConstCoeff_nonneg d N r t
  have := patternHeightCoeff_nonneg d N r t
  have := log_two_mul_add_one_mul_nonneg n
  have := subspaceRatio_pos (n := n) (s := r + t) hε hA
  rw [penultimateCoeff]; positivity

/-- **The threshold of Layer 5.6 is at most `penultimateCoeff Λ`.** -/
theorem penultimateThreshold_le [DecidableEq ι] [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {n : ℕ} (hn : n ≤ Fintype.card ι)
    {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) :
    penultimateThreshold Sfin L n ε A ≤ penultimateCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin n ε A * thresholdScale Sfin L := by
  obtain rfl : ‹DecidableEq ι› = fun a b ↦ LinearOrder.toDecidableEq a b := Subsingleton.elim _ _
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  set t := #Sfin
  set B := ⌈2 * (n : ℝ) / subspaceEta n ε A + 1⌉₊
  set σ := subspaceRatio n (r + t) ε A
  set m := subspaceChainLength n (r + t) ε A
  have hσ : 0 < σ := subspaceRatio_pos hε hA
  have haux := max_auxHeightConst_le (Sfin := Sfin) (L := L)
  have hauxc := auxCoeff_nonneg d N r t
  have href := sum_log_mulHeight₁_refFamily_le_mul (Sfin := Sfin) (L := L) B
  have hrefc := refCoeff_nonneg d N r t B
  have hkap := abs_log_normalKappa_le hLInf hLFin hn
  have hkapc := kappaCoeff_nonneg d (N.choose n) n (r + t)
  have hpc := log_patternConst_le (Sfin := Sfin) (L := L)
  have hpcc := patternConstCoeff_nonneg d N r t
  have hph := log_two_mul_patternHeightBound_le hLInf hLFin
  have hphc := patternHeightCoeff_nonneg d N r t
  have hlg := log_two_mul_add_one_mul_nonneg n
  set a₁ := (d : ℝ) * Real.log (2 * ((n : ℝ) + 1) * n) + auxCoeff d N r t + 2 * refCoeff d N r t B
    with ha₁
  set a₂ := (n : ℝ) * σ⁻¹ * ((m : ℝ) + 1) * (auxCoeff d N r t + 4 * d)
      + kappaCoeff d (N.choose n) n (r + t) with ha₂
  set a₃ := 4 * ((d + t) * patternConstCoeff d N r t + patternHeightCoeff d N r t) + 1 with ha₃
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  have hsplit : penultimateCoeff d N r t n ε A * Λ
      = Λ + 8 * ((n : ℝ) + 1) * (a₁ * Λ) / ε + 8 * ((r + t : ℕ) : ℝ) * (a₂ * Λ) / ε
        + a₃ * Λ / ε := by
    rw [penultimateCoeff]; ring
  have hT1 : 0 ≤ 8 * ((n : ℝ) + 1) * (a₁ * Λ) / ε := by positivity
  have hT2 : 0 ≤ 8 * ((r + t : ℕ) : ℝ) * (a₂ * Λ) / ε := by positivity
  have hT3 : 0 ≤ a₃ * Λ / ε := by positivity
  rw [hsplit, penultimateThreshold, chainThreshold]
  refine max_le (by linarith) (max_le (max_le (by linarith) (max_le ?_ ?_)) ?_)
  · refine le_trans ?_ (by linarith : 8 * ((n : ℝ) + 1) * (a₁ * Λ) / ε ≤ _)
    gcongr
    refine max_le ?_ (by positivity)
    have h1 : (d : ℝ) * Real.log (2 * ((n : ℝ) + 1) * n)
        ≤ (d : ℝ) * Real.log (2 * ((n : ℝ) + 1) * n) * Λ :=
      le_mul_of_one_le_right (by positivity) hΛ
    rw [totalWeight_eq_finrank, ha₁]
    nlinarith
  · refine le_trans ?_ (by linarith : 8 * ((r + t : ℕ) : ℝ) * (a₂ * Λ) / ε ≤ _)
    gcongr
    have h1 : max (auxHeightConst Sfin L) 0 + 4 * (totalWeight K : ℝ)
        ≤ (auxCoeff d N r t + 4 * d) * Λ := by
      have : (4 : ℝ) * d ≤ 4 * d * Λ := le_mul_of_one_le_right (by positivity) hΛ
      rw [totalWeight_eq_finrank]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : (0 : ℝ) ≤ (n : ℝ) * σ⁻¹ * ((m : ℝ) + 1))
    have h3 := max_le hkap (by positivity :
      (0 : ℝ) ≤ kappaCoeff d (N.choose n) n (r + t) * Λ)
    rw [ha₂]
    nlinarith
  · refine le_trans ?_ (by linarith : a₃ * Λ / ε ≤ _)
    gcongr
    have h1 : ((totalWeight K + t : ℕ) : ℝ) * Real.log (patternConst Sfin L)
        ≤ ((d : ℝ) + t) * (patternConstCoeff d N r t * Λ) := by
      rw [totalWeight_eq_finrank]; push_cast
      exact mul_le_mul_of_nonneg_left hpc (by positivity)
    have e : a₃ * Λ = 4 * (((d : ℝ) + t) * (patternConstCoeff d N r t * Λ)
        + patternHeightCoeff d N r t * Λ) + Λ := by rw [ha₃]; ring
    rw [e]
    linarith

end Penultimate

section Parametric

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

/-- The coefficient of the scale of the wedge forms: `1 + (r + t) binom(N, p) ^ 2 detCoeff d p`. -/
noncomputable def wedgeScaleCoeff (d N r t p : ℕ) : ℝ :=
  1 + ((r : ℝ) + t) * (N.choose p : ℝ) ^ 2 * detCoeff d p

theorem one_le_wedgeScaleCoeff (d N r t p : ℕ) : 1 ≤ wedgeScaleCoeff d N r t p := by
  have := detCoeff_nonneg d p
  rw [wedgeScaleCoeff]
  exact le_add_of_nonneg_right (by positivity)

omit [NumberField K] [LinearOrder ι] in
theorem card_powersetCard (p : ℕ) :
    Fintype.card (Set.powersetCard ι p) = (Fintype.card ι).choose p := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]

/-- **The scale of the wedge forms** is at most `wedgeScaleCoeff` times the scale of the forms. -/
theorem thresholdScale_wedgeForms_le (p : ℕ) [DecidableEq (Set.powersetCard ι p)] :
    thresholdScale Sfin (fun v ↦ exteriorPower.wedgeForms (L v) p)
      ≤ wedgeScaleCoeff (finrank ℚ K) (Fintype.card ι) (Fintype.card (InfinitePlace K)) #Sfin p
        * thresholdScale Sfin L := by
  have h1 := formLogHeight_wedgeForms_le Sfin L p
  rw [card_powersetCard] at h1
  have hD := detLogBound_formLogHeight_le (Sfin := Sfin) (L := L) p
  have h2 : ((Fintype.card (InfinitePlace K) : ℝ) + #Sfin) * ((Fintype.card ι).choose p : ℝ) ^ 2
        * detLogBound K p (formLogHeight Sfin L)
      ≤ ((Fintype.card (InfinitePlace K) : ℝ) + #Sfin) * ((Fintype.card ι).choose p : ℝ) ^ 2
        * (detCoeff (finrank ℚ K) p * thresholdScale Sfin L) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hh := formLogHeight_nonneg Sfin L
  have hrest : thresholdScale Sfin (fun v ↦ exteriorPower.wedgeForms (L v) p)
      = formLogHeight Sfin (fun v ↦ exteriorPower.wedgeForms (L v) p)
        + (thresholdScale Sfin L - formLogHeight Sfin L) := by
    simp only [thresholdScale]; ring
  rw [hrest, wedgeScaleCoeff]
  nlinarith

/-- **The coefficient of the threshold of Layer 6.1 along one size `p` of subsets**: one term for
each argument of `parametricStepThreshold`, the wedge terms scaled by `wedgeScaleCoeff`. -/
noncomputable def parametricStepCoeff (d N r t p : ℕ) (ε A : ℝ) : ℝ :=
  1 + minimaCoeff d N r t + Real.log 2 + 2 * wedgeWeightCoeff d N t p / ε + pluckerCoeff d N
    + (rankCoeff d (N.choose p) t (parametricDelta N ε / 2)
      + penultimateCoeff d (N.choose p) r t (N.choose p - 1) (parametricDelta N ε)
        (parametricWedgeAbsWeight N d p ε A)) * wedgeScaleCoeff d N r t p

theorem minimaCoeff_nonneg (d N r t : ℕ) : 0 ≤ minimaCoeff d N r t :=
  add_nonneg (pointCoeff_nonneg d N r t) (normCoeff_nonneg d N t)

theorem parametricStepCoeff_nonneg (d N r t p : ℕ) {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hA : 0 ≤ A) : 0 ≤ parametricStepCoeff d N r t p ε A := by
  have hδ := parametricDelta_pos hN hε
  have := minimaCoeff_nonneg d N r t
  have := wedgeWeightCoeff_nonneg d N t p
  have := pluckerCoeff_nonneg d N
  have := rankCoeff_nonneg d (N.choose p) t (by linarith : 0 ≤ parametricDelta N ε / 2)
  have := penultimateCoeff_nonneg d (N.choose p) r t (N.choose p - 1) hδ
    (parametricWedgeAbsWeight_nonneg N d p hε.le hA)
  have := one_le_wedgeScaleCoeff d N r t p
  have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  rw [parametricStepCoeff]; positivity

/-- **The threshold of Layer 6.1 along one size `p` is at most `parametricStepCoeff Λ`.** -/
theorem parametricStepThreshold_le [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A)
    {p : ℕ} (hp : p ≤ Fintype.card ι) :
    parametricStepThreshold Sfin L ε A p ≤ parametricStepCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin p ε A * thresholdScale Sfin L := by
  let : LinearOrder (Set.powersetCard ι p) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  have : Nonempty (Set.powersetCard ι p) := Set.powersetCard.nonempty_iff.2 hp
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  set t := #Sfin
  set M := N.choose p
  have hN : 0 < N := Fintype.card_pos
  have hM : Fintype.card (Set.powersetCard ι p) = M := card_powersetCard p
  have hWInf : ∀ w : InfinitePlace K,
      LinearIndependent K (exteriorPower.wedgeForms (L w.1) p) := fun w ↦
    exteriorPower.linearIndependent_wedgeForms (hLInf w) p
  have hWFin : ∀ v ∈ Sfin, LinearIndependent K (exteriorPower.wedgeForms (L v.1) p) :=
    fun v hv ↦ exteriorPower.linearIndependent_wedgeForms (hLFin v hv) p
  have hδ : 0 < parametricDelta N ε := parametricDelta_pos hN hε
  have hA' := parametricWedgeAbsWeight_nonneg N d p hε.le hA
  have hws := thresholdScale_wedgeForms_le (Sfin := Sfin) (L := L) p
  have hws1 := one_le_wedgeScaleCoeff d N r t p
  set ws := wedgeScaleCoeff d N r t p
  have hrank := log_rankThreshold_le (Sfin := Sfin)
    (L := fun v ↦ exteriorPower.wedgeForms (L v) p) hWInf hWFin (half_pos hδ)
  have hpen := penultimateThreshold_le (Sfin := Sfin)
    (L := fun v ↦ exteriorPower.wedgeForms (L v) p) hWInf hWFin (n := M - 1)
    (by rw [hM]; omega) hδ hA'
  rw [hM] at hrank hpen
  have hrc := rankCoeff_nonneg d M t (by linarith : 0 ≤ parametricDelta N ε / 2)
  have hpc := penultimateCoeff_nonneg d M r t (M - 1) hδ hA'
  have hmin := log_minimaThreshold_le hLInf hLFin (Sfin := Sfin) (L := L)
  have hminc := minimaCoeff_nonneg d N r t
  have hww := log_wedgeWeightConst_le hLInf hLFin (Sfin := Sfin) (L := L) p
  have hwwc := wedgeWeightCoeff_nonneg d N t p
  have hpl := log_pluckerConst_le (L := L) (Sfin := Sfin) N
  have hplc := pluckerCoeff_nonneg d N
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hrank' := hrank.trans (mul_le_mul_of_nonneg_left hws hrc)
  have hpen' := hpen.trans (mul_le_mul_of_nonneg_left hws hpc)
  have hww' : 2 * Real.log (wedgeWeightConst Sfin L (pluckerConst K N) p) / ε
      ≤ 2 * wedgeWeightCoeff d N t p / ε * Λ := by
    rw [div_mul_eq_mul_div, mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hww zero_le_two) hε.le
  have hwwc' : 0 ≤ 2 * wedgeWeightCoeff d N t p / ε * Λ := by positivity
  have h2 : Real.log 2 ≤ Real.log 2 * Λ := le_mul_of_one_le_right hlog2 hΛ
  have hsplit : parametricStepCoeff d N r t p ε A * Λ
      = Λ + minimaCoeff d N r t * Λ + Real.log 2 * Λ + 2 * wedgeWeightCoeff d N t p / ε * Λ
        + pluckerCoeff d N * Λ
        + rankCoeff d M t (parametricDelta N ε / 2) * (ws * Λ)
        + penultimateCoeff d M r t (M - 1) (parametricDelta N ε)
            (parametricWedgeAbsWeight N d p ε A) * (ws * Λ) := by
    rw [parametricStepCoeff]; ring
  have hΛ0 : 0 ≤ Λ := by linarith
  have e1 : 0 ≤ minimaCoeff d N r t * Λ := mul_nonneg hminc hΛ0
  have e2 : 0 ≤ Real.log 2 * Λ := mul_nonneg hlog2 hΛ0
  have e3 : 0 ≤ pluckerCoeff d N * Λ := mul_nonneg hplc hΛ0
  have e4 : 0 ≤ rankCoeff d M t (parametricDelta N ε / 2) * (ws * Λ) := by positivity
  have e5 : 0 ≤ penultimateCoeff d M r t (M - 1) (parametricDelta N ε)
      (parametricWedgeAbsWeight N d p ε A) * (ws * Λ) := by positivity
  rw [hsplit, parametricStepThreshold]
  refine max_le (by linarith) (max_le (by linarith) (max_le (max_le (by linarith)
    (by linarith)) (max_le (by linarith) (max_le (by linarith) ?_))))
  linarith

end Parametric

section Final

variable {ι : Type*} [Fintype ι]
variable {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}

omit [Fintype ι] in
/-- The scale does not depend on the decidability instance. -/
theorem thresholdScale_congr [Fintype ι] (i j : DecidableEq ι) :
    @thresholdScale K _ _ ι _ i Sfin L = @thresholdScale K _ _ ι _ j Sfin L := by
  cases Subsingleton.elim i j; rfl

/-- **The coefficient `a` of the threshold of Layer 6.1**: `1 + rankCoeff d N t ε` plus the sum
over `0 < p < N` of `parametricStepCoeff`, and `1` for `p = 0`. It depends on `N = #ι`,
`d = [K : ℚ]`, the number `r` of infinite places, `t = #Sfin`, `ε` and `A` alone. -/
noncomputable def parametricCoeff (d N r t : ℕ) (ε A : ℝ) : ℝ :=
  1 + rankCoeff d N t ε
    + ∑ p ∈ Finset.range N, if 0 < p then parametricStepCoeff d N r t p ε A else 1

theorem parametricCoeff_nonneg (d N r t : ℕ) {ε A : ℝ} (hN : 0 < N) (hε : 0 < ε) (hA : 0 ≤ A) :
    0 ≤ parametricCoeff d N r t ε A := by
  have := rankCoeff_nonneg d N t hε.le
  have : 0 ≤ ∑ p ∈ Finset.range N,
      if 0 < p then parametricStepCoeff d N r t p ε A else 1 :=
    Finset.sum_nonneg fun p _ ↦ by
      split_ifs
      · exact parametricStepCoeff_nonneg d N r t p hN hε hA
      · exact zero_le_one
  rw [parametricCoeff]; positivity

open scoped Classical in
/-- **The threshold of Layer 6.1 is linear in the heights**: `parametricThreshold ≤ a Λ` with
`a = parametricCoeff` a formula in `#ι`, `[K : ℚ]`, the number of infinite places, `#Sfin`, `ε`
and `A`, and `Λ = formLogHeight + log |D_K| + ∑_{v ∈ Sfin} log N(v) + 1`. -/
theorem parametricThreshold_le [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) :
    parametricThreshold Sfin L ε A ≤ parametricCoeff (finrank ℚ K) (Fintype.card ι)
      (Fintype.card (InfinitePlace K)) #Sfin ε A * thresholdScale Sfin L := by
  set Λ := thresholdScale Sfin L
  have hΛ : 1 ≤ Λ := one_le_thresholdScale Sfin L
  let o : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hsc := thresholdScale_congr (Sfin := Sfin) (L := L)
    (fun a b ↦ @LinearOrder.toDecidableEq ι o a b) (fun a b ↦ Classical.propDecidable (a = b))
  set N := Fintype.card ι
  set d := finrank ℚ K
  set r := Fintype.card (InfinitePlace K)
  set t := #Sfin
  have hN : 0 < N := Fintype.card_pos
  have hrank : Real.log (rankThreshold Sfin L ε) ≤ rankCoeff d N t ε * Λ := by
    have h := log_rankThreshold_le hLInf hLFin hε (Sfin := Sfin) (L := L)
    rw [hsc] at h; exact h
  have hrc := rankCoeff_nonneg d N t hε.le
  have hstep : ∀ p ∈ Finset.range N, (if 0 < p then parametricStepThreshold Sfin L ε A p else 1)
      ≤ (if 0 < p then parametricStepCoeff d N r t p ε A else 1) * Λ := fun p hp ↦ by
    split_ifs
    · have h := parametricStepThreshold_le hLInf hLFin hε hA (Sfin := Sfin) (L := L)
        (p := p) (Finset.mem_range.1 hp).le
      rwa [hsc] at h
    · rw [one_mul]; exact hΛ
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.sum_mul] at hsum
  have hsum0 : 0 ≤ ∑ p ∈ Finset.range N,
      if 0 < p then parametricStepCoeff d N r t p ε A else 1 :=
    Finset.sum_nonneg fun p _ ↦ by
      split_ifs
      · exact parametricStepCoeff_nonneg d N r t p hN hε hA
      · exact zero_le_one
  have hsplit : parametricCoeff d N r t ε A * Λ = Λ + rankCoeff d N t ε * Λ
      + (∑ p ∈ Finset.range N, if 0 < p then parametricStepCoeff d N r t p ε A else 1) * Λ := by
    rw [parametricCoeff]; ring
  have e1 : 0 ≤ rankCoeff d N t ε * Λ := mul_nonneg hrc (by linarith)
  have e2 := mul_nonneg hsum0 (by linarith : 0 ≤ Λ)
  rw [hsplit, parametricThreshold]
  refine max_le (by linarith) (max_le (by linarith) ?_)
  linarith

end Final

end NumberField
