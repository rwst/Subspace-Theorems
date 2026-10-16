/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SystemGrid
public import QuantitativeSubspace.FormSystemCount
public import Schlickewei1990.ProductInequality

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import DiophantineApproximation.SubspaceReduction

/-!
# The Subspace step: the large solutions (Lemma 3.1)

Schlickewei's Lemma 3.1 puts the solutions `y' = (α₁ x₁, …, αₙ xₙ)` of large height into few
proper subspaces of `Kⁿ`, by the quantitative Subspace Theorem applied in each class (3.12). Here
the class is a choice `ρ` of a largest coordinate at every place of the system
(`NumberField.classChoice`, `(n + 1) ^ t` of them, `t` the number of places of `S∞ ∪ S`), the
point is the balanced representative `z = β y'` of S90.2
(`NumberField.exists_smul_balanced_unitClass`, normalized for Q4.3 with the constants
`balancedConst` of product `1`), and the product inequality (3.20) is turned into one of
`((n + 1) N + 1) ^ (n t)` normalized systems, `N = 4 t n`, by the grid of
`DiophantineApproximation/SystemGrid.lean` with `δ = 1/4`. Each system is counted by Q4.3
(`NumberField.exists_finset_submodule_of_isNormalizedSystem_ef` with `E = K`); its count
`NumberField.stepCount` does not depend on the class or the grid point, because the forms have
coefficients `0` and `1`, so the height `H` of Q4.3 is `1`.

The largest form at each place is at least `1 / n` times the sup norm of `z`
(`NumberField.iSup_le_card_mul_iSup_sumForms`), and the sup norms bound the affine height of the
balanced representative up to `κ²`. This is what the grid needs, and it costs the threshold

```text
H(y') > θ = (κ ^ (n + 2) · A' · (κ² · n ^ (d + #S)) ^ n) ²,   A' = ∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v,
```

`κ = scalarConst K S` (`NumberField.stepThreshold`). Schlickewei's threshold is `A² n^{3n+2}`;
the extra factors are the price of an explicit representative (S90.3 check, `README.md`), and the
range up to `θ` is S90.4's.

⚠ **`S` must have a finite place `P₀`**, where the balanced representative puts its slack. The
unit equation does not mind enlarging `S` (`NumberField.projUnitSolutions_mono`).

## Main results

* `NumberField.classChoice`, `NumberField.exists_classChoice`: the classes (3.12).
* `NumberField.isNormalizedSystem_sumForms`: the forms (3.7) with a grid of exponents are a
  normalized system.
* `NumberField.exists_mem_systemSet_of_stepThreshold_lt`: **a large solution solves one of the
  systems**.
* `NumberField.exists_finset_submodule_of_stepThreshold_lt`: **Lemma 3.1**, the large solutions
  lie in at most `(n + 1) ^ t ((n + 1) N + 1) ^ (n t) · stepCount` proper subspaces.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
Lemma 3.1.

This is milestone S90.3 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height Module Finset

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The classes -/

open scoped Classical in
/-- **The class of a choice** `ρ` of a coordinate at every place of the system: `ρ p` at the
place `systemPlace S p`, and `none` off `S∞ ∪ S`. -/
noncomputable def classChoice (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : InfinitePlace K ⊕ S → Option ι) : AbsoluteValue K ℝ → Option ι :=
  fun v ↦ if h : ∃ p, systemPlace S p = v then ρ h.choose else none

omit [Fintype ι] [DecidableEq ι] in
/-- **Every point has a class** (3.12) among the `(n + 1) ^ t` choices. -/
theorem exists_classChoice [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : Option ι → K) :
    ∃ ρ : InfinitePlace K ⊕ S → Option ι,
      ∀ v ∈ relevantPlaces S, v (y (classChoice S ρ v)) = ⨆ o, v (y o) := by
  classical
  have hmax : ∀ v : AbsoluteValue K ℝ, ∃ o, v (y o) = ⨆ o', v (y o') := fun v ↦ by
    obtain ⟨o, ho⟩ := Finite.exists_max fun o ↦ v (y o)
    exact ⟨o, le_antisymm (le_ciSup (f := fun o ↦ v (y o)) (Finite.bddAbove_range _) o)
      (ciSup_le ho)⟩
  set F : AbsoluteValue K ℝ → Option ι := fun v ↦ (hmax v).choose with hF
  refine ⟨fun p ↦ F (systemPlace S p), fun v hv ↦ ?_⟩
  unfold classChoice
  split_ifs with h
  · dsimp only
    rw [h.choose_spec]
    exact (hmax v).choose_spec
  · exact absurd (exists_systemPlace_eq hv) h

/-! ### The systems -/

/-- **The forms (3.7) with the exponents of a grid point are a normalized system**, with
coefficients of height `1` and degree `1`, at most `n + 1` distinct forms, and `δ = 1/4`, once the
grid point has a zero at every place and `∑ k p i / N ≥ n + 1/4`. -/
theorem isNormalizedSystem_sumForms (S : Finset (HeightOneSpectrum (𝓞 K)))
    {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S) (r : AbsoluteValue K ℝ → Option ι) {N M : ℕ}
    {k : InfinitePlace K ⊕ S → ι → Fin M} (hk0 : ∀ p, ∃ i, (k p i : ℕ) = 0)
    (hks : (Fintype.card ι : ℝ) + 1 / 4 ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N) :
    IsNormalizedSystem S (fun v ↦ v) (sumForms r) (balancedConst S P₀) (systemGridExponent S N k)
      1 1 (Fintype.card ι + 1) (1 / 4) where
  height_le p i j := by
    rcases sumForms_basisFun r (systemPlace S p) i j with h | h
    · rw [h, absMulHeight₁_zero]
    · rw [h, absMulHeight₁_one]
  degree_le p i j := (minpoly.natDegree_le _).trans (by rw [Module.finrank_self])
  ncard_le := by
    calc _ ≤ (Set.range fun o : Option ι ↦
            o.elim (∑ j, LinearMap.proj j) fun j ↦ LinearMap.proj j).ncard :=
          Set.ncard_le_ncard (by rintro _ ⟨q, rfl⟩; exact sumForms_mem_range r _ q.2)
            (Set.finite_range _)
      _ ≤ (Set.univ : Set (Option ι)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = Fintype.card ι + 1 := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option]
  const_pos := balancedConst_pos S P₀
  const_le := by
    rw [systemConst_balancedConst S hP₀, systemDet]
    simp [systemAbs, det_pi_sumForms]
  delta_pos := by norm_num
  delta_le_one := by norm_num
  weight_le := systemWeight_systemGridExponent_le S N hks
  exponent_le := systemGridExponent_le S N k
  exists_exponent_eq := exists_systemGridExponent_eq S N hk0

variable (K) in
/-- **The threshold of Q4.3 for the forms (3.7)**: the bound of `efSystemThreshold_le` at `E = K`,
coefficient height `1`, `n + 1` forms and `δ = 1/4`. It does not depend on the class. -/
noncomputable def stepX (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℝ :=
  max (domainThreshold n (finrank ℚ K) ((n + 1) * 1) (efEps 1 (1 / 4)) (efSpread 1 n (1 / 4))
      ((Fintype.card (InfinitePlace K) + #(systemPlacesOver K S)) * n ^ 2 *
        (finrank ℚ K * Real.log 1)))
    (max (finrank ℚ K * (2 * n / (1 / 4)) * Real.log n)
      (systemHeightThreshold n (finrank ℚ K) (Fintype.card (InfinitePlace K) + #S) (1 / 4) 1
        (Real.log (scalarConst K S))))

variable (K) in
/-- **The count of Q4.3 for one system** of the forms (3.7), uniform in the class and the grid
point. -/
noncomputable def stepCount (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℝ :=
  (1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * finrank ℚ K) + 4 * n * Real.log (Real.log (4 * 1))) +
    (1 + Real.log (systemMiddleRatio (finrank ℚ K) n 1 (1 / 4) (stepX K S n)) /
      Real.log (1 + 1 / 4 / (2 * n))) +
    efLargeCount n 1 (n + 1) (1 / 4)

/-- The count of one system is nonnegative. -/
theorem stepCount_nonneg (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    0 ≤ stepCount K S n := by
  have h4 : 0 ≤ Real.log (Real.log (4 * 1)) := by
    refine Real.log_nonneg ?_
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (4 * 1) :=
        Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hm : 0 ≤ Real.log (systemMiddleRatio (finrank ℚ K) n 1 (1 / 4) (stepX K S n)) :=
    Real.log_nonneg (le_max_left _ _)
  have hl : 0 ≤ Real.log (1 + 1 / 4 / (2 * n)) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have he := one_le_efLargeCount n 1 (n + 1) (δ := 1 / 4) (by norm_num) (by omega)
  rw [stepCount]
  have : 0 ≤ Real.log (systemMiddleRatio (finrank ℚ K) n 1 (1 / 4) (stepX K S n)) /
      Real.log (1 + 1 / 4 / (2 * n)) := div_nonneg hm hl
  have : 0 ≤ (1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * finrank ℚ K) + 4 * n * Real.log
      (Real.log (4 * 1))) := by positivity
  linarith

/-- **One system of the forms (3.7)** lies in at most `stepCount` proper subspaces. -/
theorem exists_finset_submodule_sumForms (S : Finset (HeightOneSpectrum (𝓞 K)))
    {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S) (r : AbsoluteValue K ℝ → Option ι) {N M : ℕ}
    {k : InfinitePlace K ⊕ S → ι → Fin M} (hk0 : ∀ p, ∃ i, (k p i : ℕ) = 0)
    (hks : (Fintype.card ι : ℝ) + 1 / 4 ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N) :
    ∃ T : Finset (Submodule K (ι → K)), (#T : ℝ) ≤ stepCount K S (Fintype.card ι) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ z ∈ systemSet S (fun v ↦ v) (sumForms r) (balancedConst S P₀)
        (systemGridExponent S N k), ∃ U ∈ T, z ∈ U := by
  have hN := isNormalizedSystem_sumForms S hP₀ r hk0 hks
  have hwInf : ∀ v : InfinitePlace K, ((fun v ↦ v) v.1 : AbsoluteValue K ℝ).LiesOver v.1 :=
    fun v ↦ AbsoluteValue.liesOver_self _
  have hwFin : ∀ v ∈ S, ((fun v ↦ v) (FinitePlace.mk v).1 : AbsoluteValue K ℝ).LiesOver
      (FinitePlace.mk v).1 := fun v _ ↦ AbsoluteValue.liesOver_self _
  obtain ⟨T, hT, htop, hcov⟩ :=
    exists_finset_submodule_of_isNormalizedSystem_ef (E := K) S (fun v ↦ v) hwInf hwFin hN
  have hX := efSystemThreshold_le hwInf hwFin hN
  rw [Module.finrank_self] at hT hX
  refine ⟨T, hT.trans ?_, htop, hcov⟩
  set n := Fintype.card ι
  have hn : 0 < n := by
    have := hN.two_le_card
    omega
  have hl : 0 < Real.log (1 + 1 / 4 / (2 * n)) :=
    Real.log_pos (lt_add_of_pos_right _ (by positivity))
  have hc : 0 ≤ (finrank ℚ K : ℝ) * Real.log (max (2 * 1) ((n : ℝ) ^ (2 * (n : ℝ) / (1 / 4)))) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (le_max_of_le_left (by norm_num)))
  have hmono : Real.log (systemMiddleRatio (finrank ℚ K) n 1 (1 / 4)
      (efSystemThreshold K S (fun v ↦ v) (sumForms r) (n + 1) 1 (1 / 4))) /
        Real.log (1 + 1 / 4 / (2 * n)) ≤
      Real.log (systemMiddleRatio (finrank ℚ K) n 1 (1 / 4) (stepX K S n)) /
        Real.log (1 + 1 / 4 / (2 * n)) := by
    refine div_le_div_of_nonneg_right (Real.log_le_log
      (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_) hl.le
    exact max_le_max le_rfl (div_le_div_of_nonneg_right hX hc)
  rw [stepCount]
  linarith

/-! ### The large solutions -/

variable (K) in
/-- **The size of the grid**, `N = 4 t n` with `t` the number of places of `S∞ ∪ S`: then
`N · (1/4)` is the number of pairs `(p, i)`. -/
noncomputable def stepGrid (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℕ :=
  4 * Fintype.card (InfinitePlace K ⊕ S) * n

variable (K) in
/-- **The threshold of the Subspace step**,
`θ = (κ ^ (n + 2) · A' · (κ² · n ^ (d + #S)) ^ n) ²` with `A' = ∏ᵢ ∏_{v ∈ S∞ ∪ S} ‖αᵢ‖_v` and
`κ = scalarConst K S`. -/
noncomputable def stepThreshold (S : Finset (HeightOneSpectrum (𝓞 K))) (α : Option ι → K) : ℝ :=
  (scalarConst K S ^ (Fintype.card ι + 2) * (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) *
    (scalarConst K S ^ 2 * (Fintype.card ι : ℝ) ^ (finrank ℚ K + #S)) ^ Fintype.card ι) ^ 2

/-- **A large solution solves one of the systems.** For `P₀ ∈ S`, nonzero `S`-integral `α`, and
`S`-units `x` with `∑ αᵢ xᵢ = 0` and `H(y') > θ`, some class `ρ`, some `β ≠ 0` and some grid point
`k` with a zero at every place and `∑ k p i / N ≥ n + 1/4` make `β y'` a solution of the system of
the forms (3.7) of the class with the exponents of `k`. -/
theorem exists_mem_systemSet_of_stepThreshold_lt [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S)
    {α : Option ι → K} (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hα0 : ∀ o, α o ≠ 0) {x : Option ι → Kˣ}
    (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ o, α o * x o = 0)
    (hθ : stepThreshold K S α < mulHeight (fun i ↦ α (some i) * (x (some i) : K))) :
    ∃ ρ : InfinitePlace K ⊕ S → Option ι, ∃ β : K, β ≠ 0 ∧
      ∃ k : InfinitePlace K ⊕ S → ι →
          Fin ((Fintype.card ι + 1) * stepGrid K S (Fintype.card ι) + 1),
        (∀ p, ∃ i, (k p i : ℕ) = 0) ∧
        (Fintype.card ι : ℝ) + 1 / 4 ≤
          ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / stepGrid K S (Fintype.card ι) ∧
        (β • fun i ↦ α (some i) * (x (some i) : K)) ∈ systemSet S (fun v ↦ v)
          (sumForms (classChoice S ρ)) (balancedConst S P₀)
          (systemGridExponent S (stepGrid K S (Fintype.card ι)) k) := by
  set n := Fintype.card ι with hn
  set y' : ι → K := fun i ↦ α (some i) * (x (some i) : K) with hy'
  obtain ⟨ρ, hρ⟩ := exists_classChoice S fun o ↦ α o * (x o : K)
  set r := classChoice S ρ with hr
  obtain ⟨β, hβ0, hzS, hsys, hbal, hHz⟩ :=
    exists_smul_balanced_unitClass S hP₀ r hα hα0 hx hsum hρ
  set z := β • y' with hz
  set H := mulHeightAff z with hH
  set κ := scalarConst K S with hκ
  set A' := ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) with hA'
  set Λ := κ ^ 2 * (n : ℝ) ^ (finrank ℚ K + #S) with hΛ
  set B := κ ^ (n + 2) * A' with hB
  have hn0 : 0 < n := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hκ1 : 1 ≤ κ := one_le_scalarConst S
  have hA'1 : 1 ≤ A' := by
    calc (1 : ℝ) = ∏ _o : Option ι, (1 : ℝ) := by simp
      _ ≤ A' := Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one)
          fun o _ ↦ one_le_placeProd_univ_of_mem_integer S (hα o) (hα0 o)
  have hΛ1 : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ1) (one_le_pow₀ hn1)
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ1) hA'1
  have hBΛ : 1 ≤ B * Λ ^ n := one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hΛ1)
  have hθH : (B * Λ ^ n) ^ 2 < H := by
    have h1 : mulHeight y' = mulHeight z := (mulHeight_smul_eq_mulHeight y' hβ0).symm
    calc (B * Λ ^ n) ^ 2 = stepThreshold K S α := by unfold stepThreshold; rfl
      _ < mulHeight y' := hθ
      _ = mulHeight z := h1
      _ ≤ H := mulHeight_le_mulHeightAff z
  have hH1 : 1 < H := lt_of_le_of_lt (one_le_pow₀ hBΛ) hθH
  have hH0 : 0 < H := zero_lt_one.trans hH1
  -- no form vanishes at `z`
  have hform : ∀ v i, sumForms r v i z ≠ 0 := fun v i ↦ by
    rw [hz, map_smul, smul_eq_mul]
    exact mul_ne_zero hβ0 (sumForms_ne_zero r v (y := fun o ↦ α o * (x o : K)) hsum
      (fun o ↦ mul_ne_zero (hα0 o) (x o).ne_zero) i)
  have hpos : ∀ p i, 0 < systemValue S (fun v ↦ v) (sumForms r) p i z := fun p i ↦ by
    simp only [systemValue, systemAbs, Algebra.algebraMap_self, RingHom.id_apply]
    exact pow_pos ((systemPlace S p).pos (hform _ i)) _
  -- the largest forms bound the height
  have hHM : H ≤ Λ * ∏ p, ⨆ i, systemValue S (fun v ↦ v) (sumForms r) p i z := by
    have hPS := placeProd_iSup_le_mul_prod_iSup_systemValue (S := S) (L := sumForms r) (x := z)
      (Nat.cast_nonneg n) fun p ↦ iSup_le_card_mul_iSup_sumForms r (systemPlace S p) z
    calc H ≤ κ ^ 2 * placeProd S Set.univ (fun v ↦ ⨆ i, v (z i)) := hHz
      _ ≤ κ ^ 2 * ((n : ℝ) ^ (finrank ℚ K + #S) *
          ∏ p, ⨆ i, systemValue S (fun v ↦ v) (sumForms r) p i z) :=
        mul_le_mul_of_nonneg_left hPS (by positivity)
      _ = _ := by rw [hΛ, mul_assoc]
  have hbal' : (∏ p, ∏ i, systemValue S (fun v ↦ v) (sumForms r) p i z) * H ≤ B := by
    rw [← affineProd_eq_prod_systemValue]
    exact hbal
  set P := ∏ p, ∏ i, systemValue S (fun v ↦ v) (sumForms r) p i z with hP
  set Mp := ∏ p, ⨆ i, systemValue S (fun v ↦ v) (sumForms r) p i z with hMp
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun p _ ↦ Finset.prod_nonneg fun i _ ↦ (hpos p i).le
  have hMp0 : 0 ≤ Mp := Finset.prod_nonneg fun p _ ↦ Real.iSup_nonneg fun i ↦ (hpos p i).le
  have hprod : P * H ^ ((n : ℝ) + 2 * (1 / 4)) ≤ Mp ^ n := by
    have hs : H ^ ((n : ℝ) + 2 * (1 / 4)) = H ^ n * √H := by
      rw [Real.rpow_add hH0, Real.rpow_natCast, Real.sqrt_eq_rpow]
      norm_num
    have hsH : 0 < √H := Real.sqrt_pos.2 hH0
    have hsq : B * Λ ^ n ≤ √H :=
      (le_abs_self _).trans (Real.abs_le_sqrt hθH.le)
    have hsqH : √H * √H = H := Real.mul_self_sqrt hH0.le
    have hpow : H ^ n ≤ Λ ^ n * Mp ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hH0.le hHM n
    have h1 : P * √H * Λ ^ n ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hsH
      calc P * √H * Λ ^ n * √H = P * (√H * √H) * Λ ^ n := by ring
        _ = P * H * Λ ^ n := by rw [hsqH]
        _ ≤ B * Λ ^ n := mul_le_mul_of_nonneg_right hbal' (by positivity)
        _ ≤ 1 * √H := by rw [one_mul]; exact hsq
    calc P * H ^ ((n : ℝ) + 2 * (1 / 4)) = P * (H ^ n * √H) := by rw [hs]
      _ ≤ P * (Λ ^ n * Mp ^ n * √H) := by gcongr
      _ = (P * √H * Λ ^ n) * Mp ^ n := by ring
      _ ≤ 1 * Mp ^ n := by gcongr
      _ = Mp ^ n := one_mul _
  have htpos : 0 < Fintype.card (InfinitePlace K ⊕ S) := Fintype.card_pos
  have hNpos : 0 < stepGrid K S n := by rw [stepGrid]; positivity
  have hq : (Fintype.card (InfinitePlace K ⊕ S) * Fintype.card ι : ℝ) ≤
      (stepGrid K S n : ℝ) * (1 / 4) :=
    le_of_eq (by rw [stepGrid]; push_cast; ring)
  obtain ⟨k, hk0, hks, hmem⟩ :=
    exists_mem_systemSet_systemGridExponent hNpos (by norm_num) hq hzS hH1 hpos hsys hprod
  exact ⟨ρ, β, hβ0, k, hk0, hks, hmem⟩

omit [DecidableEq ι] in
/-- **Lemma 3.1, the Subspace step.** For `P₀ ∈ S` and nonzero `S`-integral coefficients `α`,
the points `y' = (α₁ x₁, …, αₙ xₙ)` of the solutions of `∑ αᵢ xᵢ = 0` in `S`-units with
`H(y') > θ` (`NumberField.stepThreshold`) lie in at most
`(n + 1) ^ t ((n + 1) N + 1) ^ (n t) · stepCount` proper subspaces of `Kⁿ`, `t` the number of
places of `S∞ ∪ S` and `N = 4 t n`. -/
theorem exists_finset_submodule_of_stepThreshold_lt [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S)
    {α : Option ι → K} (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hα0 : ∀ o, α o ≠ 0) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ ((Fintype.card ι + 1) ^ Fintype.card (InfinitePlace K ⊕ S) *
          ((Fintype.card ι + 1) * stepGrid K S (Fintype.card ι) + 1) ^
            (Fintype.card ι * Fintype.card (InfinitePlace K ⊕ S)) : ℕ) *
        stepCount K S (Fintype.card ι) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        ∑ o, α o * x o = 0 →
        stepThreshold K S α < mulHeight (fun i ↦ α (some i) * (x (some i) : K)) →
        ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U := by
  classical
  set n := Fintype.card ι
  set N := stepGrid K S n
  have hsys : ∀ (ρ : InfinitePlace K ⊕ S → Option ι)
      (k : InfinitePlace K ⊕ S → ι → Fin ((n + 1) * N + 1)),
      ∃ T : Finset (Submodule K (ι → K)), (#T : ℝ) ≤ stepCount K S n ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ((∀ p, ∃ i, (k p i : ℕ) = 0) → (n : ℝ) + 1 / 4 ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N →
          ∀ z ∈ systemSet S (fun v ↦ v) (sumForms (classChoice S ρ)) (balancedConst S P₀)
            (systemGridExponent S N k), ∃ U ∈ T, z ∈ U) := by
    intro ρ k
    by_cases hk : (∀ p, ∃ i, (k p i : ℕ) = 0) ∧ (n : ℝ) + 1 / 4 ≤ ∑ p, ∑ i, ((k p i : ℕ) : ℝ) / N
    · obtain ⟨T, hT, htop, hcov⟩ :=
        exists_finset_submodule_sumForms S hP₀ (classChoice S ρ) hk.1 hk.2
      exact ⟨T, hT, htop, fun _ _ ↦ hcov⟩
    · exact ⟨∅, by simpa using stepCount_nonneg S n, by simp,
        fun h0 hs ↦ absurd ⟨h0, hs⟩ hk⟩
  choose T hTcard hTtop hTcov using hsys
  refine ⟨Finset.univ.biUnion fun q : (InfinitePlace K ⊕ S → Option ι) ×
      (InfinitePlace K ⊕ S → ι → Fin ((n + 1) * N + 1)) ↦ T q.1 q.2, ?_, ?_, ?_⟩
  · calc (#(Finset.univ.biUnion fun q : (InfinitePlace K ⊕ S → Option ι) ×
          (InfinitePlace K ⊕ S → ι → Fin ((n + 1) * N + 1)) ↦ T q.1 q.2) : ℝ)
        ≤ ∑ q : (InfinitePlace K ⊕ S → Option ι) ×
          (InfinitePlace K ⊕ S → ι → Fin ((n + 1) * N + 1)), (#(T q.1 q.2) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _q : (InfinitePlace K ⊕ S → Option ι) ×
          (InfinitePlace K ⊕ S → ι → Fin ((n + 1) * N + 1)), stepCount K S n :=
          Finset.sum_le_sum fun q _ ↦ hTcard q.1 q.2
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          congr 2
          simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
            ← pow_mul]
          rfl
  · intro U hU
    obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 hU
    exact hTtop q.1 q.2 U hq
  · intro x hx hsum hθ
    obtain ⟨ρ, β, hβ0, k, hk0, hks, hmem⟩ :=
      exists_mem_systemSet_of_stepThreshold_lt S hP₀ hα hα0 hx hsum hθ
    obtain ⟨U, hU, hzU⟩ := hTcov ρ k hk0 hks _ hmem
    refine ⟨U, Finset.mem_biUnion.2 ⟨(ρ, k), Finset.mem_univ _, hU⟩, ?_⟩
    have := U.smul_mem β⁻¹ hzU
    rwa [smul_smul, inv_mul_cancel₀ hβ0, one_smul] at this

end NumberField
