/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Schlickewei1990.GapPrinciple
public import Schlickewei1990.SmallSolutions

-- Used only inside proofs.
import DiophantineApproximation.BalancedPoint
import DiophantineApproximation.NormForm

/-!
# All the solutions (Lemma 6.1)

Lemma 6.1 is the union of the three ranges: the small solutions (S90.5, `H(y) < B₀`), the
windows of the gap principle (S90.4) and the Subspace step (S90.3, `H(y') > θ`). The count has to
be uniform in the coefficients, and S90.4's count `gapWindows n B (n^d θ)` is not if `B` is
fixed: `θ` grows with `A' = ∏ᵢ ∏_{S∞∪S} ‖αᵢ‖`. Two facts repair that:

* **every solution has `A ≤ H(y) ^ (n + 1)`** (`NumberField.gapConst_le_mulHeight_pow`: in its
  class the relative sizes are at most `1` and multiply to `A / H(y) ^ (n + 1)`), so the windows
  may start at `B = max (B₀, A ^ (1 / (n + 1)))`;
* **for normalized coefficients `A' ≤ A (2^d √|D_K|) ^ (n + 1)`**
  (`NumberField.prod_placeProd_le_gapConst_mul`, Minkowski's class bound).

Then `n^d θ ≤ windowConst · B ^ (2 (n + 1))` (`NumberField.mul_stepThreshold_le`) and the number
of windows is at most `⌊log windowRatio / log (1 + 1/(4n))⌋ + 1`, free of `α`
(`NumberField.gapWindows_le`). That is what makes the count `log log` in `|D_K|` and `∏ N(q)`.

## Main definitions

* `NumberField.smallBound K n`: `B₀ = (n!) ^ (2 [K : ℚ]) + 1`.
* `NumberField.windowConst`, `NumberField.windowRatio`: the constants of the windows.
* `NumberField.lemmaCount K S n`: the count of Lemma 6.1.

## Main results

* `NumberField.exists_finset_submodule_of_sum_eq_zero`: **Lemma 6.1**.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
Lemma 6.1.

This is milestone S90.6 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height Module Finset

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **Every solution has height at least `A ^ (1 / (n + 1))`**: in its class the relative sizes
are at most `1` and multiply to `A / H(y) ^ (n + 1)` (`NumberField.prod_gapRatio`). -/
theorem gapConst_le_mulHeight_pow (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K}
    (hα0 : ∀ o, α o ≠ 0) {x : Option ι → Kˣ}
    (hx : ∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ o, α o * x o = 0) :
    gapConst S α ≤ mulHeight (fun o ↦ α o * (x o : K)) ^ (Fintype.card ι + 1) := by
  classical
  obtain ⟨r, hr, -⟩ := exists_unitClass S (fun o ↦ α o * (x o : K))
  have hy0 : ∀ o, α o * (x o : K) ≠ 0 := fun o ↦ mul_ne_zero (hα0 o) (x o).ne_zero
  have h := prod_gapRatio S r hα0 hx hsum hr
  have hle : ∏ p, ∏ i, gapRatio S r (fun o ↦ α o * x o) p i ≤ 1 :=
    prod_le_one₀ (fun p _ ↦ prod_nonneg fun i _ ↦ (gapRatio_pos S r hsum hy0 p i).le) fun p _ ↦
      prod_le_one₀ (fun i _ ↦ (gapRatio_pos S r hsum hy0 p i).le) fun i _ ↦
        gapRatio_le_one S hsum hy0 hr p i
  rw [h, div_le_one (pow_pos (zero_lt_one.trans_le (one_le_mulHeight _)) _)] at hle
  exact hle

/-- **For normalized coefficients, `A' ≤ A m ^ (n + 1)`**, `A'` the product in the threshold of
S90.3 and `m = 2 ^ d √|D_K|` the constant of Minkowski's class bound
(`NumberField.placeProd_iSup_le_mul_mulHeight` at `x = 1`). -/
theorem prod_placeProd_le_gapConst_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) (hint : ∀ o, IsIntegral ℤ (α o))
    (hm : (2 ^ finrank ℚ K * √|(discr K : ℝ)|)⁻¹ ≤ ∏ᶠ v : FinitePlace K, ⨆ o, v (α o)) :
    ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) ≤
      gapConst S α * (2 ^ finrank ℚ K * √|(discr K : ℝ)|) ^ (Fintype.card ι + 1) := by
  set m : ℝ := 2 ^ finrank ℚ K * √|(discr K : ℝ)|
  have hm0 : 0 < m := mul_pos (by positivity)
    (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero K)))
  set Pα := placeProd S Set.univ (fun v ↦ ⨆ o, v (α o))
  have hPα0 : 0 < Pα := placeProd_pos S _ fun v _ ↦
    (v.pos (hα0 none)).trans_le (le_ciSup (f := fun o ↦ v (α o)) (Finite.bddAbove_range _) none)
  have hH0 : 0 < mulHeight α := zero_lt_one.trans_le (one_le_mulHeight α)
  have hP : Pα ≤ m * mulHeight α := by
    have h := placeProd_iSup_le_mul_mulHeight S hint hm0 hm (x := fun _ ↦ 1)
      (fun _ ↦ one_mem _) (fun h ↦ hα0 none (by simpa using congrFun h none))
    simpa using h
  have hA' : 0 ≤ ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) :=
    prod_nonneg fun o _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _
  rw [gapConst, mul_assoc, ← mul_pow]
  refine le_mul_of_one_le_right hA' (one_le_pow₀ ?_)
  rw [div_mul_eq_mul_div, le_div_iff₀ hPα0, one_mul, mul_comm]
  exact hP

variable (K) in
/-- **The end of the small solutions**, `B₀ = (n!) ^ (2 [K : ℚ]) + 1`, just above the start of the
gap principle. -/
noncomputable def smallBound (n : ℕ) : ℝ := (((n.factorial : ℕ) : ℝ) ^ finrank ℚ K) ^ 2 + 1

theorem one_lt_smallBound (n : ℕ) : 1 < smallBound K n := by
  unfold smallBound
  have : (1 : ℝ) ≤ ((n.factorial : ℕ) : ℝ) ^ finrank ℚ K :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
  nlinarith

variable (K) in
/-- **The constant of the windows**: `n ^ d (κ ^ (n + 2) m ^ (n + 1) (κ² n ^ (d + #S)) ^ n)²`
with `κ = scalarConst K S` and `m = 2 ^ d √|D_K|`. With it the threshold of S90.3, at
normalized coefficients, is at most `windowConst · B ^ (2 (n + 1))` for every `B ≥ A^{1/(n+1)}`
(`NumberField.mul_stepThreshold_le`), and it does not see the coefficients. -/
noncomputable def windowConst (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℝ :=
  (n : ℝ) ^ finrank ℚ K * (scalarConst K S ^ (n + 2) *
    (2 ^ finrank ℚ K * √|(discr K : ℝ)|) ^ (n + 1) *
      (scalarConst K S ^ 2 * (n : ℝ) ^ (finrank ℚ K + #S)) ^ n) ^ 2

theorem one_le_windowConst (S : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ windowConst K S n := by
  have hκ := one_le_scalarConst (K := K) S
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ 2 ^ finrank ℚ K * √|(discr K : ℝ)| :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (Real.one_le_sqrt.2 (by exact_mod_cast Int.one_le_abs (discr_ne_zero K)))
  unfold windowConst
  refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn') (one_le_pow₀ ?_)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ)
    (one_le_pow₀ hm)) (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ)
      (one_le_pow₀ hn')))

variable (K) in
/-- **The bound for `log Θ / log B`** over the windows: `2 (n + 1) + log windowConst / log B₀`. -/
noncomputable def windowRatio (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℝ :=
  2 * (n + 1) + Real.log (windowConst K S n) / Real.log (smallBound K n)

/-- **The threshold of S90.3 against the windows.** For normalized coefficients and
`B ≥ A ^ (1 / (n + 1))`, `n ^ d θ ≤ windowConst · B ^ (2 (n + 1))`: `A' ≤ A m ^ (n + 1)`
(`NumberField.prod_placeProd_le_gapConst_mul`) and `A ≤ B ^ (n + 1)`. -/
theorem mul_stepThreshold_le (S : Finset (HeightOneSpectrum (𝓞 K))) {α : Option ι → K}
    (hα0 : ∀ o, α o ≠ 0) (hint : ∀ o, IsIntegral ℤ (α o))
    (hm : (2 ^ finrank ℚ K * √|(discr K : ℝ)|)⁻¹ ≤ ∏ᶠ v : FinitePlace K, ⨆ o, v (α o)) {B : ℝ}
    (hB : gapConst S α ≤ B ^ (Fintype.card ι + 1)) :
    (Fintype.card ι : ℝ) ^ finrank ℚ K * stepThreshold K S α ≤
      windowConst K S (Fintype.card ι) * B ^ (2 * (Fintype.card ι + 1)) := by
  set n := Fintype.card ι
  set κ := scalarConst K S
  set m : ℝ := 2 ^ finrank ℚ K * √|(discr K : ℝ)|
  set X := κ ^ 2 * (n : ℝ) ^ (finrank ℚ K + #S)
  have hκ : 0 ≤ κ := zero_le_one.trans (one_le_scalarConst S)
  have hm0 : 0 ≤ m := by positivity
  have hX : 0 ≤ X := by positivity
  have hA' := prod_placeProd_le_gapConst_mul S hα0 hint hm
  have hA'0 : 0 ≤ ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) :=
    prod_nonneg fun o _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _
  have h1 : κ ^ (n + 2) * (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * X ^ n ≤
      κ ^ (n + 2) * m ^ (n + 1) * X ^ n * B ^ (n + 1) := by
    calc κ ^ (n + 2) * (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) * X ^ n
        ≤ κ ^ (n + 2) * (B ^ (n + 1) * m ^ (n + 1)) * X ^ n := by
          gcongr
          exact hA'.trans (mul_le_mul_of_nonneg_right hB (by positivity))
      _ = _ := by ring
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [stepThreshold, windowConst]
  calc (n : ℝ) ^ finrank ℚ K * (κ ^ (n + 2) * (∏ o, placeProd S Set.univ (fun v ↦ v (α o))) *
        X ^ n) ^ 2
      ≤ (n : ℝ) ^ finrank ℚ K * (κ ^ (n + 2) * m ^ (n + 1) * X ^ n * B ^ (n + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- **The number of windows does not see the coefficients**: for `B ≥ B₀` and
`1 ≤ Θ ≤ windowConst · B ^ (2 (n + 1))`, `gapWindows n B Θ` is at most
`⌊log (windowRatio) / log (1 + 1 / (4 n))⌋ + 1`. -/
theorem gapWindows_le (S : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (hn : 1 ≤ n) {B Θ : ℝ}
    (hB : smallBound K n ≤ B) (hΘ1 : 1 ≤ Θ) (hΘ : Θ ≤ windowConst K S n * B ^ (2 * (n + 1))) :
    gapWindows n B Θ ≤
      ⌊Real.log (windowRatio K S n) / Real.log (1 + 1 / (4 * (n : ℝ)))⌋₊ + 1 := by
  have hB0 := one_lt_smallBound (K := K) n
  have hlB0 : 0 < Real.log (smallBound K n) := Real.log_pos hB0
  have hlB : Real.log (smallBound K n) ≤ Real.log B := Real.log_le_log (by linarith) hB
  have hW := one_le_windowConst S hn
  have hlW : 0 ≤ Real.log (windowConst K S n) := Real.log_nonneg hW
  have hBpos : 0 < B := by linarith
  have hlΘ : Real.log Θ ≤ Real.log (windowConst K S n) + 2 * (n + 1) * Real.log B := by
    calc Real.log Θ ≤ Real.log (windowConst K S n * B ^ (2 * (n + 1))) :=
          Real.log_le_log (by linarith) hΘ
      _ = _ := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
          push_cast
          ring
  set q := Real.log Θ / Real.log B
  have hq0 : 0 ≤ q := div_nonneg (Real.log_nonneg hΘ1) (by linarith)
  have hqR : q ≤ windowRatio K S n := by
    rw [windowRatio, div_le_iff₀ (by linarith)]
    calc Real.log Θ ≤ Real.log (windowConst K S n) + 2 * (n + 1) * Real.log B := hlΘ
      _ ≤ Real.log (windowConst K S n) / Real.log (smallBound K n) * Real.log B +
          2 * (n + 1) * Real.log B := by
          gcongr
          rw [div_mul_eq_mul_div, le_div_iff₀ hlB0]
          exact mul_le_mul_of_nonneg_left hlB hlW
      _ = _ := by ring
  have hR1 : 1 ≤ windowRatio K S n := by
    have : 0 ≤ Real.log (windowConst K S n) / Real.log (smallBound K n) := div_nonneg hlW hlB0.le
    rw [windowRatio]
    nlinarith
  have hlq : Real.log q ≤ Real.log (windowRatio K S n) := by
    rcases hq0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]
      exact Real.log_nonneg hR1
    · exact Real.log_le_log h hqR
  have hε : 0 < Real.log (1 + 1 / (4 * (n : ℝ))) := Real.log_pos (by
    have : (0 : ℝ) < 1 / (4 * n) := by positivity
    linarith)
  unfold gapWindows
  gcongr

/-- **The threshold of S90.3 is at least `1`** for nonzero `S`-integral coefficients. -/
theorem one_le_stepThreshold [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {α : Option ι → K} (hα : ∀ o, α o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hα0 : ∀ o, α o ≠ 0) : 1 ≤ stepThreshold K S α := by
  have hκ := one_le_scalarConst (K := K) S
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA : 1 ≤ ∏ o, placeProd S Set.univ (fun v ↦ v (α o)) :=
    one_le_prod₀ fun o _ ↦ one_le_placeProd_univ_of_mem_integer S (hα o) (hα0 o)
  unfold stepThreshold
  refine one_le_pow₀ (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ) hA) (one_le_pow₀ ?_))
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ) (one_le_pow₀ hn)

variable (K) in
/-- **The count of Lemma 6.1**: the small solutions (S90.5), the windows (S90.4, at most
`⌊log windowRatio / log (1 + 1/(4n))⌋ + 1` of them) and the Subspace step (S90.3), each times its
number of classes and grid points. It sees `K` and `S` only through `d`, `t`, `κ` and `|D_K|`,
and it does not see the coefficients. -/
noncomputable def lemmaCount (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : ℝ :=
  ((northcottCount (finrank ℚ K) (max (smallBound K n) 1).toNNReal ^ n : ℕ) : ℝ) +
    (((n + 1) ^ Fintype.card (InfinitePlace K ⊕ S) *
      (gapGrid S n + 1) ^ (n * Fintype.card (InfinitePlace K ⊕ S)) *
        (⌊Real.log (windowRatio K S n) / Real.log (1 + 1 / (4 * (n : ℝ)))⌋₊ + 1) : ℕ) : ℝ) +
    ((n + 1) ^ Fintype.card (InfinitePlace K ⊕ S) *
      ((n + 1) * stepGrid K S n + 1) ^ (n * Fintype.card (InfinitePlace K ⊕ S)) : ℕ) *
        stepCount K S n

/-- **Lemma 6.1.** For `n ≥ 2`, `P₀ ∈ S` and nonzero coefficients, the points
`y' = (α₁ x₁, …, αₙ xₙ)` of all the solutions of `∑ α_o x_o = 0` in `S`-units lie in at most
`lemmaCount K S n` proper subspaces of `Kⁿ`, a count that does not see `α`.

The coefficients are first normalized by Minkowski's class bound
(`NumberField.exists_mul_isIntegral_inv_le_finprod_iSup`), which changes neither the equation
nor the points up to a scalar. Then the solutions with `H(y) < B₀` are S90.5's, those with
`H(y') > θ` are S90.3's, and the rest have `max (B₀, A ^ (1 / (n + 1))) ≤ H(y)`
(`NumberField.gapConst_le_mulHeight_pow`) and `H(y') ≤ θ`, which is S90.4 with
`B = max (B₀, A ^ (1 / (n + 1)))`; at that `B` the number of windows is bounded uniformly in
`α` (`NumberField.gapWindows_le`). -/
theorem exists_finset_submodule_of_sum_eq_zero (hι : 2 ≤ Fintype.card ι)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {P₀ : HeightOneSpectrum (𝓞 K)} (hP₀ : P₀ ∈ S)
    {α : Option ι → K} (hα0 : ∀ o, α o ≠ 0) :
    ∃ T : Finset (Submodule K (ι → K)), (#T : ℝ) ≤ lemmaCount K S (Fintype.card ι) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        ∑ o, α o * x o = 0 → ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set n := Fintype.card ι with hn
  obtain ⟨c, hc0, hint, hm⟩ := exists_mul_isIntegral_inv_le_finprod_iSup (α := α)
    fun h ↦ hα0 none (congrFun h none)
  set β : Option ι → K := fun o ↦ c * α o with hβ
  have hβ0 : ∀ o, β o ≠ 0 := fun o ↦ mul_ne_zero hc0 (hα0 o)
  have hβS : ∀ o, β o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := fun o ↦
    mem_integer_of_isIntegral (hint o)
  set A := gapConst S β
  have hA0 : 0 ≤ A := zero_le_one.trans (one_le_gapConst S hβ0)
  set B := max (smallBound K n) (A ^ (((n + 1 : ℕ) : ℝ)⁻¹))
  have hBA : A ≤ B ^ (n + 1) := by
    calc A = (A ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ^ (n + 1) :=
          (Real.rpow_inv_natCast_pow hA0 (by omega)).symm
      _ ≤ B ^ (n + 1) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have hB : (((n.factorial : ℕ) : ℝ) ^ finrank ℚ K) ^ 2 < B :=
    lt_of_lt_of_le (by unfold smallBound; linarith) (le_max_left _ _)
  obtain ⟨T₁, hT₁, hT₁top, hT₁cov⟩ :=
    exists_finset_submodule_of_mulHeight_lt hι S hβ0 (smallBound K n)
  obtain ⟨T₂, hT₂, hT₂top, hT₂cov⟩ :=
    exists_finset_submodule_of_mulHeight_some_le S hβ0 (θ := stepThreshold K S β) hB
  obtain ⟨T₃, hT₃, hT₃top, hT₃cov⟩ := exists_finset_submodule_of_stepThreshold_lt S hP₀ hβS hβ0
  refine ⟨T₁ ∪ T₂ ∪ T₃, ?_, ?_, ?_⟩
  · have hw := gapWindows_le S (n := n) (by omega) (le_max_left _ _)
      (Θ := (n : ℝ) ^ finrank ℚ K * stepThreshold K S β)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n)))
        (one_le_stepThreshold S hβS hβ0)) (mul_stepThreshold_le S hβ0 hint hm hBA)
    have h2 := hT₂.trans (Nat.mul_le_mul_left _ hw)
    calc (#(T₁ ∪ T₂ ∪ T₃) : ℝ) ≤ #T₁ + #T₂ + #T₃ := by
          exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ lemmaCount K S n := by
          unfold lemmaCount
          gcongr
  · intro U hU
    rcases mem_union.1 hU with hU | hU
    · rcases mem_union.1 hU with hU | hU
      · exact hT₁top U hU
      · exact hT₂top U hU
    · exact hT₃top U hU
  · intro x hx hsum
    have hsumβ : ∑ o, β o * x o = 0 := by
      simp only [hβ, mul_assoc, ← mul_sum, hsum, mul_zero]
    suffices h : ∃ U ∈ T₁ ∪ T₂ ∪ T₃, (fun i ↦ β (some i) * (x (some i) : K)) ∈ U by
      obtain ⟨U, hU, hmem⟩ := h
      refine ⟨U, hU, ?_⟩
      convert U.smul_mem c⁻¹ hmem using 1
      funext i
      simp only [hβ, Pi.smul_apply, smul_eq_mul]
      field_simp
    by_cases h1 : mulHeight (fun o ↦ β o * (x o : K)) < smallBound K n
    · obtain ⟨U, hU, h⟩ := hT₁cov x hx h1
      exact ⟨U, mem_union_left _ (mem_union_left _ hU), h⟩
    by_cases h3 : stepThreshold K S β < mulHeight (fun i ↦ β (some i) * (x (some i) : K))
    · obtain ⟨U, hU, h⟩ := hT₃cov x hx hsumβ h3
      exact ⟨U, mem_union_right _ hU, h⟩
    have hH := gapConst_le_mulHeight_pow S hβ0 hx hsumβ
    have hHB : B ≤ mulHeight (fun o ↦ β o * (x o : K)) := by
      refine max_le (not_lt.1 h1) ?_
      have h0 : 0 ≤ mulHeight (fun o ↦ β o * (x o : K)) := zero_le_one.trans (one_le_mulHeight _)
      calc A ^ (((n + 1 : ℕ) : ℝ)⁻¹)
          ≤ (mulHeight (fun o ↦ β o * (x o : K)) ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow hA0 hH (by positivity)
        _ = _ := Real.pow_rpow_inv_natCast h0 (by omega)
    obtain ⟨U, hU, h⟩ := hT₂cov x hx hsumβ hHB (not_lt.1 h3)
    exact ⟨U, mem_union_left _ (mem_union_right _ hU), h⟩

end NumberField
