/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Schlickewei1990.AllSolutions
public import Schlickewei1990.Induction

/-!
# The theorems of record (Theorem 1.1, S90-A)

Lemma 6.1 (`AllSolutions.lean`), fed to the induction of §7 (`Induction.lean`), bounds the number
of solutions of `a₁ x₁ + ⋯ + aₙ xₙ = 1` in `S`-units with no vanishing subsum for one field
(`NumberField.ncard_unitSolutions_le_unitCount`). A prime `P₀` above `2` is added to `S` first,
so that S90.3 has a finite place; it has norm at most `2 ^ d`.

The count of Lemma 6.1 is `C (1 + log M)` with `M = log |D_K| + ∑_{p ∈ S} log N(p) + 2`
(`NumberField.lemmaCount_le`), and `C` sees `K` and `S` only through `d = [K : ℚ]`, the number of
infinite places and `#S`. The recursion squares it at every step (`NumberField.unitCount_le`), so
Theorem 1.1 comes out as `C (1 + log M) ^ (2 ^ (n + 1) − 1)`
(`NumberField.exists_ncard_unitSolutions_le`), and uniformly over all `K` and `S` with at most `s`
places (`NumberField.ncard_unitSolutions_le`).

## Main definitions

* `NumberField.logDiscrNorm K S`: `M`.
* `NumberField.lemmaConst`, `NumberField.recursionConst`, `NumberField.unitSolutionsConst`: the
  constants.

## Main results

* `NumberField.ncard_unitSolutions_le_unitCount`: Theorem 1.1 for one field.
* `NumberField.lemmaCount_le`: Lemma 6.1's count is linear in `log M`.
* `NumberField.exists_ncard_unitSolutions_le`: Theorem 1.1 with explicit invariants.
* `NumberField.ncard_unitSolutions_le`: **Theorem 1.1, S90-A**, uniform in `K`, `S` and the
  coefficients.

## Implementation notes

The exponent `2 ^ (n + 1) − 1` of `log M` is the recursion's, and is not in the paper: Sch90's
Lemma 6.1 has a count free of `K`, and squaring a constant gives a constant. With Evertse and
Ferretti's threshold the count of Lemma 6.1 carries `log M`, and the squares raise it to that
power. S90-B (after QS Q4.4) removes `log M` from Lemma 6.1, and with it the power.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
Theorem 1.1.

This is milestone S90.6 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open IsDedekindDomain Height Module Finset

namespace NumberField

variable {K : Type} [Field K] [NumberField K]

/-- **Enlarging `S` keeps every normalized solution.** -/
theorem normUnitSolutions_mono {κ : Type*} [Fintype κ] {S S' : Finset (HeightOneSpectrum (𝓞 K))}
    (h : S ⊆ S') (α : κ → K) (k₀ : κ) :
    normUnitSolutions S α k₀ ⊆ normUnitSolutions S' α k₀ :=
  fun _ ⟨h1, hu, h2, h3⟩ ↦ ⟨h1, fun k ↦ mem_unit_of_subset (coe_subset.2 h) (hu k), h2, h3⟩

open scoped Classical in
/-- **Theorem 1.1 for one field** (S90-A before the constants are bounded). For any prime `P₀`,
the equation `a₁ x₁ + ⋯ + aₙ xₙ = 1` has at most `unitCount L (n + 1)` solutions in `S`-units
with no vanishing subsum, `L m = ⌈lemmaCount K (S ∪ {P₀}) m⌉`: Lemma 6.1
(`NumberField.exists_finset_submodule_of_sum_eq_zero`) fed to the induction of §7
(`NumberField.ncard_normUnitSolutions_le_unitCount`; `L m = 0` for `m < 2`, where it is never
used), through the homogeneous form (1.6) with
`α_{n+1} = -1`. -/
theorem ncard_unitSolutions_le_unitCount {ι : Type} [Fintype ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P₀ : HeightOneSpectrum (𝓞 K)) (a : ι → K) :
    (unitSolutions S a).ncard ≤
      unitCount (fun m ↦ if 2 ≤ m then ⌈lemmaCount K (insert P₀ S) m⌉₊ else 0)
        (Fintype.card ι + 1) := by
  set α : Option ι → K := fun o ↦ o.elim (-1) a
  have ha : a = fun i ↦ -α (some i) / α none := by
    funext i
    simp [α]
  have hL : ∀ (ι' : Type) [Fintype ι'], 2 ≤ Fintype.card ι' → ∀ β : Option ι' → K,
      (∀ o, β o ≠ 0) → ∃ T : Finset (Submodule K (ι' → K)),
        #T ≤ (if 2 ≤ Fintype.card ι' then ⌈lemmaCount K (insert P₀ S) (Fintype.card ι')⌉₊
          else 0) ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x : Option ι' → Kˣ,
          (∀ o, x o ∈ ((insert P₀ S : Finset _) : Set (HeightOneSpectrum (𝓞 K))).unit K) →
          ∑ o, β o * x o = 0 → ∃ U ∈ T, (fun i ↦ β (some i) * (x (some i) : K)) ∈ U := by
    intro ι' _ hι' β hβ
    obtain ⟨T, hT, htop, hcov⟩ :=
      exists_finset_submodule_of_sum_eq_zero hι' (insert P₀ S) (mem_insert_self P₀ S) hβ
    refine ⟨T, ?_, htop, hcov⟩
    simp only [hι', ↓reduceIte]
    exact Nat.cast_le.1 (hT.trans (Nat.le_ceil _))
  calc (unitSolutions S a).ncard = (projUnitSolutions S α).ncard := by
        rw [ncard_projUnitSolutions S (by simp [α]), ← ha]
    _ ≤ (normUnitSolutions S α none).ncard := ncard_projUnitSolutions_le S α none
    _ ≤ (normUnitSolutions (insert P₀ S) α none).ncard :=
        Set.ncard_le_ncard (normUnitSolutions_mono (subset_insert P₀ S) α none)
          (finite_normUnitSolutions _ _ _)
    _ ≤ unitCount (fun m ↦ if 2 ≤ m then ⌈lemmaCount K (insert P₀ S) m⌉₊ else 0)
          (Fintype.card (Option ι)) :=
        ncard_normUnitSolutions_le_unitCount _ _ hL _ α none
    _ = _ := by rw [Fintype.card_option]

/-! ### The constants -/

/-- **The size of the field and of `S`** that the count sees:
`M = log |D_K| + ∑_{p ∈ S} log N(p) + 2 ≥ 2`. The count of S90-A is polynomial in `log M`. -/
noncomputable def logDiscrNorm (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  Real.log |(discr K : ℝ)| + ∑ p ∈ S, Real.log (Ideal.absNorm p.asIdeal) + 2

theorem log_absNorm_nonneg (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm p.asIdeal) :=
  Real.log_nonneg (Nat.one_le_cast.2
    (Nat.one_le_iff_ne_zero.2 fun h ↦ p.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)))

theorem two_le_logDiscrNorm (S : Finset (HeightOneSpectrum (𝓞 K))) : 2 ≤ logDiscrNorm K S := by
  have := sum_nonneg fun p (_ : p ∈ S) ↦ log_absNorm_nonneg p
  have := log_abs_discr_nonneg (K := K)
  unfold logDiscrNorm
  linarith

/-- **`log κ ≤ d + M`**, `κ = scalarConst K S`. -/
theorem log_scalarConst_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Real.log (scalarConst K S) ≤ finrank ℚ K + logDiscrNorm K S := by
  have hD : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hN : ∀ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) ≠ 0 := fun q _ ↦ Nat.cast_ne_zero.2
    fun h ↦ q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [scalarConst,
    Real.log_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) (prod_ne_zero_iff.2 hN))
      (Real.sqrt_pos.2 hD).ne',
    Real.log_mul (pow_ne_zero _ two_ne_zero) (prod_ne_zero_iff.2 hN), Real.log_pow,
    Real.log_prod hN, Real.log_sqrt hD.le, logDiscrNorm]
  have := log_abs_discr_nonneg (K := K)
  have hd : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
  nlinarith

/-- `log n ≤ n`. -/
private theorem log_natCast_le (n : ℕ) : Real.log n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)
    linarith

/-- **The constant of the window ratio**,
`2 (n + 1) + ((d + 2 n (d + σ)) n + (8 n + 6)(d + 1)) / log 2` with `σ = #S`. -/
noncomputable def windowRatioConst (n d σ : ℕ) : ℝ :=
  2 * (n + 1) + (((d : ℝ) + 2 * n * (d + σ)) * n + (8 * n + 6) * (d + 1)) / Real.log 2

/-- **The window ratio is linear in `M`**: `windowRatio ≤ windowRatioConst · M`, since
`windowConst ≤ n ^ (d + 2 n (d + #S)) κ ^ (8 n + 6)` (`2 ^ d √|D_K| ≤ κ`) and `log κ ≤ d + M`. -/
theorem windowRatio_le (S : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (hn : 1 ≤ n) :
    windowRatio K S n ≤ windowRatioConst n (finrank ℚ K) #S * logDiscrNorm K S := by
  have hM := two_le_logDiscrNorm (K := K) S
  have hκ1 := one_le_scalarConst (K := K) S
  have hlκ := log_scalarConst_le (K := K) S
  have hW1 := one_le_windowConst (K := K) S hn
  set d := finrank ℚ K
  set σ := #S
  set M := logDiscrNorm K S
  set κ := scalarConst K S
  set m : ℝ := 2 ^ d * √|(discr K : ℝ)|
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 ≤ m := by positivity
  have hmκ : m ≤ κ := by
    have hN : (1 : ℝ) ≤ ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) :=
      one_le_prod₀ fun q _ ↦ Nat.one_le_cast.2
        (Nat.one_le_iff_ne_zero.2 fun h ↦ q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    calc m = 2 ^ d * 1 * √|(discr K : ℝ)| := by ring
      _ ≤ κ := by
          unfold κ scalarConst
          gcongr
  have hW : windowConst K S n ≤ (n : ℝ) ^ (d + 2 * n * (d + σ)) * κ ^ (8 * n + 6) := by
    unfold windowConst
    calc (n : ℝ) ^ d * (κ ^ (n + 2) * m ^ (n + 1) * (κ ^ 2 * (n : ℝ) ^ (d + σ)) ^ n) ^ 2
        ≤ (n : ℝ) ^ d * (κ ^ (n + 2) * κ ^ (n + 1) * (κ ^ 2 * (n : ℝ) ^ (d + σ)) ^ n) ^ 2 := by
          gcongr
      _ = _ := by ring
  have hlκ0 : 0 ≤ Real.log κ := Real.log_nonneg hκ1
  have hln := log_natCast_le n
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hlW : Real.log (windowConst K S n) ≤
      (((d : ℝ) + 2 * n * (d + σ)) * n + (8 * n + 6) * (d + 1)) * M := by
    calc Real.log (windowConst K S n)
        ≤ Real.log ((n : ℝ) ^ (d + 2 * n * (d + σ)) * κ ^ (8 * n + 6)) :=
          Real.log_le_log (by linarith) hW
      _ = ((d + 2 * n * (d + σ) : ℕ) : ℝ) * Real.log n +
          ((8 * n + 6 : ℕ) : ℝ) * Real.log κ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      _ ≤ _ := by
          push_cast
          have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
          have hσ : (0 : ℝ) ≤ σ := Nat.cast_nonneg _
          have h1 : ((d : ℝ) + 2 * n * (d + σ)) * Real.log n ≤ ((d : ℝ) + 2 * n * (d + σ)) * n :=
            mul_le_mul_of_nonneg_left hln (by positivity)
          have h2 : (8 * (n : ℝ) + 6) * Real.log κ ≤ (8 * n + 6) * (d + M) :=
            mul_le_mul_of_nonneg_left hlκ (by positivity)
          have h3 : ((d : ℝ) + 2 * n * (d + σ)) * n ≤ ((d : ℝ) + 2 * n * (d + σ)) * n * M :=
            le_mul_of_one_le_right (by positivity) (by linarith)
          have h4 : (8 * (n : ℝ) + 6) * (d + M) ≤ (8 * n + 6) * (d + 1) * M := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
          nlinarith
  have hB₀ : Real.log 2 ≤ Real.log (smallBound K n) := Real.log_le_log two_pos (by
    unfold smallBound
    have : (1 : ℝ) ≤ ((n.factorial : ℕ) : ℝ) ^ d :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
    nlinarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlW0 := Real.log_nonneg hW1
  unfold windowRatio windowRatioConst
  have h3 : Real.log (windowConst K S n) / Real.log (smallBound K n) ≤
      Real.log (windowConst K S n) / Real.log 2 :=
    div_le_div_of_nonneg_left hlW0 hl2 hB₀
  have h4 : Real.log (windowConst K S n) / Real.log 2 ≤
      (((d : ℝ) + 2 * n * (d + σ)) * n + (8 * n + 6) * (d + 1)) / Real.log 2 * M := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hlW hl2.le
  have h6 : 2 * ((n : ℝ) + 1) ≤ 2 * (n + 1) * M :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  nlinarith

/-- **The constant of the middle ratio of Q4.3**: `stepX ≤ stepXConst · M`, with
`t = #(S∞ ∪ S)`. -/
noncomputable def stepXConst (n d t : ℕ) : ℝ :=
  |domainThreshold n d ((n + 1) * 1) (efEps 1 (1 / 4)) (efSpread 1 n (1 / 4)) 0| +
    8 * d * n * n + 8 * n * (d + 1) + 16 * t * Real.log n.factorial

theorem stepX_le (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    stepX K S n ≤
      stepXConst n (finrank ℚ K) (Fintype.card (InfinitePlace K) + #S) * logDiscrNorm K S := by
  have hM := two_le_logDiscrNorm (K := K) S
  have hlκ := log_scalarConst_le (K := K) S
  have hlκ0 : 0 ≤ Real.log (scalarConst K S) := Real.log_nonneg (one_le_scalarConst S)
  unfold stepX stepXConst
  simp only [Real.log_one, mul_zero]
  set d := finrank ℚ K
  set t := Fintype.card (InfinitePlace K) + #S
  set M := logDiscrNorm K S
  have hln := log_natCast_le n
  have hlf : 0 ≤ Real.log n.factorial :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  set a := domainThreshold n d ((n + 1) * 1) (efEps 1 (1 / 4)) (efSpread 1 n (1 / 4)) 0
  have hb : (d : ℝ) * (2 * n / (1 / 4)) * Real.log n ≤ 8 * d * n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have := mul_le_mul_of_nonneg_left hln (show (0 : ℝ) ≤ 8 * d * n by positivity)
      nlinarith
  have hc : systemHeightThreshold n d t (1 / 4) 1 (Real.log (scalarConst K S)) ≤
      8 * n * (d + M) + 16 * t * Real.log n.factorial := by
    unfold systemHeightThreshold
    simp only [Real.log_one, mul_zero, add_zero]
    have := mul_le_mul_of_nonneg_left hlκ (show (0 : ℝ) ≤ 8 * n by positivity)
    nlinarith
  have hX : max a (max ((d : ℝ) * (2 * n / (1 / 4)) * Real.log n)
      (systemHeightThreshold n d t (1 / 4) 1 (Real.log (scalarConst K S)))) ≤
        |a| + 8 * d * n * n + (8 * n * (d + M) + 16 * t * Real.log n.factorial) := by
    refine max_le ?_ (max_le ?_ ?_)
    · have : (0 : ℝ) ≤ 8 * n * (d + M) + 16 * t * Real.log n.factorial := by positivity
      have : (0 : ℝ) ≤ 8 * d * n * n := by positivity
      have := le_abs_self a
      linarith
    · have : (0 : ℝ) ≤ 8 * n * (d + M) + 16 * t * Real.log n.factorial := by positivity
      have := abs_nonneg a
      linarith
    · have : (0 : ℝ) ≤ 8 * d * n * n := by positivity
      have := abs_nonneg a
      linarith
  refine hX.trans ?_
  have := abs_nonneg a
  have : (0 : ℝ) ≤ 8 * d * n * n := by positivity
  have h1 : |a| ≤ |a| * M := le_mul_of_one_le_right (abs_nonneg a) (by linarith)
  have h2 : 8 * (d : ℝ) * n * n ≤ 8 * d * n * n * M := le_mul_of_one_le_right this (by linarith)
  have h3 : 8 * (n : ℝ) * (d + M) ≤ 8 * n * (d + 1) * M := by
    have hdM : (d : ℝ) + M ≤ (d + 1) * M := by nlinarith
    calc 8 * (n : ℝ) * (d + M) ≤ 8 * n * ((d + 1) * M) :=
          mul_le_mul_of_nonneg_left hdM (by positivity)
      _ = _ := by ring
  have h4 : 16 * (t : ℝ) * Real.log n.factorial ≤ 16 * t * Real.log n.factorial * M :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  nlinarith

/-- **The constant of Lemma 6.1**, a function of `n`, `d = [K : ℚ]`, the number `t₁` of infinite
places and `σ = #S` only: `lemmaCount K S n ≤ lemmaConst n d t₁ σ · (1 + log M)`
(`NumberField.lemmaCount_le`). -/
noncomputable def lemmaConst (n d t₁ σ : ℕ) : ℝ :=
  ((northcottCount d (max ((((n.factorial : ℕ) : ℝ) ^ d) ^ 2 + 1) 1).toNNReal ^ n : ℕ) : ℝ) +
    (((n + 1) ^ (t₁ + σ) * (4 * (n + 1) * (t₁ + σ) * n + 1) ^ (n * (t₁ + σ)) : ℕ) : ℝ) *
      (Real.log (windowRatioConst n d σ) / Real.log (1 + 1 / (4 * (n : ℝ))) +
        1 / Real.log (1 + 1 / (4 * (n : ℝ))) + 1) +
    (((n + 1) ^ (t₁ + σ) * ((n + 1) * (4 * (t₁ + σ) * n) + 1) ^ (n * (t₁ + σ)) : ℕ) : ℝ) *
      (|(1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * d) + 4 * n * Real.log (Real.log (4 * 1)))| + 1 +
        Real.log (1 + stepXConst n d (t₁ + σ) / (d * Real.log 2)) /
          Real.log (1 + 1 / 4 / (2 * (n : ℝ))) +
        1 / Real.log (1 + 1 / 4 / (2 * (n : ℝ))) + |efLargeCount n 1 (n + 1) (1 / 4)|)

/-- **Lemma 6.1's count is linear in `log M`**, with a constant that sees `K` and `S` only
through `d`, `t₁` and `#S`. -/
theorem lemmaCount_le (S : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (hn : 2 ≤ n) :
    lemmaCount K S n ≤ lemmaConst n (finrank ℚ K) (Fintype.card (InfinitePlace K)) #S *
      (1 + Real.log (logDiscrNorm K S)) := by
  have hM := two_le_logDiscrNorm (K := K) S
  have hR := windowRatio_le (K := K) S (n := n) (by omega)
  have hX := stepX_le (K := K) S n
  have hcard : Fintype.card (InfinitePlace K ⊕ S) = Fintype.card (InfinitePlace K) + #S := by
    rw [Fintype.card_sum, Fintype.card_coe]
  set d := finrank ℚ K
  set M := logDiscrNorm K S
  set L := Real.log M
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ε := Real.log (1 + 1 / (4 * (n : ℝ))) with hεdef
  set ε' := Real.log (1 + 1 / 4 / (2 * (n : ℝ))) with hε'def
  have hε : 0 < ε := Real.log_pos (by
    have : (0 : ℝ) < 1 / (4 * n) := by positivity
    linarith)
  have hε' : 0 < ε' := Real.log_pos (by
    have : (0 : ℝ) < 1 / 4 / (2 * n) := by positivity
    linarith)
  -- the windows
  set cR := windowRatioConst n d #S with hcRdef
  have hcR : 0 < cR := by
    unfold cR windowRatioConst
    have : (0 : ℝ) ≤ (((d : ℝ) + 2 * n * (d + #S)) * n + (8 * n + 6) * (d + 1)) / Real.log 2 :=
      div_nonneg (by positivity) hl2.le
    linarith
  have hR1 : 1 ≤ windowRatio K S n := by
    have hW1 := one_le_windowConst (K := K) S (n := n) (by omega)
    have hB0 := Real.log_pos (one_lt_smallBound (K := K) n)
    have := div_nonneg (Real.log_nonneg hW1) hB0.le
    unfold windowRatio
    linarith
  have hfl : (⌊Real.log (windowRatio K S n) / ε⌋₊ : ℝ) + 1 ≤ Real.log cR / ε + 1 + L / ε := by
    have h1 : Real.log (windowRatio K S n) ≤ Real.log cR + L := by
      rw [← Real.log_mul hcR.ne' (by positivity)]
      exact Real.log_le_log (by linarith) hR
    have h2 := Nat.floor_le (div_nonneg (Real.log_nonneg hR1) hε.le)
    have h3 : Real.log (windowRatio K S n) / ε ≤ Real.log cR / ε + L / ε := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right h1 hε.le
    linarith
  -- the middle ratio
  set cX := stepXConst n d (Fintype.card (InfinitePlace K) + #S) with hcXdef
  have hcX : 0 ≤ cX := by
    unfold cX stepXConst
    have : 0 ≤ Real.log ((n.factorial : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
    positivity
  set cS := 1 + cX / (d * Real.log 2) with hcSdef
  have hcS : 0 < cS := by
    have : 0 ≤ cX / (d * Real.log 2) := div_nonneg hcX (by positivity)
    unfold cS
    linarith
  have hSMR : systemMiddleRatio d n 1 (1 / 4) (stepX K S n) ≤ cS * M := by
    unfold systemMiddleRatio
    have hD : (d : ℝ) * Real.log 2 ≤
        d * Real.log (max (2 * 1) ((n : ℝ) ^ ((2 : ℝ) * n / (1 / 4)))) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log two_pos (by simp)) (by positivity)
    have hq : stepX K S n / (d * Real.log (max (2 * 1) ((n : ℝ) ^ ((2 : ℝ) * n / (1 / 4))))) ≤
        cX * M / (d * Real.log 2) := by
      rcases le_or_gt (stepX K S n) 0 with h | h
      · exact (div_nonpos_of_nonpos_of_nonneg h ((mul_pos (by positivity) hl2).le.trans hD)).trans
          (div_nonneg (mul_nonneg hcX (by linarith)) (by positivity))
      · calc stepX K S n / (d * Real.log (max (2 * 1) ((n : ℝ) ^ ((2 : ℝ) * n / (1 / 4)))))
            ≤ stepX K S n / (d * Real.log 2) :=
              div_le_div_of_nonneg_left h.le (by positivity) hD
          _ ≤ cX * M / (d * Real.log 2) := div_le_div_of_nonneg_right hX (by positivity)
    refine max_le (by unfold cS; nlinarith [div_nonneg hcX (show (0 : ℝ) ≤ d * Real.log 2 by
      positivity)]) (hq.trans ?_)
    unfold cS
    rw [add_mul, one_mul, div_mul_eq_mul_div]
    nlinarith
  have hstep : stepCount K S n ≤ |(1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * d) +
      4 * n * Real.log (Real.log (4 * 1)))| + 1 + Real.log cS / ε' + L / ε' +
        |efLargeCount n 1 (n + 1) (1 / 4)| := by
    unfold stepCount
    have h1 : Real.log (systemMiddleRatio d n 1 (1 / 4) (stepX K S n)) ≤ Real.log cS + L := by
      rw [← Real.log_mul hcS.ne' (by positivity)]
      exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) hSMR
    have h2 : Real.log (systemMiddleRatio d n 1 (1 / 4) (stepX K S n)) / ε' ≤
        Real.log cS / ε' + L / ε' := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right h1 hε'.le
    have := le_abs_self ((1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * d) +
      4 * n * Real.log (Real.log (4 * 1))))
    have := le_abs_self (efLargeCount n 1 (n + 1) (1 / 4))
    linarith
  -- assembling
  unfold lemmaCount lemmaConst gapGrid stepGrid smallBound
  rw [hcard]
  push_cast
  set G₁ : ℝ := ((n : ℝ) + 1) ^ (Fintype.card (InfinitePlace K) + #S) *
    (4 * ((n : ℝ) + 1) * ((Fintype.card (InfinitePlace K) : ℝ) + #S) * n + 1) ^
      (n * (Fintype.card (InfinitePlace K) + #S))
  set G₂ : ℝ := ((n : ℝ) + 1) ^ (Fintype.card (InfinitePlace K) + #S) *
    (((n : ℝ) + 1) * (4 * ((Fintype.card (InfinitePlace K) : ℝ) + #S) * n) + 1) ^
      (n * (Fintype.card (InfinitePlace K) + #S))
  set N₁ : ℝ := ((northcottCount d (max ((((n.factorial : ℕ) : ℝ) ^ d) ^ 2 + 1) 1).toNNReal : ℕ) :
    ℝ) ^ n
  have hG₁ : 0 ≤ G₁ := by positivity
  have hG₂ : 0 ≤ G₂ := by positivity
  have hN₁ : 0 ≤ N₁ := by positivity
  rw [← hεdef, ← hε'def, ← hcRdef, ← hcXdef, ← hcSdef]
  set s₀ := |(1 / 4 : ℝ)⁻¹ * ((10 ^ 3 * n) ^ (n * d) + 4 * n * Real.log (Real.log (4 * 1)))|
  set s₁ := |efLargeCount n 1 (n + 1) (1 / 4)|
  have hs₀ : 0 ≤ s₀ := abs_nonneg _
  have hs₁ : 0 ≤ s₁ := abs_nonneg _
  have hlcR : 0 ≤ Real.log cR := Real.log_nonneg (by
    unfold cR windowRatioConst
    have : (0 : ℝ) ≤ (((d : ℝ) + 2 * n * (d + #S)) * n + (8 * n + 6) * (d + 1)) / Real.log 2 :=
      div_nonneg (by positivity) hl2.le
    linarith)
  have hlcS : 0 ≤ Real.log cS := Real.log_nonneg (by
    have : 0 ≤ cX / (d * Real.log 2) := div_nonneg hcX (by positivity)
    unfold cS
    linarith)
  calc N₁ + G₁ * ((⌊Real.log (windowRatio K S n) / ε⌋₊ : ℝ) + 1) + G₂ * stepCount K S n
      ≤ N₁ + G₁ * (Real.log cR / ε + 1 + L / ε) +
          G₂ * (s₀ + 1 + Real.log cS / ε' + L / ε' + s₁) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hfl hG₁))
          (mul_le_mul_of_nonneg_left hstep hG₂)
    _ ≤ _ := by
        have e : (N₁ + G₁ * (Real.log cR / ε + 1 / ε + 1) +
            G₂ * (s₀ + 1 + Real.log cS / ε' + 1 / ε' + s₁)) * (1 + L) -
            (N₁ + G₁ * (Real.log cR / ε + 1 + L / ε) +
              G₂ * (s₀ + 1 + Real.log cS / ε' + L / ε' + s₁)) =
            N₁ * L + G₁ * (1 / ε + L * (Real.log cR / ε + 1)) +
              G₂ * (1 / ε' + L * (s₀ + 1 + Real.log cS / ε' + s₁)) := by ring
        have : 0 ≤ N₁ * L + G₁ * (1 / ε + L * (Real.log cR / ε + 1)) +
            G₂ * (1 / ε' + L * (s₀ + 1 + Real.log cS / ε' + s₁)) := by positivity
        linarith

/-- **The constants of the recursion**: `C(0) = 1`, `C(m + 1) = C(m) + c(m) 2^m C(m)²`. -/
noncomputable def recursionConst (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => recursionConst c m + c m * 2 ^ m * recursionConst c m ^ 2

theorem one_le_recursionConst {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) (m : ℕ) : 1 ≤ recursionConst c m := by
  induction m with
  | zero => simp [recursionConst]
  | succ m ih =>
    rw [recursionConst]
    have := hc m
    have : 0 ≤ c m * 2 ^ m * recursionConst c m ^ 2 := by positivity
    linarith

/-- **The recursion squares the count at each step**: if `L m ≤ c m · X` with `X ≥ 1`, then
`unitCount L N ≤ recursionConst c N · X ^ (2 ^ N - 1)`. -/
theorem unitCount_le (L : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) {X : ℝ} (hX : 1 ≤ X)
    (hL : ∀ m, (L m : ℝ) ≤ c m * X) (N : ℕ) :
    (unitCount L N : ℝ) ≤ recursionConst c N * X ^ (2 ^ N - 1) := by
  induction N with
  | zero => simp [unitCount, recursionConst]
  | succ N ih =>
    have hC := one_le_recursionConst hc N
    have hE : 2 ^ (N + 1) - 1 = 1 + 2 * (2 ^ N - 1) := by
      have := Nat.one_le_two_pow (n := N)
      rw [pow_succ]
      omega
    have hXe : X ^ (2 ^ N - 1) ≤ X ^ (2 ^ (N + 1) - 1) :=
      pow_le_pow_right₀ hX (by rw [hE]; omega)
    rw [unitCount, recursionConst]
    push_cast
    have hZ0 : (0 : ℝ) ≤ unitCount L N := Nat.cast_nonneg _
    calc (unitCount L N : ℝ) + L N * 2 ^ N * (unitCount L N : ℝ) ^ 2
        ≤ recursionConst c N * X ^ (2 ^ N - 1) +
            c N * X * 2 ^ N * (recursionConst c N * X ^ (2 ^ N - 1)) ^ 2 := by
          have := hc N
          have := hL N
          gcongr
      _ = recursionConst c N * X ^ (2 ^ N - 1) + c N * 2 ^ N * recursionConst c N ^ 2 *
            X ^ (1 + 2 * (2 ^ N - 1)) := by ring
      _ ≤ recursionConst c N * X ^ (2 ^ (N + 1) - 1) + c N * 2 ^ N * recursionConst c N ^ 2 *
            X ^ (2 ^ (N + 1) - 1) := by
          rw [← hE]
          gcongr
      _ = _ := by ring

/-! ### The theorems of record -/

/-- **The constant of Theorem 1.1** for `n` unknowns, as a function of `d = [K : ℚ]`, the number
`t₁` of infinite places and `σ = #S + 1` (the prime `P₀` added). -/
noncomputable def unitSolutionsConst (n d t₁ σ : ℕ) : ℝ :=
  recursionConst (fun m ↦ if 2 ≤ m then |lemmaConst m d t₁ σ| + 1 else 0) (n + 1) *
    (1 + Real.log (1 + d)) ^ (2 ^ (n + 1) - 1)

theorem unitSolutionsConst_nonneg (n d t₁ σ : ℕ) : 0 ≤ unitSolutionsConst n d t₁ σ := by
  have h := one_le_recursionConst (c := fun m ↦ if 2 ≤ m then |lemmaConst m d t₁ σ| + 1 else 0)
    (fun m ↦ by split_ifs <;> positivity) (n + 1)
  have : 0 ≤ Real.log (1 + d) := Real.log_nonneg (by simp)
  unfold unitSolutionsConst
  positivity

theorem lemmaCount_nonneg (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    0 ≤ lemmaCount K S n := by
  have := stepCount_nonneg (K := K) S n
  unfold lemmaCount
  positivity

/-- **Theorem 1.1 with explicit invariants** (S90-A). The equation `a₁ x₁ + ⋯ + aₙ xₙ = 1` has at
most `unitSolutionsConst n d t₁ σ · (1 + log M) ^ (2 ^ (n + 1) - 1)` solutions in `S`-units with no
vanishing subsum, for some `σ ≤ #S + 1`, where `d = [K : ℚ]`, `t₁` is the number of infinite
places and `M = log |D_K| + ∑_{p ∈ S} log N(p) + 2`. -/
theorem exists_ncard_unitSolutions_le {ι : Type} [Fintype ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → K) :
    ∃ σ ≤ #S + 1, ((unitSolutions S a).ncard : ℝ) ≤
      unitSolutionsConst (Fintype.card ι) (finrank ℚ K) (Fintype.card (InfinitePlace K)) σ *
        (1 + Real.log (logDiscrNorm K S)) ^ (2 ^ (Fintype.card ι + 1) - 1) := by
  classical
  obtain ⟨P₀, hP₀⟩ := exists_absNorm_le_two_pow (K := K)
  set S' := insert P₀ S
  set n := Fintype.card ι
  set d := finrank ℚ K
  set t₁ := Fintype.card (InfinitePlace K)
  set E := 2 ^ (n + 1) - 1
  refine ⟨#S', card_insert_le _ _, ?_⟩
  have hM := two_le_logDiscrNorm (K := K) S
  have hM' := two_le_logDiscrNorm (K := K) S'
  set X := 1 + Real.log (logDiscrNorm K S)
  set X' := 1 + Real.log (logDiscrNorm K S')
  have hX1 : 1 ≤ X := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ logDiscrNorm K S by linarith); linarith
  have hX'1 : 1 ≤ X' := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ logDiscrNorm K S' by linarith); linarith
  set c : ℕ → ℝ := fun m ↦ if 2 ≤ m then |lemmaConst m d t₁ #S'| + 1 else 0
  have hc : ∀ m, 0 ≤ c m := fun m ↦ by unfold c; split_ifs <;> positivity
  have hL : ∀ m, ((if 2 ≤ m then ⌈lemmaCount K S' m⌉₊ else 0 : ℕ) : ℝ) ≤ c m * X' := by
    intro m
    unfold c
    split_ifs with hm
    · have h1 := (Nat.ceil_lt_add_one (lemmaCount_nonneg (K := K) S' m)).le
      have h2 := lemmaCount_le (K := K) S' hm
      have h3 : lemmaConst m d t₁ #S' * X' ≤ |lemmaConst m d t₁ #S'| * X' :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      nlinarith
    · simp
  have h1 := ncard_unitSolutions_le_unitCount S P₀ a
  have h2 := unitCount_le _ hc hX'1 hL (n + 1)
  -- `M' ≤ (1 + d) M`
  have hlP₀ : Real.log (Ideal.absNorm P₀.asIdeal) ≤ d := by
    have hP1 : (1 : ℝ) ≤ Ideal.absNorm P₀.asIdeal := Nat.one_le_cast.2
      (Nat.one_le_iff_ne_zero.2 fun h ↦ P₀.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    calc Real.log (Ideal.absNorm P₀.asIdeal) ≤ Real.log ((2 : ℝ) ^ d) :=
          Real.log_le_log (by linarith) (by exact_mod_cast hP₀)
      _ = d * Real.log 2 := Real.log_pow _ _
      _ ≤ d * 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          gcongr
          linarith
      _ = d := mul_one _
  have hMM : logDiscrNorm K S' ≤ (1 + d) * logDiscrNorm K S := by
    have hsum : ∑ p ∈ S', Real.log (Ideal.absNorm p.asIdeal) ≤
        ∑ p ∈ S, Real.log (Ideal.absNorm p.asIdeal) + d := by
      by_cases h : P₀ ∈ S
      · rw [show S' = S from insert_eq_of_mem h]
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        linarith
      · rw [sum_insert h]
        linarith
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    unfold logDiscrNorm at hM ⊢
    nlinarith
  have hld : 0 ≤ Real.log (1 + d) := Real.log_nonneg (by simp)
  have hXX : X' ≤ (1 + Real.log (1 + d)) * X := by
    have hl : Real.log (logDiscrNorm K S') ≤ Real.log (1 + d) + Real.log (logDiscrNorm K S) := by
      rw [← Real.log_mul (by positivity) (by linarith)]
      exact Real.log_le_log (by linarith) hMM
    have : 0 ≤ Real.log (1 + d) * Real.log (logDiscrNorm K S) :=
      mul_nonneg hld (Real.log_nonneg (by linarith))
    unfold X X'
    nlinarith
  have hXE : X' ^ E ≤ (1 + Real.log (1 + d)) ^ E * X ^ E := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hXX E
  have hR := one_le_recursionConst hc (n + 1)
  calc ((unitSolutions S a).ncard : ℝ)
      ≤ recursionConst c (n + 1) * X' ^ E := (Nat.cast_le.2 h1).trans h2
    _ ≤ recursionConst c (n + 1) * ((1 + Real.log (1 + d)) ^ E * X ^ E) :=
        mul_le_mul_of_nonneg_left hXE (by linarith)
    _ = _ := by
        unfold unitSolutionsConst
        ring

/-- **Theorem 1.1, S90-A** (Schlickewei 1990, with the `log log` of Evertse–Ferretti's
threshold). For `n` unknowns and a bound `s` on the number of places of `S∞ ∪ S`, there is a
constant `C` such that, over every number field `K` and every `S` with
`#M_∞(K) + #S ≤ s`, the equation `a₁ x₁ + ⋯ + aₙ xₙ = 1` has at most
`C · (1 + log (log |D_K| + ∑_{p ∈ S} log N(p) + 2)) ^ (2 ^ (n + 1) - 1)` solutions in `S`-units
with no vanishing subsum. The bound does not depend on the coefficients. -/
theorem ncard_unitSolutions_le (n s : ℕ) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (a : Fin n → K), Fintype.card (InfinitePlace K) + #S ≤ s →
      ((unitSolutions S a).ncard : ℝ) ≤
        C * (1 + Real.log (Real.log |(discr K : ℝ)| +
          ∑ p ∈ S, Real.log (Ideal.absNorm p.asIdeal) + 2)) ^ (2 ^ (n + 1) - 1) := by
  refine ⟨∑ d ∈ range (2 * s + 1), ∑ t ∈ range (s + 1), ∑ σ ∈ range (s + 2),
    unitSolutionsConst n d t σ, fun K _ _ S a hs ↦ ?_⟩
  obtain ⟨σ, hσ, h⟩ := exists_ncard_unitSolutions_le S a
  rw [Fintype.card_fin] at h
  have hd : finrank ℚ K ≤ 2 * Fintype.card (InfinitePlace K) := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hX : 0 ≤ (1 + Real.log (logDiscrNorm K S)) ^ (2 ^ (n + 1) - 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ logDiscrNorm K S by
      linarith [two_le_logDiscrNorm (K := K) S])
    positivity
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hX)
  have hnn : ∀ d t σ, 0 ≤ unitSolutionsConst n d t σ := unitSolutionsConst_nonneg n
  calc unitSolutionsConst n (finrank ℚ K) (Fintype.card (InfinitePlace K)) σ
      ≤ ∑ σ ∈ range (s + 2),
          unitSolutionsConst n (finrank ℚ K) (Fintype.card (InfinitePlace K)) σ :=
        single_le_sum (fun σ _ ↦ hnn _ _ σ) (mem_range.2 (by omega))
    _ ≤ ∑ t ∈ range (s + 1), ∑ σ ∈ range (s + 2), unitSolutionsConst n (finrank ℚ K) t σ :=
        single_le_sum (f := fun t ↦ ∑ σ ∈ range (s + 2), unitSolutionsConst n (finrank ℚ K) t σ)
          (fun t _ ↦ sum_nonneg fun σ _ ↦ hnn _ _ σ) (mem_range.2 (by omega))
    _ ≤ _ :=
        single_le_sum (f := fun d ↦ ∑ t ∈ range (s + 1), ∑ σ ∈ range (s + 2),
            unitSolutionsConst n d t σ)
          (fun d _ ↦ sum_nonneg fun t _ ↦ sum_nonneg fun σ _ ↦ hnn _ _ σ)
          (mem_range.2 (by omega))

end NumberField
