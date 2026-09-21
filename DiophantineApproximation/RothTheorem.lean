/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RothAuxiliary
public import DiophantineApproximation.RothClass
public import DiophantineApproximation.RothKeyInequality

/-!
# Roth's theorem

**Roth's theorem** (Bombieri–Gubler, Theorem 6.4.1; Roth 1955 over `ℚ` at one place, Ridout 1958
over `ℚ` at several, Lang over a number field). Let `K` be a number field, `S` a finite set of
places of `K` carried as two typed finsets, `F / K` a finite extension, `w v` an absolute value of
`F` over `v` and `α v ∈ F` a target for each `v ∈ S`. Then for every `κ > 2` the set of `β ∈ K`
with

```text
(∏ v ∈ S∞, min 1 |β − α v|_v ^ mult v) * ∏ v ∈ S₀, min 1 |β − α v|_v  ≤  H(β) ^ (−κ)
```

is finite. Heights are Mathlib's relative ones, so this is the book's statement raised to the
power `[K : ℚ]`; every quantity in it is homogeneous of the same degree and the inequality reads
the same in either normalisation.

The proof is the book's, in five steps, and the file is only their assembly:

* **Step 0** (`DiophantineApproximation/RothClass.lean`, on Layer 3.1): discard the finitely many
  `β` of height `1` and the at most `|S|` that equal a target, classify the rest by Mahler's
  reduction, and take an `(L, M)`-independent sequence inside one class. What comes out is a
  vector of exponents `λ` with `∑ a, λ a ≥ 1 − |S| / N` such that every member of the sequence
  satisfies `min 1 |β − α_a|_a ^ w_a ≤ H(β) ^ (−κ λ a)`.
* **Steps I and II** (`DiophantineApproximation/RothAuxiliary.lean`, on Layers 2.6 and 2.7): build
  the auxiliary polynomial at the multidegree `d j = ⌈D / h(β j)⌉` and differentiate it until it
  survives at `β`.
* **Steps III to V** (`DiophantineApproximation/RothKeyInequality.lean`, on Layers 2.1 and 0.3):
  bound the value at every place, multiply by the product formula, and compare.

The parameters are chosen in the book's order — `ε` and `N` from `κ`, then the number of variables
`m + 1` from the feasibility of the index theorem, then `L` and `M`, then the solutions, and only
then `D`.

## Main results

* `NumberField.finite_setOf_prod_min_one_le`: **Layer 3.2**, Roth's theorem.
* `Real.exists_le_and_mul_log_add_lt`: the elementary fact that replaces the book's `D → ∞`.

## Implementation notes

⚠ **Nothing tends to infinity.** The book lets `D → ∞` and reads off `(6.22)`; here every error
term is explicit, the only one that is not `O(D / L)` is `([K : ℚ] + 2 ∑ a, w_a) log (D + 2)`, and
one `D` large enough is produced by hand. That is also why no filter, no `IsLittleO` and no
`Tendsto` appears anywhere in Layer 3.2.

⚠ **The two degenerate families of solutions are discarded by Northcott and by injectivity.** A
`β` of height at most `1` has no logarithmic profile, and a `β` equal to a target at some place has
local factor `0` there; the first set is finite by Northcott, the second has at most one element
per place, and an infinite solution set stays infinite after both are removed. This is the book's
"non-trivial approximation".

⚠ **`κ > 2` enters exactly once**, through `1 / κ < 1 / 2`: it is what leaves room for the two
losses `4 ε` and `|S| / N`, and the contradiction is `κ (1 − |S| / N) (1/2 − 4 ε) > 1`. No other
step uses the value of `κ`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.4.1 and §6.4.2 to §6.4.10.

This is Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height MvPolynomial Module

/-- **A logarithm is eventually beaten by any positive multiple of the identity.** -/
theorem Real.exists_le_and_mul_log_add_lt {B E c D₁ : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ D : ℝ, D₁ ≤ D ∧ 0 < D ∧ B * Real.log (D + 2) + E < c * D := by
  set t : ℝ := 4 * B / c + 1 with htdef
  have ht0 : (0 : ℝ) < t := by positivity
  have hBt : B / t ≤ c / 4 := by
    rw [div_le_div_iff₀ ht0 (by norm_num), htdef]
    field_simp
    nlinarith
  set D : ℝ := max (max D₁ 1) ((c / 2 + B * Real.log t + E + 1) * 4 / (3 * c)) with hDdef
  have hD1 : D₁ ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD0 : (1 : ℝ) ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDbig : (c / 2 + B * Real.log t + E + 1) * 4 / (3 * c) ≤ D := le_max_right _ _
  refine ⟨D, hD1, by linarith, ?_⟩
  have hlog : Real.log (D + 2) ≤ (D + 2) / t + Real.log t - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (D + 2) / t) (by positivity)
    rw [Real.log_div (by linarith) ht0.ne'] at h
    linarith
  have hstep : B * Real.log (D + 2) ≤ (c / 4) * (D + 2) + B * Real.log t := by
    calc B * Real.log (D + 2) ≤ B * ((D + 2) / t + Real.log t - 1) := by
          exact mul_le_mul_of_nonneg_left hlog hB
      _ = (B / t) * (D + 2) + B * Real.log t - B := by field_simp
      _ ≤ (c / 4) * (D + 2) + B * Real.log t - B := by
          have : (B / t) * (D + 2) ≤ (c / 4) * (D + 2) :=
            mul_le_mul_of_nonneg_right hBt (by linarith)
          linarith
      _ ≤ (c / 4) * (D + 2) + B * Real.log t := by linarith
  have hfin : (c / 2 + B * Real.log t + E + 1) ≤ (3 * c / 4) * D := by
    rw [div_le_iff₀ (by positivity)] at hDbig
    nlinarith
  nlinarith

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 3.2: Roth's theorem** (Bombieri–Gubler, Theorem 6.4.1). -/
theorem finite_setOf_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hwA : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a) := by
    rintro (v | v)
    · exact hwInf v v.2
    · exact hwFin v v.2
  -- discard the finitely many degenerate solutions
  have hbad : ({β : K | mulHeight₁ β ≤ 1}
      ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}).Finite := by
    refine Set.Finite.union (finite_setOfPred_mulHeight₁_le (K := K) 1)
      (Set.finite_iUnion fun a ↦ ?_)
    exact Set.Subsingleton.finite fun x hx y hy ↦
      (algebraMap K F).injective ((Set.mem_ofPred_eq ▸ hx).trans (Set.mem_ofPred_eq ▸ hy).symm)
  have hXinf := hinf.sdiff hbad
  set X : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}
      \ ({β : K | mulHeight₁ β ≤ 1}
        ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}) with hXdef
  have hXh : ∀ β ∈ X, 1 < mulHeight₁ β := fun β hβ ↦ by
    by_contra h
    exact hβ.2 (Set.mem_union_left _ (not_lt.mp h))
  have hXne : ∀ (a : ↥Sinf ⊕ ↥Sfin), ∀ β ∈ X, algebraMap K F β ≠ α (sPlaceAbsValue a) :=
    fun a β hβ h ↦ hβ.2 (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hXsub : ∀ β ∈ X, (∏ a, localApprox Sinf Sfin w α a β) ≤ mulHeight₁ β ^ (-κ) := by
    intro β hβ
    rw [prod_localApprox]
    exact hβ.1
  have hfpos : ∀ a, ∀ β ∈ X, 0 < localApprox Sinf Sfin w α a β := fun a β hβ ↦
    pow_pos (lt_min one_pos ((w _).pos (sub_ne_zero.mpr (hXne a β hβ)))) _
  have hfle : ∀ a, ∀ β ∈ X, localApprox Sinf Sfin w α a β ≤ 1 :=
    fun a β _ ↦ localApprox_le_one _ _ _ _ _ _
  -- the parameters `ε` and `N`
  set SA : ℕ := Fintype.card (↥Sinf ⊕ ↥Sfin) with hSAdef
  clear_value SA
  obtain ⟨ε, hε0, hε1, hε4, N, hN0, hSAN, hΘ⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 0 < 1 / 2 - 4 * ε ∧ ∃ N : ℕ, 0 < N ∧
        (SA : ℝ) / N ≤ 1 ∧ 1 < κ * (1 - (SA : ℝ) / N) * (1 / 2 - 4 * ε) := by
    set η : ℝ := 1 / 2 - 1 / κ with hηdef
    have hη0 : 0 < η := by
      rw [hηdef]
      have h : 1 / κ < 1 / 2 := by
        rw [div_lt_div_iff₀ hκ0 two_pos]
        linarith
      linarith
    have hη1 : η < 1 / 2 := by
      rw [hηdef]
      have : (0 : ℝ) < 1 / κ := by positivity
      linarith
    refine ⟨η / 16, by positivity, by linarith, by linarith,
      ⌈2 * (SA : ℝ) / η⌉₊ + 1, Nat.succ_pos _, ?_, ?_⟩
    · have hNbig : 2 * (SA : ℝ) / η < ((⌈2 * (SA : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.le_ceil (2 * (SA : ℝ) / η)]
      have hNpos : (0 : ℝ) < ((⌈2 * (SA : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_one hNpos]
      rw [div_lt_iff₀ hη0] at hNbig
      have hSA0 : (0 : ℝ) ≤ (SA : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hNbig : 2 * (SA : ℝ) / η < ((⌈2 * (SA : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (2 * (SA : ℝ) / η)]
    set N : ℕ := ⌈2 * (SA : ℝ) / η⌉₊ + 1 with hNdef
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      rw [hNdef]
      positivity
    have hSA0 : (0 : ℝ) ≤ (SA : ℝ) := Nat.cast_nonneg _
    have hx : (SA : ℝ) / N < η / 2 := by
      rw [div_lt_div_iff₀ hNpos two_pos]
      rw [div_lt_iff₀ hη0] at hNbig
      linarith
    have hx0 : (0 : ℝ) ≤ (SA : ℝ) / N := by positivity
    have h1 : (1 / 2 - 4 * (η / 16)) - (SA : ℝ) / N
        ≤ (1 - (SA : ℝ) / N) * (1 / 2 - 4 * (η / 16)) := by nlinarith
    have hinv : κ * (1 / κ) = 1 := by field_simp
    have hstep1 : κ * ((1 / 2 - 4 * (η / 16)) - (SA : ℝ) / N)
        ≤ κ * ((1 - (SA : ℝ) / N) * (1 / 2 - 4 * (η / 16))) :=
      mul_le_mul_of_nonneg_left h1 hκ0.le
    have hk : 1 / κ < (1 / 2 - 4 * (η / 16)) - (SA : ℝ) / N := by
      have hkk : 1 / κ = 1 / 2 - η := by rw [hηdef]; ring
      rw [hkk]
      linarith
    have hstep2 : 1 < κ * ((1 / 2 - 4 * (η / 16)) - (SA : ℝ) / N) := by
      calc (1 : ℝ) = κ * (1 / κ) := hinv.symm
        _ < κ * ((1 / 2 - 4 * (η / 16)) - (SA : ℝ) / N) := mul_lt_mul_of_pos_left hk hκ0
    rw [mul_assoc]
    linarith
  -- the number of variables
  obtain ⟨mnum, hfeasA⟩ : ∃ mm : ℕ, (finrank K F : ℝ) * (SA : ℝ)
      * Real.exp (-(6 * ((mm : ℝ) + 1) * ε ^ 2)) < 1 / 2 := by
    have hr0 : (0 : ℝ) ≤ (finrank K F : ℝ) := Nat.cast_nonneg _
    have hSA0 : (0 : ℝ) ≤ (SA : ℝ) := Nat.cast_nonneg _
    have hY : (0 : ℝ) < 2 * (finrank K F : ℝ) * SA + 1 := by positivity
    have hε2 : (0 : ℝ) < 6 * ε ^ 2 := by positivity
    refine ⟨⌈Real.log (2 * (finrank K F : ℝ) * SA + 1) / (6 * ε ^ 2)⌉₊, ?_⟩
    have hmbig : Real.log (2 * (finrank K F : ℝ) * SA + 1)
        < 6 * ((⌈Real.log (2 * (finrank K F : ℝ) * SA + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2 := by
      have h := Nat.le_ceil (Real.log (2 * (finrank K F : ℝ) * SA + 1) / (6 * ε ^ 2))
      rw [div_le_iff₀ hε2] at h
      nlinarith
    have h1 : Real.exp (-(6 * ((⌈Real.log (2 * (finrank K F : ℝ) * SA + 1)
          / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
        ≤ 1 / (2 * (finrank K F : ℝ) * SA + 1) := by
      rw [show (1 : ℝ) / (2 * (finrank K F : ℝ) * SA + 1)
          = Real.exp (-(Real.log (2 * (finrank K F : ℝ) * SA + 1))) by
        rw [Real.exp_neg, Real.exp_log hY, one_div]]
      exact Real.exp_le_exp.mpr (by linarith)
    calc (finrank K F : ℝ) * (SA : ℝ) * Real.exp (-(6 * ((⌈Real.log
            (2 * (finrank K F : ℝ) * SA + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
        ≤ (finrank K F : ℝ) * (SA : ℝ) * (1 / (2 * (finrank K F : ℝ) * SA + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((finrank K F : ℝ) * SA) / (2 * (finrank K F : ℝ) * SA + 1) := by rw [mul_one_div]
      _ < 1 / 2 := by
          rw [div_lt_div_iff₀ hY two_pos]
          nlinarith
  set Θ : ℝ := κ * (1 - (SA : ℝ) / N) * (1 / 2 - 4 * ε) with hΘdef
  clear_value Θ
  have hΘ1 : (0 : ℝ) < Θ - 1 := by linarith
  -- the constants of the data
  set tgt : (↥Sinf ⊕ ↥Sfin) → F := fun a ↦ α (sPlaceAbsValue a) with htgtdef
  set Cα : ℝ := 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, w (sPlaceAbsValue a) (tgt a) with hCαdef
  have hCαsum0 : (0 : ℝ) ≤ ∑ a : ↥Sinf ⊕ ↥Sfin, w (sPlaceAbsValue a) (tgt a) :=
    Finset.sum_nonneg fun a _ ↦ (w _).nonneg _
  have hCα1 : (1 : ℝ) ≤ Cα := by rw [hCαdef]; linarith
  have hCα : ∀ a, w (sPlaceAbsValue a) (tgt a) ≤ Cα := fun a ↦ by
    have h := Finset.single_le_sum (f := fun b : ↥Sinf ⊕ ↥Sfin ↦ w (sPlaceAbsValue b) (tgt b))
      (fun b _ ↦ (w _).nonneg _) (Finset.mem_univ a)
    rw [hCαdef]
    linarith
  clear_value Cα
  set C₁ : ℝ := Real.log 2 + 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (tgt a) with hC₁def
  have hC₁sum0 : (0 : ℝ) ≤ ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (tgt a) :=
    Finset.sum_nonneg fun a _ ↦ absLogHeight₁_nonneg _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁0 : (0 : ℝ) ≤ C₁ := by rw [hC₁def]; linarith
  have hC₁ : ∀ a, absLogHeight₁ (tgt a) + Real.log 2 + 1 ≤ C₁ := fun a ↦ by
    have h := Finset.single_le_sum (f := fun b : ↥Sinf ⊕ ↥Sfin ↦ absLogHeight₁ (tgt b))
      (fun b _ ↦ absLogHeight₁_nonneg _) (Finset.mem_univ a)
    rw [hC₁def]
    linarith
  clear_value C₁
  -- Steps I and II
  rw [hSAdef] at hfeasA
  obtain ⟨D₀, hD₀⟩ := exists_auxiliary_deriv tgt hε0 hε1 hfeasA hC₁0 hC₁
  -- the remaining parameters
  set σ : ℝ := ε ^ 2 ^ mnum with hσdef
  have hσ0 : (0 : ℝ) < σ := pow_pos hε0 _
  have hσ1 : σ ≤ 1 / 2 := by
    rw [hσdef]
    calc ε ^ 2 ^ mnum ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le (by linarith) Nat.one_le_two_pow
      _ = ε := pow_one _
      _ ≤ 1 / 2 := hε1.le
  clear_value σ
  set tw : ℕ := totalWeight K with htwdef
  clear_value tw
  set Wsum : ℕ := ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a with hWdef
  clear_value Wsum
  have hlogCα : (0 : ℝ) ≤ Real.log Cα := Real.log_nonneg hCα1
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  set G : ℝ :=
    2 * ((Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα) + (tw : ℝ) * (C₁ + Real.log 2)) with hGdef
  have hG0 : (0 : ℝ) ≤ G := by
    rw [hGdef]
    have h1 : (0 : ℝ) ≤ (Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα) := by
      apply mul_nonneg (Nat.cast_nonneg _); linarith
    have h2 : (0 : ℝ) ≤ (tw : ℝ) * (C₁ + Real.log 2) := by
      apply mul_nonneg (Nat.cast_nonneg _); linarith
    linarith
  clear_value G
  set L : ℝ := max (max 1 (2 * (tw : ℝ) * ((mnum : ℝ) + 1) * (C₁ + 4) / σ))
    (2 * G / (Θ - 1)) with hLdef
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left 1 _) (le_max_left _ _)
  have hLroth : 2 * (tw : ℝ) * ((mnum : ℝ) + 1) * (C₁ + 4) / σ ≤ L :=
    le_trans (le_max_right 1 _) (le_max_left _ _)
  have hLfinal : 2 * G / (Θ - 1) ≤ L := le_max_right _ _
  clear_value L
  set Mind : ℝ := 2 / σ with hMdef
  have hM1 : (1 : ℝ) ≤ Mind := by
    rw [hMdef, le_div_iff₀ hσ0]
    linarith
  clear_value Mind
  -- Step 0: one approximation class, and an independent sequence inside it
  obtain ⟨lam, hlam0, hlamsum, b, hbX, hbind, hblocal⟩ :=
    exists_isHeightIndependent_forall_le_rpow (localApprox Sinf Sfin w α) hXinf hfpos hfle hκ0
      hXsub hXh hN0 L Mind
  rw [← hSAdef] at hlamsum
  have hbh0 : ∀ j, (0 : ℝ) ≤ logHeight₁ (b j) := fun j ↦ zero_le_logHeight₁ _
  have hmono : ∀ i j : ℕ, i ≤ j → logHeight₁ (b i) ≤ logHeight₁ (b j) := by
    intro i j hij
    induction j with
    | zero => rw [Nat.le_zero.mp hij]
    | succ k ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
        · exact le_trans (ih (Nat.lt_succ_iff.mp h))
            (le_trans (le_mul_of_one_le_left (hbh0 k) hM1) (hbind.2 k))
        · rw [h]
  have hbL : ∀ j, L ≤ logHeight₁ (b j) := fun j ↦ le_trans hbind.1 (hmono 0 j (Nat.zero_le j))
  -- the `mnum + 1` solutions
  set β : Fin (mnum + 1) → K := fun j ↦ b j.val with hβdef
  set Hmax : ℝ := logHeight₁ (b mnum) with hHmaxdef
  have hHmax0 : (0 : ℝ) < Hmax := lt_of_lt_of_le zero_lt_one (le_trans hL1 (hbL mnum))
  have hβle : ∀ j : Fin (mnum + 1), logHeight₁ (β j) ≤ Hmax :=
    fun j ↦ hmono j.val mnum (Nat.lt_succ_iff.mp j.isLt)
  clear_value Hmax
  have hβL : ∀ j : Fin (mnum + 1), L ≤ logHeight₁ (β j) := fun j ↦ hbL j.val
  have hβ0 : ∀ j : Fin (mnum + 1), (0 : ℝ) < logHeight₁ (β j) :=
    fun j ↦ lt_of_lt_of_le zero_lt_one (le_trans hL1 (hβL j))
  set Hβ : ℝ := ∑ j : Fin (mnum + 1), logHeight₁ (β j) with hHβdef
  have hHβ0 : (0 : ℝ) ≤ Hβ := Finset.sum_nonneg fun j _ ↦ (hβ0 j).le
  clear_value Hβ
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  -- a large `D`
  obtain ⟨D, hDbig, hD0, hDlog⟩ := Real.exists_le_and_mul_log_add_lt
    (B := (tw : ℝ) + 2 * (Wsum : ℝ)) (E := Hβ) (c := (Θ - 1) / 2)
    (D₁ := max (max L (((max D₀ 1 : ℕ) : ℝ) * Hmax)) (2 * Hmax / σ))
    (by positivity) (by linarith)
  have hDL : L ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDbig
  have hDD₀ : ((max D₀ 1 : ℕ) : ℝ) * Hmax ≤ D :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDbig
  have hDσ : 2 * Hmax / σ ≤ D := le_trans (le_max_right _ _) hDbig
  -- the multidegree
  set d : Fin (mnum + 1) → ℕ := fun j ↦ ⌈D / logHeight₁ (β j)⌉₊ with hddef
  have hdlow : ∀ j, D / logHeight₁ (β j) ≤ (d j : ℝ) := fun j ↦ Nat.le_ceil _
  have hdhigh : ∀ j, (d j : ℝ) < D / logHeight₁ (β j) + 1 := fun j ↦
    Nat.ceil_lt_add_one (by positivity)
  have hdD : ∀ j, D ≤ (d j : ℝ) * logHeight₁ (β j) := fun j ↦ by
    rw [← div_le_iff₀ (hβ0 j)]
    exact hdlow j
  have hdLbound : ∀ j, (d j : ℝ) ≤ D / L + 1 := fun j ↦ by
    refine le_of_lt (lt_of_lt_of_le (hdhigh j) ?_)
    have h : D / logHeight₁ (β j) ≤ D / L := by
      rw [div_le_div_iff₀ (hβ0 j) hL0]
      exact mul_le_mul_of_nonneg_left (hβL j) hD0.le
    linarith
  have hdD₀ : ∀ j, max D₀ 1 ≤ d j := fun j ↦ by
    have h1 : ((max D₀ 1 : ℕ) : ℝ) ≤ (d j : ℝ) := by
      calc ((max D₀ 1 : ℕ) : ℝ) ≤ D / Hmax := by rw [le_div_iff₀ hHmax0]; exact hDD₀
        _ ≤ D / logHeight₁ (β j) := by
            rw [div_le_div_iff₀ hHmax0 (hβ0 j)]
            exact mul_le_mul_of_nonneg_left (hβle j) hD0.le
        _ ≤ (d j : ℝ) := hdlow j
    exact_mod_cast h1
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (le_max_right D₀ 1) (hdD₀ j)
  -- the degrees drop fast enough for Roth's lemma
  have hratio : ∀ j : Fin mnum, (d j.succ : ℝ) ≤ σ * (d j.castSucc : ℝ) := by
    intro j
    have hsucc : Mind * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ) := by
      have h := hbind.2 j.val
      simpa [hβdef, Fin.val_succ, Fin.val_castSucc] using h
    have hquo0 : (0 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) :=
      mul_nonneg (by linarith) (div_nonneg hD0.le (hβ0 _).le)
    have heq : σ / 2 * (D / logHeight₁ (β j.castSucc))
        * (Mind * logHeight₁ (β j.castSucc)) = D := by
      rw [hMdef, show σ / 2 * (D / logHeight₁ (β j.castSucc))
          * (2 / σ * logHeight₁ (β j.castSucc))
          = σ / 2 * (2 / σ) * (D / logHeight₁ (β j.castSucc) * logHeight₁ (β j.castSucc)) from
        by ring, div_mul_cancel₀ D (hβ0 _).ne', show σ / 2 * (2 / σ) = 1 from by field_simp,
        one_mul]
    have hstep : D / logHeight₁ (β j.succ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      rw [div_le_iff₀ (hβ0 _)]
      calc D = σ / 2 * (D / logHeight₁ (β j.castSucc))
              * (Mind * logHeight₁ (β j.castSucc)) := heq.symm
        _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) * logHeight₁ (β j.succ) :=
            mul_le_mul_of_nonneg_left hsucc hquo0
    have hu2 : 2 / σ ≤ D / logHeight₁ (β j.castSucc) := by
      rw [div_le_div_iff₀ hσ0 (hβ0 _)]
      rw [div_le_iff₀ hσ0] at hDσ
      linarith [hβle j.castSucc]
    have hone : (1 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      have h := mul_le_mul_of_nonneg_left hu2 (by linarith : (0 : ℝ) ≤ σ / 2)
      rwa [show σ / 2 * (2 / σ) = 1 by field_simp] at h
    calc (d j.succ : ℝ) ≤ D / logHeight₁ (β j.succ) + 1 := (hdhigh _).le
      _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) + 1 := by linarith
      _ ≤ σ * (D / logHeight₁ (β j.castSucc)) := by linarith
      _ ≤ σ * (d j.castSucc : ℝ) := mul_le_mul_of_nonneg_left (hdlow _) hσ0.le
  -- the height condition of Roth's lemma
  have hDLone : (1 : ℝ) ≤ D / L := by rw [le_div_iff₀ hL0]; linarith
  have hdL2 : ∀ j, (d j : ℝ) ≤ 2 * D / L := fun j ↦ by
    have h1 := hdLbound j
    have : D / L + 1 ≤ 2 * D / L := by
      rw [show 2 * D / L = 2 * (D / L) by ring]
      linarith
    linarith
  have hsumd : (∑ j, (d j : ℝ)) ≤ ((mnum : ℝ) + 1) * (2 * D / L) := by
    calc (∑ j : Fin (mnum + 1), (d j : ℝ)) ≤ ∑ _j : Fin (mnum + 1), 2 * D / L :=
          Finset.sum_le_sum fun j _ ↦ hdL2 j
      _ = ((mnum : ℝ) + 1) * (2 * D / L) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hRothH : ∀ j, (tw : ℝ) * C₁ * (∑ i, (d i : ℝ))
      + 4 * ((mnum : ℝ) + 1) * (d 0 : ℝ) * (tw : ℝ)
      ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) := by
    intro j
    have htw0 : (0 : ℝ) ≤ (tw : ℝ) := Nat.cast_nonneg _
    have hm1 : (0 : ℝ) < (mnum : ℝ) + 1 := by positivity
    have h1 : (tw : ℝ) * C₁ * (∑ i, (d i : ℝ))
        ≤ (tw : ℝ) * C₁ * (((mnum : ℝ) + 1) * (2 * D / L)) := by
      refine mul_le_mul_of_nonneg_left hsumd (by positivity)
    have h2 : 4 * ((mnum : ℝ) + 1) * (d 0 : ℝ) * (tw : ℝ)
        ≤ 4 * ((mnum : ℝ) + 1) * (2 * D / L) * (tw : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdL2 0) (by positivity)) (Nat.cast_nonneg _)
    have hLb : 2 * (tw : ℝ) * ((mnum : ℝ) + 1) * (C₁ + 4) ≤ σ * L := by
      rw [div_le_iff₀ hσ0] at hLroth
      linarith
    have hkey2 : (tw : ℝ) * C₁ * (((mnum : ℝ) + 1) * (2 * D / L))
        + 4 * ((mnum : ℝ) + 1) * (2 * D / L) * (tw : ℝ) ≤ σ * D := by
      have hexp : (tw : ℝ) * C₁ * (((mnum : ℝ) + 1) * (2 * D / L))
          + 4 * ((mnum : ℝ) + 1) * (2 * D / L) * (tw : ℝ)
          = (2 * (tw : ℝ) * ((mnum : ℝ) + 1) * (C₁ + 4)) * (D / L) := by
        field_simp
      rw [hexp]
      calc (2 * (tw : ℝ) * ((mnum : ℝ) + 1) * (C₁ + 4)) * (D / L)
          ≤ (σ * L) * (D / L) := by
            refine mul_le_mul_of_nonneg_right hLb (by positivity)
        _ = σ * D := by field_simp
    have h3 : σ * D ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) :=
      mul_le_mul_of_nonneg_left (hdD j) hσ0.le
    linarith
  -- Steps I and II produce the polynomial
  obtain ⟨Q, hQβ, hQdeg, hQindex, hQheight⟩ :=
    hD₀ d (fun j ↦ le_trans (le_max_left D₀ 1) (hdD₀ j)) β hratio hRothH
  -- Steps III to V
  simp only [htgtdef] at hQindex
  have hlocalQ : ∀ (j : Fin (mnum + 1)) (a : ↥Sinf ⊕ ↥Sfin),
      localApprox Sinf Sfin w α a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) :=
    fun j a ↦ hblocal j.val a
  have hkey := roth_key_inequality hwA α (fun j ↦ hd1 j) hQdeg hQβ hQindex hlam0 hκ0.le hD0.le
    hlocalQ hdD hCα1 hCα
  have hWcast : ∑ a : ↥Sinf ⊕ ↥Sfin, ((sPlaceWeight a : ℕ) : ℝ) = (Wsum : ℝ) := by
    rw [hWdef]
    push_cast
    ring
  rw [← htwdef, hWcast] at hkey
  -- the three remaining estimates
  have hm1 : (0 : ℝ) < (mnum : ℝ) + 1 := by positivity
  have hsumlog : (∑ j, Real.log ((d j : ℝ) + 1)) ≤ ((mnum : ℝ) + 1) * Real.log (D + 2) := by
    have hDLle : D / L ≤ D := by
      rw [div_le_iff₀ hL0]
      linarith [mul_le_mul_of_nonneg_left hL1 hD0.le]
    calc (∑ j : Fin (mnum + 1), Real.log ((d j : ℝ) + 1))
        ≤ ∑ _j : Fin (mnum + 1), Real.log (D + 2) := by
          refine Finset.sum_le_sum fun j _ ↦ Real.log_le_log ?_ ?_
          · have : (0 : ℝ) ≤ (d j : ℝ) := Nat.cast_nonneg _
            linarith
          · have := hdLbound j
            linarith
      _ = ((mnum : ℝ) + 1) * Real.log (D + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hsumdh : (∑ j, (d j : ℝ) * logHeight₁ (β j)) ≤ ((mnum : ℝ) + 1) * D + Hβ := by
    have hterm : ∀ j : Fin (mnum + 1),
        (d j : ℝ) * logHeight₁ (β j) ≤ D + logHeight₁ (β j) := fun j ↦ by
      have h := mul_le_mul_of_nonneg_right (hdhigh j).le (hβ0 j).le
      rwa [add_mul, div_mul_cancel₀ D (hβ0 j).ne', one_mul] at h
    calc (∑ j : Fin (mnum + 1), (d j : ℝ) * logHeight₁ (β j))
        ≤ ∑ j : Fin (mnum + 1), (D + logHeight₁ (β j)) := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = ((mnum : ℝ) + 1) * D + Hβ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_fin, hHβdef]
          push_cast
          ring
  have hHβm : Hβ ≤ ((mnum : ℝ) + 1) * Hβ := by
    have h := mul_nonneg (show (0:ℝ) ≤ (mnum : ℝ) from Nat.cast_nonneg _) hHβ0
    linarith
  have hlogsum0 : (0 : ℝ) ≤ Real.log 4 + 2 * Real.log Cα := by linarith
  have hlhs : Θ * (((mnum : ℝ) + 1) * D)
      ≤ κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by
    have hfac : (0 : ℝ) ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) :=
      mul_nonneg hκ0.le (mul_nonneg hε4.le (mul_nonneg hm1.le hD0.le))
    have h := mul_le_mul_of_nonneg_left hlamsum hfac
    calc Θ * (((mnum : ℝ) + 1) * D)
        = κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (1 - (SA : ℝ) / N) := by
          rw [hΘdef]; ring
      _ ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (∑ a, lam a) := h
      _ = κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by ring
  have hcomb : ((mnum : ℝ) + 1) * (Θ * D)
      ≤ ((mnum : ℝ) + 1) * (((tw : ℝ) + 2 * (Wsum : ℝ)) * Real.log (D + 2)
        + G / L * D + D + Hβ) := by
    have he1 : ((mnum : ℝ) + 1) * (Θ * D) = Θ * (((mnum : ℝ) + 1) * D) := by ring
    rw [he1]
    refine le_trans hlhs (le_trans hkey ?_)
    have hb1 : ((tw : ℝ) + 2 * (Wsum : ℝ)) * ∑ j, Real.log ((d j : ℝ) + 1)
        ≤ ((tw : ℝ) + 2 * (Wsum : ℝ)) * (((mnum : ℝ) + 1) * Real.log (D + 2)) :=
      mul_le_mul_of_nonneg_left hsumlog (by positivity)
    have hb2 : (∑ j, (d j : ℝ)) * (Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα)
        ≤ (((mnum : ℝ) + 1) * (2 * D / L)) * (Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsumd (Nat.cast_nonneg _)) hlogsum0
    have hb3 : Real.log Q.mulHeight
        ≤ (tw : ℝ) * (C₁ + Real.log 2) * (((mnum : ℝ) + 1) * (2 * D / L)) :=
      le_trans hQheight (mul_le_mul_of_nonneg_left hsumd
        (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
    rw [hGdef]
    have hLne : L ≠ 0 := hL0.ne'
    have hid : (((mnum : ℝ) + 1) * (2 * D / L)) * (Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα)
        + (tw : ℝ) * (C₁ + Real.log 2) * (((mnum : ℝ) + 1) * (2 * D / L))
        = ((mnum : ℝ) + 1) * (2 * ((Wsum : ℝ) * (Real.log 4 + 2 * Real.log Cα)
            + (tw : ℝ) * (C₁ + Real.log 2)) / L * D) := by
      field_simp
    linarith [hb1, hb2, hb3, hsumdh, hHβm, hid]
  have hdiv : Θ * D ≤ ((tw : ℝ) + 2 * (Wsum : ℝ)) * Real.log (D + 2) + G / L * D + D + Hβ :=
    le_of_mul_le_mul_left hcomb hm1
  have hGL : G / L ≤ (Θ - 1) / 2 := by
    rcases eq_or_lt_of_le hG0 with h | h
    · rw [← h]
      simp only [zero_div]
      linarith
    · rw [div_le_div_iff₀ hL0 two_pos]
      rw [div_le_iff₀ hΘ1] at hLfinal
      linarith
  have hDGL : G / L * D ≤ (Θ - 1) / 2 * D := mul_le_mul_of_nonneg_right hGL hD0.le
  linarith [hDlog]

/-! ### Acceptance criteria -/

/-- **Conformance: the classical shape.** One infinite place and one target — Roth's theorem as it
is usually quoted, before any set of places appears. -/
example (v : InfinitePlace K) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hw : (w v.1).LiesOver v.1) (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult
      ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  have h := finite_setOf_prod_min_one_le {v} (∅ : Finset (FinitePlace K)) w
    (fun u hu ↦ by rwa [Finset.mem_singleton.mp hu])
    (fun u hu ↦ absurd hu (Finset.notMem_empty u)) α hκ
  simpa using h

omit [NumberField F] in
/-- The truncated product is at most `1`, whatever the data. -/
private theorem prod_min_one_le_one (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (α : AbsoluteValue K ℝ → F) (β : K) :
    (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ 1 := by
  have hnn : ∀ u : AbsoluteValue K ℝ, (0 : ℝ) ≤ min 1 (w u (algebraMap K F β - α u)) :=
    fun u ↦ le_min zero_le_one ((w u).nonneg _)
  have hA : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ pow_nonneg (hnn v.1) _)
      fun v _ ↦ pow_le_one₀ (hnn v.1) (min_le_left _ _)
  have hB : (∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ hnn v.1) fun v _ ↦ min_le_left _ _
  have hB0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) :=
    Finset.prod_nonneg fun v _ ↦ hnn v.1
  calc (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ 1 * 1 :=
      mul_le_mul hA hB hB0 zero_le_one
    _ = 1 := one_mul 1

/-- **The theorem bounds a nonempty set, at every `κ`.** With the target `0` at every place, `0`
is a solution: its local factors all vanish and its height is `1`. So the finiteness is not
finiteness of the empty set. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (κ : ℝ) :
    (0 : K) ∈ {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - (fun _ ↦ 0) v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - (fun _ ↦ 0) v.1))
        ≤ mulHeight₁ β ^ (-κ)} := by
  rw [Set.mem_ofPred_eq, mulHeight₁_zero, Real.one_rpow]
  exact prod_min_one_le_one Sinf Sfin w (fun _ ↦ 0) 0

/-- **Rejection test: a positive exponent is not decoration.** At `κ = 0` the right-hand side is
`1` and the truncated product is always at most `1`, so *every* element of `K` is a solution and
the set the theorem bounds is infinite. The hypothesis `2 < κ` is therefore doing work, and it is
the only hypothesis that is. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))
        ≤ mulHeight₁ β ^ (-(0 : ℝ))}.Infinite := by
  have huniv : {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))
        ≤ mulHeight₁ β ^ (-(0 : ℝ))} = Set.univ := by
    refine Set.eq_univ_of_forall fun β ↦ ?_
    rw [Set.mem_ofPred_eq, neg_zero, Real.rpow_zero]
    exact prod_min_one_le_one Sinf Sfin w α β
  rw [huniv]
  exact Set.infinite_univ

end NumberField

end
