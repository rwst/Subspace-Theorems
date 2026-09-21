/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GlobalBound
public import DiophantineApproximation.RothLocalBound

/-!
# Steps III to V of Roth's proof, at a fixed multidegree

This file is the heart of the proof: the upper bound at each place, the product formula, and the
comparison of the two. Given a polynomial `Q` that does not vanish at the point
`β = (β 0, …, β m)`, that has index at least `T` at the target `α v` for every `v ∈ S`, and a
family of exponents `λ` governing the local approximation factors of the `β j`, it produces the
inequality

```text
κ (∑ a, λ a) T D  ≤  ([K : ℚ] + 2 ∑ a, w_a) ∑ j, log (d j + 1)
                      + (∑ j, d j) (∑ a, w_a) (log 4 + 2 log C_α)
                      + log H(Q) + ∑ j, d j h(β j),
```

where `D` is a lower bound for every `d j h(β j)`. Everything on the right is `o(D)` or `O(D / L)`
or `m D` once the parameters are chosen, and the left-hand side is `Θ m D` with `Θ > 1`: that is
the contradiction of Step V.

The three ingredients are `MvPolynomial.exists_apply_eval_le_of_liesOver` at the places of `S`,
`MvPolynomial.apply_eval_le` and its nonarchimedean companion everywhere else, and
`NumberField.one_le_of_forall_apply_le_sum` to multiply them.

## Main definitions

* `NumberField.localApprox`: **the local approximation factor at a place of `S`**,
  `min 1 |β − α_v|_v` raised to the weight of `v`. Its product over the places of `S` is the
  quantity Roth's theorem bounds.

## Main results

* `NumberField.prod_localApprox`: that product, written out over the two typed finsets.
* `NumberField.roth_key_inequality`: **Steps III to V at a fixed multidegree**.

## Implementation notes

⚠ **The `o(D)` of the book is `∑ j, log (d j + 1)` and nothing else.** Every other error term is
`O(D / L)` and is killed by taking `L` large, which happens before `D` is introduced. Keeping the
logarithm explicit avoids any asymptotic machinery: the final contradiction is an inequality
between a linear function of `D` and a logarithm, and `Real.exists_le_and_mul_log_add_lt` settles
it at one explicit `D`.

⚠ **The surviving order `ν a` depends on the place.** The bound
`∏ j, min 1 (|β j − α_a|_a) ^ ν a j ≤ H(β j)^{−κ λ a …}` is uniform over the admissible orders
only *after* the approximation class is used, because the constraint on `ν a` is a lower bound on
`∑ j, ν a j / d j` and the heights enter through `d j h(β j) ≥ D`. That is why the orders are
chosen first and estimated afterwards.

⚠ **The weights are what make (6.10) usable.** `∑ a, c a ≥ N (1 − |S| / N)` is an *unweighted*
sum, and the product over the places of `S` is weighted; since every weight is at least `1` the
weighted sum is larger, and no separate estimate is needed.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.4.8 to §6.4.10.

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height MvPolynomial

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- **The local approximation factor at a place of `S`**, in Mathlib's relative normalisation:
`min 1 |β - α_v|_v` raised to the weight of `v`. Its product over the places of `S` is the
quantity Roth's theorem bounds. -/
noncomputable def localApprox (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
    (a : ↥Sinf ⊕ ↥Sfin) (β : K) : ℝ :=
  min 1 (w (sPlaceAbsValue a) (algebraMap K F β - α (sPlaceAbsValue a))) ^ sPlaceWeight a

theorem localApprox_nonneg (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
    (a : ↥Sinf ⊕ ↥Sfin) (β : K) : 0 ≤ localApprox Sinf Sfin w α a β :=
  pow_nonneg (le_min zero_le_one ((w _).nonneg _)) _

theorem localApprox_le_one (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
    (a : ↥Sinf ⊕ ↥Sfin) (β : K) : localApprox Sinf Sfin w α a β ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one ((w _).nonneg _)) (min_le_left _ _)

/-- **The product of the local approximation factors** is the quantity the hypothesis of Roth's
theorem bounds, written out over the two typed finsets. -/
theorem prod_localApprox (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F) (β : K) :
    ∏ a, localApprox Sinf Sfin w α a β
      = (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult)
        * ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) := by
  rw [Fintype.prod_sum_type]
  congr 1
  · rw [← Finset.prod_coe_sort Sinf fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult]
    rfl
  · rw [← Finset.prod_coe_sort Sfin fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1))]
    exact Finset.prod_congr rfl fun v _ ↦ pow_one _

/-- **Steps III to V of Roth's proof, at a fixed multidegree.** -/
theorem roth_key_inequality
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hw : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a))
    (α : AbsoluteValue K ℝ → F)
    {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ j, 0 < d j)
    {Q : MvPolynomial ι K} (hQdeg : ∀ j, Q.degreeOf j ≤ d j)
    {β : ι → K} (hQβ : eval β Q ≠ 0)
    {T : ℝ}
    (hindex : ∀ a : ↥Sinf ⊕ ↥Sfin, ENNReal.ofReal T
      ≤ index (fun j ↦ (d j : ℝ)) (fun _ ↦ α (sPlaceAbsValue a)) (Q.map (algebraMap K F)))
    {lam : (↥Sinf ⊕ ↥Sfin) → ℝ} (hlam0 : ∀ a, 0 ≤ lam a)
    {κ D : ℝ} (hκ0 : 0 ≤ κ) (hD0 : 0 ≤ D)
    (hlocal : ∀ j a, localApprox Sinf Sfin w α a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a))
    (hDd : ∀ j, D ≤ (d j : ℝ) * logHeight₁ (β j))
    {Cα : ℝ} (hCα1 : 1 ≤ Cα)
    (hCα : ∀ a : ↥Sinf ⊕ ↥Sfin, w (sPlaceAbsValue a) (α (sPlaceAbsValue a)) ≤ Cα) :
    κ * (∑ a, lam a) * T * D
      ≤ ((totalWeight K : ℝ) + 2 * ∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ))
            * ∑ j, Real.log ((d j : ℝ) + 1)
        + (∑ j, (d j : ℝ)) * (∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ))
            * (Real.log 4 + 2 * Real.log Cα)
        + Real.log Q.mulHeight + ∑ j, (d j : ℝ) * logHeight₁ (β j) := by
  classical
  set n : ℕ := ∑ j, d j with hndef
  set Wsum : ℕ := ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a with hWdef
  set Mbox : ℝ := ∏ j, ((d j : ℝ) + 1) with hMboxdef
  have hMbox1 : (1 : ℝ) ≤ Mbox := by
    rw [hMboxdef]
    calc (1 : ℝ) = ∏ _j : ι, (1 : ℝ) := by simp
      _ ≤ ∏ j, ((d j : ℝ) + 1) :=
        Finset.prod_le_prod₀ (fun j _ ↦ zero_le_one)
          (fun j _ ↦ le_add_of_nonneg_left (Nat.cast_nonneg (d j)))
  have hMbox0 : (0 : ℝ) < Mbox := lt_of_lt_of_le zero_lt_one hMbox1
  have hCα0 : (0 : ℝ) < Cα := lt_of_lt_of_le zero_lt_one hCα1
  have hQ0 : Q ≠ 0 := fun h ↦ hQβ (by rw [h, map_zero])
  -- the coefficient vector on the box
  have hxbox0 : (fun I ↦ Q.coeff (boxMonomial d I)) ≠ (0 : (∀ j, Fin (d j + 1)) → K) := by
    obtain ⟨μ, hμ⟩ := support_nonempty.mpr hQ0
    obtain ⟨I, rfl⟩ := mem_range_boxMonomial_of_mem_support hQdeg hμ
    exact fun h ↦ (mem_support_iff.mp hμ) (congrFun h I)
  have hiSup : ∀ v : AbsoluteValue K ℝ,
      (⨆ I : (∀ j, Fin (d j + 1)), v (Q.coeff (boxMonomial d I))) = ⨆ μ, v (Q.coeff μ) :=
    fun v ↦ iSup_coeff_boxMonomial v hQdeg
  have hming : ∀ (a : ↥Sinf ⊕ ↥Sfin) (j : ι),
      0 ≤ min 1 (w (sPlaceAbsValue a) (algebraMap K F (β j) - α (sPlaceAbsValue a))) :=
    fun a j ↦ le_min zero_le_one ((w _).nonneg _)
  -- the surviving Hasse derivative at each place of `S`
  have hex : ∀ a : ↥Sinf ⊕ ↥Sfin, ∃ μ : ι →₀ ℕ,
      (T ≤ μ.sum fun j k ↦ (k : ℝ) / d j) ∧
      sPlaceAbsValue a (eval β Q)
        ≤ Mbox * (⨆ I : (∀ j, Fin (d j + 1)), sPlaceAbsValue a (Q.coeff (boxMonomial d I)))
          * (∏ j, max (sPlaceAbsValue a (β j)) 1 ^ d j)
          * (Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
            * ∏ j, min 1 (w (sPlaceAbsValue a)
                (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ μ j) := by
    intro a
    obtain ⟨μ, _, hμne, hμb⟩ :=
      exists_apply_eval_le_of_liesOver (hw a) hQdeg (α (sPlaceAbsValue a)) hQβ
    refine ⟨μ, ?_, ?_⟩
    · have h1 : index (fun j ↦ (d j : ℝ)) (fun _ ↦ α (sPlaceAbsValue a))
          (Q.map (algebraMap K F)) ≤ ENNReal.ofReal (μ.sum fun j k ↦ (k : ℝ) / d j) :=
        index_le _ hμne
      have hnn : (0 : ℝ) ≤ μ.sum fun j k ↦ (k : ℝ) / d j :=
        Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (le_trans (hindex a) h1)
    · rw [hiSup, hndef, hMboxdef]
      exact hμb
  choose ν hνT hνbound using hex
  -- the global inequality
  have hg0 : ∀ a : ↥Sinf ⊕ ↥Sfin,
      0 ≤ Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j := fun a ↦
    mul_nonneg (mul_nonneg (mul_nonneg hMbox0.le (by positivity))
        (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))
      (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hming a j) _)
  have hglob := one_le_of_forall_apply_le_sum hQβ hxbox0 β d hMbox1 hg0
    (fun v : InfinitePlace K ↦ by
      have h := apply_eval_le v.1 hQdeg β
      rw [← hiSup v.1] at h
      simpa only [InfinitePlace.coe_apply] using h)
    (fun v : FinitePlace K ↦ by
      have h := apply_eval_le_of_isNonarchimedean (v := v.1) (FinitePlace.add_le v) hQdeg β
      rw [← hiSup v.1] at h
      simpa only [FinitePlace.coe_apply] using h)
    hνbound
  rw [← mulHeight_eq_mulHeight_coeff_box Q hQdeg] at hglob
  -- collecting the constants place by place
  have hstep : ∀ a : ↥Sinf ⊕ ↥Sfin,
      (Mbox * (Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a
      ≤ (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ sPlaceWeight a
        * ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j := by
    intro a
    have hmax : max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ≤ Cα :=
      max_le (hCα a) hCα1
    have heq : Mbox * (Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j)
        = (Mbox ^ 2 * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n))
          * ∏ j, min 1 (w (sPlaceAbsValue a)
              (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j := by ring
    have hlast : (∏ j, min 1 (w (sPlaceAbsValue a)
          (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j) ^ sPlaceWeight a
        = ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun j _ ↦ by
        rw [localApprox, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [heq, mul_pow, hlast]
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun j _ ↦ pow_nonneg (localApprox_nonneg _ _ _ _ _ _) _)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) hmax _) (by positivity)
  -- the approximation class makes the surviving product exponentially small
  have hTD : ∀ a : ↥Sinf ⊕ ↥Sfin, T * D ≤ ∑ j, (ν a j : ℝ) * logHeight₁ (β j) := by
    intro a
    have hsum : ((ν a).sum fun j k ↦ (k : ℝ) / d j) = ∑ j, (ν a j : ℝ) / d j :=
      Finsupp.sum_fintype _ _ fun j ↦ by simp
    have h1 : ∀ j, ((ν a j : ℝ) / d j) * D ≤ (ν a j : ℝ) * logHeight₁ (β j) := by
      intro j
      have hd0 : (0 : ℝ) < d j := by exact_mod_cast hd j
      have hq : (0 : ℝ) ≤ (ν a j : ℝ) / d j := div_nonneg (Nat.cast_nonneg _) hd0.le
      calc ((ν a j : ℝ) / d j) * D ≤ ((ν a j : ℝ) / d j) * ((d j : ℝ) * logHeight₁ (β j)) :=
            mul_le_mul_of_nonneg_left (hDd j) hq
        _ = (ν a j : ℝ) * logHeight₁ (β j) := by field_simp
    calc T * D ≤ (∑ j, (ν a j : ℝ) / d j) * D := by
          refine mul_le_mul_of_nonneg_right ?_ hD0
          rw [← hsum]
          exact hνT a
      _ = ∑ j, ((ν a j : ℝ) / d j) * D := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (ν a j : ℝ) * logHeight₁ (β j) := Finset.sum_le_sum fun j _ ↦ h1 j
  have hsmall : ∀ a : ↥Sinf ⊕ ↥Sfin, (∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j)
      ≤ Real.exp (-(κ * lam a * (T * D))) := by
    intro a
    have hc : (0 : ℝ) ≤ κ * lam a := mul_nonneg hκ0 (hlam0 a)
    have hterm : ∀ j, localApprox Sinf Sfin w α a (β j) ^ ν a j
        ≤ Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) := by
      intro j
      have hH : (0 : ℝ) < mulHeight₁ (β j) := mulHeight₁_pos _
      calc localApprox Sinf Sfin w α a (β j) ^ ν a j
          ≤ (mulHeight₁ (β j) ^ (-κ * lam a)) ^ ν a j :=
            pow_le_pow_left₀ (localApprox_nonneg _ _ _ _ _ _) (hlocal j a) _
        _ = Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) := by
            rw [← Real.rpow_natCast (mulHeight₁ (β j) ^ (-κ * lam a)) (ν a j),
              ← Real.rpow_mul hH.le, Real.rpow_def_of_pos hH, logHeight₁_eq_log_mulHeight₁]
            ring_nf
    calc (∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j)
        ≤ ∏ j, Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) :=
          Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (localApprox_nonneg _ _ _ _ _ _) _)
            fun j _ ↦ hterm j
      _ = Real.exp (∑ j, -(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (-(κ * lam a * (T * D))) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← Finset.mul_sum, neg_mul]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (hTD a) hc)
  have hsmallprod : (∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j)
      ≤ Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
    calc (∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j)
        ≤ ∏ a : ↥Sinf ⊕ ↥Sfin, Real.exp (-(κ * lam a * (T * D))) :=
          Finset.prod_le_prod₀ (fun a _ ↦ Finset.prod_nonneg fun j _ ↦
            pow_nonneg (localApprox_nonneg _ _ _ _ _ _) _) fun a _ ↦ hsmall a
      _ = Real.exp (∑ a : ↥Sinf ⊕ ↥Sfin, -(κ * lam a * (T * D))) := (Real.exp_sum _ _).symm
      _ = Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
          congr 1
          have hrw : ∀ a : ↥Sinf ⊕ ↥Sfin, -(κ * lam a * (T * D)) = lam a * (-(κ * (T * D))) :=
            fun a ↦ by ring
          simp only [hrw, ← Finset.sum_mul]
          ring
  -- the constants, collected
  have hbase0 : (0 : ℝ) < Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n) :=
    mul_pos (mul_pos (pow_pos hMbox0 2) (by positivity)) (pow_pos hCα0 _)
  have hprodS : (∏ a : ↥Sinf ⊕ ↥Sfin,
      (Mbox * (Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a)
      ≤ (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum
        * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
    calc (∏ a : ↥Sinf ⊕ ↥Sfin,
        (Mbox * (Mbox * 4 ^ n * max (w (sPlaceAbsValue a) (α (sPlaceAbsValue a))) 1 ^ (2 * n)
          * ∏ j, min 1 (w (sPlaceAbsValue a)
              (algebraMap K F (β j) - α (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a)
        ≤ ∏ a : ↥Sinf ⊕ ↥Sfin, ((Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ sPlaceWeight a
            * ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j) :=
          Finset.prod_le_prod₀ (fun a _ ↦ pow_nonneg (mul_nonneg hMbox0.le (hg0 a)) _)
            fun a _ ↦ hstep a
      _ = (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum
            * ∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w α a (β j) ^ ν a j := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hWdef]
      _ ≤ (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum
            * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) :=
          mul_le_mul_of_nonneg_left hsmallprod (pow_nonneg hbase0.le _)
  -- the multiplicative form of the final inequality
  have hQh0 : (0 : ℝ) < Q.mulHeight := MvPolynomial.mulHeight_pos Q
  have hprodH0 : (0 : ℝ) < ∏ j, mulHeight₁ (β j) ^ d j :=
    Finset.prod_pos fun j _ ↦ pow_pos (mulHeight₁_pos _) _
  have hA0 : (0 : ℝ) < Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j) :=
    mul_pos (mul_pos (pow_pos hMbox0 _) hQh0) hprodH0
  have hB0 : (0 : ℝ) < (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum := pow_pos hbase0 _
  have hfinal : 1 ≤ (Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j))
      * ((Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum
        * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))) :=
    le_trans hglob (mul_le_mul_of_nonneg_left hprodS hA0.le)
  have hexp : Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)
      ≤ Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
        * (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum := by
    calc Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)
        = 1 * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D) := (one_mul _).symm
      _ ≤ ((Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j))
            * ((Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum
              * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))))
            * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D) :=
          mul_le_mul_of_nonneg_right hfinal (Real.exp_pos _).le
      _ = (Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
            * (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum)
            * (Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))
              * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by ring
      _ = Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
            * (Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  -- take logarithms
  have hM0 : Mbox ≠ 0 := hMbox0.ne'
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have e1 : Real.log (Mbox ^ totalWeight K) = (totalWeight K : ℝ) * Real.log Mbox :=
    Real.log_pow _ _
  have e2 : Real.log (∏ j, mulHeight₁ (β j) ^ d j) = ∑ j, (d j : ℝ) * logHeight₁ (β j) := by
    rw [Real.log_prod fun j _ ↦ pow_ne_zero (d j) (mulHeight₁_pos (β j)).ne']
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [Real.log_pow, logHeight₁_eq_log_mulHeight₁]
  have e3 : Real.log ((Mbox ^ 2 * 4 ^ n * Cα ^ (2 * n)) ^ Wsum)
      = (Wsum : ℝ) * (2 * Real.log Mbox + (n : ℝ) * Real.log 4 + 2 * (n : ℝ) * Real.log Cα) := by
    rw [Real.log_pow, Real.log_mul (mul_pos (pow_pos hMbox0 2) (by positivity)).ne'
        (pow_ne_zero _ hCα0.ne'),
      Real.log_mul (pow_ne_zero _ hM0) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [Real.log_mul hA0.ne' hB0.ne',
    Real.log_mul (mul_pos (pow_pos hMbox0 _) hQh0).ne' hprodH0.ne',
    Real.log_mul (pow_ne_zero _ hM0) hQh0.ne', e1, e2, e3] at hlog
  have hlogMbox : Real.log Mbox = ∑ j, Real.log ((d j : ℝ) + 1) := by
    rw [hMboxdef, Real.log_prod fun j _ ↦ by positivity]
  have hncast : (n : ℝ) = ∑ j, (d j : ℝ) := by rw [hndef]; push_cast; ring
  have hWcast : (Wsum : ℝ) = ∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ) := by
    rw [hWdef]; push_cast; ring
  rw [hlogMbox, hncast, hWcast] at hlog
  linarith [hlog]

end NumberField

end
