/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BoxMonomial
public import DiophantineApproximation.MvHasseDerivHeight

/-!
# The height of a row of the index conditions

A condition "`∂_μ P` vanishes at `α`" is a linear form in the coefficients of `P`, and Siegel's
lemma charges for it through the height of that form. This file computes the charge. The entry
of the row at the monomial `X ^ I` is

`(∏ j, (I j).choose (μ j)) * ∏ j, α j ^ (I j - μ j)`,

a **multiplication table** over the variables, so `Height.mulHeight_fun_prod_eq` turns its height
into a product of one-variable heights, and each of those splits — by
`Height.mulHeight_mul_le` — into a binomial part and a monomial part. The binomial part is a
tuple of natural numbers at most `2 ^ d j`, the monomial part is the tuple of powers
`α j ^ k, k ≤ d j`, whose height is exactly `H(α j) ^ d j`. The answer is Bombieri–Gubler's
`∏ j, (2 H(α j)) ^ d j`.

## Main results

* `Height.mulHeight_le_pow_totalWeight`: **the transport**, from a bound on the local factors to
  a bound on the height, for a single tuple.
* `Height.mulHeight_natCast_le`: the height of a tuple of natural numbers at most `N` is at most
  `N ^ totalWeight K`.
* `Height.mulHeight_pow_range`: the height of the tuple of powers `α ^ k`, `k ≤ d`, is
  `H(α) ^ d` — *exactly*, and with no hypothesis on `α`.
* `MvPolynomial.hasseDerivRow`: the row, and `MvPolynomial.hasseDerivRow_eq_prod`, which is the
  observation that it is a multiplication table.
* `MvPolynomial.mulHeight_hasseDerivRow_le`: **the estimate**,
  `H(row) ≤ (2 ^ ∑ j, d j) ^ totalWeight K * ∏ j, H(α j) ^ d j`.

## Implementation notes

⚠ **The transport lemma the roadmap records as missing is the one-input, one-sided one, and it
is three lines.** `ArithmeticHeights/GaussLemma.lean` has
`Finsupp.mulHeight_le_of_forall_iSup_le`, which compares the local factor of one object with the
*product* of those of two others and demands **equality** at the nonarchimedean absolute values —
what Gauss's lemma supplies and what a row of binomial coefficients does not. What is needed here
is the inequality at both kinds of place with a single tuple on each side, and it follows from
`Multiset.prod_map_le_prod_map₀` at the archimedean places and `finprod_le_finprod₀` at the
others. Only the constant form (the second tuple being `1`) is stated, because that is the only
form used: the rest of the estimate is carried by the Segre relation, which is an equality.

⚠ **The whole estimate is one equality and two comparisons, and none of them is an induction on
the number of variables.** `Height.mulHeight_fun_prod_eq` is Mathlib's Segre relation for an
arbitrary finite family, so the passage from `m` variables to one is free; and
`Height.mulHeight_pow_range` is an equality rather than an estimate, so the only loss in the
whole file is the binomial factor `2 ^ ∑ j, d j` — which is exactly the `log 2` that Lemma 6.3.4
carries in its bound.

⚠ **`Height.mulHeight_pow_range` compares the tuple of powers with the pair `![α ^ d, 1]`.** The
supremum of `v (α ^ k)` over `k ≤ d` is `max (v α) 1 ^ d` whichever side of `1` the value `v α`
falls on, and that is the local factor of the pair; so the two tuples have the same height at
every absolute value at once, and `Height.mulHeight_eq_of_forall_iSup_eq` turns that into an
equality of heights. Computing the product over the places directly would need the product
formula and would not be shorter.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.4.

This is part of Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Height.AdmissibleAbsValues Real

noncomputable section

namespace Height

/-! ### Transport from local factors to the height -/

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*} [Finite ι] [Finite ι']

omit [Finite ι] [Finite ι'] in
/-- **Two tuples with the same local factors have the same height.** -/
theorem mulHeight_eq_of_forall_iSup_eq {x : ι → K} {y : ι' → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ v : AbsoluteValue K ℝ, (⨆ i, v (x i)) = ⨆ i, v (y i)) :
    mulHeight x = mulHeight y := by
  rw [mulHeight_eq hx, mulHeight_eq hy]
  congr 1
  · exact congrArg _ (Multiset.map_congr rfl fun v _ ↦ h v)
  · exact finprod_congr fun v ↦ h v.val

omit [Finite ι] [Finite ι'] in
/-- **The transport, in the form Layer 2.6 uses it**: a tuple whose local factor is at most `C`
at every archimedean absolute value and at most `1` at every nonarchimedean one has height at
most `C ^ totalWeight K`. -/
theorem mulHeight_le_pow_totalWeight {x : ι → K} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ i, v (x i)) ≤ C)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), (⨆ i, v (x i)) ≤ 1) :
    mulHeight x ≤ C ^ totalWeight K := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_pow₀ hC
  rw [mulHeight_eq hx]
  have h1 : (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod ≤ C ^ totalWeight K := by
    calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
        ≤ (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod :=
          Multiset.prod_map_le_prod_map₀ _ _
            (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) fun v hv ↦ harch v hv
      _ = C ^ totalWeight K := by rw [Multiset.map_const', Multiset.prod_replicate]; rfl
  have h2 : ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i) ≤ 1 :=
    (finprod_induction (f := fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i))
      (fun y ↦ 0 ≤ y ∧ y ≤ 1) ⟨zero_le_one, le_rfl⟩
      (fun y z hy hz ↦ ⟨mul_nonneg hy.1 hz.1, by nlinarith [hy.1, hy.2, hz.1, hz.2]⟩)
      fun v ↦ ⟨Real.iSup_nonneg fun _ ↦ v.val.nonneg _, hnon v.val v.prop⟩).2
  have hnn : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
          * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i)
      ≤ C ^ totalWeight K * 1 := mul_le_mul h1 h2 hnn (by positivity)
    _ = C ^ totalWeight K := mul_one _

/-! ### Two tuples whose height is known -/

omit [Finite ι] [Finite ι'] in
/-- **The height of a tuple of natural numbers** is at most `N ^ totalWeight K`, `N` a bound on
the entries: a rational integer has absolute value at most itself at an archimedean absolute
value and at most `1` at a nonarchimedean one. -/
theorem mulHeight_natCast_le {n : ι → ℕ} {N : ℕ} (hN : 1 ≤ N) (hn : ∀ i, n i ≤ N) :
    mulHeight (fun i ↦ (n i : K)) ≤ (N : ℝ) ^ totalWeight K := by
  refine mulHeight_le_pow_totalWeight (by exact_mod_cast hN) (fun v _ ↦ ?_) fun v hv ↦ ?_
  · exact Real.iSup_le
      (fun i ↦ (v.apply_natCast_le (n i)).trans (by exact_mod_cast hn i)) (by positivity)
  · exact Real.iSup_le
      (fun i ↦ (isNonarchimedean v hv).apply_natCast_le_one (by simp) (by simp)) zero_le_one

/-- **The height of the tuple of powers `α ^ k`, `k ≤ d`, is `H(α) ^ d`.** -/
theorem mulHeight_pow_range (α : K) (d : ℕ) :
    mulHeight (fun k : Fin (d + 1) ↦ α ^ (k : ℕ)) = mulHeight₁ α ^ d := by
  have hx : (fun k : Fin (d + 1) ↦ α ^ (k : ℕ)) ≠ 0 := Function.ne_iff.mpr ⟨0, by simp⟩
  have hy : (![α ^ d, 1] : Fin 2 → K) ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
  have key : ∀ v : AbsoluteValue K ℝ,
      (⨆ k : Fin (d + 1), v (α ^ (k : ℕ))) = ⨆ i : Fin 2, v (![α ^ d, 1] i) := by
    intro v
    have hr : (⨆ i : Fin 2, v (![α ^ d, 1] i)) = max (v α ^ d) 1 := by
      refine le_antisymm (ciSup_le fun i ↦ ?_) (max_le ?_ ?_)
      · fin_cases i <;> simp [map_pow]
      · exact Finite.le_ciSup_of_le 0 (by simp [map_pow])
      · exact Finite.le_ciSup_of_le 1 (by simp)
    rw [hr]
    refine le_antisymm (Real.iSup_le (fun k ↦ ?_) (by positivity)) (max_le ?_ ?_)
    · rw [map_pow]
      rcases le_total (v α) 1 with h | h
      · exact le_trans (pow_le_one₀ (v.nonneg _) h) (le_max_right _ _)
      · exact le_trans (pow_le_pow_right₀ h (by omega)) (le_max_left _ _)
    · exact Finite.le_ciSup_of_le (Fin.last d) (by simp [map_pow])
    · exact Finite.le_ciSup_of_le 0 (by simp)
  rw [mulHeight_eq_of_forall_iSup_eq hx hy key, ← mulHeight₁_pow, mulHeight₁_eq_mulHeight,
    mulHeight_swap]

end Height

/-! ### The row of a condition, and its height -/

namespace MvPolynomial

open Height

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] [Height.AdmissibleAbsValues F]

/-- **The height of a condition row** (Bombieri–Gubler, Lemma 6.3.4): a row of the conditions on
the box `∏ j, {0, …, d j}` at the point `α` has height at most
`(2 ^ ∑ j, d j) ^ totalWeight F * ∏ j, H(α j) ^ d j`. -/
theorem mulHeight_hasseDerivRow_le {d : σ → ℕ} (α : σ → F) {μ : σ →₀ ℕ} (hmu : ∀ j, μ j ≤ d j) :
    Height.mulHeight (hasseDerivRow d α μ)
      ≤ ((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F
        * ∏ j, Height.mulHeight₁ (α j) ^ d j := by
  have hx : ∀ j : σ,
      (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j)) ≠ 0 := by
    intro j
    have h := hmu j
    exact Function.ne_iff.mpr ⟨⟨μ j, by omega⟩, by simp⟩
  have hfac : ∀ j : σ,
      Height.mulHeight (fun k : Fin (d j + 1) ↦
          (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
        ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j := by
    intro j
    have hmuj := hmu j
    have hsplit :
        (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
          = (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F))
            * (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j)) := rfl
    have hc : Height.mulHeight (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F))
        ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F := by
      have := Height.mulHeight_natCast_le (K := F)
        (n := fun k : Fin (d j + 1) ↦ (k : ℕ).choose (μ j)) (N := 2 ^ d j) Nat.one_le_two_pow
        fun k ↦ (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      simpa using this
    have hg : Height.mulHeight (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j))
        ≤ Height.mulHeight₁ (α j) ^ d j := by
      rw [← Height.mulHeight_pow_range (α j) (d j),
        show (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j))
            = (fun k : Fin (d j + 1) ↦ α j ^ (k : ℕ))
              ∘ fun k : Fin (d j + 1) ↦ (⟨(k : ℕ) - μ j, by omega⟩ : Fin (d j + 1)) from rfl]
      exact Height.mulHeight_comp_le _ _
    calc Height.mulHeight (fun k : Fin (d j + 1) ↦
            (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
        ≤ Height.mulHeight (fun k : Fin (d j + 1) ↦ (((k : ℕ).choose (μ j) : ℕ) : F))
            * Height.mulHeight (fun k : Fin (d j + 1) ↦ α j ^ ((k : ℕ) - μ j)) := by
          rw [hsplit]; exact Height.mulHeight_mul_le _ _
      _ ≤ ((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j := by gcongr
  rw [funext (hasseDerivRow_eq_prod d α μ), Height.mulHeight_fun_prod_eq hx]
  calc ∏ j, Height.mulHeight (fun k : Fin (d j + 1) ↦
          (((k : ℕ).choose (μ j) : ℕ) : F) * α j ^ ((k : ℕ) - μ j))
      ≤ ∏ j, (((2 : ℝ) ^ d j) ^ Height.totalWeight F * Height.mulHeight₁ (α j) ^ d j) :=
        Finset.prod_le_prod₀ (fun j _ ↦ (Height.mulHeight_pos _).le) fun j _ ↦ hfac j
    _ = ((2 : ℝ) ^ (∑ j, d j)) ^ Height.totalWeight F * ∏ j, Height.mulHeight₁ (α j) ^ d j := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow_eq_pow_sum]

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the tuple of powers `α ^ k`, `k ≤ d`, has height exactly `H(α) ^ d`.** -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] (α : K) :
    Height.mulHeight (fun k : Fin 4 ↦ α ^ (k : ℕ)) = Height.mulHeight₁ α ^ 3 :=
  Height.mulHeight_pow_range α 3

/-- **Acceptance test: the transport at `C = 1`.** A tuple whose local factor is at most `1` at
every absolute value has height exactly `1`, since the height is always at least `1`. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι] {x : ι → K}
    (h : ∀ v : AbsoluteValue K ℝ, (⨆ i, v (x i)) ≤ 1) : Height.mulHeight x = 1 :=
  le_antisymm
    (by simpa using
      Height.mulHeight_le_pow_totalWeight le_rfl (fun v _ ↦ h v) fun v _ ↦ h v)
    (Height.one_le_mulHeight x)

end Acceptance

end MvPolynomial

end
