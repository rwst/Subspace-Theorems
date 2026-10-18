/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RepetitionSubspaces

-- Used only inside proofs.
import DiophantineApproximation.LinearFormSubspaces
import DiophantineApproximation.RationalPlaces

/-!
# The Subspace Theorem at `∞`, `2` and `3`

The paper uses the `p`-adic Subspace Theorem (Theorem 4.1) only with `S = {2, 3}`, with the
coordinate forms at `2` and `3`, and with forms at `∞` that have rational coefficients. This file
states that case, as the specialization of DA's
`Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le` (Layer 7.4) to the field `ℚ`: the
solutions `x ∈ ℤⁿ \ {0}` of

```text
∏ᵢ |∑ⱼ cᵢⱼ xⱼ| · ∏ᵢ |xᵢ|₂ · ∏ᵢ |xᵢ|₃ ≤ ‖x‖^(-ε)
```

lie in finitely many proper subspaces of `ℚⁿ`. With the coordinate forms at `2` and `3`, a
coordinate of the form `± 2^i 3^j` contributes nothing to the double product as long as the
coordinate form `Xᵢ` is also one of the forms at `∞` (the accounting principle, equation (1) of
the paper); the product can only be small because of the remaining forms at `∞`.

Both applications bound the double product by `K θ^n` and the size `‖x‖` by `B 3^n`, at a point
indexed by `n`. `SteeringWord.exists_forall_mul_pow_le_rpow_neg` supplies the `ε` that turns this
into the hypothesis of the theorem: `ε = log (1/θ) / (2 log 3)` makes `3^(-ε) = θ^(1/2) > θ`.

## Main results

* `SteeringWord.exists_finset_submodule_of_prod_le`: **Theorem 4.1** with `S = {2, 3}`.
* `SteeringWord.exists_forall_mul_pow_le_rpow_neg`: the choice of `ε`.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §4.1;
W. M. Schmidt, *Diophantine approximation*, LNM 785, Springer (1980); E. Bombieri and W. Gubler,
*Heights in Diophantine Geometry*, Cambridge University Press (2006), Chapter 7.
-/

public section

open Module NumberField

namespace SteeringWord

/-- The prime `2`, as an element of `Nat.Primes`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `3`, as an element of `Nat.Primes`. -/
def three : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- **Theorem 4.1, at `∞`, `2` and `3`.** For a linearly independent system of forms
`x ↦ ∑ⱼ cᵢⱼ xⱼ` with rational coefficients at `∞`, the coordinate forms at `2` and `3`, and
`ε > 0`, the nonzero integer points with
`∏ᵢ |∑ⱼ cᵢⱼ xⱼ| · ∏ᵢ |xᵢ|₂ · ∏ᵢ |xᵢ|₃ ≤ ‖x‖^(-ε)` lie in finitely many proper subspaces of `ℚⁿ`.
Ineffective: neither the subspaces nor the solutions are bounded. -/
theorem exists_finset_submodule_of_prod_le {ι : Type*} [Fintype ι] [Nontrivial ι]
    (c : ι → ι → ℚ) (hc : LinearIndependent ℚ c) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, |∑ j, (c i j : ℝ) * x j|) * ((∏ i, ((padicNorm 2 (x i) : ℚ) : ℝ))
            * ∏ i, ((padicNorm 3 (x i) : ℚ) : ℝ))
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hW : (Rat.infinitePlace.1 : AbsoluteValue ℚ ℝ).LiesOver Rat.infinitePlace.1 :=
    ⟨AbsoluteValue.ext fun q ↦ rfl⟩
  obtain ⟨T, hT, hmem⟩ := Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le
    Rat.infinitePlace.1 hW (fun i ↦ Dual.sumForm (c i)) (Dual.linearIndependent_sumForm hc)
    {two, three} hε
  refine ⟨T, hT, fun x hx hle ↦ hmem x hx (le_trans (le_of_eq ?_) hle)⟩
  have h23 : two ≠ three := by decide
  rw [Finset.prod_pair h23]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← InfinitePlace.coe_apply, Rat.infinitePlace_apply]
  simp [Dual.sumForm_apply]

/-- **The choice of `ε`.** For `θ ∈ (0, 1)`, `K` and `B > 0` there are `ε > 0` and `n₀` with
`K θ^n ≤ s^(-ε)` whenever `n ≥ n₀` and `0 < s ≤ B 3^n`. With `ε = log (1/θ) / (2 log 3)` one has
`3^(-ε) = θ^(1/2) > θ`, so `(B 3^n)^(-ε) = B^(-ε) θ^(n/2)` beats `K θ^n` for large `n`. -/
theorem exists_forall_mul_pow_le_rpow_neg {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (K : ℝ)
    {B : ℝ} (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s : ℝ, 0 < s → s ≤ B * 3 ^ n →
      K * θ ^ n ≤ s ^ (-ε) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  set ε : ℝ := -Real.log θ / (2 * Real.log 3) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  set ρ : ℝ := (3 : ℝ) ^ (-ε) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ : ρ = Real.exp (Real.log θ / 2) := by
    rw [hρdef, Real.rpow_def_of_pos (by norm_num), hεdef]
    congr 1
    field_simp
  have hθρ : θ < ρ := by
    rw [hρ, ← Real.exp_log hθ0, Real.log_exp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hq0 : 0 < θ / ρ := div_pos hθ0 hρ0
  have hq1 : θ / ρ < 1 := (div_lt_one hρ0).mpr hθρ
  have hBε : 0 < B ^ (-ε) := Real.rpow_pos_of_pos hB _
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (div_pos hBε (by positivity : (0 : ℝ) < |K| + 1))
    hq1
  refine ⟨ε, hε, n₀, fun n hn s hs hsB ↦ ?_⟩
  have hpow : (θ / ρ) ^ n ≤ (θ / ρ) ^ n₀ := pow_le_pow_of_le_one hq0.le hq1.le hn
  have hsplit : (B * 3 ^ n) ^ (-ε) = B ^ (-ε) * ρ ^ n := by
    rw [Real.mul_rpow hB.le (by positivity), hρdef, ← Real.rpow_mul_natCast (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ), mul_comm]
  have hθn : θ ^ n = (θ / ρ) ^ n * ρ ^ n := by
    rw [div_pow, div_mul_cancel₀ _ (pow_pos hρ0 n).ne']
  calc K * θ ^ n ≤ (|K| + 1) * θ ^ n :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
    _ = (|K| + 1) * (θ / ρ) ^ n * ρ ^ n := by rw [hθn]; ring
    _ ≤ B ^ (-ε) * ρ ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := (lt_div_iff₀' (by positivity : (0 : ℝ) < |K| + 1)).mp (hpow.trans_lt hn₀)
        exact h.le
    _ = (B * 3 ^ n) ^ (-ε) := hsplit.symm
    _ ≤ s ^ (-ε) := Real.rpow_le_rpow_of_nonpos hs hsB (by linarith)

/-- **A proper subspace lies in a hyperplane**: for `V ≠ ⊤` in `ℚⁿ` there is a nonzero `w` with
`∑ᵢ wᵢ xᵢ = 0` on `V`. This is how each exceptional subspace is examined by hand. -/
theorem exists_ne_zero_forall_sum_mul_eq_zero {ι : Type*} [Fintype ι]
    {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊤) :
    ∃ w : ι → ℚ, w ≠ 0 ∧ ∀ x ∈ V, ∑ i, w i * x i = 0 := by
  classical
  obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hV)
    inferInstance
  have hfx : ∀ x : ι → ℚ, f x = ∑ i, (f fun j ↦ if i = j then 1 else 0) * x i := fun x ↦ by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]
  refine ⟨fun i ↦ f fun j ↦ if i = j then 1 else 0, fun hw ↦ hf0 (LinearMap.ext fun x ↦ ?_),
    fun x hx ↦ ?_⟩
  · rw [hfx x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [show (f fun j ↦ if i = j then 1 else 0) = 0 from
      congrFun hw i, zero_mul]
  · have h : f x ∈ V.map f := Submodule.mem_map_of_mem hx
    rw [hfV, Submodule.mem_bot] at h
    rw [← hfx x, h]

/-- An integer divisible by `p ^ n` has `p`-adic size at most `(1 / p) ^ n`. -/
theorem padicNorm_le_of_dvd {p : ℕ} [Fact p.Prime] {n : ℕ} {z : ℤ} (h : (p : ℤ) ^ n ∣ z) :
    padicNorm p z ≤ (1 / p : ℚ) ^ n := by
  have h' := (padicNorm.dvd_iff_norm_le (p := p) (n := n) (z := z)).mp (by exact_mod_cast h)
  rwa [zpow_neg, zpow_natCast, ← inv_pow, ← one_div] at h'

/-- Only finitely many `a` have `(3/2)^a ≤ R`. -/
theorem finite_setOf_three_halves_pow_le (R : ℚ) : {a : ℕ | (3 / 2 : ℚ) ^ a ≤ R}.Finite := by
  obtain ⟨a₁, ha₁⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℚ) < 3 / 2)
  refine (Set.finite_Iio a₁).subset fun a ha ↦ ?_
  by_contra h
  exact absurd (ha.trans_lt ha₁) (not_lt.mpr (pow_le_pow_right₀ (by norm_num)
    (not_lt.mp h)))

end SteeringWord
