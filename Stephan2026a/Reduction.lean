/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.ComplexityFloor
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic

-- Used only inside proofs.
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Reduction to a Diophantine kernel

For a rational scale `θ ∈ (0, 1)` let `V(θ)` be the set of pairs `2 ≤ a < c` with
`‖(3/2)^c - (3/2)^a‖ ≤ θ^c` (Definition 3.1). The **kernel** (K) is the assertion that `V(θ)` is
finite for every such `θ`: exponential pair repulsion for the orbit of `(3/2)^n`, an improvement
of the trivial floor `2^(-c)` of Lemma 2.8 to every base `θ < 1`. Rational scales lose nothing,
since `V(θ)` is monotone in `θ`.

**Theorem 3.2**: (K) implies `p_T(k) / k → ∞`. If `p_T(k) ≤ C k`, pigeonhole among the windows
at `2, …, C k + 2` gives a repetition at `2 ≤ a < c ≤ (C + 2) k`; the contraction (Lemma 2.7)
puts `(a, c)` in `V(θ)` for a fixed rational `θ` with `θ^(C+2) ≥ 2/3`, and the growth ceiling
forces `c → ∞` as `k` grows.

## Main definitions

* `SteeringWord.kernelViolators θ`: the set `V(θ)`.

## Main results

* `SteeringWord.lt_complexity_of_forall_le`: the exchange rate, with an explicit threshold.
* `SteeringWord.forall_lt_complexity_of_kernel`: **Theorem 3.2**, in the form "for every `C`
  there is a `K` with `p_T(k) > C k` for `k ≥ K`".
* `SteeringWord.tendsto_complexity_div_of_kernel`: the same, as `p_T(k) / k → ∞`.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §3.
-/

@[expose] public section

namespace SteeringWord

open Function Filter

/-- The set `V(θ)` of pairs `2 ≤ a < c` with `‖(3/2)^c - (3/2)^a‖ ≤ θ^c` (Definition 3.1). -/
def kernelViolators (θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧ ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt ≤ θ ^ p.2}

/-- A rational Bernoulli certificate: for `r ∈ (0, 1)` and `N ≥ 1` the rational
`θ = 1 - (1 - r) / N` has `r ≤ θ^N`. -/
theorem exists_pow_ge (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ r ≤ θ ^ N := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hdivle : (1 - r) / N ≤ 1 - r := div_le_self (by linarith) (by exact_mod_cast hN)
  have hdivpos : 0 < (1 - r) / N := div_pos (by linarith) hN0
  refine ⟨1 - (1 - r) / N, by linarith, by linarith, ?_⟩
  calc r = 1 + (N : ℚ) * (-((1 - r) / N)) := by field_simp; ring
    _ ≤ (1 + -((1 - r) / N)) ^ N := one_add_mul_le_pow (by linarith) N
    _ = (1 - (1 - r) / N) ^ N := by rw [← sub_eq_add_neg]

/-- The contraction puts a repetition of length `k` at `2 ≤ a < c ≤ (C + 2) k` into `V(θ)` for
every rational `θ < 1` with `θ^(C+2) ≥ 2/3`. -/
theorem mem_kernelViolators_of_repetition {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {C k a c : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ (C + 2)) (ha : 2 ≤ a) (hac : a < c) (hck : c ≤ (C + 2) * k)
    (hrep : IsRepetition a c k) : (a, c) ∈ kernelViolators θ := by
  refine ⟨ha, hac, ?_⟩
  calc ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt ≤ |eps c - eps a| :=
        distToNearestInt_orbit_le a c
    _ ≤ (2 / 3 : ℚ) ^ k := abs_eps_sub_le_of_repetition hrep
    _ ≤ (θ ^ (C + 2)) ^ k := pow_le_pow_left₀ (by norm_num) hθpow k
    _ = θ ^ ((C + 2) * k) := (pow_mul θ (C + 2) k).symm
    _ ≤ θ ^ c := pow_le_pow_of_le_one hθ0.le hθ1.le hck

/-- **The exchange rate of Theorem 3.2.** If `θ ∈ (0, 1)` has `θ^(C+2) ≥ 2/3` and every pair of
`V(θ)` has `c ≤ A`, then `p_T(k) > C k` for every `k > A`. An effective `A` (Problem 5.1) thus
gives an effective complexity bound. -/
theorem lt_complexity_of_forall_le {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {C A : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ (C + 2)) (hA : ∀ p ∈ kernelViolators θ, p.2 ≤ A) {k : ℕ}
    (hk : A < k) : C * k < complexity t k := by
  by_contra hle
  have hple : complexity t k ≤ C * k := Nat.not_lt.mp hle
  -- pigeonhole among the `C k + 1` windows at positions `2, …, C k + 2`
  have hncard : complexity t k = (finite_factors k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (finite_factors k)
  have hcard : (finite_factors k).toFinset.card < (Finset.Icc 2 (C * k + 2)).card := by
    rw [Nat.card_Icc, ← hncard, show C * k + 2 + 1 - 2 = C * k + 1 by omega]
    exact Nat.lt_succ_of_le hple
  have hmaps : ∀ a ∈ Finset.Icc 2 (C * k + 2), factor t a k ∈ (finite_factors k).toFinset :=
    fun a _ ↦ (Set.Finite.mem_toFinset _).mpr ⟨a, rfl⟩
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hx hy
  obtain ⟨a, c, ha, hac, hc, hrep⟩ : ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ C * k + 2 ∧ IsRepetition a c k := by
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, hx.1, h, hy.2, factor_eq_iff.mp hfeq⟩
    · exact ⟨y, x, hy.1, by omega, hx.2, factor_eq_iff.mp hfeq.symm⟩
  have hck : c ≤ (C + 2) * k := by nlinarith
  have hcA : c ≤ A := hA (a, c) (mem_kernelViolators_of_repetition hθ0 hθ1 hθpow ha hac hck hrep)
  -- the growth ceiling: `41 k ≤ 24 c + 24 ≤ 24 A + 24`, against `k ≥ A + 1`
  have := repetition_linear_bound ha hac hrep
  omega

/-- **Theorem 3.2, the reduction**: the kernel (K) forces `p_T(k) > C k` for all large `k`, for
every `C`. -/
theorem forall_lt_complexity_of_kernel
    (hK : ∀ θ : ℚ, 0 < θ → θ < 1 → (kernelViolators θ).Finite) (C : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → C * k < complexity t k := by
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ := exists_pow_ge (2 / 3) (by norm_num) (by norm_num) (C + 2)
    (by omega)
  obtain ⟨A, hA⟩ := ((hK θ hθ0 hθ1).image Prod.snd).bddAbove
  exact ⟨A + 1, fun k hk ↦ lt_complexity_of_forall_le hθ0 hθ1 hθpow
    (fun p hp ↦ hA ⟨p, hp, rfl⟩) (by omega)⟩

/-- **Theorem 3.2, as a limit**: the kernel (K) forces `p_T(k) / k → ∞`. -/
theorem tendsto_complexity_div_of_kernel
    (hK : ∀ θ : ℚ, 0 < θ → θ < 1 → (kernelViolators θ).Finite) :
    Tendsto (fun k : ℕ ↦ (complexity t k : ℝ) / k) atTop atTop := by
  refine tendsto_atTop.mpr fun r ↦ ?_
  obtain ⟨K, hK⟩ := forall_lt_complexity_of_kernel hK ⌈r⌉₊
  refine eventually_atTop.mpr ⟨max K 1, fun k hk ↦ ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlt : ((⌈r⌉₊ * k : ℕ) : ℝ) < complexity t k := by exact_mod_cast hK k (by omega)
  rw [le_div_iff₀ hk0]
  push_cast at hlt
  nlinarith [Nat.le_ceil r]

end SteeringWord
