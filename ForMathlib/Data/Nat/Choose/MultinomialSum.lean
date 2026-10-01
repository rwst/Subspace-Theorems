/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Multinomial

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.LinearCombination

/-!
# The sum of the inverse multinomial coefficients

For a finite set `s` with `|s| = n + 1` and any `d`, the inverses of the multinomial coefficients
of degree `d` sum to at most `e^{2√n}`:
`∑_{|m| = d} m₀! ⋯ mₙ! / d! ≤ e^{2√n}` (`Finset.sum_inv_multinomial_le`).

This is G. Rémond, *Sur le théorème du produit*, J. Théor. Nombres Bordeaux **13** (2001),
Lemma 5.2, which bounds the height of a sum of monomials in Rémond's normalization. The
combinatorial half follows Rémond: grouping the `m` by their support reduces to the sums `g(T, d)`
over `m` with support exactly `T`, which satisfy the recurrence
`|T| (d + 1) g(T, d + 1) = (d + |T|) g(T, d) + ∑_{t ∈ T} g(T ∖ {t}, d)`
(`Finset.card_mul_posFactSum_succ`, an identity of natural numbers proved by the bijection
`m ↦ m - e_t`). It gives `g(T, d) ≤ 2r/(r + 1)!` for `|T| = r ≥ 1`. The analytic half is not
Rémond's, who uses Stirling's formula and numerical checks for small `n`: the term
`C(n + 1, j + 1) · 2/(j + 1)!` is at most the sum of the terms of degrees `2j + 1` and `2j + 2`
of the series of `e^{2√n}`, because `C(2j + 1, j) ≤ 4^j`.
-/

@[expose] public section

open Nat

namespace Finset

variable {σ : Type*} [DecidableEq σ]

/-- The `m` of degree `d` with support exactly `T`. -/
noncomputable def posAntidiag (T : Finset σ) (d : ℕ) : Finset (σ →₀ ℕ) :=
  {m ∈ T.finsuppAntidiag d | m.support = T}

theorem mem_posAntidiag {T : Finset σ} {d : ℕ} {m : σ →₀ ℕ} :
    m ∈ T.posAntidiag d ↔ ∑ t ∈ T, m t = d ∧ m.support = T := by
  rw [posAntidiag, mem_filter, mem_finsuppAntidiag]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.le⟩, h.2⟩⟩

/-- `∑ m₀! ⋯ mₖ!` over the `m` of degree `d` with support exactly `T`; divided by `d!` it is
Rémond's `g`. -/
noncomputable def posFactSum (T : Finset σ) (d : ℕ) : ℕ :=
  ∑ m ∈ T.posAntidiag d, ∏ t ∈ T, (m t)!

theorem posAntidiag_eq_empty {T : Finset σ} {d : ℕ} (hd : d < #T) : T.posAntidiag d = ∅ := by
  refine eq_empty_of_forall_notMem fun m hm ↦ ?_
  obtain ⟨hsum, hsupp⟩ := mem_posAntidiag.mp hm
  have : #T ≤ d := by
    rw [← hsum, card_eq_sum_ones]
    refine sum_le_sum fun t ht ↦ ?_
    rw [← hsupp, Finsupp.mem_support_iff] at ht
    omega
  omega

omit [DecidableEq σ] in
/-- The support of `m + e_t` when `t` lies in the support of `m`. -/
private theorem support_add_single_of_mem {T : Finset σ} {m : σ →₀ ℕ} (hm : m.support = T)
    {t : σ} (ht : t ∈ T) : (m + Finsupp.single t 1).support = T := by
  classical
  ext s
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, ← hm,
    Finsupp.mem_support_iff]
  by_cases hts : t = s
  · subst hts
    simpa using Finsupp.mem_support_iff.mp (hm ▸ ht)
  · simp [hts]

omit [DecidableEq σ] in
/-- The support of `c + e_t` when `c` has support `T ∖ {t}`. -/
private theorem support_add_single_of_erase [DecidableEq σ] {T : Finset σ} {c : σ →₀ ℕ} {t : σ}
    (hc : c.support = T.erase t) (ht : t ∈ T) : (c + Finsupp.single t 1).support = T := by
  ext s
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hts : t = s
  · subst hts
    simp [ht]
  · simp only [hts, ↓reduceIte, add_zero]
    rw [← Finsupp.mem_support_iff, hc, mem_erase]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Ne.symm hts, h⟩⟩

omit [DecidableEq σ] in
private theorem sum_add_single {T : Finset σ} (m : σ →₀ ℕ) {t : σ} (ht : t ∈ T) :
    ∑ s ∈ T, (m + Finsupp.single t 1 : σ →₀ ℕ) s = ∑ s ∈ T, m s + 1 := by
  classical
  simp_rw [Finsupp.add_apply, sum_add_distrib, Finsupp.single_apply]
  simp [ht]

private theorem prod_factorial_add_single {T : Finset σ} (m : σ →₀ ℕ) {t : σ} (ht : t ∈ T) :
    ∏ s ∈ T, ((m + Finsupp.single t 1 : σ →₀ ℕ) s)! =
      (m t + 1) * (m t)! * ∏ s ∈ T.erase t, (m s)! := by
  rw [← mul_prod_erase T _ ht, Finsupp.add_apply, Finsupp.single_eq_same, factorial_succ]
  congr 1
  refine prod_congr rfl fun s hs ↦ ?_
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (ne_of_mem_erase hs), add_zero]

omit [DecidableEq σ] in
/-- `m - e_t + e_t = m` when `m_t ≠ 0`. -/
private theorem sub_single_add_single {m : σ →₀ ℕ} {t : σ} (hmt : m t ≠ 0) :
    m - Finsupp.single t 1 + Finsupp.single t 1 = m := by
  refine tsub_add_cancel_of_le ?_
  rw [Finsupp.single_le_iff]
  omega

/-- The part of `posFactSum T (d + 1)` with `m_t ≥ 2`. -/
private theorem sum_filter_ne_one {T : Finset σ} {t : σ} (ht : t ∈ T) (d : ℕ) :
    ∑ m ∈ T.posAntidiag (d + 1) with m t ≠ 1, ∏ s ∈ T, (m s)! =
      ∑ a ∈ T.posAntidiag d, (a t + 1) * ∏ s ∈ T, (a s)! := by
  symm
  refine sum_nbij' (· + Finsupp.single t 1) (· - Finsupp.single t 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hsum, hsupp⟩ := mem_posAntidiag.mp ha
    have hat : a t ≠ 0 := Finsupp.mem_support_iff.mp (hsupp ▸ ht)
    simp only [mem_filter, mem_posAntidiag]
    refine ⟨⟨by rw [sum_add_single a ht, hsum], support_add_single_of_mem hsupp ht⟩, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · intro m hm
    simp only [mem_filter, mem_posAntidiag] at hm
    obtain ⟨⟨hsum, hsupp⟩, h1⟩ := hm
    have hmt : m t ≠ 0 := Finsupp.mem_support_iff.mp (hsupp ▸ ht)
    have hsupp' : (m - Finsupp.single t 1).support = T := by
      ext s
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply, ← hsupp,
        Finsupp.mem_support_iff]
      by_cases hts : t = s
      · subst hts
        simp only [↓reduceIte]
        omega
      · simp [hts]
    rw [mem_posAntidiag]
    refine ⟨?_, hsupp'⟩
    have := sum_add_single (m - Finsupp.single t 1) ht
    rw [sub_single_add_single hmt, hsum] at this
    omega
  · intro a _
    exact add_tsub_cancel_right a _
  · intro m hm
    simp only [mem_filter, mem_posAntidiag] at hm
    exact sub_single_add_single (Finsupp.mem_support_iff.mp (hm.1.2 ▸ ht))
  · intro a _
    rw [prod_factorial_add_single a ht, ← mul_prod_erase T _ ht, mul_assoc]

/-- The part of `posFactSum T (d + 1)` with `m_t = 1`. -/
private theorem sum_filter_eq_one {T : Finset σ} {t : σ} (ht : t ∈ T) (d : ℕ) :
    ∑ m ∈ T.posAntidiag (d + 1) with m t = 1, ∏ s ∈ T, (m s)! = posFactSum (T.erase t) d := by
  symm
  refine sum_nbij' (· + Finsupp.single t 1) (· - Finsupp.single t 1) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_posAntidiag] at hc
    obtain ⟨hsum, hsupp⟩ := hc
    have hct : c t = 0 := Finsupp.notMem_support_iff.mp (by simp [hsupp])
    simp only [mem_filter, mem_posAntidiag]
    refine ⟨⟨?_, support_add_single_of_erase hsupp ht⟩, by simp [hct]⟩
    rw [sum_add_single c ht, ← add_sum_erase T _ ht, hct, zero_add, hsum]
  · intro m hm
    simp only [mem_filter, mem_posAntidiag] at hm
    obtain ⟨⟨hsum, hsupp⟩, h1⟩ := hm
    rw [mem_posAntidiag]
    have hsupp' : (m - Finsupp.single t 1).support = T.erase t := by
      ext s
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply, mem_erase, ← hsupp,
        Finsupp.mem_support_iff]
      by_cases hts : t = s
      · subst hts
        simp [h1]
      · simp [hts, Ne.symm hts]
    refine ⟨?_, hsupp'⟩
    rw [← add_sum_erase T _ ht, h1] at hsum
    have : ∑ s ∈ T.erase t, (m - Finsupp.single t 1 : σ →₀ ℕ) s = ∑ s ∈ T.erase t, m s :=
      sum_congr rfl fun s hs ↦ by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (ne_of_mem_erase hs), Nat.sub_zero]
    omega
  · intro c _
    exact add_tsub_cancel_right c _
  · intro m hm
    simp only [mem_filter, mem_posAntidiag] at hm
    exact sub_single_add_single (by omega)
  · intro c hc
    rw [mem_posAntidiag] at hc
    have hct : c t = 0 := Finsupp.notMem_support_iff.mp (by simp [hc.2])
    rw [prod_factorial_add_single c ht, hct]
    simp

/-- **Rémond's recurrence**, as an identity of natural numbers:
`|T| · ∑_{|m| = d + 1} ∏ m_t! = (d + |T|) · ∑_{|m| = d} ∏ m_t! + ∑_t ∑_{|c| = d} ∏ c_s!`, the sums
over `m` with support `T` and `c` with support `T ∖ {t}`. -/
theorem card_mul_posFactSum_succ (T : Finset σ) (d : ℕ) :
    #T * posFactSum T (d + 1) =
      (d + #T) * posFactSum T d + ∑ t ∈ T, posFactSum (T.erase t) d := by
  have h : ∀ t ∈ T, posFactSum T (d + 1) =
      ∑ a ∈ T.posAntidiag d, (a t + 1) * ∏ s ∈ T, (a s)! + posFactSum (T.erase t) d := by
    intro t ht
    rw [← sum_filter_ne_one ht, ← sum_filter_eq_one ht, posFactSum]
    exact (sum_filter_not_add_sum_filter _ (fun m : σ →₀ ℕ ↦ m t = 1) _).symm
  rw [card_eq_sum_ones, sum_mul, sum_congr rfl fun t ht ↦ by rw [one_mul, h t ht],
    sum_add_distrib, sum_comm, posFactSum, mul_sum]
  congr 1
  refine sum_congr rfl fun a ha ↦ ?_
  rw [← sum_mul, sum_add_distrib, (mem_posAntidiag.mp ha).1, ← card_eq_sum_ones]

/-- The bound for `g(T, d)`, `|T| = r`: `0` below `d = r`, `1/r!` at `d = r`, then `2r/(r + 1)!`. -/
private noncomputable def bound (r d : ℕ) : ℝ :=
  if d < r then 0 else if d = r then 1 / (r ! : ℝ) else 2 * r / ((r + 1)! : ℝ)

private theorem bound_nonneg (r d : ℕ) : 0 ≤ bound r d := by
  unfold bound
  split_ifs <;> positivity

/-- The bound propagates through Rémond's recurrence. -/
private theorem bound_step (r d : ℕ) :
    (d + r + 1 : ℝ) * bound (r + 1) d + (r + 1) * bound r d ≤
      (r + 1) * (d + 1) * bound (r + 1) (d + 1) := by
  have hf1 : ((r + 1)! : ℝ) = (r + 1) * r ! := by push_cast [factorial_succ]; ring
  have hf2 : ((r + 1 + 1)! : ℝ) = (r + 2) * (r + 1) * r ! := by
    push_cast [factorial_succ]; ring
  have hr : (0 : ℝ) < r ! := by positivity
  unfold bound
  rcases lt_trichotomy d r with hd | rfl | hd
  · simp [hd, show d + 1 < r + 1 by omega, show d < r + 1 by omega]
  · simp only [lt_irrefl, ↓reduceIte, lt_add_iff_pos_right, Nat.lt_one_iff]
    rw [hf1]
    field_simp
    simp
  · rcases Nat.lt_or_ge (r + 1) d with hd' | hd'
    · simp only [show ¬d < r + 1 by omega, show d ≠ r + 1 by omega, show ¬d < r by omega,
        show d ≠ r by omega, show ¬d + 1 < r + 1 by omega, show d + 1 ≠ r + 1 by omega,
        ↓reduceIte]
      rw [hf2, hf1]
      push_cast
      field_simp
      have : (r : ℝ) + 2 ≤ d := by exact_mod_cast hd'
      nlinarith
    · obtain rfl : d = r + 1 := by omega
      simp only [lt_irrefl, ↓reduceIte, show ¬r + 1 < r by omega, show r + 1 ≠ r by omega,
        show ¬r + 1 + 1 < r + 1 by omega, show r + 1 + 1 ≠ r + 1 by omega]
      rw [hf2, hf1]
      push_cast
      field_simp
      ring_nf
      exact le_rfl

/-- **Rémond's bound for `g`.** `g(T, d) = (∑ ∏ m_t!)/d! ≤ bound |T| d`. -/
private theorem posFactSum_div_le (T : Finset σ) (d : ℕ) :
    (posFactSum T d : ℝ) / d ! ≤ bound #T d := by
  induction h : #T generalizing T d with
  | zero =>
    obtain rfl := card_eq_zero.mp h
    rcases eq_or_ne d 0 with rfl | hd
    · simpa [posFactSum, posAntidiag, bound] using (card_filter_le _ _).trans (by simp)
    · simp [posFactSum, posAntidiag, finsuppAntidiag_empty_of_ne_zero hd, bound, hd]
  | succ r ih =>
    induction d with
    | zero =>
      rw [posFactSum, posAntidiag_eq_empty (by omega)]
      simpa using bound_nonneg _ _
    | succ d ihd =>
      have hrec := congrArg (Nat.cast : ℕ → ℝ) (card_mul_posFactSum_succ T d)
      rw [h] at hrec
      push_cast at hrec
      have hd : (d ! : ℝ) ≠ 0 := by positivity
      have hdf : ((d + 1)! : ℝ) = (d + 1) * d ! := by push_cast [factorial_succ]; ring
      have hsum : ∑ t ∈ T, (posFactSum (T.erase t) d : ℝ) / d ! ≤ (r + 1) * bound r d := by
        refine (sum_le_sum fun t ht ↦ ih (T.erase t) d ?_).trans ?_
        · rw [card_erase_of_mem ht, h, Nat.add_sub_cancel]
        · rw [sum_const, h, nsmul_eq_mul]
          push_cast
          exact le_rfl
      have hpos : (0 : ℝ) < (r + 1) * (d + 1) := by positivity
      refine le_of_mul_le_mul_left ?_ hpos
      calc (r + 1) * (d + 1) * ((posFactSum T (d + 1) : ℝ) / (d + 1)!)
          = (d + r + 1) * ((posFactSum T d : ℝ) / d !) +
              ∑ t ∈ T, (posFactSum (T.erase t) d : ℝ) / d ! := by
            rw [hdf, ← Finset.sum_div]
            field_simp
            linear_combination hrec
        _ ≤ (d + r + 1) * bound (r + 1) d + (r + 1) * bound r d := by gcongr
        _ ≤ (r + 1) * (d + 1) * bound (r + 1) (d + 1) := bound_step r d

/-- **Grouping by support.** `∑_{|m| = d} 1/C(d; m) = ∑_{T ⊆ S} g(T, d)`. -/
theorem sum_inv_multinomial_eq (S : Finset σ) (d : ℕ) :
    ∑ m ∈ S.finsuppAntidiag d, ((multinomial S m : ℕ) : ℝ)⁻¹ =
      ∑ T ∈ S.powerset, (posFactSum T d : ℝ) / d ! := by
  rw [← sum_fiberwise_of_maps_to (g := Finsupp.support) (t := S.powerset)
    fun m hm ↦ mem_powerset.mpr (mem_finsuppAntidiag.mp hm).2]
  refine sum_congr rfl fun T hT ↦ ?_
  have hTS := mem_powerset.mp hT
  have hsub : ∀ m : σ →₀ ℕ, m.support = T → ∑ t ∈ T, m t = ∑ s ∈ S, m s := fun m hm ↦
    sum_subset hTS fun s _ hs ↦ Finsupp.notMem_support_iff.mp (by rwa [hm])
  have hset : {m ∈ S.finsuppAntidiag d | m.support = T} = T.posAntidiag d := by
    ext m
    rw [mem_filter, mem_finsuppAntidiag, mem_posAntidiag]
    constructor
    · rintro ⟨⟨hsum, -⟩, hm⟩
      exact ⟨(hsub m hm).trans hsum, hm⟩
    · rintro ⟨hsum, hm⟩
      exact ⟨⟨(hsub m hm).symm.trans hsum, by rw [hm]; exact hTS⟩, hm⟩
  rw [hset, posFactSum, Nat.cast_sum, Finset.sum_div]
  refine sum_congr rfl fun m hm ↦ ?_
  obtain ⟨hsum, hsupp⟩ := mem_posAntidiag.mp hm
  have hprod : ∏ s ∈ S, (m s)! = ∏ t ∈ T, (m t)! :=
    (prod_subset hTS fun s _ hs ↦ by
      rw [Finsupp.notMem_support_iff.mp (by rwa [hsupp]), factorial_zero]).symm
  have hspec := multinomial_spec S m
  rw [hprod, ← hsub m hsupp, hsum] at hspec
  have hpos : (0 : ℝ) < multinomial S m := by exact_mod_cast multinomial_pos S m
  rw [← hspec, Nat.cast_mul, inv_eq_one_div, eq_div_iff (by positivity)]
  field_simp

private theorem bound_succ_le (k d : ℕ) : bound (k + 1) d ≤ 2 / ((k + 1)! : ℝ) := by
  have hk : (0 : ℝ) < (k + 1)! := by positivity
  unfold bound
  split_ifs
  · positivity
  · gcongr
    norm_num
  · rw [show k + 1 + 1 = k + 2 by ring, factorial_succ (k + 1)]
    push_cast
    rw [div_le_div_iff₀ (by positivity) hk]
    nlinarith

private theorem bound_one_le (d : ℕ) : bound 1 d ≤ 1 := by
  unfold bound
  split_ifs <;> norm_num [factorial]

/-- Pairing the terms of degrees `2j + 1` and `2j + 2` of a series. -/
private theorem sum_pairs_le {φ : ℕ → ℝ} (hφ : ∀ m, 0 ≤ φ m) (K : ℕ) :
    ∑ j ∈ range K, (φ (2 * j + 1) + φ (2 * j + 2)) ≤ ∑ m ∈ range (2 * K + 1), φ m := by
  induction K with
  | zero => simpa using hφ 0
  | succ K ih =>
    rw [sum_range_succ, show 2 * (K + 1) + 1 = 2 * K + 1 + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    linarith

/-- The term `C(n + 1, j + 1) · 2/(j + 1)!` against the series of `e^{2√n}`. -/
private theorem choose_mul_le (n j : ℕ) (hn : 1 ≤ n) :
    ((n + 1).choose (j + 1) : ℝ) * (2 / (j + 1)!) ≤
      (2 * √n) ^ (2 * j + 1) / (2 * j + 1)! + (2 * √n) ^ (2 * j + 2) / (2 * j + 2)! := by
  have hsq : (√n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hs1 : (1 : ℝ) ≤ √n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hx1 : (2 * √n : ℝ) ^ (2 * j + 1) = 2 * 4 ^ j * n ^ j * √n := by
    have : (√n : ℝ) ^ (2 * j + 1) = n ^ j * √n := by rw [pow_succ, pow_mul, hsq]
    rw [mul_pow, this, pow_succ, pow_mul]
    norm_num
    ring
  have hx2 : (2 * √n : ℝ) ^ (2 * j + 2) = 4 ^ (j + 1) * n ^ (j + 1) := by
    rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul, mul_pow, hsq, mul_pow]
    norm_num
  set c : ℝ := (((2 * j + 1).choose j : ℕ) : ℝ) with hcdef
  have hc : c ≤ 4 ^ j := by rw [hcdef]; exact_mod_cast choose_middle_le_pow j
  have hf1 : ((2 * j + 1)! : ℝ) = c * j ! * (j + 1)! := by
    have := choose_mul_factorial_mul_factorial (show j ≤ 2 * j + 1 by omega)
    rw [show 2 * j + 1 - j = j + 1 by omega] at this
    rw [hcdef]
    exact_mod_cast this.symm
  have hf2 : ((2 * j + 2)! : ℝ) = 2 * c * (j + 1)! * (j + 1)! := by
    rw [show 2 * j + 2 = 2 * j + 1 + 1 by ring, factorial_succ]
    push_cast
    rw [hf1, factorial_succ j]
    push_cast
    ring
  have hj : (0 : ℝ) < j ! := by positivity
  have hj1 : (0 : ℝ) < (j + 1)! := by positivity
  have hc0 : (0 : ℝ) < c := by
    have := choose_pos (show j ≤ 2 * j + 1 by omega)
    positivity
  rw [choose_succ_succ', Nat.cast_add, add_mul]
  refine add_le_add ?_ ?_
  · calc (n.choose j : ℝ) * (2 / (j + 1)!) ≤ n ^ j / j ! * (2 / (j + 1)!) := by
          gcongr
          exact choose_le_pow_div j n
      _ ≤ (2 * √n) ^ (2 * j + 1) / (2 * j + 1)! := by
          rw [hx1, hf1, _root_.div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have : c ≤ 4 ^ j * √n := hc.trans (le_mul_of_one_le_right (by positivity) hs1)
          calc (n : ℝ) ^ j * 2 * (c * j ! * (j + 1)!) = (2 * n ^ j * j ! * (j + 1)!) * c := by
                ring
            _ ≤ (2 * n ^ j * j ! * (j + 1)!) * (4 ^ j * √n) := by gcongr
            _ = 2 * 4 ^ j * n ^ j * √n * (j ! * (j + 1)!) := by ring
  · calc (n.choose (j + 1) : ℝ) * (2 / (j + 1)!) ≤ n ^ (j + 1) / (j + 1)! * (2 / (j + 1)!) := by
          gcongr
          exact choose_le_pow_div (j + 1) n
      _ ≤ (2 * √n) ^ (2 * j + 2) / (2 * j + 2)! := by
          rw [hx2, hf2, _root_.div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          calc (n : ℝ) ^ (j + 1) * 2 * (2 * c * (j + 1)! * (j + 1)!) =
                (n ^ (j + 1) * (j + 1)! * (j + 1)!) * (4 * c) := by ring
            _ ≤ (n ^ (j + 1) * (j + 1)! * (j + 1)!) * 4 ^ (j + 1) := by
                gcongr
                rw [pow_succ]
                linarith
            _ = 4 ^ (j + 1) * n ^ (j + 1) * ((j + 1)! * (j + 1)!) := by ring

/-- The bound summed over the subsets of an `N`-element set is at most `e^{2√(N - 1)}`. -/
private theorem sum_choose_mul_bound_le (N d : ℕ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * bound k d ≤ Real.exp (2 * √((N : ℝ) - 1)) := by
  rw [sum_range_succ']
  have hexp : 1 ≤ Real.exp (2 * √((N : ℝ) - 1)) := Real.one_le_exp (by positivity)
  rcases eq_or_ne d 0 with rfl | hd
  · have : ∀ k ∈ range N, (N.choose (k + 1) : ℝ) * bound (k + 1) 0 = 0 := fun k _ ↦ by
      simp [bound]
    rw [sum_congr rfl this]
    simp [bound]
  have h0 : bound 0 d = 0 := by simp [bound, hd]
  rw [h0, mul_zero, add_zero]
  rcases N with _ | _ | n
  · simpa using (zero_le_one.trans hexp)
  · simpa using bound_one_le d
  set x : ℝ := 2 * √(n : ℝ)
  have hx : 0 ≤ x := by positivity
  have hN : ((n + 1 + 1 : ℕ) : ℝ) - 1 = n + 1 := by push_cast; ring
  rw [hN]
  calc ∑ k ∈ range (n + 1 + 1), ((n + 1 + 1).choose (k + 1) : ℝ) * bound (k + 1) d
      ≤ ∑ k ∈ range (n + 1 + 1), ((n + 1 + 1).choose (k + 1) : ℝ) * (2 / (k + 1)!) :=
        sum_le_sum fun k _ ↦ by gcongr; exact bound_succ_le k d
    _ ≤ ∑ k ∈ range (n + 1 + 1), ((2 * √((n : ℝ) + 1)) ^ (2 * k + 1) / (2 * k + 1)! +
          (2 * √((n : ℝ) + 1)) ^ (2 * k + 2) / (2 * k + 2)!) :=
        sum_le_sum fun k _ ↦ by
          have := choose_mul_le (n + 1) k (by omega)
          push_cast at this
          exact this
    _ ≤ ∑ m ∈ range (2 * (n + 1 + 1) + 1), (2 * √((n : ℝ) + 1)) ^ m / m ! :=
        sum_pairs_le (φ := fun m ↦ (2 * √((n : ℝ) + 1)) ^ m / m !) (fun m ↦ by positivity) _
    _ ≤ Real.exp (2 * √((n : ℝ) + 1)) := Real.sum_le_exp_of_nonneg (by positivity) _

/-- **Rémond's Lemma 5.2.** For a finite set `S` with `|S| = n + 1`, the inverses of the
multinomial coefficients of degree `d` sum to at most `e^{2√n}`:
`∑_{|m| = d} m₀! ⋯ mₙ! / d! ≤ e^{2√n}`. For `S = ∅` the bound reads `1`. -/
theorem sum_inv_multinomial_le (S : Finset σ) (d : ℕ) :
    ∑ m ∈ S.finsuppAntidiag d, ((multinomial S m : ℕ) : ℝ)⁻¹ ≤
      Real.exp (2 * √((#S : ℝ) - 1)) := by
  rw [sum_inv_multinomial_eq]
  calc ∑ T ∈ S.powerset, (posFactSum T d : ℝ) / d ! ≤ ∑ T ∈ S.powerset, bound #T d :=
        sum_le_sum fun T _ ↦ posFactSum_div_le T d
    _ = ∑ k ∈ range (#S + 1), ((#S).choose k : ℝ) * bound k d := by
        rw [sum_powerset_apply_card (fun k ↦ bound k d)]
        simp_rw [nsmul_eq_mul]
    _ ≤ _ := sum_choose_mul_bound_le _ d

end Finset
