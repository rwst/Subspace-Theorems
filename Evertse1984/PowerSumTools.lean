/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.PlaceProd
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.Perm.Basic

-- Used only inside proofs.
import ArithmeticHeights.Extension
import ArithmeticHeights.Kronecker
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tools for Evertse's Theorem 3

Ingredients of the proof of Theorem 3 (Evertse 1984, §4) that have nothing to do with
recurrences.

* **Heights.** A nonzero `θ ∈ K` that is not a root of unity has `H(θ) > 1` (Kronecker), and
  `H(x) / H(y) ≤ H(x y)`.
* **Exponentials beat polynomials**: `A r ^ M < h ^ r` for large `r` when `h > 1`; and
  `h ^ (r - s) ≤ (C r ^ N) ^ 4` forces `r - s ≤ β r ^ γ`.
* **Minimal vanishing subsums.** A vanishing sum splits into disjoint vanishing subsums none of
  whose nonempty proper subsums vanish. For a sum `∑_i ξ_i + ∑_i ξ'_i = 0` with all `ξ_i ≠ 0`,
  either one block contains two of the `ξ_i`, or the blocks are the pairs `{ξ_i, ξ'_{σ i}}` for
  a permutation `σ`.
* **The telescoping estimate of Case 2**: from `r x_k - s x_{k+1} = y_k - y_{k+1}` along a cycle
  of length `ℓ`, with `0 ≤ s < r` and `|y_k| ≤ Y`, it follows that `r x_0 ≤ 2 Y`.
* **Shifts.** For a nonconstant polynomial `f` over a field of characteristic zero and `h ≠ 0`,
  neither of `f(X + h)`, `f(X)` divides the other.
* **Linear independence of exponential polynomials**: `∑_i f_i(k) α_i ^ k = 0` for all `k ∈ ℕ`,
  with distinct nonzero `α_i`, forces all `f_i = 0` (induction on the degrees, applying
  `u(k) ↦ u(k + 1) - α_{i₀} u(k)`).

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §4.
-/

@[expose] public section

open Height Module Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Kronecker's theorem, as a strict inequality**: a nonzero element of a number field that is
not a root of unity has height greater than `1`. -/
theorem one_lt_mulHeight₁ {θ : K} (h0 : θ ≠ 0) (h : ∀ n : ℕ, 0 < n → θ ^ n ≠ 1) :
    1 < mulHeight₁ θ := by
  refine lt_of_le_of_ne (one_le_mulHeight₁ θ) fun h1 ↦ ?_
  have hnn : 0 ≤ absMulHeight₁ θ := by
    rw [absMulHeight₁_eq]; exact Real.rpow_nonneg (mulHeight₁_pos θ).le _
  have habs : absMulHeight₁ θ = 1 := by
    have hp := absMulHeight₁_pow_finrank θ
    rw [← h1] at hp
    exact (pow_eq_one_iff_of_nonneg hnn finrank_pos.ne').mp hp
  rcases (absMulHeight₁_eq_one_iff (Algebra.IsIntegral.isIntegral θ)).mp habs with h' | ⟨n, hn, hn1⟩
  · exact h0 h'
  · exact h n hn hn1

end NumberField

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- The height of a quotient. -/
theorem mulHeight₁_div_le (x y : K) : mulHeight₁ (x / y) ≤ mulHeight₁ x * mulHeight₁ y := by
  rw [div_eq_mul_inv, ← mulHeight₁_inv y]
  exact mulHeight₁_mul_le _ _

/-- A lower bound for the height of a product. -/
theorem div_le_mulHeight₁_mul {x y : K} (hy : y ≠ 0) :
    mulHeight₁ x / mulHeight₁ y ≤ mulHeight₁ (x * y) := by
  rw [div_le_iff₀ (mulHeight₁_pos y)]
  calc mulHeight₁ x = mulHeight₁ (x * y / y) := by rw [mul_div_cancel_right₀ _ hy]
    _ ≤ mulHeight₁ (x * y) * mulHeight₁ y := mulHeight₁_div_le _ _

end Height

/-- **Exponentials beat polynomials**: for `h > 1`, eventually `A r ^ M < h ^ r`. -/
theorem exists_forall_mul_pow_lt_pow {h : ℝ} (hh : 1 < h) (A : ℝ) (M : ℕ) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → A * (r : ℝ) ^ M < h ^ r := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt M hh
  have hpos : (0 : ℝ) < (|A| + 1)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨R, fun r hr ↦ ?_⟩
  have h1 := hR r hr
  have hhr : 0 < h ^ r := pow_pos (zero_lt_one.trans hh) r
  rw [div_lt_iff₀ hhr] at h1
  have h2 : (|A| + 1) * (r : ℝ) ^ M < h ^ r := by
    have := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < |A| + 1)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  have h3 : A * (r : ℝ) ^ M ≤ (|A| + 1) * (r : ℝ) ^ M :=
    mul_le_mul_of_nonneg_right ((le_abs_self A).trans (by linarith)) (by positivity)
  linarith

/-- **Exponential against polynomial, for differences**: if `h ^ (r - s) ≤ (C r ^ N) ^ 4` with
`h > 1`, then `r - s ≤ β r ^ γ` for a `β` depending only on `h, C, N, γ`. -/
theorem exists_forall_sub_le_mul_rpow {h C γ : ℝ} (hh : 1 < h) (hC : 1 ≤ C) (N : ℕ)
    (hγ0 : 0 < γ) : ∃ β > 0, ∀ r s : ℕ, s < r → h ^ (r - s) ≤ (C * (r : ℝ) ^ N) ^ 4 →
      ((r - s : ℕ) : ℝ) ≤ β * (r : ℝ) ^ γ := by
  set L := Real.log h with hL
  have hL0 : 0 < L := Real.log_pos hh
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨(4 * Real.log C + 4 * N / γ) / L + 1, by positivity, fun r s hsr hup ↦ ?_⟩
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_of_lt hsr
  have hlog := Real.log_le_log (by positivity) hup
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hlog
  have hlr : Real.log (r : ℝ) ≤ (r : ℝ) ^ γ / γ := Real.log_le_rpow_div (by positivity) hγ0
  have hrγ : 1 ≤ (r : ℝ) ^ γ := Real.one_le_rpow hr1' hγ0.le
  rw [← hL, Nat.cast_ofNat] at hlog
  have h0 : ((r - s : ℕ) : ℝ) * L ≤ 4 * Real.log C + 4 * N * Real.log (r : ℝ) := by
    linarith [hlog]
  have h1 : ((r - s : ℕ) : ℝ) * L ≤ 4 * Real.log C + 4 * N * ((r : ℝ) ^ γ / γ) := by
    have := mul_le_mul_of_nonneg_left hlr (by positivity : (0 : ℝ) ≤ 4 * N)
    linarith
  have h2 : 4 * Real.log C + 4 * N * ((r : ℝ) ^ γ / γ) ≤
      (4 * Real.log C + 4 * N / γ) * (r : ℝ) ^ γ := by
    rw [add_mul, mul_div_assoc', div_mul_eq_mul_div]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h3 : ((r - s : ℕ) : ℝ) ≤ (4 * Real.log C + 4 * N / γ) / L * (r : ℝ) ^ γ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
    linarith
  nlinarith

section Blocks

variable {α M : Type*} [AddCommGroup M]

/-- **A vanishing sum splits into minimal vanishing subsums**: disjoint nonempty blocks covering
`s`, each with vanishing sum and no vanishing nonempty proper subsum. -/
theorem exists_blocks (ξ : α → M) (s : Finset α) (hs : ∑ a ∈ s, ξ a = 0) :
    ∃ P : Finset (Finset α),
      (∀ B ∈ P, B ⊆ s ∧ B.Nonempty ∧ ∑ a ∈ B, ξ a = 0 ∧
        ∀ I ⊆ B, I.Nonempty → I ≠ B → ∑ a ∈ I, ξ a ≠ 0) ∧
      (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧ ∀ a ∈ s, ∃ B ∈ P, a ∈ B := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨J, hJ, hmin⟩ :=
      (s.powerset.filter fun J ↦ J.Nonempty ∧ ∑ a ∈ J, ξ a = 0).exists_min_image
        Finset.card ⟨s, by simp [hne, hs]⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hJ hmin
    obtain ⟨hJs, hJne, hJ0⟩ := hJ
    have hJmin : ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ a ∈ I, ξ a ≠ 0 := fun I hIJ hI hIne h0 ↦
      (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hIJ, hIne⟩)).not_ge
        (hmin I ⟨hIJ.trans hJs, hI, h0⟩)
    have hsub : s \ J ⊂ s := Finset.sdiff_ssubset hJs hJne
    have hs' : ∑ a ∈ s \ J, ξ a = 0 := by
      have := Finset.sum_sdiff hJs (f := ξ)
      rw [hJ0, add_zero] at this
      rw [this, hs]
    obtain ⟨P, hP, hPd, hPc⟩ := ih _ hsub hs'
    have hJP : J ∉ P := fun h ↦ by
      obtain ⟨a, ha⟩ := hJne
      exact (Finset.mem_sdiff.mp ((hP J h).1 ha)).2 ha
    refine ⟨insert J P, fun B hB ↦ ?_, fun B hB B' hB' hBB' ↦ ?_, fun a ha ↦ ?_⟩
    · rcases Finset.mem_insert.mp hB with rfl | hB
      · exact ⟨hJs, hJne, hJ0, hJmin⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hP B hB
        exact ⟨h1.trans Finset.sdiff_subset, h2, h3, h4⟩
    · have hdisj : ∀ B ∈ P, Disjoint J B := fun B hB ↦
        Finset.disjoint_of_subset_right (hP B hB).1 Finset.disjoint_sdiff
      rcases Finset.mem_insert.mp hB with hBJ | hB <;>
        rcases Finset.mem_insert.mp hB' with hB'J | hB'
      · exact absurd (hBJ.trans hB'J.symm) hBB'
      · exact hBJ ▸ hdisj B' hB'
      · exact hB'J ▸ (hdisj B hB).symm
      · exact hPd B hB B' hB' hBB'
    · by_cases haJ : a ∈ J
      · exact ⟨J, Finset.mem_insert_self _ _, haJ⟩
      · obtain ⟨B, hB, haB⟩ := hPc a (Finset.mem_sdiff.mpr ⟨ha, haJ⟩)
        exact ⟨B, Finset.mem_insert_of_mem hB, haB⟩

variable {ι : Type*} [Fintype ι]

/-- **The shape of a vanishing sum `∑_i ξ_i + ∑_i ξ'_i = 0` with all `ξ_i ≠ 0`.** Either some
minimal vanishing subsum contains two of the `ξ_i`, or `ξ_i + ξ'_{σ i} = 0` for a permutation
`σ`. -/
theorem exists_pair_or_exists_perm (ξ : ι ⊕ ι → M) (hξ : ∑ a, ξ a = 0)
    (hne : ∀ i, ξ (Sum.inl i) ≠ 0) :
    (∃ i j, i ≠ j ∧ ∃ J : Finset (ι ⊕ ι), Sum.inl i ∈ J ∧ Sum.inl j ∈ J ∧
      ∑ a ∈ J, ξ a = 0 ∧ ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ a ∈ I, ξ a ≠ 0) ∨
    ∃ σ : Equiv.Perm ι, ∀ i, ξ (Sum.inl i) + ξ (Sum.inr (σ i)) = 0 := by
  classical
  obtain ⟨P, hP, hPd, hPc⟩ := exists_blocks ξ Finset.univ hξ
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  choose B hBP hiB using fun i ↦ hPc (Sum.inl i) (Finset.mem_univ _)
  -- a block has only one `inl`
  have hone : ∀ i j, Sum.inl j ∈ B i → j = i := fun i j hj ↦ by
    by_contra hji
    obtain ⟨-, -, h0, hmin⟩ := hP (B i) (hBP i)
    obtain ⟨I, hIJ, hI, hIne, hI0⟩ := hA i j (Ne.symm hji) (B i) (hiB i) hj h0
    exact hmin I hIJ hI hIne hI0
  -- two blocks sharing an element are equal
  have heq : ∀ i i' a, a ∈ B i → a ∈ B i' → i = i' := fun i i' a ha ha' ↦ by
    by_cases hBB : B i = B i'
    · exact (hone i i' (hBB ▸ hiB i')).symm
    · exact absurd ha' (Finset.disjoint_left.mp (hPd _ (hBP i) _ (hBP i') hBB) ha)
  -- each block contains an `inr`
  have hinr : ∀ i, ∃ k, Sum.inr k ∈ B i := fun i ↦ by
    by_contra h
    push Not at h
    have hBi : B i = {Sum.inl i} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hiB i, fun a ha ↦ ?_⟩
      rcases a with j | k
      · rw [hone i j ha]
      · exact absurd ha (h k)
    have h0 := (hP (B i) (hBP i)).2.2.1
    rw [hBi, Finset.sum_singleton] at h0
    exact hne i h0
  choose τ hτ using hinr
  have hτinj : Function.Injective τ := fun i i' h ↦
    heq i i' (Sum.inr (τ i)) (hτ i) (h ▸ hτ i')
  set σ := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  obtain ⟨i, hi⟩ := hB σ
  have hBi : B i = {Sum.inl i, Sum.inr (τ i)} := by
    refine Finset.Subset.antisymm (fun a ha ↦ ?_) ?_
    · rcases a with j | k
      · rw [hone i j ha]; exact Finset.mem_insert_self _ _
      · obtain ⟨i'', rfl⟩ := (Finite.injective_iff_surjective.mp hτinj) k
        rw [heq i i'' _ ha (hτ i'')]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exact Finset.insert_subset (hiB i) (Finset.singleton_subset_iff.mpr (hτ i))
  have h0 := (hP (B i) (hBP i)).2.2.1
  rw [hBi, Finset.sum_pair Sum.inl_ne_inr] at h0
  exact hi h0

end Blocks

/-- **The telescoping estimate of Case 2.** If `r x_k - s x_{k+1} = y_k - y_{k+1}` for `k < ℓ`,
with `x_ℓ = x_0`, `y_ℓ = y_0`, `0 ≤ s < r`, `ℓ > 0` and `|y_k| ≤ Y`, then `r x_0 ≤ 2 Y`. -/
theorem mul_le_two_mul_of_telescope {ℓ : ℕ} (hℓ : 0 < ℓ) {r s Y : ℝ} (hs : 0 ≤ s) (hsr : s < r)
    (x y : ℕ → ℝ) (hrel : ∀ k < ℓ, r * x k - s * x (k + 1) = y k - y (k + 1))
    (hx : x ℓ = x 0) (hy : y ℓ = y 0) (hY : ∀ k ≤ ℓ, |y k| ≤ Y) : r * x 0 ≤ 2 * Y := by
  have hr : 0 < r := hs.trans_lt hsr
  set ρ := s / r with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs hr.le
  have hρ1 : ρ < 1 := (div_lt_one hr).mpr hsr
  set p : ℕ → ℝ := fun k ↦ ρ ^ k * (x k - y k / r) with hp
  have hstep : ∀ k < ℓ, p k - p (k + 1) = ρ ^ k * y (k + 1) * (ρ - 1) / r := by
    intro k hk
    have h := hrel k hk
    simp only [hp, hρ, pow_succ]
    field_simp
    linear_combination (s / r) ^ k * r * h
  have hsum : p 0 - p ℓ = ∑ k ∈ Finset.range ℓ, ρ ^ k * y (k + 1) * (ρ - 1) / r := by
    rw [← Finset.sum_range_sub' p ℓ]
    exact Finset.sum_congr rfl fun k hk ↦ hstep k (Finset.mem_range.mp hk)
  have hlhs : p 0 - p ℓ = (1 - ρ ^ ℓ) * (x 0 - y 0 / r) := by
    simp only [hp, hx, hy, pow_zero, one_mul]; ring
  have hgeom : (1 - ρ) * ∑ k ∈ Finset.range ℓ, ρ ^ k = 1 - ρ ^ ℓ := by
    rw [mul_comm, geom_sum_mul_neg]
  have hbound : |∑ k ∈ Finset.range ℓ, ρ ^ k * y (k + 1)| ≤
      Y * ∑ k ∈ Finset.range ℓ, ρ ^ k := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 k), mul_comm]
    exact mul_le_mul_of_nonneg_right (hY (k + 1) (Finset.mem_range.mp hk)) (pow_nonneg hρ0 k)
  have hpos : 0 < 1 - ρ ^ ℓ := sub_pos.mpr (pow_lt_one₀ hρ0 hρ1 hℓ.ne')
  have hkey : (1 - ρ ^ ℓ) * (x 0 - y 0 / r) ≤ (1 - ρ ^ ℓ) * (Y / r) := by
    rw [← hlhs, hsum, ← Finset.sum_div, ← Finset.sum_mul]
    have h1 : -(∑ k ∈ Finset.range ℓ, ρ ^ k * y (k + 1)) ≤ Y * ∑ k ∈ Finset.range ℓ, ρ ^ k :=
      (neg_le_abs _).trans hbound
    rw [div_le_iff₀ hr]
    have h2 : 0 ≤ 1 - ρ := by linarith
    calc (∑ k ∈ Finset.range ℓ, ρ ^ k * y (k + 1)) * (ρ - 1)
        = (1 - ρ) * -(∑ k ∈ Finset.range ℓ, ρ ^ k * y (k + 1)) := by ring
      _ ≤ (1 - ρ) * (Y * ∑ k ∈ Finset.range ℓ, ρ ^ k) := mul_le_mul_of_nonneg_left h1 h2
      _ = (1 - ρ ^ ℓ) * (Y / r) * r := by rw [← hgeom]; field_simp
  have h3 := le_of_mul_le_mul_left hkey hpos
  have h4 : y 0 ≤ Y := (le_abs_self _).trans (hY 0 (Nat.zero_le _))
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hr] at h3
  linarith

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **A nonconstant polynomial is not a divisor or multiple of a nontrivial shift of itself.** -/
theorem not_comp_X_add_C_dvd {f : K[X]} (hf : 0 < f.natDegree) {h : K} (hh : h ≠ 0) :
    ¬ f.comp (X + C h) ∣ f ∧ ¬ f ∣ f.comp (X + C h) := by
  have hf0 : f ≠ 0 := fun h0 ↦ by simp [h0] at hf
  have hdeg : (f.comp (X + C h)).natDegree = f.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hlc : (f.comp (X + C h)).leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C,
      one_pow, mul_one]
  have hq0 : f.comp (X + C h) ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hdeg; omega
  -- if one divides the other, they are equal
  have hequal : ∀ {p q : K[X]}, p ≠ 0 → q ≠ 0 → p.natDegree = q.natDegree →
      p.leadingCoeff = q.leadingCoeff → p ∣ q → p = q := by
    intro p q hp hq hdpq hlpq ⟨t, ht⟩
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hq ht
    have htd : t.natDegree = 0 := by
      have := congrArg natDegree ht
      rw [natDegree_mul hp ht0] at this
      omega
    rw [eq_C_of_natDegree_eq_zero htd] at ht
    have hc : t.coeff 0 = 1 := by
      have := congrArg leadingCoeff ht
      rw [leadingCoeff_mul, leadingCoeff_C, ← hlpq] at this
      exact (mul_eq_left₀ (leadingCoeff_ne_zero.mpr hp)).mp this.symm
    rw [ht, hc, C_1, mul_one]
  -- a polynomial invariant under the shift is constant
  have hconst : f.comp (X + C h) ≠ f := by
    intro heq
    have hshift : ∀ x, f.eval (x + h) = f.eval x := fun x ↦ by
      have := congrArg (eval x) heq
      rwa [eval_comp, eval_add, eval_X, eval_C] at this
    have hn : ∀ n : ℕ, f.eval (n * h) = f.eval 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hshift, ih]
    have hzero : f - C (f.eval 0) = 0 := by
      refine eq_zero_of_infinite_isRoot _ (Set.Infinite.mono ?_
        (Set.infinite_range_of_injective (f := fun n : ℕ ↦ (n : K) * h) fun a b hab ↦ ?_))
      · rintro _ ⟨n, rfl⟩
        simp [IsRoot, hn n]
      · exact Nat.cast_injective (mul_right_cancel₀ hh hab)
    have := congrArg natDegree (sub_eq_zero.mp hzero)
    rw [natDegree_C] at this
    omega
  exact ⟨fun hd ↦ hconst (hequal hq0 hf0 hdeg hlc hd),
    fun hd ↦ hconst (hequal hf0 hq0 hdeg.symm hlc.symm hd).symm⟩

/-- **Exponential polynomials are linearly independent**: if `∑_i f_i(k) α_i ^ k = 0` for all
`k ∈ ℕ`, with distinct nonzero `α_i`, then all `f_i` vanish. -/
theorem eq_zero_of_forall_sum_eval_mul_pow_eq_zero {ι : Type*} [Fintype ι] {α : ι → K}
    (hα : Function.Injective α) (hα0 : ∀ i, α i ≠ 0) {f : ι → K[X]}
    (h : ∀ k : ℕ, ∑ i, (f i).eval (k : K) * α i ^ k = 0) (i : ι) : f i = 0 := by
  classical
  -- induction on `∑_i (deg f_i + 1)`, over the nonzero `f_i`
  let μ : K[X] → ℕ := fun p ↦ if p = 0 then 0 else p.natDegree + 1
  suffices H : ∀ n (f : ι → K[X]), ∑ i, μ (f i) = n →
      (∀ k : ℕ, ∑ i, (f i).eval (k : K) * α i ^ k = 0) → ∀ i, f i = 0 from H _ f rfl h i
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn h
  by_contra! hne
  obtain ⟨i₀, hi₀⟩ := hne
  -- apply `E - α_{i₀}`
  set g : ι → K[X] := fun j ↦ C (α j) * (f j).comp (X + C 1) - C (α i₀) * f j with hg
  have hgsum : ∀ k : ℕ, ∑ j, (g j).eval (k : K) * α j ^ k = 0 := fun k ↦ by
    have h1 := h (k + 1)
    have h0 := h k
    calc ∑ j, (g j).eval (k : K) * α j ^ k
        = ∑ j, (f j).eval ((k + 1 : ℕ) : K) * α j ^ (k + 1) -
            α i₀ * ∑ j, (f j).eval (k : K) * α j ^ k := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [hg, eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X]
          push_cast; ring
      _ = 0 := by rw [h1, h0, mul_zero, sub_zero]
  have hdeg : ∀ j, ((f j).comp (X + C 1)).natDegree = (f j).natDegree := fun j ↦ by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hcoeff : ∀ j, ((f j).comp (X + C 1)).coeff (f j).natDegree = (f j).leadingCoeff :=
    fun j ↦ by
      rw [← hdeg j, coeff_natDegree,
        leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C,
        one_pow, mul_one]
  have hgle : ∀ j, (g j).natDegree ≤ (f j).natDegree := fun j ↦
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (hdeg j).le)
      (natDegree_C_mul_le _ _))
  -- for `j ≠ i₀` the leading coefficient of `g j` is `(α j - α i₀) lc(f j)`
  have hgj : ∀ j, j ≠ i₀ → f j ≠ 0 → (g j).coeff (f j).natDegree ≠ 0 := fun j hj hf ↦ by
    simp only [hg, coeff_sub, coeff_C_mul, hcoeff, coeff_natDegree, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (hα.ne hj)) (leadingCoeff_ne_zero.mpr hf)
  have hμ : ∀ j, j ≠ i₀ → μ (g j) = μ (f j) := fun j hj ↦ by
    by_cases hf : f j = 0
    · simp [μ, hg, hf]
    · have hc := hgj j hj hf
      have hg0 : g j ≠ 0 := fun h0 ↦ by simp [h0] at hc
      simp only [μ, hf, hg0, ite_false,
        natDegree_eq_of_le_of_coeff_ne_zero (hgle j) hc]
  have hμ₀ : μ (g i₀) < μ (f i₀) := by
    simp only [μ, hi₀, ite_false]
    split_ifs with hg0
    · omega
    · -- `g i₀ = α i₀ (f(X + 1) - f(X))` has smaller degree
      have hc : (g i₀).coeff (f i₀).natDegree = 0 := by
        simp only [hg, coeff_sub, coeff_C_mul, hcoeff, coeff_natDegree, sub_self]
      have := hgle i₀
      have hne : (g i₀).natDegree ≠ (f i₀).natDegree := fun heq ↦ by
        rw [← heq, coeff_natDegree, leadingCoeff_eq_zero] at hc; exact hg0 hc
      omega
  have hlt : ∑ j, μ (g j) < n := hn ▸ Finset.sum_lt_sum
    (fun j _ ↦ if hj : j = i₀ then hj ▸ hμ₀.le else (hμ j hj).le) ⟨i₀, Finset.mem_univ _, hμ₀⟩
  have hg0 := ih _ hlt g rfl hgsum
  -- so every `f j` with `j ≠ i₀` vanishes
  have hf0 : ∀ j, j ≠ i₀ → f j = 0 := fun j hj ↦ by
    by_contra hf
    exact hgj j hj hf (by rw [hg0 j, coeff_zero])
  -- and then `f i₀` has infinitely many roots
  refine hi₀ (eq_zero_of_infinite_isRoot _ (Set.Infinite.mono ?_
    (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))))
  rintro _ ⟨k, rfl⟩
  have := h k
  rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by simp [hf0 j hj]) (by simp)] at this
  exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ (hα0 i₀))

end Polynomial
