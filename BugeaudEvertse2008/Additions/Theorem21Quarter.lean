/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.Additions.PlaneLiouville
public import BugeaudEvertse2008.Additions.SmallGap
public import BugeaudEvertse2008.Repetitions

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences

/-!
# Bugeaud–Evertse 2008, Theorem 2.1, with `1/4`

**The complexity of an algebraic irrational number is not `O(n (log n)^η)` for `η < 1/4`**: if
`ξ = ofDigits a` is real algebraic irrational, then `p(n) > C n (log n)^η` for infinitely many `n`,
for every `C` (`Real.frequently_lt_complexity_of_lt_quarter`). BE08 prove this for `η < 1/11`;
`BugeaudEvertse2008/Theorem21.lean` has `η < 1/7`.

Suppose instead `p(n) ≤ c n (log n)^u` for large `n`, `0 ≤ u < 1/4`, and pick `u < v < 1/4`.
Lemma 6.1 gives the points `x_n = (b^{t_n}, b^{r_n}, p_n)`, and `ε = (log t_{2N})^{-v}`. Split the
`N` points `N ≤ n < 2N` by their gap `s_n = t_n - r_n`:

* **Large gap** `ε t_n < 4 s_n`: the three-variable step puts them in `K₂ ε⁻⁴ (1 + log ε⁻¹)²`
  planes (`Real.exists_planes_of_approx`), each holding at most `K₃ (1 + log ε⁻¹)` of them
  (`Real.card_mem_plane_le_log`: Liouville's inequality on planes with `z₃ ≠ 0`, a window of the
  doubling sequence on the constant-gap planes).
* **Small gap** `4 s_n ≤ ε t_n`: the points `(b^{t_n} - b^{r_n}, p_n)` lie on
  `K₄ ε⁻³ (1 + log ε⁻¹)²` lines (`Real.exists_lines_of_small_gap`), at most one per line
  (`Int.dvd_of_pow_sub_pow_mul_eq`).

Hence `N ≤ (K₂ K₃ + K₄) ε⁻⁴ (1 + log ε⁻¹)³`, which is `< N` for large `N` since `4 v < 1`. The
exponent is `4 = 1 + 3` (classes, planes per class): a plane costs a logarithm instead of BE08's
second Subspace count `ε⁻³`. The split of the gap is the one of the `(3/2)^n` steering word
(`Stephan2026a/QuantitativeTheorem.lean`). The interval form of the quantitative Subspace Theorem
gives `η < 1/3` (`BugeaudEvertse2008/Additions/Theorem21Third.lean`).

## Main results

* `Real.frequently_lt_complexity_of_lt_quarter`: **Theorem 2.1** with `η < 1/4`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Theorem 2.1 and §7;
R. Stephan, *The exponent `1/4` in three complexity bounds: integer bases, continued fractions, and
the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), Theorem 1.1 and §3.
-/

@[expose] public section

open Filter Finset

namespace Real

variable {b : ℕ}

/-- **Bugeaud–Evertse 2008, Theorem 2.1, with `1/4` in place of `1/11`.** If the base-`b` digits
`a` of a real algebraic irrational number are given, then for every `η < 1/4` and every `C` the
complexity exceeds `C n (log n)^η` for infinitely many `n`.
First proved as Theorem 1.1 of Stephan's *The exponent `1/4` in three complexity bounds* (2026,
arXiv:2610.30937). -/
theorem frequently_lt_complexity_of_lt_quarter (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (ofDigits a)) (halg : IsAlgebraic ℚ (ofDigits a)) {η : ℝ} (hη : η < 1 / 4)
    (C : ℝ) : ∃ᶠ n : ℕ in atTop, C * n * log n ^ η < Function.complexity a n := by
  classical
  by_contra h
  rw [not_frequently] at h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  -- `p(n) ≤ c n (log n)^u` with `c = max C 1`, `u = max η 0`
  set u := max η 0 with hudef
  set c := max C 1 with hcdef
  have hu : 0 ≤ u := le_max_right _ _
  have hu4 : u < 1 / 4 := max_lt hη (by norm_num)
  have hp : ∀ n ≥ max n₀ 3, (Function.complexity a n : ℝ) ≤ c * n * log n ^ u := by
    intro n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hlog : 1 ≤ log n := by
      rw [le_log_iff_exp_le (by linarith)]
      have := exp_one_lt_d9
      linarith
    have h1 := not_lt.mp (hn₀ n ((le_max_left _ _).trans hn))
    have h2 : 0 ≤ (n : ℝ) * log n ^ η := by positivity
    calc (Function.complexity a n : ℝ) ≤ C * n * log n ^ η := h1
      _ = C * ((n : ℝ) * log n ^ η) := by ring
      _ ≤ c * ((n : ℝ) * log n ^ η) := by gcongr; exact le_max_left _ _
      _ ≤ c * ((n : ℝ) * log n ^ u) := by
          gcongr
          exact le_max_left _ _
      _ = c * n * log n ^ u := by ring
  -- `u < v < 1/4`
  set v := (u + 1 / 4) / 2 with hvdef
  have huv : u < v := by rw [hvdef]; linarith
  have hv : 0 < v := by linarith
  have hv4 : (4 : ℕ) * v < 1 := by push_cast; rw [hvdef]; linarith
  set ξ := ofDigits a with hξ
  obtain ⟨Cg, r, t, p, hrt, hgap, hbd, hdvd, hpb, happ⟩ :=
    exists_approx_of_complexity_le hb hu huv (max n₀ 3) hp
  have htm : StrictMono t := strictMono_nat_of_lt_succ fun n ↦ by have := hgap n; omega
  obtain ⟨K₂, hK₂, hT⟩ := exists_planes_of_approx hb halg
  obtain ⟨K₃, hK₃, hPl⟩ := card_mem_plane_le_log hb halg hirr
  obtain ⟨K₄, hK₄, hL⟩ := exists_lines_of_small_gap hb halg
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set K := K₂ + K₄ + K₂ * K₃ with hK
  have hK0 : 0 < K := by have := mul_pos hK₂ (by linarith : (0 : ℝ) < K₃); linarith
  obtain ⟨N, hN⟩ := (eventually_doubling_thresholds 4 3 (by norm_num) (by norm_num) (C := Cg) hv
    hv4 hK0 (log_pos hbR)).exists
  obtain ⟨hε0, hε1, hεle, hthr, hcount⟩ := hN t hgap hbd
  set ε := log (t (2 * N)) ^ (-v) with hε
  have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε0 |>.mpr hε1
  have hlogε : 0 ≤ log ε⁻¹ := log_nonneg hεinv
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hT ε hε0 hε1
  obtain ⟨T', hT'card, hT'top, hT'mem⟩ := hL ε hε0 hε1
  -- the points `x_n`, `N ≤ n < 2N`
  set I := Ico N (2 * N) with hI
  have happε : ∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    refine (happ n).trans (rpow_le_rpow_of_exponent_le (one_le_pow₀ hbR.le) ?_)
    exact neg_le_neg (hεle n hn1 hn2.le)
  have happ1 : ∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ 1 := fun n hn ↦
    (happε n hn).trans (rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hbR.le) (by linarith))
  have hthr' : ∀ n ∈ I, K₂ * ε⁻¹ ≤ t n * log b ∧ K₄ * ε⁻¹ ≤ t n * log b := by
    intro n hn
    have h := hthr n (mem_Ico.mp hn).1
    have : 0 ≤ ε⁻¹ := by positivity
    constructor <;> nlinarith [mul_nonneg (mul_nonneg hK₂.le (by linarith : (0 : ℝ) ≤ K₃)) this]
  -- the large gaps: planes
  set I₁ := I.filter fun n ↦ ε * t n < 4 * ((t n : ℝ) - r n) with hI₁
  set I₂ := I.filter fun n ↦ ¬ ε * t n < 4 * ((t n : ℝ) - r n) with hI₂
  have hφ : ∀ n ∈ I₁, ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U := fun n hn ↦
    have hnI := (mem_filter.mp hn).1
    hTmem (r n) (t n) (p n) (hrt n) (hpb n) (happε n hnI) (hthr' n hnI).1
  choose! φ hφT hφU using hφ
  set Y := 1 + log ε⁻¹ with hY
  have hfib : ∀ U ∈ T, (#(I₁.filter fun n ↦ φ n = U) : ℝ) ≤ K₃ * Y := by
    intro U hU
    refine hPl ε hε0 hε1 r t p hgap U (hTtop U hU) (I₁.filter fun n ↦ φ n = U)
      (fun n _ ↦ hrt n) (fun n _ ↦ hdvd n) (fun n _ ↦ hpb n)
      (fun n hn ↦ happ1 n (mem_filter.mp (mem_filter.mp hn).1).1)
      (fun n hn ↦ (mem_filter.mp (mem_filter.mp hn).1).2) (fun n hn ↦ ?_)
    obtain ⟨hn, hφn⟩ := mem_filter.mp hn
    rw [← hφn]; exact hφU n hn
  have hI₁card : (#I₁ : ℝ) ≤ #T * (K₃ * Y) := by
    have hsum := card_eq_sum_card_fiberwise (s := I₁) (t := T) (f := φ) hφT
    calc (#I₁ : ℝ) = ∑ U ∈ T, (#(I₁.filter fun n ↦ φ n = U) : ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T, K₃ * Y := sum_le_sum hfib
      _ = #T * (K₃ * Y) := by rw [sum_const, nsmul_eq_mul]
  -- the small gaps: lines, one point each
  have hψ : ∀ n ∈ I₂, ∃ U ∈ T', ![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)] ∈ U := by
    intro n hn
    obtain ⟨hnI, hsm⟩ := mem_filter.mp hn
    exact hT'mem (r n) (t n) (p n) (hrt n) (hpb n) (happε n hnI) (not_lt.mp hsm) (hthr' n hnI).2
  choose! ψ hψT hψU using hψ
  have hsmall : ∀ n ∈ I₂, 3 * t n ≤ 4 * r n := by
    intro n hn
    have h := not_lt.mp (mem_filter.mp hn).2
    have ht0 : (0 : ℝ) ≤ t n := Nat.cast_nonneg _
    have : (3 : ℝ) * t n ≤ 4 * r n := by nlinarith
    exact_mod_cast this
  have hlt : ∀ n ∈ I₂, ∀ m ∈ I₂, n < m → r n < r m := by
    intro n hn m hm hnm
    have h1 : 2 * t n < t m := (hgap n).trans_le (htm.monotone hnm)
    have := hsmall m hm
    have := hrt n
    omega
  have hone : ∀ n ∈ I₂, ∀ m ∈ I₂, n < m → ψ n ≠ ψ m := by
    intro n hn m hm hnm heq
    have hu := hψU n hn
    have hv := hψU m hm
    rw [heq] at hu
    have h := Submodule.det_eq_zero_of_forall_mem (hT'top _ (hψT m hm))
      ![![(b : ℚ) ^ t n - (b : ℚ) ^ r n, (p n : ℚ)], ![(b : ℚ) ^ t m - (b : ℚ) ^ r m, (p m : ℚ)]]
      (fun i ↦ by fin_cases i; exacts [hu, hv])
    rw [Matrix.det_fin_two] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    have h' : ((b : ℤ) ^ t n - (b : ℤ) ^ r n) * p m = ((b : ℤ) ^ t m - (b : ℤ) ^ r m) * p n := by
      have : ((b : ℚ) ^ t n - (b : ℚ) ^ r n) * p m = ((b : ℚ) ^ t m - (b : ℚ) ^ r m) * p n := by
        linear_combination h
      exact_mod_cast this
    have hr := hlt n hn m hm hnm
    exact hdvd m (by omega) (Int.dvd_of_pow_sub_pow_mul_eq (by exact_mod_cast (by omega : b ≠ 0))
      (hrt n) hr (hrt m).le h')
  have hI₂card : (#I₂ : ℝ) ≤ #T' := by
    have : #I₂ ≤ #T' := by
      refine card_le_card_of_injOn ψ (fun n hn ↦ hψT n hn) fun n hn m hm hnm ↦ ?_
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hone n hn m hm h hnm
      · exact hone m hm n hn h hnm.symm
    exact_mod_cast this
  -- `N ≤ (K₂ K₃ + K₄) ε⁻⁴ (1 + log ε⁻¹)³ < N`
  have hIcard : (N : ℝ) = #I₁ + #I₂ := by
    have hc := card_filter_add_card_filter_not (s := I) (fun n ↦ ε * t n < 4 * ((t n : ℝ) - r n))
    rw [hI, Nat.card_Ico, show 2 * N - N = N by omega] at hc
    rw [hI₁, hI₂]
    exact_mod_cast hc.symm
  have hY1 : 1 ≤ Y := by rw [hY]; linarith
  have hE : (1 : ℝ) ≤ ε⁻¹ ^ 4 := one_le_pow₀ hεinv
  have hfin : (N : ℝ) ≤ K * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 3 := by
    rw [← hY]
    have h1 : (#I₁ : ℝ) ≤ K₂ * K₃ * ε⁻¹ ^ 4 * Y ^ 3 := by
      calc (#I₁ : ℝ) ≤ #T * (K₃ * Y) := hI₁card
        _ ≤ K₂ * ε⁻¹ ^ 4 * Y ^ 2 * (K₃ * Y) := by gcongr
        _ = K₂ * K₃ * ε⁻¹ ^ 4 * Y ^ 3 := by ring
    have h2 : (#I₂ : ℝ) ≤ K₄ * ε⁻¹ ^ 4 * Y ^ 3 := by
      calc (#I₂ : ℝ) ≤ #T' := hI₂card
        _ ≤ K₄ * ε⁻¹ ^ 3 * Y ^ 2 := hT'card
        _ ≤ K₄ * ε⁻¹ ^ 4 * Y ^ 3 := by
            have : ε⁻¹ ^ 3 ≤ ε⁻¹ ^ 4 := pow_le_pow_right₀ hεinv (by norm_num)
            have : Y ^ 2 ≤ Y ^ 3 := pow_le_pow_right₀ hY1 (by norm_num)
            gcongr
    have h3 : 0 ≤ K₂ * ε⁻¹ ^ 4 * Y ^ 3 := by positivity
    rw [hIcard, hK]
    nlinarith
  linarith

end Real
