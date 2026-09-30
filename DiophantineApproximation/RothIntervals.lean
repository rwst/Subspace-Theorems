/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.CountingApproximations
public import DiophantineApproximation.LiouvilleInequality
public import DiophantineApproximation.RothInfinity

/-!
# Roth's theorem as an interval result

**Layer 3.7, restated for `N = 2`** in the form Layer 9.4 consumes. Above a height `L`, the
solutions `β ∈ K` of Roth's inequality `Λ(β) ≤ H(β) ^ (−κ)` have absolute height in the union of
at most `m (N + s).choose s` intervals `[Q, Q ^ M)`, with `m = rothChainLength κ s r`,
`M = rothRatio κ s r`, `N = rothClassSize κ s`, `s = |S|` and `r = [F : K]`
(`NumberField.exists_forall_mem_interval_of_prod_min_one_le`). This is the *interval result* of
the quantitative theory — Evertse's Theorem 3.1 has this shape — for the projective line, where
`β` is the point `(1 : β)`: the number of intervals depends on `κ`, `s` and `r` alone, and only
`L` and the intervals' positions depend on the targets.

The proof is the core of Roth's proof, `NumberField.roth_no_chain`, and a greedy covering
(`Finset.exists_subset_card_le_of_not_exists_chain`): in one approximation class there is no
chain of `m + 1` solutions whose logarithmic heights grow by the ratio `M`, so the lowest
solution, the lowest one at least `M` times higher, and so on, are at most `m` points whose
windows `[h, M h)` cover the class.

## Main results

* `Finset.exists_subset_card_le_of_not_exists_chain`: a finite set with no chain of `m + 1` points
  is covered by the windows `[h p, M h p)` of at most `m` of its points.
* `NumberField.exists_forall_mem_interval_of_prod_min_one_le`: **Roth's theorem as an interval
  result**.
* `NumberField.exists_forall_mem_interval_of_prod_onePointApprox_le`: the same with targets in
  `OnePoint F` and a constant, in logarithmic heights with a bounded shift, above the explicit
  threshold `NumberField.rothOnePointThreshold` — the form `RothSubspaceCount.lean` feeds to
  Layer 9.4.
* `NumberField.rothOnePointBound`: that threshold as a function of scalars, monotone in the
  heights of the targets and the constant (`NumberField.rothOnePointBound_mono`).
* `NumberField.mobiusConst_le_exp`: the distortion constant of the Möbius change of variable,
  bounded by the heights of the targets through Liouville's inequality at one place.
* `NumberField.mulHeight₁_rpow_inv_finrank`: the absolute height is `exp` of the absolute
  logarithmic height.

## Implementation notes

⚠ **This is the interval result, not its count.** 6.5.7
(`NumberField.ncard_setOf_lt_absLogHeight₁_le`) bounds the number of large solutions by
counting each interval with the gap principle; here the intervals are the conclusion and no gap
principle is used. Evertse's covering (Layer 9.4) turns intervals into a count of subspaces; the
link, which reads a normalized system in `K ^ 2` as Roth's inequality, is
`DiophantineApproximation/RothSubspaceCount.lean`.

⚠ **Targets at infinity cost a shift, not a ratio.** The Möbius change of variable
`β ↦ (β - j)⁻¹` of Layer 3.3 moves the absolute logarithmic height by at most
`e = mobiusShift s = log (2 (s + 1))`, so the windows of the second form are `[t - e, M t + e)`;
the constant in front of the height is absorbed by lowering the exponent to `(κ + 2) / 2` and
raising the threshold.

⚠ **The base point is a small integer, so the threshold is explicit.** Among `0, …, s` one
natural number `j` is none of the `s` targets. Its height is at most `log (s + 1)`, and at a
finite target `a` Liouville's inequality at one place gives `min 1 |a - j|_w ≥ H(a - j)⁻¹`, which
bounds the distortion constant by `2 H(a - j) ^ 2`. A base point taken from the complement of
the targets, as in `NumberField.finite_setOf_prod_onePointApprox_le`, has no such bound.

⚠ **The threshold may be raised.** The conclusion holds for every `L' ≥ L`, with every `Q` above
`exp L'`, so that a consumer can impose its own lower bound on the intervals, as 9.4 imposes
`Q ≥ n ^ (2 n / δ)`. Heights in the intervals are absolute, `mulHeight₁ β ^ (1 / [K : ℚ])`, as in
Layer 9; the ratio `M` is the same in both normalizations.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.5.7. J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377**
(2010), 217–240 (arXiv:1008.2268), Theorem 3.1 and the proof of Theorem 2.1.

This is Layer 3.7 of the `DiophantineApproximation` roadmap, restated as Layer 9.4 asks.
-/

@[expose] public section

open Height Module

namespace Finset

/-- **A finite set without long chains is covered by few windows.** If `T` contains no chain of
`m + 1` points each with height at least `M` times the height of the previous one, then at most
`m` points of `T` have windows `[h p, M h p)` covering `T`. The proof is the greedy grouping of
`Finset.card_le_mul_of_not_exists_chain`. -/
theorem exists_subset_card_le_of_not_exists_chain {α : Type*} (h : α → ℝ) (M : ℝ) :
    ∀ (m : ℕ) (T : Finset α),
      (¬ ∃ s : Fin (m + 1) → α, (∀ j, s j ∈ T) ∧
        ∀ j : Fin m, M * h (s j.castSucc) ≤ h (s j.succ)) →
      ∃ P ⊆ T, P.card ≤ m ∧ ∀ x ∈ T, ∃ p ∈ P, h p ≤ h x ∧ h x < M * h p := by
  classical
  intro m
  induction m with
  | zero =>
      intro T hchain
      refine ⟨∅, Finset.empty_subset _, le_rfl, fun x hx ↦ ?_⟩
      exact absurd ⟨fun _ ↦ x, fun _ ↦ hx, fun j ↦ j.elim0⟩ hchain
  | succ m ih =>
      intro T hchain
      rcases T.eq_empty_or_nonempty with hT | hT
      · exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp [hT]⟩
      obtain ⟨x₀, hx₀, hmin⟩ := T.exists_min_image h hT
      obtain ⟨P, hPT, hPcard, hP⟩ := ih {y ∈ T | M * h x₀ ≤ h y} fun ⟨s, hsT, hs⟩ ↦ by
        refine hchain ⟨Fin.cons x₀ s, fun j ↦ ?_, fun j ↦ ?_⟩
        · refine Fin.cases ?_ (fun j ↦ ?_) j
          · simpa using hx₀
          · simpa using (Finset.mem_filter.mp (hsT j)).1
        · refine Fin.cases ?_ (fun j ↦ ?_) j
          · simpa using (Finset.mem_filter.mp (hsT 0)).2
          · simpa [← Fin.succ_castSucc] using hs j
      refine ⟨insert x₀ P, Finset.insert_subset hx₀ (hPT.trans (Finset.filter_subset _ _)),
        (Finset.card_insert_le _ _).trans (by omega), fun x hx ↦ ?_⟩
      by_cases hMx : M * h x₀ ≤ h x
      · obtain ⟨p, hp, hpx⟩ := hP x (Finset.mem_filter.mpr ⟨hx, hMx⟩)
        exact ⟨p, Finset.mem_insert_of_mem hp, hpx⟩
      · exact ⟨x₀, Finset.mem_insert_self _ _, hmin x hx, not_le.mp hMx⟩

end Finset

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

omit [NumberField F] in
/-- The absolute multiplicative height is the exponential of the absolute logarithmic one. -/
theorem mulHeight₁_rpow_inv_finrank (β : K) :
    mulHeight₁ β ^ ((finrank ℚ K : ℝ)⁻¹) = Real.exp (absLogHeight₁ β) := by
  rw [Real.rpow_def_of_pos (mulHeight₁_pos β), absLogHeight₁_eq_inv_mul_logHeight₁,
    logHeight₁_eq_log_mulHeight₁, mul_comm]

/-- **Roth's theorem as an interval result** (Layer 3.7 restated for `N = 2`, the form Evertse's
covering of Layer 9.4 consumes). For every `L'` at least `L = rothLargeThreshold`, which is
linear in the heights of the targets, the solutions `β` of `Λ(β) ≤ H(β) ^ (−κ)` with absolute
logarithmic height above `L'` have absolute height `H(β) = mulHeight₁ β ^ (1 / [K : ℚ])` in the
union of at most `m (N + s).choose s` intervals `[Q i, Q i ^ M)`, all with `Q i > exp L'`. Here
`m = rothChainLength κ s r`, `M = rothRatio κ s r`, `N = rothClassSize κ s`, `s = |S|` and
`r = [F : K]`, so the number of intervals depends on `κ`, `s` and `r` alone. -/
theorem exists_forall_mem_interval_of_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∀ L' : ℝ, rothLargeThreshold Sinf Sfin α κ ≤ L' → ∃ k : ℕ,
      k ≤ rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) *
        (rothClassSize κ (Sinf.card + Sfin.card) + (Sinf.card + Sfin.card)).choose
          (Sinf.card + Sfin.card) ∧
      ∃ Q : Fin k → ℝ, (∀ i, Real.exp L' < Q i) ∧
        ∀ β : K, (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
            ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) →
          L' < absLogHeight₁ β →
          ∃ i, Q i ≤ mulHeight₁ β ^ ((finrank ℚ K : ℝ)⁻¹) ∧
            mulHeight₁ β ^ ((finrank ℚ K : ℝ)⁻¹) <
              Q i ^ rothRatio κ (Sinf.card + Sfin.card) (finrank K F) := by
  classical
  set s := Sinf.card + Sfin.card with hsdef
  set r := finrank K F with hrdef
  set N := rothClassSize κ s with hNdef
  set m := rothChainLength κ s r with hmdef
  set M := rothRatio κ s r with hMdef
  have hκ0 : 0 < κ := by linarith
  have hN : 0 < N := (rothClassSize_spec hκ s).1
  have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = s := by
    rw [hsdef, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  have hLr := roth_no_chain Sinf Sfin w hwInf hwFin α hκ
  set Lr := rothThreshold Sinf Sfin α κ with hLrdef
  intro L' hL'
  set U : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      L' < absLogHeight₁ β} with hUdef
  -- finiteness from the count of 6.5.7, not from Roth's theorem
  have hUfin : U.Finite :=
    (ncard_setOf_lt_absLogHeight₁_le Sinf Sfin w hwInf hwFin α hκ).1.subset fun β hβ ↦
      ⟨hβ.1, lt_of_le_of_lt hL' hβ.2⟩
  have hgap := one_lt_rothGap hκ s
  rw [← hNdef] at hgap
  have hX₀ : 0 < Real.log 16 / ((1 - (s : ℝ) / N) * κ - 1 - 1) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  have hthr : rothLargeThreshold Sinf Sfin α κ
      = max (Lr / totalWeight K) (Real.log 16 / ((1 - (s : ℝ) / N) * κ - 1 - 1)) := rfl
  replace hL' : max (Lr / totalWeight K) 0 ≤ L' := by
    rw [hthr] at hL'
    exact max_le ((le_max_left _ _).trans hL') (hX₀.le.trans ((le_max_right _ _).trans hL'))
  have hsolU : ∀ β ∈ U, ∏ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ) :=
    fun β hβ ↦ by
      rw [prod_localApprox]
      exact hβ.1
  have hposU : ∀ β ∈ U, 0 < absLogHeight₁ β := fun β hβ ↦
    lt_of_le_of_lt ((le_max_right _ _).trans hL') hβ.2
  have hHU : ∀ β ∈ U, 1 < mulHeight₁ β := fun β hβ ↦ by
    have h1 : 0 < logHeight₁ β := by
      rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
      exact mul_pos hd (hposU β hβ)
    rw [logHeight₁_eq_log_mulHeight₁] at h1
    exact (Real.log_pos_iff (mulHeight₁_pos _).le).mp h1
  have hLU : ∀ β ∈ U, Lr ≤ logHeight₁ β := fun β hβ ↦ by
    have h1 := lt_of_le_of_lt ((le_max_left _ _).trans hL') hβ.2
    rw [div_lt_iff₀ hd] at h1
    rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
    linarith
  set U' : Finset K := hUfin.toFinset with hU'def
  have hmemU : ∀ β ∈ U', β ∈ U := fun β hβ ↦ hUfin.mem_toFinset.mp hβ
  -- one class at a time: at most `m` windows
  have hfiber : ∀ c₀ : (↥Sinf ⊕ ↥Sfin) → ℕ, ∃ P ⊆ {β ∈ U' | approxClass Sinf Sfin w α N β = c₀},
      P.card ≤ m ∧ ∀ x ∈ {β ∈ U' | approxClass Sinf Sfin w α N β = c₀}, ∃ p ∈ P,
        absLogHeight₁ p ≤ absLogHeight₁ x ∧ absLogHeight₁ x < M * absLogHeight₁ p := by
    intro c₀
    refine Finset.exists_subset_card_le_of_not_exists_chain absLogHeight₁ M m _ ?_
    rintro ⟨sq, hsq, hchain⟩
    have hsqU : ∀ j, sq j ∈ U := fun j ↦ hmemU _ (Finset.mem_filter.mp (hsq j)).1
    have hsqc : ∀ j, approxClass Sinf Sfin w α N (sq j) = c₀ :=
      fun j ↦ (Finset.mem_filter.mp (hsq j)).2
    have hsum := one_sub_card_div_le_sum_approxClass hκ0 hN (hsolU _ (hsqU 0)) (hHU _ (hsqU 0))
    rw [hsqc 0] at hsum
    refine hLr (fun a ↦ (c₀ a : ℝ) / N) (fun a ↦ by positivity) hsum sq (hLU _ (hsqU 0))
      (fun j ↦ ?_) fun j a ↦ ?_
    · rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁,
        logHeight₁_eq_totalWeight_mul_absLogHeight₁]
      have h1 := mul_le_mul_of_nonneg_left (hchain j) hd.le
      linarith
    · have h1 := localApprox_le_rpow_approxClass hκ0 hN (hsolU _ (hsqU j)) (hHU _ (hsqU j)) a
      rw [hsqc j] at h1
      exact h1
  choose P hPsub hPcard hP using hfiber
  -- all classes together
  set C := U'.image (approxClass Sinf Sfin w α N) with hCdef
  set Pt := C.biUnion P with hPtdef
  have himage : C.card ≤ (N + s).choose s := by
    have h1 := Set.ncard_le_ncard (s := ↑C)
      (t := {c' : (↥Sinf ⊕ ↥Sfin) → ℕ | ∑ a, c' a ≤ N}) (fun c' hc' ↦ by
        obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hc'
        exact sum_approxClass_le Sinf Sfin w α N β) (Set.finite_setOf_sum_le _ N)
    rw [Set.ncard_coe_finset, Set.ncard_setOf_sum_le, hcard] at h1
    exact h1
  have hPtcard : Pt.card ≤ m * (N + s).choose s :=
    calc Pt.card ≤ ∑ c₀ ∈ C, (P c₀).card := Finset.card_biUnion_le
      _ ≤ ∑ _c₀ ∈ C, m := Finset.sum_le_sum fun c₀ _ ↦ hPcard c₀
      _ = C.card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (N + s).choose s * m := Nat.mul_le_mul_right _ himage
      _ = m * (N + s).choose s := mul_comm _ _
  have hPtU : ∀ p ∈ Pt, p ∈ U := fun p hp ↦ by
    obtain ⟨c₀, -, hp⟩ := Finset.mem_biUnion.mp hp
    exact hmemU p (Finset.mem_filter.mp (hPsub c₀ hp)).1
  refine ⟨Pt.card, hPtcard, fun i ↦ Real.exp (absLogHeight₁ (Pt.equivFin.symm i : K)),
    fun i ↦ Real.exp_lt_exp.mpr (hPtU _ (Pt.equivFin.symm i).2).2, fun β hβ hβL ↦ ?_⟩
  have hβU' : β ∈ U' := hUfin.mem_toFinset.mpr ⟨hβ, hβL⟩
  obtain ⟨p, hp, hlo, hhi⟩ := hP (approxClass Sinf Sfin w α N β) β
    (Finset.mem_filter.mpr ⟨hβU', rfl⟩)
  have hpPt : p ∈ Pt := Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem _ hβU', hp⟩
  refine ⟨Pt.equivFin ⟨p, hpPt⟩, ?_⟩
  simp only [Equiv.symm_apply_apply, mulHeight₁_rpow_inv_finrank]
  refine ⟨Real.exp_le_exp.mpr hlo, ?_⟩
  rw [← Real.exp_mul, mul_comm]
  exact Real.exp_lt_exp.mpr hhi

/-!
### The Möbius base point, in heights

The base point `c` of the change of variable `β ↦ (β - c)⁻¹` is a natural number `j ≤ |S|`
missing from the `|S|` targets, so `h(c) + log 2 ≤ log (2 (|S| + 1))`: that is the shift `e`.
Liouville's inequality at one place bounds the distortion constant at a finite target `a` by
`2 H(a - c) ^ 2`, a height.
-/

/-- The shift of absolute logarithmic heights under the Möbius change of variable with a base
point `j ≤ s`: `log (2 (s + 1))`. -/
noncomputable def mobiusShift (s : ℕ) : ℝ := Real.log (2 * ((s : ℝ) + 1))

theorem mobiusShift_nonneg (s : ℕ) : 0 ≤ mobiusShift s :=
  Real.log_nonneg (by have : (0 : ℝ) ≤ s := s.cast_nonneg; linarith)

open OnePoint in
/-- The absolute logarithmic height of a target in `OnePoint F`, with `0` at `∞`. -/
noncomputable def onePointHeight : OnePoint F → ℝ
  | ∞ => 0
  | (a : F) => absLogHeight₁ a

@[simp] theorem onePointHeight_infty : onePointHeight (OnePoint.infty : OnePoint F) = 0 := rfl

@[simp] theorem onePointHeight_coe (a : F) : onePointHeight (a : OnePoint F) = absLogHeight₁ a :=
  rfl

theorem onePointHeight_nonneg (t : OnePoint F) : 0 ≤ onePointHeight t := by
  induction t with
  | infty => exact le_rfl
  | coe a => exact absLogHeight₁_nonneg a

/-- The absolute logarithmic height of a sum exceeds the sum of the heights by at most `log 2`. -/
theorem absLogHeight₁_add_le (x y : K) :
    absLogHeight₁ (x + y) ≤ absLogHeight₁ x + absLogHeight₁ y + Real.log 2 := by
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have h := logHeight₁_add_le x y
  rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁, logHeight₁_eq_totalWeight_mul_absLogHeight₁,
    logHeight₁_eq_totalWeight_mul_absLogHeight₁, totalWeight_eq_finrank] at h
  refine le_of_mul_le_mul_left ?_ hd
  linarith

/-- The absolute logarithmic height of a difference exceeds the sum of the heights by at most
`log 2`. -/
theorem absLogHeight₁_sub_le (x y : K) :
    absLogHeight₁ (x - y) ≤ absLogHeight₁ x + absLogHeight₁ y + Real.log 2 := by
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have h := logHeight₁_sub_le x y
  rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁, logHeight₁_eq_totalWeight_mul_absLogHeight₁,
    logHeight₁_eq_totalWeight_mul_absLogHeight₁, totalWeight_eq_finrank] at h
  refine le_of_mul_le_mul_left ?_ hd
  linarith

theorem absLogHeight₁_inv (x : K) : absLogHeight₁ x⁻¹ = absLogHeight₁ x := by
  rw [absLogHeight₁_eq_inv_mul_logHeight₁, absLogHeight₁_eq_inv_mul_logHeight₁, logHeight₁_inv]

/-- The absolute logarithmic height of a natural number `j` is at most `log (j + 1)`. -/
theorem absLogHeight₁_natCast_le (j : ℕ) : absLogHeight₁ (j : K) ≤ Real.log (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [absLogHeight₁_zero]
  · have : NeZero j := ⟨hj.ne'⟩
    have h1 : absLogHeight₁ (j : K) = absLogHeight₁ (j : ℚ) := by
      rw [← absLogHeight₁_comp (Algebra.ofId ℚ K) (j : ℚ), map_natCast]
    rw [h1, absLogHeight₁_eq_inv_mul_logHeight₁, Module.finrank_self, Rat.logHeight₁_natCast,
      Nat.cast_one, inv_one, one_mul]
    exact Real.log_le_log (by exact_mod_cast hj) (by linarith)

/-- A base point `j ≤ s` costs at most the shift: `h(j) + log 2 ≤ log (2 (s + 1))`. -/
theorem absLogHeight₁_natCast_add_log_two_le {j s : ℕ} (hjs : j ≤ s) :
    absLogHeight₁ (j : K) + Real.log 2 ≤ mobiusShift s := by
  have hj : (j : ℝ) ≤ s := by exact_mod_cast hjs
  have h0 : (0 : ℝ) ≤ j := j.cast_nonneg
  calc absLogHeight₁ (j : K) + Real.log 2 ≤ Real.log (j + 1) + Real.log 2 := by
        linarith [absLogHeight₁_natCast_le (K := K) j]
    _ = Real.log (2 * ((j : ℝ) + 1)) := by
        rw [Real.log_mul (by norm_num) (by linarith)]; ring
    _ ≤ mobiusShift s := Real.log_le_log (by linarith) (by linarith)

/-- The moved target has height at most the target's plus the shift. -/
theorem absLogHeight₁_onePointMobius_le {j s : ℕ} (hjs : j ≤ s) (t : OnePoint F) :
    absLogHeight₁ (AbsoluteValue.onePointMobius (j : F) t) ≤ onePointHeight t + mobiusShift s := by
  induction t with
  | infty =>
      rw [AbsoluteValue.onePointMobius_infty, absLogHeight₁_zero, onePointHeight_infty, zero_add]
      exact mobiusShift_nonneg s
  | coe a =>
      rw [AbsoluteValue.onePointMobius_coe, absLogHeight₁_inv, onePointHeight_coe]
      linarith [absLogHeight₁_sub_le a (j : F), absLogHeight₁_natCast_add_log_two_le (K := F) hjs]

/-- **The distortion constant, bounded by heights.** At an absolute value `W` of `F` satisfying
Liouville's inequality `H(x)⁻¹ ≤ min 1 |x|_W`, the constant of the Möbius change of variable with
base point `j ≤ s` at a target `t ≠ j` is at most `exp (log 2 + 2 [F : ℚ] (h(t) + e))`. -/
theorem mobiusConst_le_exp (W : AbsoluteValue F ℝ)
    (hW : ∀ x : F, x ≠ 0 → (mulHeight₁ x)⁻¹ ≤ min 1 (W x)) {j s : ℕ} (hjs : j ≤ s)
    {t : OnePoint F} (ht : t ≠ ((j : F) : OnePoint F)) :
    W.mobiusConst (j : F) t
      ≤ Real.exp (Real.log 2 + 2 * finrank ℚ F * (onePointHeight t + mobiusShift s)) := by
  have hn : (1 : ℝ) ≤ finrank ℚ F := by exact_mod_cast finrank_pos
  have he := mobiusShift_nonneg s
  induction t with
  | infty =>
      rw [AbsoluteValue.mobiusConst_infty, onePointHeight_infty, zero_add]
      have hj : W (j : F) ≤ s := (W.apply_nat_le_self j).trans (by exact_mod_cast hjs)
      calc 1 + W (j : F) ≤ 2 * ((s : ℝ) + 1) := by
            have : (0 : ℝ) ≤ s := s.cast_nonneg; linarith
        _ = Real.exp (mobiusShift s) := by
            rw [mobiusShift, Real.exp_log (by have : (0 : ℝ) ≤ s := s.cast_nonneg; linarith)]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  | coe a =>
      have hac : a - (j : F) ≠ 0 := sub_ne_zero.mpr fun h ↦ ht (by rw [h])
      refine (W.mobiusConst_coe_le (mulHeight₁_pos _) (hW _ hac)).trans ?_
      have hH : mulHeight₁ (a - (j : F))
          = Real.exp (finrank ℚ F * absLogHeight₁ (a - (j : F))) := by
        rw [absLogHeight₁_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
          Real.exp_log (mulHeight₁_pos _)]
      have hsub : absLogHeight₁ (a - (j : F)) ≤ absLogHeight₁ a + mobiusShift s := by
        linarith [absLogHeight₁_sub_le a (j : F), absLogHeight₁_natCast_add_log_two_le (K := F) hjs]
      rw [hH, onePointHeight_coe]
      calc 2 * Real.exp (finrank ℚ F * absLogHeight₁ (a - (j : F))) ^ 2
          = Real.exp (Real.log 2 + 2 * finrank ℚ F * absLogHeight₁ (a - (j : F))) := by
            rw [Real.exp_add, Real.exp_log (by norm_num), sq, ← Real.exp_add]
            congr 2
            ring
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- **The threshold of Roth's interval result with targets at infinity, in scalars**: `s = |S|`,
`r = [F : K]`, `nF = [F : ℚ]`, `nK = [K : ℚ]`, the sum `Ht` of the absolute heights of the
targets, `logC = log (max C 1)` and the exponent `κ`. With `κ₁ = (κ + 2) / 2` and the shift
`e = mobiusShift s`, it is the largest of the threshold of the count at `κ₁` for the moved
targets, whose heights add up to at most `Ht + s e`, and the height above which the distortion
constant `C · ∏ exp (log 2 + 2 nF (h(t) + e))` is absorbed by lowering the exponent from `κ` to
`κ₁`. It is monotone in `Ht` and `logC` (`NumberField.rothOnePointBound_mono`). -/
noncomputable def rothOnePointBound (s r nF nK : ℕ) (Ht logC κ : ℝ) : ℝ :=
  max (max ((1 + Ht + s * mobiusShift s) / rothDelta ((κ + 2) / 2) s r nF)
      (Real.log 16 / ((1 - (s : ℝ) / rothClassSize ((κ + 2) / 2) s) * ((κ + 2) / 2) - 1 - 1)))
    ((2 * s * Real.log 2 + 4 * nF * (Ht + s * mobiusShift s) + logC + κ * nK * mobiusShift s)
      / ((κ - 2) / 2 * nK))

theorem rothOnePointBound_mono {s r nF nK : ℕ} {Ht Ht' logC logC' κ : ℝ} (hκ : 2 < κ)
    (hHt : Ht ≤ Ht') (hC : logC ≤ logC') :
    rothOnePointBound s r nF nK Ht logC κ ≤ rothOnePointBound s r nF nK Ht' logC' κ := by
  have hδ := rothDelta_pos (by linarith : 2 < (κ + 2) / 2) s r (Nat.cast_nonneg nF)
  have hnF : (0 : ℝ) ≤ nF := nF.cast_nonneg
  have hnK : (0 : ℝ) ≤ nK := nK.cast_nonneg
  refine max_le_max (max_le_max ?_ le_rfl) ?_
  · exact div_le_div_of_nonneg_right (by linarith) hδ.le
  · exact div_le_div_of_nonneg_right (by nlinarith) (mul_nonneg (by linarith) hnK)

/-- **The threshold of Roth's interval result with targets at infinity**, a formula in the
absolute heights `h(t)` of the targets, the constant `C`, `κ`, `s = |S|` and the degrees: the
scalar threshold `NumberField.rothOnePointBound` at `Ht = ∑ h(t)` and `logC = log (max C 1)`. -/
noncomputable def rothOnePointThreshold (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (α : AbsoluteValue K ℝ → OnePoint F) (C κ : ℝ) : ℝ :=
  rothOnePointBound (Sinf.card + Sfin.card) (finrank K F) (finrank ℚ F) (finrank ℚ K)
    (∑ a : ↥Sinf ⊕ ↥Sfin, onePointHeight (α (sPlaceAbsValue a))) (Real.log (max C 1)) κ

/-- **Roth's theorem with targets at infinity, as an interval result** (Layers 3.3 and 3.7). For
targets in `OnePoint F` and a constant `C` in front of the height, for every `L'` at least the
explicit `rothOnePointThreshold Sinf Sfin α C κ`, the solutions with absolute logarithmic height
above `L' + e` have it in the union of at most `m (N + s).choose s` shifted windows
`[t i - e, M t i + e)`, all with `t i > L'`, where `e = mobiusShift s = log (2 (s + 1))`. Here
`m`, `M` and `N` are Roth's parameters at the exponent `(κ + 2) / 2`. The Möbius change of
variable `β ↦ (β - j)⁻¹` of Layer 3.3, with a natural number `j ≤ s` that is none of the
targets, moves the targets to finite ones and the heights by at most `e`; Liouville's inequality
at one place bounds its distortion constant by the heights of the targets. -/
theorem exists_forall_mem_interval_of_prod_onePointApprox_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) (C : ℝ) {κ : ℝ} (hκ : 2 < κ) :
    ∀ L' : ℝ, rothOnePointThreshold Sinf Sfin α C κ ≤ L' → ∃ k : ℕ,
      k ≤ rothChainLength ((κ + 2) / 2) (Sinf.card + Sfin.card) (finrank K F) *
        (rothClassSize ((κ + 2) / 2) (Sinf.card + Sfin.card) + (Sinf.card + Sfin.card)).choose
          (Sinf.card + Sfin.card) ∧
      ∃ t : Fin k → ℝ, (∀ i, L' < t i) ∧
        ∀ β : K, (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
            ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
              ≤ C * mulHeight₁ β ^ (-κ) →
          L' + mobiusShift (Sinf.card + Sfin.card) < absLogHeight₁ β →
          ∃ i, t i - mobiusShift (Sinf.card + Sfin.card) ≤ absLogHeight₁ β ∧ absLogHeight₁ β <
            rothRatio ((κ + 2) / 2) (Sinf.card + Sfin.card) (finrank K F) * t i
              + mobiusShift (Sinf.card + Sfin.card) := by
  classical
  intro L' hL'
  -- a base point `j ≤ |S|` of the Möbius change of variable that is none of the targets
  obtain ⟨j, hjs, hc⟩ : ∃ j : ℕ, j ≤ Sinf.card + Sfin.card ∧ ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) → α v ≠ (((j : F) : F) : OnePoint F) := by
    set T : Finset (OnePoint F) :=
      Sinf.image (fun u ↦ α u.1) ∪ Sfin.image (fun u ↦ α u.1) with hTdef
    set R : Finset (OnePoint F) := (Finset.range (Sinf.card + Sfin.card + 1)).image
      (fun n : ℕ ↦ ((n : F) : OnePoint F)) with hRdef
    have hR : R.card = Sinf.card + Sfin.card + 1 := by
      rw [hRdef, Finset.card_image_of_injective _ fun m n h ↦ ?_, Finset.card_range]
      exact_mod_cast OnePoint.coe_injective h
    have hT : T.card ≤ Sinf.card + Sfin.card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    obtain ⟨x, hxR, hxT⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := T) (t := R)
      (by omega)
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hxR
    refine ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), fun v hv hcon ↦ hxT ?_⟩
    rw [← hcon]
    rcases hv with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
  set c : K := (j : K) with hcdef
  set c' : F := algebraMap K F c with hc'def
  have hc'j : c' = (j : F) := by rw [hc'def, hcdef, map_natCast]
  have hc' : ∀ v : AbsoluteValue K ℝ, ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) →
      α v ≠ (c' : OnePoint F) := by
    rw [hc'j]; exact hc
  set e : ℝ := mobiusShift (Sinf.card + Sfin.card) with hedef
  have he0 : 0 ≤ e := mobiusShift_nonneg _
  have hce : absLogHeight₁ c + Real.log 2 ≤ e := absLogHeight₁_natCast_add_log_two_le hjs
  set α' : AbsoluteValue K ℝ → F := fun u ↦ AbsoluteValue.onePointMobius c' (α u) with hα'def
  -- the constants
  set Cfun : AbsoluteValue K ℝ → ℝ := fun u ↦ (w u).mobiusConst c' (α u) with hCfundef
  set Ctot : ℝ := (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) * ∏ v ∈ Sfin, Cfun v.1 with hCtotdef
  have hCfun1 : ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) → 1 ≤ Cfun v :=
    fun v hv ↦ AbsoluteValue.one_le_mobiusConst _ (hc' v hv)
  have hCtot1 : 1 ≤ Ctot := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · exact Finset.one_le_prod₀ fun u hu ↦ one_le_pow₀ (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))
    · exact Finset.one_le_prod₀ fun u hu ↦ hCfun1 u.1 (Or.inr ⟨u, hu, rfl⟩)
  -- the constants, bounded by heights
  set b : AbsoluteValue K ℝ → ℝ :=
    fun v ↦ Real.log 2 + 2 * finrank ℚ F * (onePointHeight (α v) + e) with hbdef
  have hb0 : ∀ v, 0 ≤ b v := fun v ↦ by
    have := onePointHeight_nonneg (α v)
    have : (0 : ℝ) ≤ finrank ℚ F := (finrank ℚ F).cast_nonneg
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    simp only [hbdef]; positivity
  have hCb : ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) → Cfun v ≤ Real.exp (b v) := by
    intro v hv
    have hW : ∀ x : F, x ≠ 0 → (mulHeight₁ x)⁻¹ ≤ min 1 (w v x) := by
      rcases hv with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact fun x hx ↦ inv_mulHeight₁_le_min_one_of_infinitePlace u (hwInf u hu) hx
      · exact fun x hx ↦ inv_mulHeight₁_le_min_one_of_finitePlace u (hwFin u hu) hx
    simp only [hCfundef, hbdef, hc'j]
    exact mobiusConst_le_exp (w v) hW hjs (hc v hv)
  have hCtotle : Ctot ≤ Real.exp (∑ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a)) := by
    have hsplit : ∑ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a)
        = ∑ v ∈ Sinf, 2 * b v.1 + ∑ v ∈ Sfin, 2 * b v.1 := by
      rw [Fintype.sum_sum_type, ← Finset.sum_coe_sort Sinf fun v ↦ 2 * b v.1,
        ← Finset.sum_coe_sort Sfin fun v ↦ 2 * b v.1]
      rfl
    rw [hsplit, Real.exp_add, Real.exp_sum, Real.exp_sum, hCtotdef]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun u hu ↦
      le_trans zero_le_one (hCfun1 u.1 (Or.inr ⟨u, hu, rfl⟩)))
      (Finset.prod_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    · refine Finset.prod_le_prod₀ (fun u hu ↦
        pow_nonneg (le_trans zero_le_one (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))) _) fun u hu ↦ ?_
      have h2 : u.mult ≤ 2 := sPlaceWeight_le_two (Sfin := Sfin) (Sum.inl ⟨u, hu⟩)
      calc Cfun u.1 ^ u.mult ≤ Real.exp (b u.1) ^ u.mult :=
            pow_le_pow_left₀ (le_trans zero_le_one (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩)))
              (hCb u.1 (Or.inl ⟨u, hu, rfl⟩)) _
        _ ≤ Real.exp (b u.1) ^ 2 := pow_le_pow_right₀ (Real.one_le_exp (hb0 _)) h2
        _ = Real.exp (2 * b u.1) := by rw [← Real.exp_nat_mul]; norm_num
    · refine Finset.prod_le_prod₀ (fun u hu ↦
        le_trans zero_le_one (hCfun1 u.1 (Or.inr ⟨u, hu, rfl⟩))) fun u hu ↦ ?_
      exact (hCb u.1 (Or.inr ⟨u, hu, rfl⟩)).trans (Real.exp_le_exp.mpr (by linarith [hb0 u.1]))
  -- heights in the absolute normalization
  set d : ℝ := (finrank ℚ K : ℝ) with hddef
  have hd : 0 < d := by rw [hddef]; exact_mod_cast Module.finrank_pos
  have habs : ∀ x : K, absLogHeight₁ x = Real.log (mulHeight₁ x) / d := fun x ↦ by
    rw [absLogHeight₁_eq_inv_mul_logHeight₁, logHeight₁_eq_log_mulHeight₁, hddef, inv_mul_eq_div]
  have hexp : ∀ x : K, mulHeight₁ x = Real.exp (d * absLogHeight₁ x) := fun x ↦ by
    rw [habs, mul_div_cancel₀ _ hd.ne', Real.exp_log (mulHeight₁_pos x)]
  set M : ℝ := Real.exp (d * e) with hMdef
  have hM1 : 1 ≤ M := Real.one_le_exp (mul_nonneg hd.le he0)
  have hM0 : (0 : ℝ) < M := by linarith
  set κ₁ : ℝ := (κ + 2) / 2 with hκ₁def
  have hκ₁2 : 2 < κ₁ := by rw [hκ₁def]; linarith
  have hκ₁κ : κ₁ < κ := by rw [hκ₁def]; linarith
  set C' : ℝ := max C 1 with hC'def
  set C₂ : ℝ := Ctot * C' * M ^ κ with hC₂def
  have hC₂1 : 1 ≤ C₂ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCtot1 (le_max_right _ _))
      (Real.one_le_rpow hM1 (by linarith))
  set B : ℝ := C₂ ^ (κ - κ₁)⁻¹ with hBdef
  have hB1 : 1 ≤ B := Real.one_le_rpow hC₂1 (inv_nonneg.mpr (by linarith))
  have hlogB : Real.log B / d ≤ (∑ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a)
      + Real.log C' + κ * d * e) / ((κ - 2) / 2 * d) := by
    have hCtot0 : 0 < Ctot := by linarith
    have hC'0 : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hlogC₂ : Real.log C₂ ≤ ∑ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a)
        + Real.log C' + κ * d * e := by
      rw [hC₂def, Real.log_mul (mul_pos hCtot0 hC'0).ne' (Real.rpow_pos_of_pos hM0 κ).ne',
        Real.log_mul hCtot0.ne' hC'0.ne', hMdef, ← Real.exp_mul, Real.log_exp]
      have h1 := (Real.log_le_iff_le_exp hCtot0).mpr hCtotle
      nlinarith
    have hκκ : κ - κ₁ = (κ - 2) / 2 := by rw [hκ₁def]; ring
    rw [hBdef, Real.log_rpow (by linarith), hκκ, inv_mul_eq_div, div_div]
    exact div_le_div_of_nonneg_right hlogC₂ (mul_pos (by linarith) hd).le
  -- the threshold
  have hLr := exists_forall_mem_interval_of_prod_min_one_le Sinf Sfin w hwInf hwFin α' hκ₁2
  set Lr := rothLargeThreshold Sinf Sfin α' κ₁ with hLrdef
  simp only [rothOnePointThreshold, rothOnePointBound, max_le_iff] at hL'
  obtain ⟨⟨hL'1, hL'2⟩, hL'3⟩ := hL'
  have hcardA : ((Finset.univ : Finset (↥Sinf ⊕ ↥Sfin)).card : ℝ)
      = ((Sinf.card + Sfin.card : ℕ) : ℝ) := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  have hsum_e : ∑ a : ↥Sinf ⊕ ↥Sfin, (onePointHeight (α (sPlaceAbsValue a)) + e)
      = ∑ a : ↥Sinf ⊕ ↥Sfin, onePointHeight (α (sPlaceAbsValue a))
        + ((Sinf.card + Sfin.card : ℕ) : ℝ) * e := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardA]
  have hsumb : ∑ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a)
      = 2 * ((Sinf.card + Sfin.card : ℕ) : ℝ) * Real.log 2 + 4 * (finrank ℚ F : ℝ) *
        (∑ a : ↥Sinf ⊕ ↥Sfin, onePointHeight (α (sPlaceAbsValue a))
          + ((Sinf.card + Sfin.card : ℕ) : ℝ) * e) := by
    have h2b : ∀ a : ↥Sinf ⊕ ↥Sfin, 2 * b (sPlaceAbsValue a) = 2 * Real.log 2
        + 4 * (finrank ℚ F : ℝ) * (onePointHeight (α (sPlaceAbsValue a)) + e) :=
      fun a ↦ by simp only [hbdef]; ring
    rw [Finset.sum_congr rfl fun a _ ↦ h2b a, Finset.sum_add_distrib, Finset.sum_const,
      ← Finset.mul_sum, hsum_e, nsmul_eq_mul, hcardA]
    ring
  replace hL'1 : (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, (onePointHeight (α (sPlaceAbsValue a)) + e))
      / rothDelta ((κ + 2) / 2) (Sinf.card + Sfin.card) (finrank K F) (finrank ℚ F) ≤ L' := by
    rw [hsum_e, ← add_assoc]; exact hL'1
  rw [← hsumb] at hL'3
  have hδ := rothDelta_pos hκ₁2 (Sinf.card + Sfin.card) (finrank K F)
    (Nat.cast_nonneg (finrank ℚ F))
  have hsum0 : 0 ≤ ∑ a : ↥Sinf ⊕ ↥Sfin,
      (onePointHeight (α (sPlaceAbsValue a)) + mobiusShift (Sinf.card + Sfin.card)) :=
    Finset.sum_nonneg fun a _ ↦ add_nonneg (onePointHeight_nonneg _) he0
  have hL'0 : 0 ≤ L' := le_trans (div_nonneg (by linarith) hδ.le) hL'1
  have hL'r : Lr ≤ L' := by
    rw [hLrdef, rothLargeThreshold]
    refine max_le (le_trans ?_ hL'1) hL'2
    have htw : (totalWeight K : ℝ) ≠ 0 := by
      rw [totalWeight_eq_finrank]; exact_mod_cast Module.finrank_pos.ne'
    rw [rothThreshold, mul_div_assoc, mul_div_cancel_left₀ _ htw]
    refine div_le_div_of_nonneg_right (add_le_add le_rfl (Finset.sum_le_sum fun a _ ↦ ?_)) hδ.le
    simp only [hα'def, hc'j]
    exact absLogHeight₁_onePointMobius_le hjs _
  have hL'B : Real.log B / d ≤ L' := hlogB.trans hL'3
  obtain ⟨k, hk, Q, hQ, hcov⟩ := hLr L' hL'r
  have hQ0 : ∀ i, 0 < Q i := fun i ↦ (Real.exp_pos L').trans (hQ i)
  refine ⟨k, hk, fun i ↦ Real.log (Q i), fun i ↦ ?_, fun β hβ hβL ↦ ?_⟩
  · rw [Real.lt_log_iff_exp_lt (hQ0 i)]
    exact hQ i
  -- `β` is not the base point
  have hβc : β ≠ c := by
    intro h
    rw [h] at hβL
    linarith [Real.log_pos one_lt_two]
  have hbc : β - c ≠ 0 := sub_ne_zero.mpr hβc
  have hbc' : algebraMap K F β ≠ c' := fun h ↦ hβc ((algebraMap K F).injective h)
  set γ : K := (β - c)⁻¹ with hγdef
  have hmapγ : algebraMap K F γ = (algebraMap K F β - c')⁻¹ := by
    rw [hγdef, map_inv₀, map_sub, hc'def]
  -- the two height comparisons
  have hγle : absLogHeight₁ γ ≤ e + absLogHeight₁ β := by
    rw [hγdef, absLogHeight₁_inv]
    linarith [absLogHeight₁_sub_le β c]
  have hβle : absLogHeight₁ β ≤ e + absLogHeight₁ γ := by
    have h1 := absLogHeight₁_add_le (β - c) c
    rw [sub_add_cancel] at h1
    rw [hγdef, absLogHeight₁_inv]
    linarith
  have hγβ : mulHeight₁ γ ≤ M * mulHeight₁ β := by
    rw [hexp γ, hexp β, hMdef, ← Real.exp_add, Real.exp_le_exp, ← mul_add]
    exact mul_le_mul_of_nonneg_left hγle hd.le
  have hγL : L' < absLogHeight₁ γ := by linarith
  -- `γ` is a solution of Roth's inequality at `κ₁`
  have hγpos : (0 : ℝ) < mulHeight₁ γ := mulHeight₁_pos γ
  have hβpos : (0 : ℝ) < mulHeight₁ β := mulHeight₁_pos β
  have hγB : B < mulHeight₁ γ := by
    have h1 : Real.log B / d < Real.log (mulHeight₁ γ) / d := by rw [← habs]; linarith
    have h2 := (div_lt_div_iff_of_pos_right hd).mp h1
    exact (Real.log_lt_log_iff (by linarith) hγpos).mp h2
  have hstep : ∀ v : AbsoluteValue K ℝ, ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) →
      min 1 (w v (algebraMap K F γ - α' v))
        ≤ Cfun v * (w v).onePointApprox (α v) (algebraMap K F β) := by
    intro v hv
    rw [hmapγ, hα'def, hCfundef]
    exact AbsoluteValue.min_one_sub_onePointMobius_le (w v) (hc' v hv) hbc'
  have hnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ min 1 (w v (algebraMap K F γ - α' v)) :=
    fun v ↦ le_min zero_le_one ((w v).nonneg _)
  have hA : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult)
      ≤ (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
        ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg (hnn u.1) _) fun u hu ↦ ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hnn u.1) (hstep u.1 (Or.inl ⟨u, hu, rfl⟩)) _
  have hBb : (∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1)))
      ≤ (∏ v ∈ Sfin, Cfun v.1) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun u _ ↦ hnn u.1) fun u hu ↦ hstep u.1 (Or.inr ⟨u, hu, rfl⟩)
  have hrpow : mulHeight₁ β ^ (-κ) ≤ M ^ κ * mulHeight₁ γ ^ (-κ) := by
    have h1 : mulHeight₁ γ / M ≤ mulHeight₁ β := by
      rw [div_le_iff₀ hM0]; linarith [hγβ]
    have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith : -κ ≤ 0)
    rwa [Real.div_rpow hγpos.le hM0.le, Real.rpow_neg hM0.le, div_inv_eq_mul, mul_comm] at h2
  have hC₂le : C₂ ≤ mulHeight₁ γ ^ (κ - κ₁) := by
    have hBκ : B ^ (κ - κ₁) = C₂ := by
      rw [hBdef, Real.rpow_inv_rpow (by linarith) (by linarith)]
    rw [← hBκ]
    exact Real.rpow_le_rpow (by positivity) hγB.le (by linarith)
  have hroth : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ≤ mulHeight₁ γ ^ (-κ₁) := by
    have h0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1)) :=
      Finset.prod_nonneg fun u _ ↦ hnn u.1
    have h1 : (0 : ℝ) ≤ (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
        ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult := by
      refine mul_nonneg (Finset.prod_nonneg fun u hu ↦ ?_) (Finset.prod_nonneg fun u _ ↦ ?_)
      · exact pow_nonneg (le_trans zero_le_one (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))) _
      · exact pow_nonneg ((w u.1).onePointApprox_nonneg _ _) _
    have hβ' : (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
          ≤ C' * mulHeight₁ β ^ (-κ) :=
      hβ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hβpos.le _))
    calc (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F γ - α' v.1)) ^ v.mult) *
          ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F γ - α' v.1))
        ≤ ((∏ v ∈ Sinf, Cfun v.1 ^ v.mult) *
            ∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
          ((∏ v ∈ Sfin, Cfun v.1) *
            ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)) :=
          mul_le_mul hA hBb h0 h1
      _ = Ctot * ((∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
            ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)) := by
          rw [hCtotdef]; ring
      _ ≤ Ctot * (C' * mulHeight₁ β ^ (-κ)) := mul_le_mul_of_nonneg_left hβ' (by linarith)
      _ ≤ Ctot * (C' * (M ^ κ * mulHeight₁ γ ^ (-κ))) := by
          gcongr
      _ = C₂ * mulHeight₁ γ ^ (-κ) := by rw [hC₂def]; ring
      _ ≤ mulHeight₁ γ ^ (κ - κ₁) * mulHeight₁ γ ^ (-κ) :=
          mul_le_mul_of_nonneg_right hC₂le (Real.rpow_nonneg hγpos.le _)
      _ = mulHeight₁ γ ^ (-κ₁) := by
          rw [← Real.rpow_add hγpos]
          ring_nf
  -- the interval of `γ`, moved back to `β`
  obtain ⟨i, hlo, hhi⟩ := hcov γ hroth hγL
  rw [mulHeight₁_rpow_inv_finrank] at hlo hhi
  have hlo' : Real.log (Q i) ≤ absLogHeight₁ γ := by
    rw [Real.log_le_iff_le_exp (hQ0 i)]; exact hlo
  have hhi' : absLogHeight₁ γ < rothRatio κ₁ (Sinf.card + Sfin.card) (finrank K F) *
      Real.log (Q i) := by
    rw [mul_comm, ← Real.exp_lt_exp, Real.exp_mul, Real.exp_log (hQ0 i)]
    exact hhi
  exact ⟨i, by linarith, by linarith⟩

end NumberField
