/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.CountingApproximations
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
  `OnePoint F` and a constant, in logarithmic heights with a bounded shift — the form
  `RothSubspaceCount.lean` feeds to Layer 9.4.
* `NumberField.mulHeight₁_rpow_inv_finrank`: the absolute height is `exp` of the absolute
  logarithmic height.

## Implementation notes

⚠ **This is the interval result, not its count.** 6.5.7
(`NumberField.exists_ncard_setOf_lt_absLogHeight₁_le`) bounds the number of large solutions by
counting each interval with the gap principle; here the intervals are the conclusion and no gap
principle is used. Evertse's covering (Layer 9.4) turns intervals into a count of subspaces; the
link, which reads a normalized system in `K ^ 2` as Roth's inequality, is
`DiophantineApproximation/RothSubspaceCount.lean`.

⚠ **Targets at infinity cost a shift, not a ratio.** The Möbius change of variable
`β ↦ (β - c)⁻¹` of Layer 3.3 moves the absolute logarithmic height by at most
`e = log (2 ^ [K : ℚ] H(c)) / [K : ℚ]`, so the windows of the second form are `[t - e, M t + e)`;
the constant in front of the height is absorbed by lowering the exponent to `(κ + 2) / 2` and
raising the threshold.

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
covering of Layer 9.4 consumes). There is a height `L`, depending on `K`, `S` and the targets,
such that for every `L' ≥ L` the solutions `β` of `Λ(β) ≤ H(β) ^ (−κ)` with absolute logarithmic
height above `L'` have absolute height `H(β) = mulHeight₁ β ^ (1 / [K : ℚ])` in the union of at
most `m (N + s).choose s` intervals `[Q i, Q i ^ M)`, all with `Q i > exp L'`. Here
`m = rothChainLength κ s r`, `M = rothRatio κ s r`, `N = rothClassSize κ s`, `s = |S|` and
`r = [F : K]`, so the number of intervals depends on `κ`, `s` and `r` alone. -/
theorem exists_forall_mem_interval_of_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L : ℝ, ∀ L' : ℝ, L ≤ L' → ∃ k : ℕ,
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
  obtain ⟨Lr, hLr⟩ := roth_no_chain Sinf Sfin w hwInf hwFin α hκ
  refine ⟨max (Lr / totalWeight K) 0, fun L' hL' ↦ ?_⟩
  set U : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      L' < absLogHeight₁ β} with hUdef
  have hUfin : U.Finite :=
    (finite_setOf_prod_min_one_le Sinf Sfin w hwInf hwFin α hκ).subset fun β hβ ↦ hβ.1
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

/-- **Roth's theorem with targets at infinity, as an interval result** (Layers 3.3 and 3.7). For
targets in `OnePoint F` and a constant `C` in front of the height, there are a height `L` and a
shift `e ≥ 0` such that for every `L' ≥ L` the solutions with absolute logarithmic height above
`L' + e` have it in the union of at most `m (N + s).choose s` shifted windows
`[t i - e, M t i + e)`, all with `t i > L'`. Here `m`, `M` and `N` are Roth's parameters at the
exponent `(κ + 2) / 2`. The Möbius change of variable `β ↦ (β - c)⁻¹` of Layer 3.3 moves the
targets to finite ones and the heights by at most `e`. -/
theorem exists_forall_mem_interval_of_prod_onePointApprox_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) (C : ℝ) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L e : ℝ, 0 ≤ e ∧ ∀ L' : ℝ, L ≤ L' → ∃ k : ℕ,
      k ≤ rothChainLength ((κ + 2) / 2) (Sinf.card + Sfin.card) (finrank K F) *
        (rothClassSize ((κ + 2) / 2) (Sinf.card + Sfin.card) + (Sinf.card + Sfin.card)).choose
          (Sinf.card + Sfin.card) ∧
      ∃ t : Fin k → ℝ, (∀ i, L' < t i) ∧
        ∀ β : K, (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
            ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
              ≤ C * mulHeight₁ β ^ (-κ) →
          L' + e < absLogHeight₁ β →
          ∃ i, t i - e ≤ absLogHeight₁ β ∧ absLogHeight₁ β <
            rothRatio ((κ + 2) / 2) (Sinf.card + Sfin.card) (finrank K F) * t i + e := by
  classical
  -- a base point of the Möbius change of variable that is none of the targets
  obtain ⟨c, hc⟩ : ∃ c : K, ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) →
      α v ≠ ((algebraMap K F c : F) : OnePoint F) := by
    set T : Set (OnePoint F) := ((fun u : InfinitePlace K ↦ α u.1) '' (Sinf : Set _))
      ∪ ((fun u : FinitePlace K ↦ α u.1) '' (Sfin : Set _)) with hTdef
    have hT : T.Finite := (Sinf.finite_toSet.image _).union (Sfin.finite_toSet.image _)
    set g : K → OnePoint F := fun x ↦ ((algebraMap K F x : F) : OnePoint F) with hgdef
    have hg : Function.Injective g := fun x y h ↦
      (algebraMap K F).injective (OnePoint.coe_injective h)
    have hpre : (g ⁻¹' T).Finite := Set.Finite.preimage hg.injOn hT
    obtain ⟨c, hcmem⟩ := hpre.infinite_compl.nonempty
    refine ⟨c, fun v hv hcon ↦ hcmem ?_⟩
    rcases hv with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact Or.inl ⟨u, hu, hcon⟩
    · exact Or.inr ⟨u, hu, hcon⟩
  set c' : F := algebraMap K F c with hc'def
  set α' : AbsoluteValue K ℝ → F := fun u ↦ AbsoluteValue.onePointMobius c' (α u) with hα'def
  -- the constants
  set Cfun : AbsoluteValue K ℝ → ℝ := fun u ↦ (w u).mobiusConst c' (α u) with hCfundef
  set Ctot : ℝ := (∏ v ∈ Sinf, Cfun v.1 ^ v.mult) * ∏ v ∈ Sfin, Cfun v.1 with hCtotdef
  have hCfun1 : ∀ v : AbsoluteValue K ℝ,
      ((∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v) → 1 ≤ Cfun v :=
    fun v hv ↦ AbsoluteValue.one_le_mobiusConst _ (hc v hv)
  have hCtot1 : 1 ≤ Ctot := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · exact Finset.one_le_prod₀ fun u hu ↦ one_le_pow₀ (hCfun1 u.1 (Or.inl ⟨u, hu, rfl⟩))
    · exact Finset.one_le_prod₀ fun u hu ↦ hCfun1 u.1 (Or.inr ⟨u, hu, rfl⟩)
  set M : ℝ := 2 ^ totalWeight K * mulHeight₁ c with hMdef
  have hM1 : 1 ≤ M :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mulHeight₁ c)
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
  -- heights in the absolute normalization
  set d : ℝ := (finrank ℚ K : ℝ) with hddef
  have hd : 0 < d := by rw [hddef]; exact_mod_cast Module.finrank_pos
  have habs : ∀ x : K, absLogHeight₁ x = Real.log (mulHeight₁ x) / d := fun x ↦ by
    rw [absLogHeight₁_eq_inv_mul_logHeight₁, logHeight₁_eq_log_mulHeight₁, hddef, inv_mul_eq_div]
  set e : ℝ := Real.log M / d with hedef
  have he0 : 0 ≤ e := div_nonneg (Real.log_nonneg hM1) hd.le
  have hcomp : ∀ x y : K, mulHeight₁ x ≤ M * mulHeight₁ y →
      absLogHeight₁ x ≤ e + absLogHeight₁ y := fun x y hxy ↦ by
    rw [habs, habs, hedef, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hd.le
    rw [← Real.log_mul hM0.ne' (mulHeight₁_pos y).ne']
    exact Real.log_le_log (mulHeight₁_pos x) hxy
  obtain ⟨Lr, hLr⟩ := exists_forall_mem_interval_of_prod_min_one_le Sinf Sfin w hwInf hwFin α'
    hκ₁2
  refine ⟨max Lr (max (Real.log B / d) 0), e, he0, fun L' hL' ↦ ?_⟩
  have hL'r : Lr ≤ L' := (le_max_left _ _).trans hL'
  have hL'B : Real.log B / d ≤ L' := ((le_max_left _ _).trans (le_max_right _ _)).trans hL'
  have hL'0 : 0 ≤ L' := ((le_max_right _ _).trans (le_max_right _ _)).trans hL'
  obtain ⟨k, hk, Q, hQ, hcov⟩ := hLr L' hL'r
  have hQ0 : ∀ i, 0 < Q i := fun i ↦ (Real.exp_pos L').trans (hQ i)
  refine ⟨k, hk, fun i ↦ Real.log (Q i), fun i ↦ ?_, fun β hβ hβL ↦ ?_⟩
  · rw [Real.lt_log_iff_exp_lt (hQ0 i)]
    exact hQ i
  -- `β` is not the base point
  have hβc : β ≠ c := by
    have hcM : mulHeight₁ c ≤ M * mulHeight₁ (1 : K) := by
      rw [mulHeight₁_one, mul_one, hMdef]
      exact le_mul_of_one_le_left (mulHeight₁_pos c).le (one_le_pow₀ (by norm_num))
    have hce := hcomp c 1 hcM
    rw [habs 1, mulHeight₁_one, Real.log_one, zero_div, add_zero] at hce
    intro h
    rw [h] at hβL
    linarith
  have hbc : β - c ≠ 0 := sub_ne_zero.mpr hβc
  have hbc' : algebraMap K F β ≠ c' := fun h ↦ hβc ((algebraMap K F).injective h)
  set γ : K := (β - c)⁻¹ with hγdef
  have hmapγ : algebraMap K F γ = (algebraMap K F β - c')⁻¹ := by
    rw [hγdef, map_inv₀, map_sub, hc'def]
  -- the two height comparisons
  have hγβ : mulHeight₁ γ ≤ M * mulHeight₁ β := by
    rw [hγdef, mulHeight₁_inv, hMdef]
    calc mulHeight₁ (β - c) ≤ 2 ^ totalWeight K * mulHeight₁ β * mulHeight₁ c :=
          mulHeight₁_sub_le β c
      _ = 2 ^ totalWeight K * mulHeight₁ c * mulHeight₁ β := by ring
  have hβγ : mulHeight₁ β ≤ M * mulHeight₁ γ := by
    rw [hγdef, mulHeight₁_inv, hMdef]
    calc mulHeight₁ β = mulHeight₁ ((β - c) + c) := by ring_nf
      _ ≤ 2 ^ totalWeight K * mulHeight₁ (β - c) * mulHeight₁ c := mulHeight₁_add_le _ _
      _ = 2 ^ totalWeight K * mulHeight₁ c * mulHeight₁ (β - c) := by ring
  have hγle := hcomp γ β hγβ
  have hβle := hcomp β γ hβγ
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
    exact AbsoluteValue.min_one_sub_onePointMobius_le (w v) (hc v hv) hbc'
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
