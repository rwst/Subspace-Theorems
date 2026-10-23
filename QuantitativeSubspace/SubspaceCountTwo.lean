/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.SubspaceCount

/-!
# The quantitative Subspace Theorem in two variables

Y. Bugeaud and J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Appendix (Proposition A.1): for `n = 2` the parametric Subspace Theorem
holds with `225 δ⁻³ log (2 r) log (δ⁻¹ log (2 r))` subspaces, `r` the number of distinct forms,
which is the best count known in two variables. Their proof is Evertse 1996 specialized to
`n = 2`: a chain of `m ≍ δ⁻² log (2 r)` levels (A.26) whose logarithms grow at the rate
`162 m² / δ` (A.30), Roth's lemma (A.7) in the form of Evertse 1995, and the gap principle
(A.3, A.4) inside each of the `m - 1` intervals that the chain leaves.

The same shape comes out of Layer Q0 when `#ι = 2`. Then the domains at large levels have rank
`0` or `1 = #ι - 1` (Layer 4.3), so Layer 5.6 applies to them directly and Layer 6.1, with its
wedges and its grids of exponents, is not needed. The interval result has `m` intervals of ratio
`4 σ⁻¹`, and Q0.3's assembly (`NumberField.exists_finset_submodule_of_forall_interval`) turns
each into `1 + log (4 σ⁻¹) / log (1 + δ / 4)` windows of the gap principle. With Evertse's Roth
lemma (Q1.5) `4 σ⁻¹ = 16 (m + 1) / η` is polynomial, so the count is
`m (1 + O(δ⁻¹ log (m / η)))` with `m = O(η⁻² log s)`: Bugeaud–Evertse's
`δ⁻³ log · log (δ⁻¹ log)` (`NumberField.systemLargeCountTwo_evertse_le`).

## Main definitions

* `NumberField.twoThreshold`: the threshold of the interval result in two variables, the larger
  of Layer 4.3's rank threshold and Layer 5.6's `penultimateThreshold`.
* `NumberField.systemThresholdTwo`, `NumberField.systemLargeCountTwo`: Q0.3's threshold and count
  of the large solutions for `n = 2`, with Layer 5.6 in place of 6.1.
* `NumberField.systemGapCountTwo`: the same count with a gap principle of ratio `ρ` supplied by
  the caller, plus the range `[Y, X₀)` below the threshold.
* `NumberField.systemThresholdTwoAt`: the threshold at the caller's margin `ε`, parameter `A`,
  form count `s` and fraction `τ` of `δ` spent on the scalar.
* `NumberField.twoThresholdAt`, `NumberField.systemThresholdTwoExplicit`: the thresholds at an
  explicit chain length `m`, `η` and height cost `F`, `g` of the Roth lemma.

## Main results

* `NumberField.exists_forall_mem_interval_approxDomain_two`: **the parametric Subspace Theorem in
  two variables as an interval result**, with at most two subspaces (`⊥` and Layer 5.4's
  exceptional one) and `m = subspaceChainLength 1 s (2 ε) A` intervals of ratio `4 σ⁻¹`. No grids.
* `NumberField.twoThreshold_le`, `NumberField.systemThresholdTwo_le`: the thresholds, linear in
  the heights.
* `NumberField.exists_finset_submodule_of_systemThresholdTwo_le`,
  `NumberField.exists_finset_submodule_of_isNormalizedSystem_two`: Q0.3 for `n = 2`, any Roth
  lemma.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_two_evertse`: the same with
  Evertse's.
* `NumberField.systemLargeCountTwo_evertse_le`: **the count in closed form**. With `s = R e`
  distinct forms over `E` and `Y = 449 / δ`,

  `systemLargeCountTwo ≤ 2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)`, `ℓ = 1 + log (4 s)`.
* `NumberField.exists_forall_mem_interval_systemSet_two`: the large solutions of a system lie in
  two subspaces or have `log H(x)` in `m` intervals of ratio `4 σ⁻¹`, the same for every
  solution (over `ℚ`, the generic parameters of [Ste26], §7.3).
* `NumberField.exists_forall_mem_interval_approxDomain_two_of_budget`,
  `NumberField.exists_forall_mem_interval_systemSet_two_at`, `NumberField.systemThresholdTwoAt_le`:
  the same **at the caller's parameters**, from the weight budget of Steps IV and VI. The domain's
  weight is used exactly, the absolute weight is the system's own, and the whole budget goes to
  `η`: with `A = 0`, `η = W / (4 (A₀ + 2))` for weight `-W` and absolute weight `A₀`, against
  `δ / 448` over `ℚ` with `systemEps` and `systemAbsBound`. For the exceptions to
  `‖(3/2)^n‖ ≥ (3/4)^n` this cuts `m` from `4.9·10⁶` to `8445`.
* `NumberField.exists_forall_mem_interval_approxDomain_two_of_rothLemmaAt`,
  `NumberField.exists_forall_mem_interval_systemSet_two_of_rothLemmaAt`,
  `NumberField.systemThresholdTwoExplicit_le`: the same **at explicit parameters**, with `m`, `η`
  and a Roth lemma at them chosen by the caller (`NumberField.RothLemmaAt`) under Layer 5.2's
  condition `log ((q + 1) / q · f) < (m + 1) · layerRate 1 η`, `f ≥ R [E : K]`, Siegel's
  exponent `q ≥ 1`. The margin `ε` no longer bounds `η`, so `η → W / (2 D)` as `ε → 0`, for a
  threshold `∝ ε⁻¹`; `f` counts the forms themselves; `Finset.layerRate 1 η ≥ 6 η² - 16 η³` is
  the variance form of the Chernoff bound, four times the book's `3 η² / 2`
  (`Finset.layerRate_one_ge`); and the deviation error is charged `D = min (2 A₀) D₀`,
  `D₀ = [E : K] (2 (2 + δ) + N)` (`NumberField.approxDevWeight`), with `N = 0` when every place
  has a nonnegative exponent. For the exceptions to `‖(3/2)^n‖ ≥ (3/4)^n` this cuts `m` from
  `8445` to `241`. Over `ℚ` this is [Ste26], Theorem 7.2, with the budget (11), the chain
  condition (12) and items (a)–(g).
* `NumberField.exists_finset_submodule_of_gap_two`: **the count with the caller's gap
  principle**. If solutions on distinct lines with `Y ≤ log H(x) ≤ log H(y)` have
  `ρ log H(x) ≤ log H(y)`, each interval holds `1 + log (4 σ⁻¹) / log ρ` lines instead of
  `1 + log (4 σ⁻¹) / log (1 + δ / 4)`, and the range `[Y, X₀)` holds `1 + log (X₀ / Y) / log ρ`
  ([Ste26], Remark 7.7, where `ρ = 1.2618` against `1 + δ / 4 ≈ 1.065` cuts the line count of the
  exceptions to `‖(3/2)^n‖ ≥ (3/4)^n` from `3.87·10⁹` to `1.05·10⁹` at the generic parameters;
  Theorem 7.6 there is the same count at the parameters of Theorem 7.2, `22 900`).
* `Real.finite_and_ncard_le_of_lacunary`, `Submodule.exists_finset_span_singleton_of_lacunary`:
  a `ρ`-lacunary set in `[a, b)` has at most `1 + log (b / a) / log ρ` elements, and a lacunary
  family meets at most that many lines ([Ste26], Lemma 7.5).

## Comparison with Bugeaud–Evertse

The main term `10 (1 + log (4 s)) Y² log (32 (1 + log (4 s)) Y³) / δ` is
`O(δ⁻³ log s · log (δ⁻¹ log s))`, Bugeaud–Evertse's `δ⁻³ log (2 r) log (δ⁻¹ log (2 r))` with
`s = R [E : K]` forms, the conjugates over `E` of the system's `R` (Q1.8b: Layer 5.2 imposes its
conditions per form). It depends neither on `|S|` nor on the number `t` of places of the
system: Q0.3's raised exponents have absolute weight at most `[E : K] (2 n + 2)`, as
Bugeaud–Evertse's are normalized by (A.7), `∑ max c ≤ 1`, and one scalar absorbs the constants
(Q1.8a).

## References

Y. Bugeaud and J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250 (arXiv:0709.1560), Appendix.

[Ste26] R. Stephan, *Line counts and a census for the exceptions to `‖(3/2)^n‖ ≥ (3/4)^n`, with an
application to Waring's problem*, preprint (2026), doi:10.13140/RG.2.2.15019.20008, §7:
§7.3 (the interval result for the solutions; Theorem 7.2 at given parameters, under the budget
(11) and the chain condition (12), with items (a)–(g) against the generic parameters),
Lemma 7.5 (lines in a range), Theorem 7.6 and Remark 7.7 (the line count with the gap `ρ₀`, at
the parameters of Theorem 7.2 and at the generic ones). The results above marked [Ste26] appear
there first.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

/-! ### Lacunary sets and the lines through them -/

namespace Real

/-- In a finite set of reals `≥ a` with gap ratio `ρ ≥ 1`, some element is at least
`ρ ^ (#s - 1) a`. -/
theorem exists_mem_pow_mul_le_of_lacunary {ρ a : ℝ} (hρ : 1 ≤ ρ) (s : Finset ℝ) :
    (∀ u ∈ s, ∀ v ∈ s, u < v → ρ * u ≤ v) → (∀ u ∈ s, a ≤ u) → s.Nonempty →
      ∃ v ∈ s, ρ ^ (#s - 1) * a ≤ v := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ h; exact absurd h Finset.not_nonempty_empty
  | insert v s hv ih =>
    intro hgap ha _
    have hvs : v ∉ s := fun h ↦ lt_irrefl v (hv v h)
    rw [Finset.card_insert_of_notMem hvs]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨v, Finset.mem_insert_self _ _, by simpa using ha v (Finset.mem_insert_self _ _)⟩
    obtain ⟨u, hu, hua⟩ := ih
      (fun x hx y hy hxy ↦ hgap x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
      (fun x hx ↦ ha x (Finset.mem_insert_of_mem hx)) hs
    refine ⟨v, Finset.mem_insert_self _ _, ?_⟩
    have huv := hgap u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_self _ _) (hv u hu)
    have hcard : #s + 1 - 1 = (#s - 1) + 1 := by have := hs.card_pos; omega
    rw [hcard, pow_succ]
    calc ρ ^ (#s - 1) * ρ * a = ρ * (ρ ^ (#s - 1) * a) := by ring
      _ ≤ ρ * u := mul_le_mul_of_nonneg_left hua (by linarith)
      _ ≤ v := huv

/-- **A lacunary set of reals in `[a, b)` is small**: a finite set of reals in `[a, b)`,
`0 < a ≤ b`, in which any two elements `u < v` have `ρ u ≤ v`, `ρ > 1`, has at most
`1 + log (b / a) / log ρ` elements. This is the count in the proof of Lemma 7.5 of [Ste26]. -/
theorem card_le_one_add_log_div_log_of_lacunary {ρ a b : ℝ} (hρ : 1 < ρ) (ha : 0 < a)
    (hab : a ≤ b) (s : Finset ℝ) (hgap : ∀ u ∈ s, ∀ v ∈ s, u < v → ρ * u ≤ v)
    (hs : ∀ u ∈ s, a ≤ u ∧ u < b) :
    (#s : ℝ) ≤ 1 + Real.log (b / a) / Real.log ρ := by
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  have hba : 0 ≤ Real.log (b / a) / Real.log ρ :=
    div_nonneg (Real.log_nonneg ((one_le_div ha).2 hab)) hlρ.le
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; linarith
  obtain ⟨v, hv, hva⟩ := exists_mem_pow_mul_le_of_lacunary hρ.le s hgap (fun u hu ↦ (hs u hu).1) hne
  have hpow : ρ ^ (#s - 1) < b / a := by
    rw [lt_div_iff₀ ha]; exact hva.trans_lt (hs v hv).2
  have hlog : ((#s - 1 : ℕ) : ℝ) * Real.log ρ < Real.log (b / a) := by
    rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hpow
  have hc : (#s : ℝ) = ((#s - 1 : ℕ) : ℝ) + 1 := by
    have := hne.card_pos
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  have : ((#s - 1 : ℕ) : ℝ) ≤ Real.log (b / a) / Real.log ρ := by
    rw [le_div_iff₀ hlρ]; exact hlog.le
  linarith

/-- **A lacunary set of reals in `[a, b)` is finite and small**: the set form of
`Real.card_le_one_add_log_div_log_of_lacunary`. -/
theorem finite_and_ncard_le_of_lacunary {ρ a b : ℝ} (hρ : 1 < ρ) (ha : 0 < a) (hab : a ≤ b)
    {s : Set ℝ} (hgap : ∀ u ∈ s, ∀ v ∈ s, u < v → ρ * u ≤ v) (hs : ∀ u ∈ s, a ≤ u ∧ u < b) :
    s.Finite ∧ (s.ncard : ℝ) ≤ 1 + Real.log (b / a) / Real.log ρ := by
  have key : ∀ t : Finset ℝ, ↑t ⊆ s → (#t : ℝ) ≤ 1 + Real.log (b / a) / Real.log ρ :=
    fun t hts ↦ card_le_one_add_log_div_log_of_lacunary hρ ha hab t
      (fun u hu v hv ↦ hgap u (hts hu) v (hts hv)) fun u hu ↦ hs u (hts hu)
  have hfin : s.Finite := by
    by_contra hinf
    obtain ⟨t, hts, ht⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌊1 + Real.log (b / a) / Real.log ρ⌋₊ + 1)
    have h := key t hts
    rw [ht] at h
    push_cast at h
    linarith [Nat.lt_floor_add_one (1 + Real.log (b / a) / Real.log ρ)]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card s hfin]
  exact key _ (by simp)

end Real

namespace Submodule

/-- **Few lines through a lacunary family meet a window.** Let `h` be a real function on a
space `V` of finite dimension at least `2`, and `X` a set of vectors such that any two
`x, y ∈ X` on distinct lines with `a ≤ h x ≤ h y` have `ρ h x ≤ h y`, `ρ > 1`, `0 < a ≤ b`. Then
the `x ∈ X` with `h x ∈ [a, b)` lie on at most `1 + log (b / a) / log ρ` lines. This is Lemma 7.5
of [Ste26], with `h` the logarithmic height in place of the index. -/
theorem exists_finset_span_singleton_of_lacunary {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (hV : 1 < finrank K V) (h : V → ℝ) {X : Set V}
    {ρ a b : ℝ} (hρ : 1 < ρ) (ha : 0 < a) (hab : a ≤ b)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, a ≤ h x → h x ≤ h y → K ∙ x ≠ K ∙ y → ρ * h x ≤ h y) :
    ∃ T : Finset (Submodule K V), (#T : ℝ) ≤ 1 + Real.log (b / a) / Real.log ρ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ X, a ≤ h x → h x < b → ∃ U ∈ T, x ∈ U := by
  classical
  set Xw : Set V := {x | x ∈ X ∧ a ≤ h x ∧ h x < b} with hXw
  set P : Set (Submodule K V) := (fun x ↦ K ∙ x) '' Xw with hP
  set g := Function.invFunOn (fun x ↦ K ∙ x) Xw with hg
  have hgP : ∀ U ∈ P, g U ∈ Xw ∧ K ∙ g U = U := fun U hU ↦
    ⟨Function.invFunOn_mem hU, Function.invFunOn_eq hU⟩
  -- representatives of distinct lines
  have hne : ∀ U ∈ P, ∀ W ∈ P, U ≠ W → h (g U) ≤ h (g W) → ρ * h (g U) ≤ h (g W) := by
    intro U hU W hW hUW hle
    obtain ⟨⟨hxU, haU, -⟩, hfU⟩ := hgP U hU
    obtain ⟨⟨hxW, -, -⟩, hfW⟩ := hgP W hW
    exact hgap _ hxU _ hxW haU hle fun heq ↦ hUW (hfU.symm.trans (heq.trans hfW))
  have hinj : Set.InjOn (h ∘ g) P := by
    intro U hU W hW hUW
    by_contra hne'
    have hUW' : h (g U) = h (g W) := hUW
    have hpos : 0 < h (g U) := ha.trans_le (hgP U hU).1.2.1
    have := hne U hU W hW hne' hUW'.le
    nlinarith [mul_lt_mul_of_pos_right hρ hpos]
  obtain ⟨hfin, hcard⟩ := Real.finite_and_ncard_le_of_lacunary hρ ha hab (s := (h ∘ g) '' P)
    (by
      rintro _ ⟨U, hU, rfl⟩ _ ⟨W, hW, rfl⟩ hlt
      refine hne U hU W hW (fun hUW ↦ ?_) hlt.le
      subst hUW
      exact lt_irrefl _ hlt)
    (by
      rintro _ ⟨U, hU, rfl⟩
      exact ⟨(hgP U hU).1.2.1, (hgP U hU).1.2.2⟩)
  have hPfin : P.Finite := Set.Finite.of_finite_image hfin hinj
  refine ⟨hPfin.toFinset, ?_, fun U hU ↦ ?_, fun x hx hax hxb ↦ ?_⟩
  · rw [← Set.ncard_eq_toFinset_card P hPfin, ← hinj.ncard_image]
    exact hcard
  · obtain ⟨x, -, rfl⟩ := hPfin.mem_toFinset.1 hU
    intro htop
    have h1 := finrank_span_le_card (R := K) ({x} : Set V)
    have htop' : K ∙ x = ⊤ := htop
    rw [htop', finrank_top] at h1
    simp only [Set.toFinset_singleton, Finset.card_singleton] at h1
    omega
  · exact ⟨K ∙ x, hPfin.mem_toFinset.2 ⟨x, ⟨hx, hax, hxb⟩, rfl⟩,
      Submodule.mem_span_singleton_self x⟩

end Submodule

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]

/-! ### The parametric theorem in two variables -/

variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) in
open scoped Classical in
/-- **The threshold of the interval result in two variables**, on the scale of `log Q`: the
largest of `1`, the logarithm of Layer 4.3's rank threshold at weight `-ε`, and Layer 5.6's
`penultimateThreshold` in dimension `1` at margin `2 ε`. An order on `ι` is chosen by transport
from `Fin #ι`, as for `parametricThreshold`. -/
noncomputable def twoThreshold (R : RothParams) (s : ℕ) (ε A : ℝ) : ℝ :=
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  max 1 (max (Real.log (rankThreshold Sfin L ε)) (penultimateThreshold Sfin L R 1 s (2 * ε) A))

variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) in
open scoped Classical in
/-- **The threshold of the interval result in two variables at given parameters**: `twoThreshold`
with `penultimateThresholdAt` for the chain length `m`, `η`, Siegel's exponent `q` and the height
cost `F`, `g` of the Roth lemma. -/
noncomputable def twoThresholdAt (m : ℕ) (η q ε F g : ℝ) : ℝ :=
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  max 1 (max (Real.log (rankThreshold Sfin L ε))
    (penultimateThresholdAt Sfin L 1 m η q (2 * ε) F g))

/-- `twoThreshold` is `twoThresholdAt` at the parameters of Steps IV and VI. -/
theorem twoThreshold_eq_at (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (R : RothParams) (s : ℕ) (ε A : ℝ) :
    twoThreshold Sfin L R s ε A = twoThresholdAt Sfin L (subspaceChainLength 1 s (2 * ε) A)
      (subspaceEta 1 (2 * ε) A) 1 ε (R.factor 1 s (2 * ε) A) (R.shift 1 s (2 * ε) A) := by
  simp only [twoThreshold, twoThresholdAt, penultimateThreshold_eq_at]

open scoped Classical in
/-- **The parametric Subspace Theorem in two variables, as an interval result, at given
parameters**: `NumberField.exists_forall_mem_interval_approxDomain_two` with the chain length `m`,
the `η` of the auxiliary polynomial and a generalized Roth lemma at them
(`NumberField.exists_forall_mem_interval_approxSpan_of_rothLemmaAt` at `n = 1`, margin `2 ε`):
Layer 5.2's condition `log ((q + 1) / q · f) < (m + 1) · layerRate 1 η` for a bound `f` on the
number of distinct forms and Siegel's exponent `q ≥ 1`, and the budget `w / 2 + η DW ≤ -ε / 4`,
where `w` is the weight and `DW = approxDevWeight` the deviation weight, `2 |c₁ - c₂|` per place
with a nonnegative exponent (at most `2 AW`, `AW` the absolute weight). At most `m` intervals of
ratio `4 σ⁻¹` above `twoThresholdAt` ([Ste26], items (c)–(g)). -/
theorem exists_forall_mem_interval_approxDomain_two_of_rothLemmaAt
    (hcard : Fintype.card ι = 2) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {m : ℕ} {η σ F g : ℝ} (hη0 : 0 < η)
    (hσ0 : 0 < σ) (hF0 : 0 ≤ F) (hg0 : 0 ≤ g) (hR : RothLemmaAt.{u} K 1 m η σ F g)
    (hbudget : approxWeight Sfin c / 2 + η * approxDevWeight Sfin c ≤ -(ε / 4))
    {f : ℕ} (hf : formCount Sfin L ≤ f) {q : ℝ} (hq : 1 ≤ q)
    (hm : Real.log ((q + 1) / q * (f : ℝ)) < ((m : ℝ) + 1) * Finset.layerRate 1 η) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ 2 ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ Q₀' : ℝ, twoThresholdAt Sfin L m η q ε F g ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ m ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < 4 * σ⁻¹ * t := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hε2 : 0 < 2 * ε := by positivity
  have hb : approxWeight Sfin c / (((1 : ℕ) : ℝ) + 1)
      + η * approxDevWeight Sfin c
      ≤ -(2 * ε / (4 * (((1 : ℕ) : ℝ) + 1))) := by
    have e : -(2 * ε / (4 * (((1 : ℕ) : ℝ) + 1))) = -(ε / 4) := by push_cast; ring
    rw [e]
    push_cast
    linarith
  obtain ⟨𝒲, Q₀, h𝒲fin, h𝒲card, -, hQ₀eq, hint⟩ :=
    exists_forall_mem_interval_approxSpan_of_rothLemmaAt (n := 1) le_rfl hcard hLInf hLFin hε2
      (by linarith) hη0 hσ0 hF0 hg0 hR hb hf hq hm
  set T : Finset (Submodule K (ι → K)) := insert ⊥ (h𝒲fin.toFinset.filter (· ≠ ⊤)) with hT
  refine ⟨T, ?_, ?_, fun Q₀' hQ₀' ↦ ?_⟩
  · refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
    refine (Finset.card_filter_le _ _).trans ?_
    rw [← Set.ncard_eq_toFinset_card 𝒲 h𝒲fin]
    exact h𝒲card
  · intro W hW
    rcases Finset.mem_insert.1 hW with rfl | hW
    · exact bot_ne_top
    · exact (Finset.mem_filter.1 hW).2
  have hQ₀ : Q₀ ≤ Q₀' := by
    rw [hQ₀eq]
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans hQ₀'
  obtain ⟨k, hk, t, ht, hint⟩ := hint Q₀' hQ₀
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans (by simpa using hk), fun u hu ↦ ?_,
    fun Q hQ1 hQ ↦ ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    exact ht i
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have ha0 : 0 < rankThreshold Sfin L ε := by
    rw [rankThreshold]
    positivity
  have hrank := finrank_approxSpan_lt_of_rankThreshold_le hLInf hLFin hε hc
    ((Real.log_le_log_iff ha0 hQ0).1
      ((((le_max_left _ _).trans (le_max_right _ _)).trans hQ₀').trans hQ))
  rw [hcard] at hrank
  rcases Nat.lt_or_ge (finrank K (approxSpan Sfin L c Q)) 1 with hR0 | hR1
  · refine Or.inl ⟨⊥, Finset.mem_insert_self _ _, fun z hz ↦ ?_⟩
    have hmem : z ∈ approxSpan Sfin L c Q := Submodule.subset_span hz
    have h0 : finrank K (approxSpan Sfin L c Q) = 0 := by omega
    rwa [Submodule.finrank_eq_zero.1 h0] at hmem
  have hR : finrank K (approxSpan Sfin L c Q) = 1 := by omega
  by_cases hW : approxSpan Sfin L c Q ∈ 𝒲
  · have htop : approxSpan Sfin L c Q ≠ ⊤ := fun h ↦ by
      rw [h, finrank_top, Module.finrank_fintype_fun_eq_card, hcard] at hR
      omega
    exact Or.inl ⟨_, Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨h𝒲fin.mem_toFinset.2 hW, htop⟩), Submodule.subset_span⟩
  · obtain ⟨i, h1, h2⟩ := hint Q hQ1 hQ hR hW
    exact Or.inr ⟨t i, Finset.mem_image_of_mem t (Finset.mem_univ i), h1, h2⟩

open scoped Classical in
/-- **The parametric Subspace Theorem in two variables, as an interval result, from the weight
budget**: `NumberField.exists_forall_mem_interval_approxDomain_two` with the absolute-weight bound
`≤ A` replaced by the budget `w / 2 + 2 η AW ≤ -ε / 4` of Steps IV and VI
(`NumberField.exists_forall_not_chain_of_budget` at `n = 1`, margin `2 ε`), where `w` is the
weight, `AW` the absolute weight and `η = subspaceEta 1 (2 ε) A`. The parameter `A` then only
fixes the chain, the Roth lemma and the threshold; `A = 0` gives the largest `η`. -/
theorem exists_forall_mem_interval_approxDomain_two_of_budget (R : SubspaceRoth.{u} K)
    (hcard : Fintype.card ι = 2) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ} (hA0 : 0 ≤ A)
    (hbudget : approxWeight Sfin c / 2 + 2 * subspaceEta 1 (2 * ε) A * approxAbsWeight Sfin c
      ≤ -(ε / 4))
    {s : ℕ} (hs : formCount Sfin L ≤ 2 * s) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ 2 ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ Q₀' : ℝ, twoThreshold Sfin L R.toRothParams s ε A ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ subspaceChainLength 1 s (2 * ε) A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < 4 * (R.ratio 1 s (2 * ε) A)⁻¹ * t := by
  rw [twoThreshold_eq_at]
  have hε2 : 0 < 2 * ε := by positivity
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hdev := mul_le_mul_of_nonneg_left (approxDevWeight_le (n := 1) le_rfl (by omega) Sfin c)
    (subspaceEta_pos (n := 1) hε2 hA0).le
  refine exists_forall_mem_interval_approxDomain_two_of_rothLemmaAt hcard hLInf hLFin hε hc
    (subspaceEta_pos hε2 hA0) (R.ratio_pos hε2 hA0) (R.factor_nonneg hε2 hA0)
    (R.shift_nonneg hε2 hA0) (R.rothLemmaAt le_rfl hε2 hA0) (by push_cast at hdev; linarith) hs
    le_rfl ?_
  have h := subspaceChainLength_spec 1 s hε2 hA0
  have e : (1 + 1) * s = 2 * s := by ring
  rw [e] at h
  have h' := Finset.lt_mul_layerRate h (by positivity)
  push_cast at h' ⊢
  norm_num at h' ⊢
  linarith

open scoped Classical in
/-- **The parametric Subspace Theorem in two variables, as an interval result** (Bugeaud–Evertse
2008, Proposition A.1, in the form of Layer 6.1's interval result). For `#ι = 2`, forms linearly
independent at every place of `S`, at most `2 s` distinct forms, and exponents with
`approxWeight ≤ -ε < 0` and `approxAbsWeight ≤ A`, there is a set `T` of at most two proper
subspaces such that
for every `Q₀' ≥ twoThreshold` the levels `Q` with `log Q ≥ Q₀'` at which the domain lies in no
member of `T` have `log Q` in at most `m = subspaceChainLength 1 s (2 ε) A` intervals
`[t, 4 σ⁻¹ t)` with `t ≥ Q₀'`, where `σ` is the ratio of the Roth lemma `R`.

Above the rank threshold the domain has rank `0` or `1` (Layer 4.3), and rank `1 = #ι - 1` is
Layer 5.6's case, so 5.6 applies to the domain itself: no wedges and no grids. -/
theorem exists_forall_mem_interval_approxDomain_two (R : SubspaceRoth.{u} K)
    (hcard : Fintype.card ι = 2) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hA : approxAbsWeight Sfin c ≤ A) {s : ℕ} (hs : formCount Sfin L ≤ 2 * s) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ 2 ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ Q₀' : ℝ, twoThreshold Sfin L R.toRothParams s ε A ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ subspaceChainLength 1 s (2 * ε) A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < 4 * (R.ratio 1 s (2 * ε) A)⁻¹ * t := by
  refine exists_forall_mem_interval_approxDomain_two_of_budget R hcard hLInf hLFin hε hc
    ((approxAbsWeight_nonneg Sfin c).trans hA) ?_ hs
  have h := budget_of_weight_le (n := 1) (by positivity : 0 < 2 * ε)
    (show approxWeight Sfin c ≤ -(2 * ε) / 2 by linarith) hA
  have e : -(2 * ε / (4 * (((1 : ℕ) : ℝ) + 1))) = -(ε / 4) := by push_cast; ring
  rw [e] at h
  push_cast at h
  linarith

open scoped Classical in
/-- **The threshold in two variables is linear in the heights**: `twoThreshold ≤ a Λ` with
`a = 1 + rankCoeff + penultimateCoeff` and `Λ = thresholdScale`. -/
theorem twoThreshold_le (R : RothParams) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (hcard : Fintype.card ι = 2) (s : ℕ)
    {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) :
    twoThreshold Sfin L R s ε A ≤ (1 + rankCoeff (finrank ℚ K) 2 #Sfin ε
      + penultimateCoeff R (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin s 1 (2 * ε) A)
        * thresholdScale Sfin L := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  let o : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hsc := thresholdScale_congr (Sfin := Sfin) (L := L)
    (fun a b ↦ @LinearOrder.toDecidableEq ι o a b) (fun a b ↦ Classical.propDecidable (a = b))
  have hΛ : 1 ≤ thresholdScale Sfin L := one_le_thresholdScale Sfin L
  have hrank := log_rankThreshold_le hLInf hLFin hε (Sfin := Sfin) (L := L)
  have hpen := penultimateThreshold_le R hLInf hLFin (n := 1) (by omega) s (ε := 2 * ε)
    (by positivity) hA (Sfin := Sfin) (L := L)
  rw [hcard, hsc] at hrank hpen
  have h1 := rankCoeff_nonneg (finrank ℚ K) 2 #Sfin hε.le
  have h2 := penultimateCoeff_nonneg R (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin s 1
    (by positivity : 0 < 2 * ε) hA
  have e1 := mul_nonneg h1 (by linarith : 0 ≤ thresholdScale Sfin L)
  have e2 := mul_nonneg h2 (by linarith : 0 ≤ thresholdScale Sfin L)
  rw [twoThreshold]
  refine max_le (by nlinarith) (max_le ?_ ?_) <;> nlinarith

open scoped Classical in
/-- **The threshold in two variables at given parameters is linear in the heights**:
`twoThresholdAt ≤ a Λ` with `a = 1 + rankCoeff + penultimateCoeffAt`. -/
theorem twoThresholdAt_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (hcard : Fintype.card ι = 2) (m : ℕ)
    {η q ε F g : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) (hF : 0 ≤ F) (hg : 0 ≤ g) :
    twoThresholdAt Sfin L m η q ε F g ≤ (1 + rankCoeff (finrank ℚ K) 2 #Sfin ε
      + penultimateCoeffAt (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin 1 m η q (2 * ε)
        F g) * thresholdScale Sfin L := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  let o : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hsc := thresholdScale_congr (Sfin := Sfin) (L := L)
    (fun a b ↦ @LinearOrder.toDecidableEq ι o a b) (fun a b ↦ Classical.propDecidable (a = b))
  have hΛ : 1 ≤ thresholdScale Sfin L := one_le_thresholdScale Sfin L
  have hrank := log_rankThreshold_le hLInf hLFin hε (Sfin := Sfin) (L := L)
  have hpen := penultimateThresholdAt_le hLInf hLFin (n := 1) (by omega) m (η := η)
    (ε := 2 * ε) hq (by positivity) hF hg (Sfin := Sfin) (L := L)
  rw [hcard, hsc] at hrank hpen
  have h1 := rankCoeff_nonneg (finrank ℚ K) 2 #Sfin hε.le
  have h2 := penultimateCoeffAt_nonneg (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin 1 m
    (η := η) hq (by positivity : 0 < 2 * ε) hF hg
  have e1 := mul_nonneg h1 (by linarith : 0 ≤ thresholdScale Sfin L)
  have e2 := mul_nonneg h2 (by linarith : 0 ≤ thresholdScale Sfin L)
  rw [twoThresholdAt]
  refine max_le (by nlinarith) (max_le ?_ ?_) <;> nlinarith

/-! ### Systems in two variables -/

section System

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

variable (E) in
open scoped Classical in
/-- **The threshold of the quantitative Subspace Theorem for a system in two variables**, on the
scale of `log H(x)`: `systemThreshold` with `twoThreshold` in place of Layer 6.1's
`parametricThreshold`. -/
noncomputable def systemThresholdTwo (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (R : RothParams) (r : ℕ) (H δ : ℝ) : ℝ :=
  max (twoThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) R
      (r * finrank K E) (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι)))
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S))))

/-- **The number of subspaces of the large solutions in two variables**: `⊥`, Layer 5.6's
exceptional subspace and, for each of its `m` intervals of ratio `4 σ⁻¹`, the windows of the gap
principle. The parameters are `e = [E : K]` and a bound `s` on the number of distinct forms over
`E`; for a system with `R` distinct forms `s = R e` (`NumberField.formCount_conjSystem_le`). -/
noncomputable def systemLargeCountTwo (R : RothParams) (e s : ℕ) (δ : ℝ) : ℝ :=
  2 + (subspaceChainLength 1 s (2 * systemEps e δ) (systemAbsBound e 2) : ℝ) *
    (1 + Real.log (4 * (R.ratio 1 s (2 * systemEps e δ) (systemAbsBound e 2))⁻¹) /
      Real.log (1 + δ / (2 * 2)))

variable [IsGalois K E]

open scoped Classical in
/-- **The quantitative Subspace Theorem for the large solutions of a system in two variables**:
Q0.3's assembly (`NumberField.exists_finset_submodule_of_forall_interval`) fed with the interval
result in two variables (`NumberField.exists_forall_mem_interval_approxDomain_two`) in place of
Layer 6.1's. -/
theorem exists_finset_submodule_of_systemThresholdTwo_le (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ systemLargeCountTwo RL.toRothParams (finrank K E) (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        systemThresholdTwo E S w L RL.toRothParams R H δ ≤ Real.log (mulHeightAff x) →
        ∃ U ∈ T, x ∈ U := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  set e := finrank K E with he
  set dE := finrank ℚ E with hdE
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set ε := systemEps e δ with hε
  set A := systemAbsBound e (Fintype.card ι) with hA
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hε2 : 0 < 2 * ε := by positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  set s := R * e with hs
  have hsE : formCount Sfin' L' ≤ 2 * s :=
    (formCount_conjSystem_le hwInf hwFin hN.ncard_le).trans (Nat.le_mul_of_pos_left _ two_pos)
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := systemThresholdTwo E S w L RL.toRothParams R H δ with hX₀
  have hX₀P : twoThreshold Sfin' L' RL.toRothParams s ε A ≤ X₀ := le_max_left _ _
  set σ := RL.ratio 1 s (2 * ε) A with hσ
  have hσ0 : 0 < σ := RL.ratio_pos hε2 hA0
  have hσ1 : σ ≤ 1 := RL.ratio_le_one hε2 hA0
  have hρ1 : 1 ≤ 4 * σ⁻¹ := by
    have : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  obtain ⟨T, hTcard, hTtop, hT⟩ := exists_finset_submodule_of_forall_interval S w hwInf hwFin hN
    (X₀ := X₀) (ρ := 4 * σ⁻¹) (NS := 2)
    (NI := subspaceChainLength 1 s (2 * ε) A)
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    hρ1 fun c' hcw hcA _ _ ↦ by
      obtain ⟨T, hTcard, hTtop, hint⟩ :=
        exists_forall_mem_interval_approxDomain_two (K := E) (Sfin := Sfin') (L := L') RL hcard
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA hsE
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ hX₀P
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩
  refine ⟨T, hTcard.trans_eq ?_, hTtop, hT⟩
  simp only [systemLargeCountTwo, hσ, hA, hε, hs, hcard]
  push_cast
  ring

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system in two variables**: all solutions lie in at
most Layer 9.3's count, plus one interval of Layer 9.4 below `X₀ = systemThresholdTwo`, plus
`systemLargeCountTwo` proper subspaces. -/
theorem exists_finset_submodule_of_isNormalizedSystem_two (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * H))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) H δ
            (systemThresholdTwo E S w L RL.toRothParams R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCountTwo RL.toRothParams (finrank K E) (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_of_large S w hwInf hwFin hN
    (exists_finset_submodule_of_systemThresholdTwo_le RL hcard S w hwInf hwFin hN)

open scoped Classical in
/-- **The threshold in two variables is linear in the height of the coefficients**: as
`NumberField.systemThreshold_le`, with the coefficient of `twoThreshold_le` in place of
`parametricCoeff`. -/
theorem systemThresholdTwo_le (RL : RothParams) (hcard : Fintype.card ι = 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemThresholdTwo E S w L RL R H δ ≤
      max ((1 + rankCoeff (finrank ℚ E) 2 #(systemPlacesOver E S) (systemEps (finrank K E) δ)
          + penultimateCoeff RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
            #(systemPlacesOver E S) (R * finrank K E) 1 (2 * systemEps (finrank K E) δ)
            (systemAbsBound (finrank K E) (Fintype.card ι)))
          * ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hε : 0 < systemEps (finrank K E) δ := by rw [systemEps]; positivity
  have hA : 0 ≤ systemAbsBound (finrank K E) (Fintype.card ι) := by
    rw [systemAbsBound]; positivity
  refine max_le_max ?_ le_rfl
  refine (twoThreshold_le RL (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) hcard (R * finrank K E) hε hA).trans ?_
  have h1 := rankCoeff_nonneg (finrank ℚ E) 2 #(systemPlacesOver E S) hε.le
  have h2 := penultimateCoeff_nonneg RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
    #(systemPlacesOver E S) (R * finrank K E) 1
    (by positivity : 0 < 2 * systemEps (finrank K E) δ) hA
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

omit [IsGalois K E] in
/-- **The count in two variables with Evertse's Roth lemma, in closed form.** With at most `s`
distinct forms over `E` (`s = R e` for `R` forms of the system), `ℓ = 1 + log (4 s)` and
`Y = 449 / δ`,

`systemLargeCountTwo ≤ 2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)`.

The intervals number at most `T ≤ 2 ℓ Y²`, their ratio is at most `16 T X ≤ 32 ℓ Y³`
(`four_mul_inv_evertseRatio_le`), and `log (1 + δ / 4) ≥ δ / 5`. The main term is
`O(δ⁻³ log s · log (δ⁻¹ log s))`: Bugeaud–Evertse's shape. -/
theorem systemLargeCountTwo_evertse_le (b : ℕ → ℝ) {e s : ℕ} (he : 1 ≤ e)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    systemLargeCountTwo (RothParams.evertse b) e s δ ≤
      2 + 2 * (1 + Real.log (4 * (s : ℝ))) * (449 / δ) ^ 2 *
        (1 + 5 * Real.log (32 * (1 + Real.log (4 * (s : ℝ))) * (449 / δ) ^ 3) / δ) := by
  set ε := 2 * systemEps e δ with hε
  set A := systemAbsBound e 2 with hA
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  set X := evertseEtaInvBound 1 ε A with hX
  set T := evertseChainBound 1 s ε A with hT
  set Y : ℝ := 449 / δ with hY
  set ℓ : ℝ := 1 + Real.log (4 * (s : ℝ)) with hℓ
  have hℓ0 : 0 ≤ Real.log (4 * (s : ℝ)) := by
    have : (4 * (s : ℝ)) = ((4 * s : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.log_natCast_nonneg _
  have hX1 : 1 ≤ X := one_le_evertseEtaInvBound 1 hε0 hA0
  -- `X ≤ Y`
  have hXY : X ≤ Y := by
    have hAe : A + 1 ≤ 7 * e := by
      rw [hA, systemAbsBound]
      push_cast
      linarith
    have h1 : 8 * ((1 : ℕ) + 1 : ℝ) ^ 2 * (A + 1) / ε ≤ 448 / δ := by
      rw [div_le_div_iff₀ hε0 hδ, hε, systemEps]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hAe (by positivity : (0 : ℝ) ≤ δ)]
    have h2 : 1 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    rw [hX, evertseEtaInvBound, hY]
    have : (449 : ℝ) / δ = 448 / δ + 1 / δ := by ring
    rw [this]
    linarith
  have hY0 : 0 ≤ Y := by positivity
  -- `T ≤ 2 ℓ Y²`
  have hTY : T ≤ 2 * ℓ * Y ^ 2 := by
    rw [hT, evertseChainBound, hℓ]
    have : (2 * (((1 : ℕ) : ℝ) + 1) * (s : ℝ)) = 4 * s := by push_cast; ring
    rw [this]
    gcongr
  have hm : (subspaceChainLength 1 s ε A : ℝ) ≤ 2 * ℓ * Y ^ 2 := by
    have := subspaceChainLength_add_one_le 1 s hε0 hA0
    linarith
  -- the ratio
  have hσ0 : 0 < evertseRatio 1 s ε A := (RothParams.evertse b).ratio_pos hε0 hA0
  have hσ1 : evertseRatio 1 s ε A ≤ 1 := (RothParams.evertse b).ratio_le_one hε0 hA0
  have hρ1 : 1 ≤ 4 * (evertseRatio 1 s ε A)⁻¹ := by
    have : 1 ≤ (evertseRatio 1 s ε A)⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  have hρY : 4 * (evertseRatio 1 s ε A)⁻¹ ≤ 32 * ℓ * Y ^ 3 := by
    refine (four_mul_inv_evertseRatio_le 1 s hε0 hA0).trans ?_
    rw [← hT, ← hX]
    have hT0 : 0 ≤ T := (two_le_evertseChainBound 1 s hε0 hA0).trans' zero_le_two
    calc 16 * T * X ≤ 16 * (2 * ℓ * Y ^ 2) * Y := by gcongr
      _ = 32 * ℓ * Y ^ 3 := by ring
  have hlogρ : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) ≤ Real.log (32 * ℓ * Y ^ 3) :=
    Real.log_le_log (by linarith) hρY
  have hlogρ0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) := Real.log_nonneg hρ1
  -- `log (1 + δ / 4) ≥ δ / 5`
  have hL : δ / 5 ≤ Real.log (1 + δ / (2 * 2)) := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos (by positivity))
    rw [show (1 : ℝ) - (1 + δ / (2 * 2))⁻¹ = δ / (4 + δ) by field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hW : 1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2))
      ≤ 1 + 5 * Real.log (32 * ℓ * Y ^ 3) / δ := by
    have hδ5 : 0 < δ / 5 := by positivity
    have := div_le_div₀ (hlogρ0.trans hlogρ) hlogρ hδ5 hL
    rw [show Real.log (32 * ℓ * Y ^ 3) / (δ / 5) = 5 * Real.log (32 * ℓ * Y ^ 3) / δ by
      field_simp] at this
    linarith
  have hW0 : 0 ≤ 1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)) :=
    add_nonneg zero_le_one (div_nonneg hlogρ0 ((by positivity : (0 : ℝ) ≤ δ / 5).trans hL))
  rw [systemLargeCountTwo]
  change _ + _ * (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / _) ≤ _
  refine add_le_add le_rfl ?_
  calc (subspaceChainLength 1 s ε A : ℝ) *
        (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)))
      ≤ 2 * ℓ * Y ^ 2 * (1 + 5 * Real.log (32 * ℓ * Y ^ 3) / δ) :=
        mul_le_mul hm hW hW0 (by positivity)
    _ = _ := by rw [hℓ, hY]

/-- **The quantitative Subspace Theorem for a system in two variables, with Evertse's Roth
lemma** (Q1.6, Bugeaud–Evertse's case):
`NumberField.exists_finset_submodule_of_isNormalizedSystem_two` run with
`NumberField.SubspaceRoth.evertse`. Its large count is bounded in closed form by
`NumberField.systemLargeCountTwo_evertse_le`. -/
theorem exists_finset_submodule_of_isNormalizedSystem_two_evertse
    (Hm : ∀ m : ℕ, MultiprojectiveHeight (K := E) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * H))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) H δ
            (systemThresholdTwo E S w L (RothParams.evertse fun m ↦ (Hm m).botBound 1) R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCountTwo (RothParams.evertse fun m ↦ (Hm m).botBound 1) (finrank K E)
          (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_two (SubspaceRoth.evertse.{u} Hm) hcard S w
    hwInf hwFin hN

/-! ### A gap principle of the caller's -/

open scoped Classical in
/-- **The large solutions of a system in two variables lie in two subspaces or in `m` height
intervals**: for every `X₀ ≥ systemThresholdTwo`, at most two proper subspaces and at most
`m = subspaceChainLength 1 s (2 ε) A` intervals `[s, 4 σ⁻¹ s)`, `s ≥ X₀`, of `log H(x)`, with
`s = R [E : K]`, `ε = systemEps [E : K] δ`, `A = systemAbsBound [E : K] 2` and `σ` the ratio of
the Roth lemma. `NumberField.exists_forall_mem_interval_systemSet` fed with the interval result
in two variables; over `ℚ`, the generic parameters of [Ste26], §7.3. -/
theorem exists_forall_mem_interval_systemSet_two (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ : ℝ}
    (hX₀ : systemThresholdTwo E S w L RL.toRothParams R H δ ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ subspaceChainLength 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
          (systemAbsBound (finrank K E) 2) ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
        ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ s ∈ 𝒯, s ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) <
              4 * (RL.ratio 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
                (systemAbsBound (finrank K E) 2))⁻¹ * s := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  have hε0 : 0 < systemEps (finrank K E) δ := by
    have := hN.delta_pos
    have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
    rw [systemEps]; positivity
  have hsE : formCount (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) ≤
      2 * (R * finrank K E) :=
    (formCount_conjSystem_le hwInf hwFin hN.ncard_le).trans (Nat.le_mul_of_pos_left _ two_pos)
  have hX₀T := (le_max_right _ _).trans hX₀
  have hX₀P : twoThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)
      RL.toRothParams (R * finrank K E) (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι)) ≤ X₀ := (le_max_left _ _).trans hX₀
  rw [hcard] at hX₀P
  have h := exists_forall_mem_interval_systemSet S w hwInf hwFin hN (X₀ := X₀)
    (ρ := 4 * (RL.ratio 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) 2))⁻¹) (NS := 2)
    (NI := subspaceChainLength 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) 2))
    ((le_max_right _ _).trans hX₀T) ((le_max_left _ _).trans hX₀T) fun c' hcw hcA _ _ ↦ by
      rw [hcard] at hcA
      obtain ⟨T, hTcard, hTtop, hint⟩ :=
        exists_forall_mem_interval_approxDomain_two (K := E) RL hcard
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA hsE
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ hX₀P
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩
  exact h

variable (E) in
open scoped Classical in
/-- **The threshold of the interval result for a system in two variables, at given parameters**:
`systemThresholdTwo` with the margin `ε`, the parameter `A` and the form count `s` of the
caller's, and with the scalar costing a fraction `τ` of `δ`, so with `systemHeightThreshold`
divided by `2 τ` (`NumberField.exists_forall_mem_interval_systemSet_of_shift`). -/
noncomputable def systemThresholdTwoAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (R : RothParams) (s : ℕ) (H δ τ ε A : ℝ) : ℝ :=
  max (twoThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) R s ε A)
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S)) / (2 * τ)))

variable (E) in
open scoped Classical in
/-- **The threshold of the interval result for a system in two variables, at explicit
parameters**: `systemThresholdTwoAt` with `twoThresholdAt` for the chain length `m`, `η`,
Siegel's exponent `q` and the height cost `F`, `g` of the Roth lemma (the `X₁` of [Ste26],
Theorem 7.2). -/
noncomputable def systemThresholdTwoExplicit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (m : ℕ) (H δ τ η q ε F g : ℝ) : ℝ :=
  max (twoThresholdAt (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) m η q
      ε F g)
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S)) / (2 * τ)))

omit [IsGalois K E] in
/-- `systemThresholdTwoAt` is `systemThresholdTwoExplicit` at the parameters of Steps IV and VI. -/
theorem systemThresholdTwoAt_eq_explicit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (R : RothParams) (s : ℕ) (H δ τ ε A : ℝ) :
    systemThresholdTwoAt E S w L R s H δ τ ε A = systemThresholdTwoExplicit E S w L
      (subspaceChainLength 1 s (2 * ε) A) H δ τ (subspaceEta 1 (2 * ε) A) 1 ε
      (R.factor 1 s (2 * ε) A) (R.shift 1 s (2 * ε) A) := by
  rw [systemThresholdTwoAt, systemThresholdTwoExplicit, twoThreshold_eq_at]

open scoped Classical in
/-- **The threshold at explicit parameters is linear in the height of the coefficients**: as
`NumberField.systemThresholdTwoAt_le`, for the chain length `m`, `η` and the height cost `F`, `g`
of the Roth lemma. -/
theorem systemThresholdTwoExplicit_le (hcard : Fintype.card ι = 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (m : ℕ) (τ : ℝ) {η q ε F g : ℝ} (hq : 0 ≤ q)
    (hε : 0 < ε) (hF : 0 ≤ F) (hg : 0 ≤ g) :
    systemThresholdTwoExplicit E S w L m H δ τ η q ε F g ≤
      max ((1 + rankCoeff (finrank ℚ E) 2 #(systemPlacesOver E S) ε
          + penultimateCoeffAt (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
            #(systemPlacesOver E S) 1 m η q (2 * ε) F g)
          * ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) / (2 * τ))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have h1 := rankCoeff_nonneg (finrank ℚ E) 2 #(systemPlacesOver E S) hε.le
  have h2 := penultimateCoeffAt_nonneg (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
    #(systemPlacesOver E S) 1 m (η := η) hq (by positivity : 0 < 2 * ε) hF hg
  refine max_le_max ?_ le_rfl
  refine (twoThresholdAt_le (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) hcard m hq hε hF hg).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

open scoped Classical in
/-- **The threshold at given parameters is linear in the height of the coefficients**: as
`NumberField.systemThresholdTwo_le`, at the margin `ε`, the parameter `A`, the form count `s`
and the fraction `τ`. -/
theorem systemThresholdTwoAt_le (RL : RothParams) (hcard : Fintype.card ι = 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (s : ℕ) (τ : ℝ) {ε A : ℝ} (hε : 0 < ε)
    (hA0 : 0 ≤ A) :
    systemThresholdTwoAt E S w L RL s H δ τ ε A ≤
      max ((1 + rankCoeff (finrank ℚ E) 2 #(systemPlacesOver E S) ε
          + penultimateCoeff RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
            #(systemPlacesOver E S) s 1 (2 * ε) A)
          * ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) / (2 * τ))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have h1 := rankCoeff_nonneg (finrank ℚ E) 2 #(systemPlacesOver E S) hε.le
  have h2 := penultimateCoeff_nonneg RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
    #(systemPlacesOver E S) s 1 (by positivity : 0 < 2 * ε) hA0
  refine max_le_max ?_ le_rfl
  refine (twoThreshold_le RL (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) hcard s hε hA0).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

open scoped Classical in
/-- **The large solutions of a system in two variables lie in two subspaces or in `m` height
intervals, at explicit parameters.** As `NumberField.exists_forall_mem_interval_systemSet_two_at`,
with the chain length `m`, the `η` of the auxiliary polynomial and a generalized Roth lemma
`RothLemmaAt E 1 m η σ F g` chosen by the caller: the budget `-W / 2 + η · min (2 A₀) D₀ ≤ -ε / 4`,
`W = [E : K] (1 - τ) δ`, `A₀ = [E : K] (2 P + (1 + τ) δ)`, `P = systemPosWeight c`,
`D₀ = [E : K] (2 (2 + δ) + N)`, `N = systemNegWeight c` (`0` when every place has a nonnegative
exponent), and Layer 5.2's
condition `log ((q + 1) / q · f) < (m + 1) · layerRate 1 η` for `f ≥ R [E : K]` and Siegel's
exponent `q ≥ 1` give at most `m` intervals of ratio `4 σ⁻¹`. The margin `ε ≤ W` is now free of
`η`: `η` may take almost all of the budget, `η → W / (4 A₀)` as `ε → 0`, at the cost of a
threshold `∝ ε⁻¹`. Over `ℚ` this is Theorem 7.2 of [Ste26], with `η`, `q`, `ε` its `η_R`, `ν`,
`ε₀`, the budget (11), the chain condition (12) (`Λ = layerRate 1`) and items (a)–(g) there. -/
theorem exists_forall_mem_interval_systemSet_two_of_rothLemmaAt (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hεW : ε ≤ finrank K E * ((1 - τ) * δ)) {m : ℕ} {η σ F g : ℝ} (hη0 : 0 < η) (hσ0 : 0 < σ)
    (hF0 : 0 ≤ F) (hg0 : 0 ≤ g) (hRL : RothLemmaAt.{u} E 1 m η σ F g)
    (hbudget : -(finrank K E * ((1 - τ) * δ)) / 2 + η *
      min (2 * (finrank K E * (2 * systemPosWeight c + (1 + τ) * δ)))
        (finrank K E * (2 * (2 + δ) + systemNegWeight c)) ≤ -(ε / 4))
    {f : ℕ} (hf : R * finrank K E ≤ f) {q : ℝ} (hq : 1 ≤ q)
    (hm : Real.log ((q + 1) / q * (f : ℝ)) < ((m : ℝ) + 1) * Finset.layerRate 1 η) {X₀ : ℝ}
    (hX₀ : systemThresholdTwoExplicit E S w L m H δ τ η q ε F g ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ m ∧ (∀ t ∈ 𝒯, X₀ ≤ t) ∧
        ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) <
              4 * σ⁻¹ * t := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  have hsE : formCount (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) ≤
      f := (formCount_conjSystem_le hwInf hwFin hN.ncard_le).trans hf
  have hX₀T := (le_max_right _ _).trans hX₀
  have hX₀P := (le_max_left _ _).trans hX₀
  have hX₀H : systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
      (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) ≤ 2 * τ * X₀ := by
    have h := (le_max_right _ _).trans hX₀T
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  exact exists_forall_mem_interval_systemSet_of_shift S w hwInf hwFin hN hτ hX₀H
    ((le_max_left _ _).trans hX₀T) fun c' hcw hcA _ hcD ↦ by
      have hdev : approxDevWeight (systemPlacesOver E S) c' ≤
          min (2 * (finrank K E * (2 * systemPosWeight c + (1 + τ) * δ)))
            (finrank K E * (2 * (2 + δ) + systemNegWeight c)) := by
        refine le_min ((approxDevWeight_le (n := 1) le_rfl (by omega) _ c').trans ?_) ?_
        · push_cast
          linarith
        · rw [hcard] at hcD
          push_cast at hcD
          exact hcD
      obtain ⟨T, hTcard, hTtop, hint⟩ :=
        exists_forall_mem_interval_approxDomain_two_of_rothLemmaAt (K := E) hcard
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε
          (by rw [hcw]; linarith) hη0 hσ0 hF0 hg0 hRL (by
            rw [hcw]
            have := mul_le_mul_of_nonneg_left hdev hη0.le
            linarith) hsE hq hm
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ hX₀P
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩

open scoped Classical in
/-- **The large solutions of a system in two variables lie in two subspaces or in `m` height
intervals, from the weight budget.** `NumberField.exists_forall_mem_interval_systemSet_two` with
the parameters chosen by the caller: the scalar costs a fraction `τ` of `δ`, so the exponents of
the domain have weight exactly `-W`, `W = [E : K] (1 - τ) δ`, and absolute weight at most
`A₀ = [E : K] (2 P + (1 + τ) δ)`, `P = systemPosWeight c`; any margin `ε ≤ W` and parameter
`A ≥ 0` with `-W / 2 + 2 η A₀ ≤ -ε / 4`, `η = subspaceEta 1 (2 ε) A`, and any `s` with
`R [E : K] ≤ 2 s`, give at most `m = subspaceChainLength 1 s (2 ε) A` intervals of ratio `4 σ⁻¹`.
With `A = 0` and `ε = 4 W / (A₀ + 2)` this is `η = W / (4 (A₀ + 2))`, against
`[E : K] δ / (64 (6 [E : K] + 1))` for `systemEps` and `systemAbsBound`. -/
theorem exists_forall_mem_interval_systemSet_two_at (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {τ ε A : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hεW : ε ≤ finrank K E * ((1 - τ) * δ)) (hA0 : 0 ≤ A)
    (hbudget : -(finrank K E * ((1 - τ) * δ)) / 2 + 2 * subspaceEta 1 (2 * ε) A *
      (finrank K E * (2 * systemPosWeight c + (1 + τ) * δ)) ≤ -(ε / 4))
    {s : ℕ} (hs : R * finrank K E ≤ 2 * s) {X₀ : ℝ}
    (hX₀ : systemThresholdTwoAt E S w L RL.toRothParams s H δ τ ε A ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ subspaceChainLength 1 s (2 * ε) A ∧ (∀ t ∈ 𝒯, X₀ ≤ t) ∧
        ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) <
              4 * (RL.ratio 1 s (2 * ε) A)⁻¹ * t := by
  rw [systemThresholdTwoAt_eq_explicit] at hX₀
  have hε2 : 0 < 2 * ε := by positivity
  refine exists_forall_mem_interval_systemSet_two_of_rothLemmaAt hcard S w hwInf hwFin hN hτ hε hεW
    (subspaceEta_pos hε2 hA0) (RL.ratio_pos hε2 hA0) (RL.factor_nonneg hε2 hA0)
    (RL.shift_nonneg hε2 hA0) (RL.rothLemmaAt le_rfl hε2 hA0) (by
      have := mul_le_mul_of_nonneg_left (min_le_left
        (2 * (finrank K E * (2 * systemPosWeight c + (1 + τ) * δ)))
        (finrank K E * (2 * (2 + δ) + systemNegWeight c)))
        (subspaceEta_pos (n := 1) hε2 hA0).le
      linarith) hs le_rfl ?_ hX₀
  have h := subspaceChainLength_spec 1 s hε2 hA0
  have e : (1 + 1) * s = 2 * s := by ring
  rw [e] at h
  have h' := Finset.lt_mul_layerRate h (by positivity)
  push_cast at h' ⊢
  norm_num at h' ⊢
  linarith

/-- **The number of subspaces in two variables with a gap principle of the caller's**: `⊥` and
Layer 5.6's exceptional subspace; for each of the `m` intervals of ratio `4 σ⁻¹`, at most
`1 + log (4 σ⁻¹) / log ρ` lines; and `1 + log (X₀ / Y) / log ρ` lines with `log H(x)` in
`[Y, X₀)`. It is `systemLargeCountTwo` with `ρ` in place of `1 + δ / 4`, plus the range below
`X₀`; the count `N(δ)` of Theorem 7.6 of [Ste26] has this shape. -/
noncomputable def systemGapCountTwo (R : RothParams) (e s : ℕ) (δ ρ X₀ Y : ℝ) : ℝ :=
  2 + (subspaceChainLength 1 s (2 * systemEps e δ) (systemAbsBound e 2) : ℝ) *
      (1 + Real.log (4 * (R.ratio 1 s (2 * systemEps e δ) (systemAbsBound e 2))⁻¹) /
        Real.log ρ) +
    (1 + Real.log (X₀ / Y) / Real.log ρ)

open scoped Classical in
/-- **The quantitative Subspace Theorem in two variables with a gap principle of the caller's.**
Let `X` be a set of solutions of a normalized system in two variables such that any two `x, y ∈ X`
on distinct lines with `Y ≤ log H(x) ≤ log H(y)` have `ρ log H(x) ≤ log H(y)`, for some
`ρ > 1` and `Y > 0`. Then for every `X₀ ≥ max (Y, systemThresholdTwo)` the `x ∈ X` with
`log H(x) ≥ Y` lie in at most `systemGapCountTwo` proper subspaces: the interval result
(`NumberField.exists_forall_mem_interval_systemSet_two`) above `X₀`, each of its intervals and the
range `[Y, X₀)` counted with the caller's gap (`Submodule.exists_finset_span_singleton_of_lacunary`)
in place of Layer 9.4's ratio `1 + δ / 4`. No count for the solutions below `Y` is included.

This is the count of Remark 7.7 of [Ste26] (at the generic parameters; Theorem 7.6 there counts
the same way after `NumberField.exists_forall_mem_interval_systemSet_two_of_rothLemmaAt`), where
the exceptions to `‖(3/2)^n‖ ≥ (3/4)^n` have the gap `ρ₀ = 1.2618` from `n > 10⁵` on, against
`1 + δ / 4 ≈ 1.065`. -/
theorem exists_finset_submodule_of_gap_two (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ : ℝ}
    (hX₀ : systemThresholdTwo E S w L RL.toRothParams R H δ ≤ X₀) {X : Set (ι → K)}
    (hX : X ⊆ systemSet S w L C c) {ρ Y : ℝ} (hρ : 1 < ρ) (hY : 0 < Y) (hYX₀ : Y ≤ X₀)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, Y ≤ Real.log (mulHeightAff x) →
      Real.log (mulHeightAff x) ≤ Real.log (mulHeightAff y) → K ∙ x ≠ K ∙ y →
        ρ * Real.log (mulHeightAff x) ≤ Real.log (mulHeightAff y)) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ systemGapCountTwo RL.toRothParams (finrank K E) (R * finrank K E) δ ρ X₀ Y ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ X, Y ≤ Real.log (mulHeightAff x) → ∃ U ∈ T, x ∈ U := by
  obtain ⟨T₁, hT₁, hT₁top, 𝒯, h𝒯, h𝒯ge, hint⟩ :=
    exists_forall_mem_interval_systemSet_two RL hcard S w hwInf hwFin hN hX₀
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hε2 : 0 < 2 * systemEps (finrank K E) δ := by rw [systemEps]; positivity
  have hA0 : (0 : ℝ) ≤ systemAbsBound (finrank K E) 2 := by rw [systemAbsBound]; positivity
  set m := subspaceChainLength 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
    (systemAbsBound (finrank K E) 2) with hm
  set σ := RL.ratio 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
    (systemAbsBound (finrank K E) 2) with hσ
  have hσ0 : 0 < σ := RL.ratio_pos hε2 hA0
  have hσ1 : σ ≤ 1 := RL.ratio_le_one hε2 hA0
  have hρ'1 : 1 ≤ 4 * σ⁻¹ := by
    have : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  have hV : 1 < finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]; norm_num
  -- one window of `log H`
  have hwin : ∀ a b, Y ≤ a → a ≤ b → ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ 1 + Real.log (b / a) / Real.log ρ ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x ∈ X, a ≤ Real.log (mulHeightAff x) → Real.log (mulHeightAff x) < b →
          ∃ U ∈ T, x ∈ U := fun a b hYa hab ↦
    Submodule.exists_finset_span_singleton_of_lacunary hV (fun x ↦ Real.log (mulHeightAff x)) hρ
      (hY.trans_le hYa) hab fun x hx y hy hax hxy hne ↦ hgap x hx y hy (hYa.trans hax) hxy hne
  have hw𝒯 : ∀ s ∈ 𝒯, ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ 1 + Real.log (4 * σ⁻¹) / Real.log ρ ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x ∈ X, s ≤ Real.log (mulHeightAff x) → Real.log (mulHeightAff x) < 4 * σ⁻¹ * s →
          ∃ U ∈ T, x ∈ U := by
    intro s hs
    have hYs := hYX₀.trans (h𝒯ge s hs)
    have hs0 : 0 < s := hY.trans_le hYs
    obtain ⟨T, hT, hTtop, hTmem⟩ := hwin s (4 * σ⁻¹ * s) hYs (le_mul_of_one_le_left hs0.le hρ'1)
    refine ⟨T, ?_, hTtop, hTmem⟩
    rwa [mul_div_assoc, div_self hs0.ne', mul_one] at hT
  choose! Tw hTw using hw𝒯
  obtain ⟨T₀, hT₀, hT₀top, hT₀mem⟩ := hwin Y X₀ le_rfl hYX₀
  refine ⟨T₁ ∪ 𝒯.biUnion Tw ∪ T₀, ?_, fun U hU ↦ ?_, fun x hx hYx ↦ ?_⟩
  · have hper : 0 ≤ 1 + Real.log (4 * σ⁻¹) / Real.log ρ :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hρ'1) (Real.log_pos hρ).le)
    have h1 : (#(T₁ ∪ 𝒯.biUnion Tw ∪ T₀) : ℝ) ≤ #T₁ + #(𝒯.biUnion Tw) + #T₀ := by
      exact_mod_cast (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h2 : (#(𝒯.biUnion Tw) : ℝ) ≤ m * (1 + Real.log (4 * σ⁻¹) / Real.log ρ) :=
      calc (#(𝒯.biUnion Tw) : ℝ) ≤ ∑ s ∈ 𝒯, (#(Tw s) : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ 𝒯, (1 + Real.log (4 * σ⁻¹) / Real.log ρ) :=
            Finset.sum_le_sum fun s hs ↦ (hTw s hs).1
        _ = #𝒯 * (1 + Real.log (4 * σ⁻¹) / Real.log ρ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ m * (1 + Real.log (4 * σ⁻¹) / Real.log ρ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h𝒯) hper
    have h3 : (#T₁ : ℝ) ≤ 2 := by exact_mod_cast hT₁
    rw [systemGapCountTwo, ← hm, ← hσ]
    linarith
  · rcases Finset.mem_union.1 hU with hU | hU
    · rcases Finset.mem_union.1 hU with hU | hU
      · exact hT₁top U hU
      · obtain ⟨s, hs, hU⟩ := Finset.mem_biUnion.1 hU
        exact (hTw s hs).2.1 U hU
    · exact hT₀top U hU
  · by_cases hlt : Real.log (mulHeightAff x) < X₀
    · obtain ⟨U, hU, hxU⟩ := hT₀mem x hx hYx hlt
      exact ⟨U, Finset.mem_union_right _ hU, hxU⟩
    push Not at hlt
    rcases hint x (hX hx) hlt with ⟨U, hU, hxU⟩ | ⟨s, hs, h1, h2⟩
    · exact ⟨U, Finset.mem_union_left _ (Finset.mem_union_left _ hU), hxU⟩
    · obtain ⟨U, hU, hxU⟩ := (hTw s hs).2.2 x hx h1 h2
      exact ⟨U, Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨s, hs, hU⟩)), hxU⟩

end System

end NumberField
