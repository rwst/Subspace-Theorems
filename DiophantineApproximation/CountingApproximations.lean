/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GapPrinciple
public import DiophantineApproximation.RothTheorem

/-!
# Counting approximations

Roth's theorem (Layer 3.2) says that `Λ(β) ≤ H(β) ^ (−κ)` has finitely many solutions `β ∈ K` for
`κ > 2`. This file bounds **how many**, following Bombieri–Gubler 6.5.3 to 6.5.7 (Davenport and
Roth 1955 at one place). Heights are absolute and logarithmic throughout, and
`c = (1 − |S| / N) κ − 1` is the constant of the strong gap principle
(`DiophantineApproximation/GapPrinciple.lean`).

* **The count in a window** (Lemma 6.5.6). When `c > 1` and `X ≥ log 16 / (c − 1)`, at most
  `⌈log A / log ((c + 1) / 2)⌉ (N + |S|).choose |S|` solutions have height in `(X, A X]`. Inside
  one approximation class the gap principle makes the heights grow by the factor `(c + 1) / 2`,
  so a window of ratio `A` holds at most `⌈log A / log ((c + 1) / 2)⌉` of them, and Lemma 6.4.3
  counts the classes.
* **The count of large solutions** (6.5.7). With Roth's parameters `N = rothClassSize κ s`,
  `m = rothChainLength κ s r` and `M = rothRatio κ s r`, where `s = |S|` and `r = [F : K]`, there
  is a height `L` above which there are at most `m ⌈log M / log ((c + 1) / 2)⌉ (N + s).choose s`
  solutions. The core of Roth's proof, `NumberField.roth_no_chain`, forbids a chain of `m + 1`
  solutions in one class whose heights grow by the factor `M`; the book's greedy grouping then
  leaves at most `m` blocks of ratio `M` in each class, and the window count bounds each block.

The combinatorics is in two lemmas that know nothing of heights: points with a multiplicative gap
in a window, and a finite set without long chains.

## Main definitions

* `NumberField.rothLargeCount`: the bound on the number of large solutions, a function of `κ`,
  `|S|` and `[F : K]`.

## Main results

* `Set.ncard_le_ceil_mul_ncard_of_gap` and `Set.ncard_le_ceil_mul_ncard_of_gap_Ioc`: points with a
  multiplicative gap in a window of ratio `A` number at most `⌈log A / log q⌉` per label.
* `Finset.card_le_mul_of_not_exists_chain`: a finite set whose blocks have at most `k` points and
  which has no chain of `m + 1` points has at most `m k` points.
* `NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le`: **Lemma 6.5.6**, the count in a window.
* `NumberField.exists_ncard_setOf_lt_absLogHeight₁_le`: **6.5.7**, the count of large solutions.
* `NumberField.one_lt_rothGap`: the classes Roth's proof uses have gap constant `c > 1`.

## Implementation notes

⚠ **Counting the large solutions needed Roth's proof restructured, not quoted.** Roth's theorem is
a finiteness statement, and a finite set can be as large as it likes; what the count consumes is
the statement *inside* the proof — no chain of `m + 1` solutions in one class above a height `L`
— with `m`, `M` and `N` visibly depending on `κ`, `|S|` and `[F : K]` alone. Layer 3.2 proved it
only inside a proof by contradiction; `DiophantineApproximation/RothTheorem.lean` now proves it as
`NumberField.roth_no_chain`, with the parameters as definitions, and derives Roth's theorem from
it. The book's 6.5.7 does the same by pointing back into its proof.

⚠ **Nothing is effective, and the asymmetry is in the statement.** The bound on the large
solutions is a bound on their **number**. `L` is explicit, but nothing here bounds the height of a
solution above `L`, and nothing can be read off the proof: it shows that a chain cannot be long,
never where it ends. That is the ineffectivity of Roth's method.

⚠ **The window hypothesis is `X ≥ log 16 / (c − 1)`, not `>`.** The book states Lemma 6.5.6 with
the strict inequality and applies it in 6.5.7 (b) at equality; the proof needs only `≤`. The
count of small solutions it then states, `⌈log L / log ((c + 1) / 2)⌉ (N + |S|).choose |S|`, has
`log L` where the lemma gives `log (L / X)`; the first bounds the second only when `X ≥ 1`, that
is when `c ≤ 1 + log 16`. The acceptance criteria state the count the lemma gives.

⚠ **The book multiplies by the number of variables; the bound here uses one less.** No chain of
`m + 1` solutions means at most `m` blocks per class, and `m + 1` is the number of variables of the
auxiliary polynomial. The book's `m` is its number of variables, so its bound is larger by one
block per class.

⚠ **The very small solutions are left to Northcott, as in the book.** Those of height at most
`log 16 / (c − 1)` are finitely many, but their number depends on `K`, and no count of them is
stated.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.5.6 and §6.5.7. H. Davenport and K. F. Roth, "Rational approximations to algebraic
numbers", *Mathematika* 2 (1955), 160–167.

This is the second half of Layer 3.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Module

/-! ### Two counting lemmas -/

namespace Set

/-- **Points with a multiplicative gap in a window.** If the points of `T` carry labels in a
finite set `C`, have heights in `[Y, A Y)` with `Y > 0`, and any two different points with one
label have heights at least a factor `q > 1` apart, then `T` has at most
`⌈log A / log q⌉ · |C|` points. -/
theorem ncard_le_ceil_mul_ncard_of_gap {ι γ : Type*} {T : Set ι} {C : Set γ} (hC : C.Finite)
    (lab : ι → γ) (hlab : ∀ x ∈ T, lab x ∈ C) (h : ι → ℝ) {Y A q : ℝ} (hY : 0 < Y) (hq : 1 < q)
    (hT : ∀ x ∈ T, Y ≤ h x ∧ h x < A * Y)
    (hgap : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lab x = lab y → h x ≤ h y → q * h x ≤ h y) :
    T.ncard ≤ ⌈Real.log A / Real.log q⌉₊ * C.ncard := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hq0 : 0 < q := by linarith
  set u : ι → ℝ := fun x ↦ Real.log (h x / Y) / Real.log q with hudef
  have hu0 : ∀ x ∈ T, 0 ≤ u x := fun x hx ↦
    div_nonneg (Real.log_nonneg ((one_le_div hY).mpr (hT x hx).1)) hlq.le
  have hut : ∀ x ∈ T, u x < Real.log A / Real.log q := fun x hx ↦ by
    have hx0 : 0 < h x := lt_of_lt_of_le hY (hT x hx).1
    refine div_lt_div_of_pos_right ?_ hlq
    refine Real.log_lt_log (div_pos hx0 hY) ?_
    rw [div_lt_iff₀ hY]
    exact (hT x hx).2
  have hstep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lab x = lab y → h x ≤ h y → ⌊u x⌋₊ < ⌊u y⌋₊ := by
    intro x hx y hy hne hl hle
    have hx0 : 0 < h x := lt_of_lt_of_le hY (hT x hx).1
    have hqx := hgap x hx y hy hne hl hle
    have hlog : Real.log (h x / Y) + Real.log q ≤ Real.log (h y / Y) := by
      rw [← Real.log_mul (div_pos hx0 hY).ne' hq0.ne']
      refine Real.log_le_log (mul_pos (div_pos hx0 hY) hq0) ?_
      rw [show h x / Y * q = q * h x / Y by ring]
      exact div_le_div_of_nonneg_right hqx hY.le
    have huy : u x + 1 ≤ u y := by
      simp only [hudef]
      rw [div_add_one hlq.ne']
      exact div_le_div_of_nonneg_right hlog hlq.le
    calc ⌊u x⌋₊ < ⌊u x⌋₊ + 1 := Nat.lt_succ_self _
      _ = ⌊u x + 1⌋₊ := (Nat.floor_add_one (hu0 x hx)).symm
      _ ≤ ⌊u y⌋₊ := Nat.floor_le_floor huy
  have hmaps : ∀ x ∈ T, (lab x, ⌊u x⌋₊)
      ∈ C ×ˢ (↑(Finset.range ⌈Real.log A / Real.log q⌉₊) : Set ℕ) := by
    intro x hx
    refine ⟨hlab x hx, ?_⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (Nat.floor_lt (hu0 x hx)).mpr (lt_of_lt_of_le (hut x hx) (Nat.le_ceil _))
  have hinj : Set.InjOn (fun x ↦ (lab x, ⌊u x⌋₊)) T := by
    intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hl, hi⟩ := hxy
    by_contra hne
    rcases le_total (h x) (h y) with hle | hle
    · exact (hstep x hx y hy hne hl hle).ne hi
    · exact (hstep y hy x hx (Ne.symm hne) hl.symm hle).ne hi.symm
  calc T.ncard ≤ (C ×ˢ (↑(Finset.range ⌈Real.log A / Real.log q⌉₊) : Set ℕ)).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (hC.prod (Finset.finite_toSet _))
    _ = ⌈Real.log A / Real.log q⌉₊ * C.ncard := by
        rw [Set.ncard_prod, Set.ncard_coe_finset, Finset.card_range, mul_comm]

/-- **Points with a multiplicative gap in a half-open window `(X, A X]`**, the shape of
Bombieri–Gubler's Lemma 6.5.6. -/
theorem ncard_le_ceil_mul_ncard_of_gap_Ioc {ι γ : Type*} {T : Set ι} {C : Set γ} (hC : C.Finite)
    (lab : ι → γ) (hlab : ∀ x ∈ T, lab x ∈ C) (h : ι → ℝ) {X A q : ℝ} (hX : 0 < X) (hq : 1 < q)
    (hT : ∀ x ∈ T, X < h x ∧ h x ≤ A * X)
    (hgap : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lab x = lab y → h x ≤ h y → q * h x ≤ h y) :
    T.ncard ≤ ⌈Real.log A / Real.log q⌉₊ * C.ncard := by
  by_cases hfin : T.Finite
  swap
  · rw [Set.Infinite.ncard hfin]
    exact Nat.zero_le _
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · rw [hT0, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨x₀, hx₀, hmin⟩ := hfin.toFinset.exists_min_image h (hfin.toFinset_nonempty.mpr hTne)
  rw [Set.Finite.mem_toFinset] at hx₀
  have hA : 0 < A := by
    obtain ⟨h1, h2⟩ := hT x₀ hx₀
    by_contra hA
    push Not at hA
    nlinarith
  refine ncard_le_ceil_mul_ncard_of_gap hC lab hlab h (lt_trans hX (hT x₀ hx₀).1) hq
    (fun x hx ↦ ⟨hmin x (hfin.mem_toFinset.mpr hx), ?_⟩) hgap
  calc h x ≤ A * X := (hT x hx).2
    _ < A * h x₀ := mul_lt_mul_of_pos_left (hT x₀ hx₀).1 hA

end Set

namespace Finset

/-- **A finite set without long chains is small.** If every block
`{y | h x ≤ h y < M h x}` of `T` has at most `k` points, and `T` contains no chain of `m + 1`
points each with height at least `M` times the height of the previous one, then `T` has at most
`m k` points. The proof is the book's greedy grouping (Bombieri–Gubler 6.5.7): cut off the block
of the lowest point and recurse. -/
theorem card_le_mul_of_not_exists_chain {α : Type*} (h : α → ℝ) (M : ℝ) (k : ℕ) :
    ∀ (m : ℕ) (T : Finset α), (∀ x ∈ T, {y ∈ T | h x ≤ h y ∧ h y < M * h x}.card ≤ k) →
      (¬ ∃ s : Fin (m + 1) → α, (∀ j, s j ∈ T) ∧
        ∀ j : Fin m, M * h (s j.castSucc) ≤ h (s j.succ)) →
      T.card ≤ m * k := by
  classical
  intro m
  induction m with
  | zero =>
      intro T _ hchain
      rw [Nat.zero_mul, Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact hchain ⟨fun _ ↦ x, fun _ ↦ hx, fun j ↦ j.elim0⟩
  | succ m ih =>
      intro T hblock hchain
      rcases T.eq_empty_or_nonempty with hT | hT
      · simp [hT]
      obtain ⟨x₀, hx₀, hmin⟩ := T.exists_min_image h hT
      have hT' : {y ∈ T | M * h x₀ ≤ h y}.card ≤ m * k := by
        refine ih _ (fun x hx ↦ le_trans (Finset.card_le_card fun y hy ↦ ?_)
          (hblock x (Finset.mem_filter.mp hx).1)) ?_
        · simp only [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1.1, hy.2⟩
        · rintro ⟨s, hsT, hs⟩
          refine hchain ⟨Fin.cons x₀ s, fun j ↦ ?_, fun j ↦ ?_⟩
          · refine Fin.cases ?_ (fun j ↦ ?_) j
            · simpa using hx₀
            · simpa using (Finset.mem_filter.mp (hsT j)).1
          · refine Fin.cases ?_ (fun j ↦ ?_) j
            · simpa using (Finset.mem_filter.mp (hsT 0)).2
            · simpa [← Fin.succ_castSucc] using hs j
      have hrest : {y ∈ T | ¬ M * h x₀ ≤ h y}.card ≤ k := by
        refine le_trans (Finset.card_le_card fun y hy ↦ ?_) (hblock x₀ hx₀)
        simp only [Finset.mem_filter, not_le] at hy ⊢
        exact ⟨hy.1, hmin y hy.1, hy.2⟩
      have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun y ↦ M * h x₀ ≤ h y)
      rw [Nat.succ_mul]
      omega

end Finset

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

omit [NumberField F] in
/-- An element of positive absolute height has height greater than `1`. -/
private theorem one_lt_mulHeight₁_of_pos {β : K} (hβ : 0 < absLogHeight₁ β) :
    1 < mulHeight₁ β := by
  have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  have hpos : 0 < logHeight₁ β := by
    rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
    exact mul_pos hd hβ
  rw [logHeight₁_eq_log_mulHeight₁] at hpos
  exact (Real.log_pos_iff (mulHeight₁_pos _).le).mp hpos

omit [NumberField F] in
/-- **Remark 6.5.5, the geometric growth**: above `log 16 / (c − 1)` the strong gap principle
gives a factor `(c + 1) / 2 > 1`. -/
private theorem mul_le_of_gap {c h h' : ℝ} (hc : 1 < c) (hgap : c * h - Real.log 4 ≤ h')
    (hh : Real.log 16 / (c - 1) ≤ h) : (c + 1) / 2 * h ≤ h' := by
  have hc1 : 0 < c - 1 := by linarith
  have hlog16 : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [div_le_iff₀ hc1] at hh
  nlinarith

/-- **Lemma 6.5.6, the count in a window** (Bombieri–Gubler). With
`c = (1 − |S| / N) κ − 1 > 1` and `X ≥ log 16 / (c − 1)`, at most
`⌈log A / log ((c + 1) / 2)⌉ · (N + |S|).choose |S|` solutions of `Λ(β) ≤ H(β) ^ (−κ)` have
absolute height in `(X, A X]`. -/
theorem ncard_setOf_absLogHeight₁_mem_Ioc_le {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {c : ℝ}
    (hcdef : c = (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) (hc : 1 < c)
    {X A : ℝ} (hX : Real.log 16 / (c - 1) ≤ X) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      X < absLogHeight₁ β ∧ absLogHeight₁ β ≤ A * X}.ncard
      ≤ ⌈Real.log A / Real.log ((c + 1) / 2)⌉₊
        * (N + (Sinf.card + Sfin.card)).choose (Sinf.card + Sfin.card) := by
  have hc1 : 0 < c - 1 := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (div_pos (Real.log_pos (by norm_num)) hc1) hX
  have hq : 1 < (c + 1) / 2 := by linarith
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = Sinf.card + Sfin.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  have hCn : {c' : (↥Sinf ⊕ ↥Sfin) → ℕ | ∑ a, c' a ≤ N}.ncard
      = (N + (Sinf.card + Sfin.card)).choose (Sinf.card + Sfin.card) := by
    rw [Set.ncard_setOf_sum_le, hcard]
  rw [← hCn]
  refine Set.ncard_le_ceil_mul_ncard_of_gap_Ioc (Set.finite_setOf_sum_le _ N)
    (approxClass Sinf Sfin w α N) (fun β _ ↦ sum_approxClass_le Sinf Sfin w α N β)
    absLogHeight₁ hX0 hq (fun β hβ ↦ ⟨hβ.2.1, hβ.2.2⟩) ?_
  intro β hβ β' hβ' hne hcl hle
  have hgap := mul_absLogHeight₁_sub_le_of_approxClass_eq hwInf hwFin hκ hN hβ.1 hβ'.1 hne hcl hle
  rw [← hcdef] at hgap
  exact mul_le_of_gap hc hgap (le_trans hX hβ.2.1.le)

/-! ### The count of large solutions -/

/-- **The bound on the number of large solutions of Roth's inequality** (Bombieri–Gubler 6.5.7):
`m ⌈log M / log ((c + 1) / 2)⌉ (N + s).choose s`, with `m = rothChainLength κ s r`,
`M = rothRatio κ s r`, `N = rothClassSize κ s` and `c = (1 − s / N) κ − 1`, so that
`(c + 1) / 2 = (1 − s / N) κ / 2`. It depends on `κ`, the number `s` of places and `r = [F : K]`
alone. -/
noncomputable def rothLargeCount (κ : ℝ) (s r : ℕ) : ℕ :=
  rothChainLength κ s r
    * ⌈Real.log (rothRatio κ s r) / Real.log ((1 - (s : ℝ) / rothClassSize κ s) * κ / 2)⌉₊
    * (rothClassSize κ s + s).choose s

omit [NumberField F] in
/-- **The gap constant of Roth's class size exceeds `1`**: `c = (1 − s / N) κ − 1 > 1` at
`N = rothClassSize κ s`, so Remark 6.5.5 applies to the classes Roth's proof uses. -/
theorem one_lt_rothGap {κ : ℝ} (hκ : 2 < κ) (s : ℕ) :
    1 < (1 - (s : ℝ) / rothClassSize κ s) * κ - 1 := by
  obtain ⟨hε0, -, hε4⟩ := rothEps_spec hκ
  obtain ⟨-, -, hΘ⟩ := rothClassSize_spec hκ s
  by_contra h
  push Not at h
  have h2 : (1 - (s : ℝ) / rothClassSize κ s) * κ ≤ 2 := by linarith
  have h3 : κ * (1 - (s : ℝ) / rothClassSize κ s) * (1 / 2 - 4 * rothEps κ)
      ≤ 2 * (1 / 2 - 4 * rothEps κ) := by
    rw [mul_comm κ]
    exact mul_le_mul_of_nonneg_right h2 hε4.le
  linarith

/-- **6.5.7, the count of large solutions** (Bombieri–Gubler; Davenport and Roth 1955 at one
place). There is a height `L` — depending on `K`, `S` and the targets — above which Roth's
inequality `Λ(β) ≤ H(β) ^ (−κ)` has at most `rothLargeCount κ |S| [F : K]` solutions, a number
depending on `κ`, `|S|` and `[F : K]` alone. Absolute logarithmic heights.

⚠ This bounds the **number** of large solutions and says nothing about their height: `L` is
explicit, but no statement here bounds the height of a solution above `L`, and none can be read
off the proof — which is the ineffectivity of Roth's method. -/
theorem exists_ncard_setOf_lt_absLogHeight₁_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L : ℝ, {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      L < absLogHeight₁ β}.ncard ≤ rothLargeCount κ (Sinf.card + Sfin.card) (finrank K F) := by
  classical
  set s := Sinf.card + Sfin.card with hsdef
  set r := finrank K F with hrdef
  set N := rothClassSize κ s with hNdef
  set m := rothChainLength κ s r with hmdef
  set M := rothRatio κ s r with hMdef
  set c : ℝ := (1 - (s : ℝ) / N) * κ - 1 with hcdef
  set q : ℝ := (1 - (s : ℝ) / N) * κ / 2 with hqdef
  have hqc : q = (c + 1) / 2 := by rw [hqdef, hcdef]; ring
  have hc : 1 < c := one_lt_rothGap hκ s
  have hc1 : 0 < c - 1 := by linarith
  have hq : 1 < q := by rw [hqc]; linarith
  have hκ0 : 0 < κ := by linarith
  have hN : 0 < N := (rothClassSize_spec hκ s).1
  have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = s := by
    rw [hsdef, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  obtain ⟨Lr, hLr⟩ := roth_no_chain Sinf Sfin w hwInf hwFin α hκ
  set X₀ : ℝ := Real.log 16 / (c - 1) with hX₀def
  have hX₀ : 0 < X₀ := div_pos (Real.log_pos (by norm_num)) hc1
  refine ⟨max (Lr / totalWeight K) X₀, ?_⟩
  set U : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      max (Lr / totalWeight K) X₀ < absLogHeight₁ β} with hUdef
  have hUfin : U.Finite :=
    (finite_setOf_prod_min_one_le Sinf Sfin w hwInf hwFin α hκ).subset fun β hβ ↦ hβ.1
  -- what the members of `U` satisfy
  have hsolU : ∀ β ∈ U, ∏ a, localApprox Sinf Sfin w α a β ≤ mulHeight₁ β ^ (-κ) :=
    fun β hβ ↦ by
      rw [prod_localApprox]
      exact hβ.1
  have hbigU : ∀ β ∈ U, X₀ < absLogHeight₁ β := fun β hβ ↦ lt_of_le_of_lt (le_max_right _ _) hβ.2
  have hHU : ∀ β ∈ U, 1 < mulHeight₁ β := fun β hβ ↦
    one_lt_mulHeight₁_of_pos (hX₀.trans (hbigU β hβ))
  have hLU : ∀ β ∈ U, Lr ≤ logHeight₁ β := fun β hβ ↦ by
    have h1 := lt_of_le_of_lt (le_max_left _ _) hβ.2
    rw [div_lt_iff₀ hd] at h1
    rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
    linarith
  have hgapU : ∀ β ∈ U, ∀ β' ∈ U, β ≠ β' →
      approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β' →
      absLogHeight₁ β ≤ absLogHeight₁ β' → q * absLogHeight₁ β ≤ absLogHeight₁ β' := by
    intro β hβ β' hβ' hne hcl hle
    have hgap := mul_absLogHeight₁_sub_le_of_approxClass_eq hwInf hwFin hκ0 hN hβ.1 hβ'.1 hne
      hcl hle
    rw [← hcdef] at hgap
    rw [hqc]
    exact mul_le_of_gap hc hgap (hbigU β hβ).le
  -- one class at a time
  set k : ℕ := ⌈Real.log M / Real.log q⌉₊ with hkdef
  set U' : Finset K := hUfin.toFinset with hU'def
  have hmemU : ∀ β ∈ U', β ∈ U := fun β hβ ↦ hUfin.mem_toFinset.mp hβ
  have hfiber : ∀ c₀ : (↥Sinf ⊕ ↥Sfin) → ℕ,
      {β ∈ U' | approxClass Sinf Sfin w α N β = c₀}.card ≤ m * k := by
    intro c₀
    refine Finset.card_le_mul_of_not_exists_chain absLogHeight₁ M k m _ ?_ ?_
    · -- a block has at most `k` points, by the gap principle
      intro x hx
      have hxU := hmemU x (Finset.mem_filter.mp hx).1
      set B : Finset K := {y ∈ {β ∈ U' | approxClass Sinf Sfin w α N β = c₀} |
        absLogHeight₁ x ≤ absLogHeight₁ y ∧ absLogHeight₁ y < M * absLogHeight₁ x} with hBdef
      have hblock := Set.ncard_le_ceil_mul_ncard_of_gap (T := (↑B : Set K))
        (C := (Set.univ : Set Unit)) Set.finite_univ (fun _ ↦ ()) (fun _ _ ↦ Set.mem_univ _)
        absLogHeight₁ (Y := absLogHeight₁ x) (A := M) (hX₀.trans (hbigU x hxU)) hq
        (fun y hy ↦ (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2) fun y hy z hz hne _ hle ↦ by
          have hy' := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
          have hz' := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).1
          exact hgapU y (hmemU y hy'.1) z (hmemU z hz'.1) hne (hy'.2.trans hz'.2.symm) hle
      rw [Set.ncard_coe_finset, Set.ncard_univ, Nat.card_unique, mul_one] at hblock
      exact hblock
    · -- no chain of `m + 1` points, by the core of Roth's proof
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
  -- sum over the classes
  have hmaps : Set.MapsTo (approxClass Sinf Sfin w α N) ↑U'
      ↑(U'.image (approxClass Sinf Sfin w α N)) :=
    fun β hβ ↦ Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hβ)
  have himage : (U'.image (approxClass Sinf Sfin w α N)).card ≤ (N + s).choose s := by
    have h1 := Set.ncard_le_ncard (s := ↑(U'.image (approxClass Sinf Sfin w α N)))
      (t := {c' : (↥Sinf ⊕ ↥Sfin) → ℕ | ∑ a, c' a ≤ N}) (fun c' hc' ↦ by
        obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hc'
        exact sum_approxClass_le Sinf Sfin w α N β) (Set.finite_setOf_sum_le _ N)
    rw [Set.ncard_coe_finset, Set.ncard_setOf_sum_le, hcard] at h1
    exact h1
  calc U.ncard = U'.card := Set.ncard_eq_toFinset_card U hUfin
    _ = ∑ b ∈ U'.image (approxClass Sinf Sfin w α N),
          {β ∈ U' | approxClass Sinf Sfin w α N β = b}.card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ U'.image (approxClass Sinf Sfin w α N), m * k :=
        Finset.sum_le_sum fun b _ ↦ hfiber b
    _ = (U'.image (approxClass Sinf Sfin w α N)).card * (m * k) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (N + s).choose s * (m * k) := Nat.mul_le_mul_right _ himage
    _ = rothLargeCount κ s r := by
        rw [rothLargeCount]
        ring

/-! ### Acceptance criteria -/

omit [NumberField F] in
/-- **Conformance: the book's count of small solutions** (Bombieri–Gubler 6.5.7 (b)). The window
lemma at `X = log 16 / (c − 1)` and `A = L / X` counts the solutions with height in
`(log 16 / (c − 1), L]`. ⚠ The book applies Lemma 6.5.6 at exactly this `X`, which its own
hypothesis `X > log 16 / (c − 1)` excludes; the proof needs only `≤`, which is what
`NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le` assumes. The count is
`⌈log (L / X) / log ((c + 1) / 2)⌉ (N + |S|).choose |S|`; the book writes `log L`, which is an
upper bound for `log (L / X)` only when `X ≥ 1`. -/
example {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {c : ℝ}
    (hcdef : c = (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * κ - 1) (hc : 1 < c) (L : ℝ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      Real.log 16 / (c - 1) < absLogHeight₁ β ∧ absLogHeight₁ β ≤ L}.ncard
      ≤ ⌈Real.log (L / (Real.log 16 / (c - 1))) / Real.log ((c + 1) / 2)⌉₊
        * (N + (Sinf.card + Sfin.card)).choose (Sinf.card + Sfin.card) := by
  have hX0 : 0 < Real.log 16 / (c - 1) := div_pos (Real.log_pos (by norm_num)) (by linarith)
  have h := ncard_setOf_absLogHeight₁_mem_Ioc_le hwInf hwFin α hκ hN hcdef hc le_rfl
    (A := L / (Real.log 16 / (c - 1)))
  rwa [div_mul_cancel₀ L hX0.ne'] at h

/-- **Conformance: the bound on the large solutions is uniform in the targets.** One number, fixed
by `κ`, `|S|` and `[F : K]`, bounds the large solutions for *every* choice of targets; only the
threshold `L` moves with them. This is the quantifier order the milestone asks for. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) :
    ∃ B : ℕ, ∀ α : AbsoluteValue K ℝ → F, ∃ L : ℝ,
      {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ) ∧
      L < absLogHeight₁ β}.ncard ≤ B :=
  ⟨rothLargeCount κ (Sinf.card + Sfin.card) (finrank K F),
    fun α ↦ exists_ncard_setOf_lt_absLogHeight₁_le Sinf Sfin w hwInf hwFin α hκ⟩

/-- **Conformance: the chain bound is sharp.** Heights `1` and `2` with ratio `3`: every block
holds at most `2` points and no two points form a chain, and the set has exactly `1 · 2` points.
So `Finset.card_le_mul_of_not_exists_chain` cannot be improved in general. -/
example : ({1, 2} : Finset ℕ).card = 1 * 2 ∧
    (∀ x ∈ ({1, 2} : Finset ℕ),
      (({1, 2} : Finset ℕ).filter fun y : ℕ ↦ (x : ℝ) ≤ y ∧ (y : ℝ) < 3 * x).card ≤ 2) ∧
    ¬ ∃ s : Fin (1 + 1) → ℕ, (∀ j, s j ∈ ({1, 2} : Finset ℕ)) ∧
      ∀ j : Fin 1, (3 : ℝ) * (s j.castSucc : ℝ) ≤ (s j.succ : ℝ) := by
  refine ⟨rfl, fun x _ ↦ (Finset.card_filter_le _ _).trans (by rfl), ?_⟩
  rintro ⟨s, hs, hch⟩
  have h01 := hch 0
  have h0 : 1 ≤ s 0 := by
    have := hs 0
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have h1 : s 1 ≤ 2 := by
    have := hs 1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have h0' : (1 : ℝ) ≤ s 0 := by exact_mod_cast h0
  have h1' : (s 1 : ℝ) ≤ 2 := by exact_mod_cast h1
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h01
  linarith

end NumberField

end
