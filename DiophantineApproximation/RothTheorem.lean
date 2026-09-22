/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RothAuxiliary
public import DiophantineApproximation.RothClass
public import DiophantineApproximation.RothKeyInequality

/-!
# Roth's theorem

**Roth's theorem** (Bombieri–Gubler, Theorem 6.4.1; Roth 1955 over `ℚ` at one place, Ridout 1958
over `ℚ` at several, Lang over a number field). Let `K` be a number field, `S` a finite set of
places of `K` carried as two typed finsets, `F / K` a finite extension, `w v` an absolute value of
`F` over `v` and `α v ∈ F` a target for each `v ∈ S`. Then for every `κ > 2` the set of `β ∈ K`
with

```text
(∏ v ∈ S∞, min 1 |β − α v|_v ^ mult v) * ∏ v ∈ S₀, min 1 |β − α v|_v  ≤  H(β) ^ (−κ)
```

is finite. Heights are Mathlib's relative ones, so this is the book's statement raised to the
power `[K : ℚ]`; every quantity in it is homogeneous of the same degree and the inequality reads
the same in either normalisation.

The proof is the book's, in five steps, and the file is only their assembly:

* **Step 0** (`DiophantineApproximation/RothClass.lean`, on Layer 3.1): discard the finitely many
  `β` of height `1` and the at most `|S|` that equal a target, classify the rest by Mahler's
  reduction, and take an `(L, M)`-independent sequence inside one class. What comes out is a
  vector of exponents `λ` with `∑ a, λ a ≥ 1 − |S| / N` such that every member of the sequence
  satisfies `min 1 |β − α_a|_a ^ w_a ≤ H(β) ^ (−κ λ a)`.
* **Steps I and II** (`DiophantineApproximation/RothAuxiliary.lean`, on Layers 2.6 and 2.7): build
  the auxiliary polynomial at the multidegree `d j = ⌈D / h(β j)⌉` and differentiate it until it
  survives at `β`.
* **Steps III to V** (`DiophantineApproximation/RothKeyInequality.lean`, on Layers 2.1 and 0.3):
  bound the value at every place, multiply by the product formula, and compare.

The parameters are chosen in the book's order — `ε` and `N` from `κ`, then the number of variables
`m + 1` from the feasibility of the index theorem, then `L` and `M`, then the solutions, and only
then `D`. Everything chosen before `L` is a definition depending on `κ`, `|S|` and `[F : K]`
alone, and Steps I to V are proved as a statement about a chain already in hand, in which every
member carries its own targets, `NumberField.roth_no_moving_chain`: no chain of `m + 1` solutions
in one approximation class, with heights growing by the ratio `M`, has targets small against it.
Its constant case is `NumberField.roth_no_chain` — above a height `L` there is no
`(L, M)`-independent chain of solutions in one class — and Roth's theorem is that statement fed
by Step 0.

## Main definitions

* `NumberField.rothEps`, `NumberField.rothClassSize`, `NumberField.rothChainLength` and
  `NumberField.rothRatio`: the `ε`, the `N`, the `m` and the `M` of the proof.

## Main results

* `NumberField.finite_setOf_prod_min_one_le`: **Layer 3.2**, Roth's theorem.
* `NumberField.roth_no_moving_chain`: **the core of the proof, with moving targets** — no chain
  of `rothChainLength κ |S| [F : K] + 1` solutions in one class, each with its own targets, has
  `1 + ∑ v, h(α j v) ≤ δ h(β j)` throughout — which is what Layer 3.8 consumes.
* `NumberField.roth_no_chain`: its constant case — no chain above a height `L` — which is what
  Layer 3.7 counts with.
* `NumberField.max_apply_one_le_mulHeight₁_sPlaceAbsValue`: the size of a target at a place of
  `S` is at most its height.
* `Real.exists_le_and_mul_log_add_lt`: the elementary fact that replaces the book's `D → ∞`.

## Implementation notes

⚠ **Nothing tends to infinity.** The book lets `D → ∞` and reads off `(6.22)`; here every error
term is explicit, the only one that is not `O(D / L)` is `([K : ℚ] + 2 ∑ a, w_a) log (D + 2)`, and
one `D` large enough is produced by hand. That is also why no filter, no `IsLittleO` and no
`Tendsto` appears anywhere in Layer 3.2.

⚠ **The two degenerate families of solutions are discarded by Northcott and by injectivity.** A
`β` of height at most `1` has no logarithmic profile, and a `β` equal to a target at some place has
local factor `0` there; the first set is finite by Northcott, the second has at most one element
per place, and an infinite solution set stays infinite after both are removed. This is the book's
"non-trivial approximation".

⚠ **`κ > 2` enters exactly once**, through `1 / κ < 1 / 2`: it is what leaves room for the two
losses `4 ε` and `|S| / N`, and the contradiction is `κ (1 − |S| / N) (1/2 − 4 ε) > 1`. No other
step uses the value of `κ`.

⚠ **The proof was restructured for Layer 3.7, and the theorem did not change.** Layer 3.2 first
proved Roth's theorem as one proof by contradiction, with `ε`, `N` and `m` obtained from
existentials inside it. Counting solutions needs the chain statement with its parameters in view,
so the parameters became definitions and the steps after Step 0 became
`NumberField.roth_no_chain`; the statement of `NumberField.finite_setOf_prod_min_one_le` is
unchanged. From outside, the targets enter only through `L`: the length `m`, the ratio `M` and
the class size `N` do not see them.

⚠ **It was restructured again for Layer 3.8, and none of this file's public statements changed.**
The core now takes a chain whose members have their own targets: Steps I and II put the index at the
point `(α 0 v, …, α m v)`, Steps III to V take one target and one size bound per coordinate, and the
condition on the targets is `1 + ∑ v, h(α j v) ≤ δ h(β j)` with `δ` independent of them; the
statements of those steps were generalized, and nothing outside Layer 3.2 quotes them. That needs
the size `|α j v|_v` bounded by the height, which the fixed-target proof could leave as a constant:
`NumberField.max_apply_one_le_mulHeight₁_sPlaceAbsValue`, from Layer 0.1's classification.
`NumberField.roth_no_chain` is then the constant case, with `L = [K : ℚ] (1 + ∑ v, h(α v)) / δ`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.4.1 and §6.4.2 to §6.4.10; Theorem 6.5.2 for the core with moving targets.

This is Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height MvPolynomial Module

/-- **A logarithm is eventually beaten by any positive multiple of the identity.** -/
theorem Real.exists_le_and_mul_log_add_lt {B E c D₁ : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ D : ℝ, D₁ ≤ D ∧ 0 < D ∧ B * Real.log (D + 2) + E < c * D := by
  set t : ℝ := 4 * B / c + 1 with htdef
  have ht0 : (0 : ℝ) < t := by positivity
  have hBt : B / t ≤ c / 4 := by
    rw [div_le_div_iff₀ ht0 (by norm_num), htdef]
    field_simp
    nlinarith
  set D : ℝ := max (max D₁ 1) ((c / 2 + B * Real.log t + E + 1) * 4 / (3 * c)) with hDdef
  have hD1 : D₁ ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD0 : (1 : ℝ) ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDbig : (c / 2 + B * Real.log t + E + 1) * 4 / (3 * c) ≤ D := le_max_right _ _
  refine ⟨D, hD1, by linarith, ?_⟩
  have hlog : Real.log (D + 2) ≤ (D + 2) / t + Real.log t - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (D + 2) / t) (by positivity)
    rw [Real.log_div (by linarith) ht0.ne'] at h
    linarith
  have hstep : B * Real.log (D + 2) ≤ (c / 4) * (D + 2) + B * Real.log t := by
    calc B * Real.log (D + 2) ≤ B * ((D + 2) / t + Real.log t - 1) := by
          exact mul_le_mul_of_nonneg_left hlog hB
      _ = (B / t) * (D + 2) + B * Real.log t - B := by field_simp
      _ ≤ (c / 4) * (D + 2) + B * Real.log t - B := by
          have : (B / t) * (D + 2) ≤ (c / 4) * (D + 2) :=
            mul_le_mul_of_nonneg_right hBt (by linarith)
          linarith
      _ ≤ (c / 4) * (D + 2) + B * Real.log t := by linarith
  have hfin : (c / 2 + B * Real.log t + E + 1) ≤ (3 * c / 4) * D := by
    rw [div_le_iff₀ (by positivity)] at hDbig
    nlinarith
  nlinarith

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-! ### The parameters

Everything the proof chooses before it sees a solution, as functions of `κ`, of the number `s`
of places and of `r = [F : K]`. The choices are the book's up to constants, and nothing here
depends on `K` or on the targets: that is what lets Layer 3.7 count solutions with a bound that
does not either.
-/

/-- **The `ε` of Roth's proof**, `(1 / 2 − 1 / κ) / 16`. It is positive exactly when `κ > 2`, and
it leaves room for the two losses `4 ε` of Roth's lemma and `|S| / N` of the classification. -/
noncomputable def rothEps (κ : ℝ) : ℝ := (1 / 2 - 1 / κ) / 16

/-- **The size `1 / N` of the approximation classes of Roth's proof**, as the integer `N`: large
enough that the loss `|S| / N` in (6.10) is at most half the margin `1 / 2 − 1 / κ`. -/
noncomputable def rothClassSize (κ : ℝ) (s : ℕ) : ℕ := ⌈2 * (s : ℝ) / (1 / 2 - 1 / κ)⌉₊ + 1

/-- **The length of the longest chain Roth's proof allows**: the proof uses one more variable than
this, and no `(L, M)`-independent chain of `rothChainLength κ s r + 1` solutions lies in one
approximation class. The number is the book's `log (2 r |S|) / (6 ε ^ 2)`, from the feasibility
of the index theorem. -/
noncomputable def rothChainLength (κ : ℝ) (s r : ℕ) : ℕ :=
  ⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * rothEps κ ^ 2)⌉₊

/-- **The ratio `M` of `(L, M)`-independence in Roth's proof**, `2 / ε ^ (2 ^ m)`: the heights of
consecutive members of a chain must grow at least this fast for Roth's lemma to apply. -/
noncomputable def rothRatio (κ : ℝ) (s r : ℕ) : ℝ := 2 / rothEps κ ^ 2 ^ rothChainLength κ s r

/-- The three facts about `rothEps` that the proof uses. -/
theorem rothEps_spec {κ : ℝ} (hκ : 2 < κ) :
    0 < rothEps κ ∧ rothEps κ < 1 / 2 ∧ 0 < 1 / 2 - 4 * rothEps κ := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hη0 : 0 < 1 / 2 - 1 / κ := by
    have h : 1 / κ < 1 / 2 := by
      rw [div_lt_div_iff₀ hκ0 two_pos]
      linarith
    linarith
  have hη1 : 1 / 2 - 1 / κ < 1 / 2 := by
    have : (0 : ℝ) < 1 / κ := by positivity
    linarith
  unfold rothEps
  exact ⟨by positivity, by linarith, by linarith⟩

/-- **The class size is admissible**: `κ (1 − s / N) (1 / 2 − 4 ε) > 1`, which is the inequality
Step V contradicts. -/
theorem rothClassSize_spec {κ : ℝ} (hκ : 2 < κ) (s : ℕ) :
    0 < rothClassSize κ s ∧ (s : ℝ) / rothClassSize κ s ≤ 1 ∧
      1 < κ * (1 - (s : ℝ) / rothClassSize κ s) * (1 / 2 - 4 * rothEps κ) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / 2 - 1 / κ := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    have h : 1 / κ < 1 / 2 := by
      rw [div_lt_div_iff₀ hκ0 two_pos]
      linarith
    linarith
  have hη1 : η < 1 / 2 := by
    rw [hηdef]
    have : (0 : ℝ) < 1 / κ := by positivity
    linarith
  have hε : rothEps κ = η / 16 := by rw [rothEps, hηdef]
  have hNdef : (rothClassSize κ s : ℝ) = (⌈2 * (s : ℝ) / η⌉₊ : ℝ) + 1 := by
    rw [rothClassSize, hηdef]
    push_cast
    ring
  have hNbig : 2 * (s : ℝ) / η < (rothClassSize κ s : ℝ) := by
    rw [hNdef]
    linarith [Nat.le_ceil (2 * (s : ℝ) / η)]
  have hNpos : (0 : ℝ) < (rothClassSize κ s : ℝ) := by
    rw [hNdef]
    positivity
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  rw [div_lt_iff₀ hη0] at hNbig
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · rw [div_le_one hNpos]
    nlinarith [mul_lt_mul_of_pos_left hη1 hNpos]
  rw [hε]
  set N : ℝ := (rothClassSize κ s : ℝ) with hN
  have hx : (s : ℝ) / N < η / 2 := by
    rw [div_lt_div_iff₀ hNpos two_pos]
    linarith
  have hx0 : (0 : ℝ) ≤ (s : ℝ) / N := by positivity
  have h1 : (1 / 2 - 4 * (η / 16)) - (s : ℝ) / N
      ≤ (1 - (s : ℝ) / N) * (1 / 2 - 4 * (η / 16)) := by nlinarith
  have hinv : κ * (1 / κ) = 1 := by field_simp
  have hstep1 : κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N)
      ≤ κ * ((1 - (s : ℝ) / N) * (1 / 2 - 4 * (η / 16))) :=
    mul_le_mul_of_nonneg_left h1 hκ0.le
  have hk : 1 / κ < (1 / 2 - 4 * (η / 16)) - (s : ℝ) / N := by
    have hkk : 1 / κ = 1 / 2 - η := by rw [hηdef]; ring
    rw [hkk]
    linarith
  have hstep2 : 1 < κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N) := by
    calc (1 : ℝ) = κ * (1 / κ) := hinv.symm
      _ < κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N) := mul_lt_mul_of_pos_left hk hκ0
  rw [mul_assoc]
  linarith

/-- **The chain length is feasible for the index theorem**: `r s e ^ {−6 (m + 1) ε ^ 2} < 1 / 2`,
the book's `r V_m(t) < 1 / 2` after Lemma 6.3.5. -/
theorem rothChainLength_spec {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) :
    (r : ℝ) * s * Real.exp (-(6 * ((rothChainLength κ s r : ℝ) + 1) * rothEps κ ^ 2)) < 1 / 2 := by
  obtain ⟨hε0, -, -⟩ := rothEps_spec hκ
  set ε := rothEps κ with hεdef
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hY : (0 : ℝ) < 2 * (r : ℝ) * s + 1 := by positivity
  have hε2 : (0 : ℝ) < 6 * ε ^ 2 := by positivity
  have hm : (rothChainLength κ s r : ℝ)
      = (⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) := by
    rw [rothChainLength]
  rw [hm]
  have hmbig : Real.log (2 * (r : ℝ) * s + 1)
      < 6 * ((⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2 := by
    have h := Nat.le_ceil (Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2))
    rw [div_le_iff₀ hε2] at h
    nlinarith
  have h1 : Real.exp (-(6 * ((⌈Real.log (2 * (r : ℝ) * s + 1)
        / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
      ≤ 1 / (2 * (r : ℝ) * s + 1) := by
    rw [show (1 : ℝ) / (2 * (r : ℝ) * s + 1)
        = Real.exp (-(Real.log (2 * (r : ℝ) * s + 1))) by
      rw [Real.exp_neg, Real.exp_log hY, one_div]]
    exact Real.exp_le_exp.mpr (by linarith)
  calc (r : ℝ) * s * Real.exp (-(6 * ((⌈Real.log
          (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
      ≤ (r : ℝ) * s * (1 / (2 * (r : ℝ) * s + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((r : ℝ) * s) / (2 * (r : ℝ) * s + 1) := by rw [mul_one_div]
    _ < 1 / 2 := by
        rw [div_lt_div_iff₀ hY two_pos]
        nlinarith

/-- The ratio of a chain is at least `1`, so the heights along a chain increase. -/
theorem one_le_rothRatio {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) : 1 ≤ rothRatio κ s r := by
  obtain ⟨hε0, hε1, -⟩ := rothEps_spec hκ
  have hσ0 : 0 < rothEps κ ^ 2 ^ rothChainLength κ s r := pow_pos hε0 _
  have hσ1 : rothEps κ ^ 2 ^ rothChainLength κ s r ≤ 1 / 2 :=
    le_trans (pow_le_of_le_one hε0.le (by linarith) (by positivity)) hε1.le
  rw [rothRatio, le_div_iff₀ hσ0]
  linarith

/-! ### The core of the proof -/

/-- **The size of a target is bounded by its height** at every place of `S`: the absolute value
`w v` lies over `v`, so by Layer 0.1 it is an infinite place of `F` or a root of a finite one. -/
theorem max_apply_one_le_mulHeight₁_sPlaceAbsValue {Sinf : Finset (InfinitePlace K)}
    {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (a : ↥Sinf ⊕ ↥Sfin) (x : F) : max (w (sPlaceAbsValue a) x) 1 ≤ mulHeight₁ x := by
  rcases a with v | v
  · have := hwInf v.1 v.2
    exact max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace v.1 (w v.1.1) x
  · have := hwFin v.1 v.2
    exact max_apply_one_le_mulHeight₁_of_liesOver_finitePlace v.1 (w v.1.1) x

/-- The core of Roth's proof at arbitrary admissible parameters: Steps I to V, applied to a chain
that is already in hand, each member of which carries its own targets. -/
private theorem roth_no_moving_chain_aux (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ0 : 0 < κ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hε4 : 0 < 1 / 2 - 4 * ε) {N : ℕ}
    (hΘ : 1 < κ * (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * (1 / 2 - 4 * ε)) {mnum : ℕ}
    (hfeasA : (finrank K F : ℝ) * ((Sinf.card + Sfin.card : ℕ) : ℝ)
      * Real.exp (-(6 * ((mnum : ℝ) + 1) * ε ^ 2)) < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N ≤ ∑ a, lam a →
      ∀ (α : Fin (mnum + 1) → AbsoluteValue K ℝ → F) (β : Fin (mnum + 1) → K),
        (∀ j, 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a))
          ≤ δ * absLogHeight₁ (β j)) →
        (∀ j : Fin mnum, 2 / ε ^ 2 ^ mnum * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, localApprox Sinf Sfin w (α j) a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
  have hwA : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a) := by
    rintro (v | v)
    · exact hwInf v v.2
    · exact hwFin v v.2
  set SA : ℕ := Sinf.card + Sfin.card with hSAdef
  have hSAcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = SA := by
    rw [hSAdef, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  clear_value SA
  set Θ : ℝ := κ * (1 - (SA : ℝ) / N) * (1 / 2 - 4 * ε) with hΘdef
  clear_value Θ
  have hΘ1 : (0 : ℝ) < Θ - 1 := by linarith
  rw [← hSAcard] at hfeasA
  -- the parameters that do not see the chain
  set σ : ℝ := ε ^ 2 ^ mnum with hσdef
  have hσ0 : (0 : ℝ) < σ := pow_pos hε0 _
  have hσ1 : σ ≤ 1 / 2 := by
    rw [hσdef]
    calc ε ^ 2 ^ mnum ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le (by linarith) Nat.one_le_two_pow
      _ = ε := pow_one _
      _ ≤ 1 / 2 := hε1.le
  clear_value σ
  set tw : ℕ := totalWeight K with htwdef
  have htw1 : (1 : ℝ) ≤ (tw : ℝ) := by
    rw [htwdef]
    exact_mod_cast totalWeight_pos K
  clear_value tw
  set Wsum : ℕ := ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a with hWdef
  clear_value Wsum
  set rF : ℝ := (finrank ℚ F : ℝ) with hrFdef
  have hrF1 : (1 : ℝ) ≤ rF := by
    rw [hrFdef]
    exact_mod_cast Module.finrank_pos
  set Mind : ℝ := 2 / σ with hMdef
  have hM1 : (1 : ℝ) ≤ Mind := by
    rw [hMdef, le_div_iff₀ hσ0]
    linarith
  clear_value Mind
  have hm1 : (0 : ℝ) < (mnum : ℝ) + 1 := by positivity
  have hW0 : (0 : ℝ) ≤ (Wsum : ℝ) := Nat.cast_nonneg _
  set δ : ℝ := min (σ / (12 * ((mnum : ℝ) + 1))) ((Θ - 1) / (2 * (4 * rF * (Wsum : ℝ) + 8)))
    with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδσ : 12 * ((mnum : ℝ) + 1) * δ ≤ σ := by
    have h := min_le_left (σ / (12 * ((mnum : ℝ) + 1)))
      ((Θ - 1) / (2 * (4 * rF * (Wsum : ℝ) + 8)))
    rw [← hδdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hδΘ : 2 * (4 * rF * (Wsum : ℝ) + 8) * δ ≤ Θ - 1 := by
    have h := min_le_right (σ / (12 * ((mnum : ℝ) + 1)))
      ((Θ - 1) / (2 * (4 * rF * (Wsum : ℝ) + 8)))
    rw [← hδdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hδ1 : δ ≤ 1 := by
    have := mul_nonneg (Nat.cast_nonneg mnum : (0 : ℝ) ≤ mnum) hδ0.le
    linarith
  clear_value δ
  refine ⟨δ, hδ0, fun lam hlam0 hlamsum α β hαβ hchain hblocal ↦ ?_⟩
  -- the heights of the targets, against the heights of the chain
  set Hα : Fin (mnum + 1) → ℝ :=
    fun j ↦ ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a)) with hHαdef
  have hHα0 : ∀ j, 0 ≤ Hα j := fun j ↦ Finset.sum_nonneg fun a _ ↦ absLogHeight₁_nonneg _
  have hsingle : ∀ j a, absLogHeight₁ (α j (sPlaceAbsValue a)) ≤ Hα j := fun j a ↦
    Finset.single_le_sum (f := fun b : ↥Sinf ⊕ ↥Sfin ↦ absLogHeight₁ (α j (sPlaceAbsValue b)))
      (fun b _ ↦ absLogHeight₁_nonneg _) (Finset.mem_univ a)
  have hαβ' : ∀ j, 1 + Hα j ≤ δ * absLogHeight₁ (β j) := fun j ↦ hαβ j
  have hfrK : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have habs : ∀ j, (tw : ℝ) * absLogHeight₁ (β j) = logHeight₁ (β j) := fun j ↦ by
    rw [absLogHeight₁_eq_inv_mul, htwdef, totalWeight_eq_finrank, logHeight₁_eq_log_mulHeight₁]
    field_simp
  have habsF : ∀ x : F, Real.log (mulHeight₁ x) = rF * absLogHeight₁ x := fun x ↦ by
    have hfrF : (0 : ℝ) < (finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
    rw [absLogHeight₁_eq_inv_mul, hrFdef]
    field_simp
  have hsmall : ∀ j, (tw : ℝ) * (1 + Hα j) ≤ δ * logHeight₁ (β j) := fun j ↦ by
    rw [← habs j]
    have h := mul_le_mul_of_nonneg_left (hαβ' j) (by linarith : (0 : ℝ) ≤ (tw : ℝ))
    linarith
  have hβpos : ∀ j, 0 < logHeight₁ (β j) := fun j ↦ by
    have h1 := hsmall j
    have h2 : (0 : ℝ) < (tw : ℝ) * (1 + Hα j) := by
      have := hHα0 j
      positivity
    by_contra hneg
    push Not at hneg
    have h3 := mul_le_mul_of_nonneg_left hneg hδ0.le
    linarith
  have hβ1 : ∀ j, (1 : ℝ) ≤ logHeight₁ (β j) := fun j ↦ by
    have h1 := hsmall j
    have h2 : (1 : ℝ) ≤ (tw : ℝ) * (1 + Hα j) :=
      one_le_mul_of_one_le_of_one_le htw1 (by linarith [hHα0 j])
    have h3 := mul_le_mul_of_nonneg_right hδ1 (hβpos j).le
    linarith
  have hmono : Monotone fun j ↦ logHeight₁ (β j) :=
    Fin.monotone_iff_le_succ.mpr fun j ↦
      le_trans (le_mul_of_one_le_left (hβpos _).le hM1) (hchain j)
  set Hmax : ℝ := logHeight₁ (β (Fin.last mnum)) with hHmaxdef
  have hHmax0 : (0 : ℝ) < Hmax := hβpos _
  have hβle : ∀ j : Fin (mnum + 1), logHeight₁ (β j) ≤ Hmax := fun j ↦ hmono (Fin.le_last j)
  clear_value Hmax
  set Hβ : ℝ := ∑ j : Fin (mnum + 1), logHeight₁ (β j) with hHβdef
  have hHβ0 : (0 : ℝ) ≤ Hβ := Finset.sum_nonneg fun j _ ↦ (hβpos j).le
  clear_value Hβ
  -- the targets as points, and the two constants that measure them
  set tgt : (↥Sinf ⊕ ↥Sfin) → Fin (mnum + 1) → F := fun a j ↦ α j (sPlaceAbsValue a)
    with htgtdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set C₁ : Fin (mnum + 1) → ℝ := fun j ↦ Real.log 2 + 1 + Hα j with hC₁def
  have hC₁0 : ∀ j, 0 ≤ C₁ j := fun j ↦ by
    simp only [hC₁def]
    linarith [hHα0 j]
  have hC₁ : ∀ a j, absLogHeight₁ (tgt a j) + Real.log 2 + 1 ≤ C₁ j := fun a j ↦ by
    simp only [htgtdef, hC₁def]
    linarith [hsingle j a]
  have hC₁le : ∀ j, (tw : ℝ) * C₁ j ≤ 2 * δ * logHeight₁ (β j) := fun j ↦ by
    have h := hsmall j
    have h2 : C₁ j ≤ 2 * (1 + Hα j) := by
      simp only [hC₁def]
      linarith [hHα0 j]
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ (tw : ℝ))
    linarith
  set Cα : Fin (mnum + 1) → ℝ := fun j ↦ Real.exp (rF * Hα j) with hCαdef
  have hCα1 : ∀ j, 1 ≤ Cα j := fun j ↦ Real.one_le_exp (by
    have := hHα0 j
    positivity)
  have hCα : ∀ (a : ↥Sinf ⊕ ↥Sfin) j, w (sPlaceAbsValue a) (α j (sPlaceAbsValue a)) ≤ Cα j := by
    intro a j
    have h1 := max_apply_one_le_mulHeight₁_sPlaceAbsValue hwInf hwFin a (α j (sPlaceAbsValue a))
    have h2 : mulHeight₁ (α j (sPlaceAbsValue a)) ≤ Cα j := by
      rw [← Real.exp_log (mulHeight₁_pos _), habsF]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsingle j a) (by linarith))
    exact le_trans (le_max_left _ _) (le_trans h1 h2)
  have hlogCα : ∀ j, Real.log 4 + 2 * Real.log (Cα j) ≤ 2 * rF * δ * logHeight₁ (β j) := by
    intro j
    rw [show Real.log (Cα j) = rF * Hα j from Real.log_exp _]
    have h := hsmall j
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      linarith
    have h2 : Real.log 4 + 2 * (rF * Hα j) ≤ 2 * rF * (1 + Hα j) := by linarith
    have h3 : 2 * rF * (1 + Hα j) ≤ 2 * rF * ((tw : ℝ) * (1 + Hα j)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith [hHα0 j]) htw1)
        (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * rF)
    linarith
  -- Steps I and II
  obtain ⟨D₀, hD₀⟩ := exists_auxiliary_deriv tgt hε0 hε1 hfeasA hC₁0 hC₁
  rw [← hσdef, ← htwdef] at hD₀
  -- a large `D`
  obtain ⟨D, hDbig, hD0, hDlog⟩ := Real.exists_le_and_mul_log_add_lt
    (B := (tw : ℝ) + 2 * (Wsum : ℝ)) (E := Hβ) (c := (Θ - 1) / 2)
    (D₁ := max (((max D₀ 1 : ℕ) : ℝ) * Hmax) (2 * Hmax / σ))
    (by positivity) (by linarith only [hΘ1])
  have hDD₀ : ((max D₀ 1 : ℕ) : ℝ) * Hmax ≤ D := le_trans (le_max_left _ _) hDbig
  have hDσ : 2 * Hmax / σ ≤ D := le_trans (le_max_right _ _) hDbig
  have hmax1 : (1 : ℝ) ≤ ((max D₀ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right D₀ 1
  have hDH : ∀ j, logHeight₁ (β j) ≤ D := fun j ↦
    le_trans (hβle j) (le_trans (le_mul_of_one_le_left hHmax0.le hmax1) hDD₀)
  -- the multidegree
  set d : Fin (mnum + 1) → ℕ := fun j ↦ ⌈D / logHeight₁ (β j)⌉₊ with hddef
  have hdlow : ∀ j, D / logHeight₁ (β j) ≤ (d j : ℝ) := fun j ↦ Nat.le_ceil _
  have hdhigh : ∀ j, (d j : ℝ) < D / logHeight₁ (β j) + 1 := fun j ↦
    Nat.ceil_lt_add_one (div_nonneg hD0.le (hβpos j).le)
  have hdD : ∀ j, D ≤ (d j : ℝ) * logHeight₁ (β j) := fun j ↦ by
    rw [← div_le_iff₀ (hβpos j)]
    exact hdlow j
  have hdone : ∀ j, (1 : ℝ) ≤ D / logHeight₁ (β j) := fun j ↦ by
    rw [le_div_iff₀ (hβpos j), one_mul]
    exact hDH j
  have hd2 : ∀ j, (d j : ℝ) * logHeight₁ (β j) ≤ 2 * D := fun j ↦ by
    have h : (d j : ℝ) ≤ 2 * (D / logHeight₁ (β j)) := by linarith only [hdhigh j, hdone j]
    calc (d j : ℝ) * logHeight₁ (β j) ≤ 2 * (D / logHeight₁ (β j)) * logHeight₁ (β j) :=
          mul_le_mul_of_nonneg_right h (hβpos j).le
      _ = 2 * D := by rw [mul_assoc, div_mul_cancel₀ D (hβpos j).ne']
  have hdD₀ : ∀ j, max D₀ 1 ≤ d j := fun j ↦ by
    have h1 : ((max D₀ 1 : ℕ) : ℝ) ≤ (d j : ℝ) := by
      calc ((max D₀ 1 : ℕ) : ℝ) ≤ D / Hmax := by rw [le_div_iff₀ hHmax0]; exact hDD₀
        _ ≤ D / logHeight₁ (β j) := by
            rw [div_le_div_iff₀ hHmax0 (hβpos j)]
            exact mul_le_mul_of_nonneg_left (hβle j) hD0.le
        _ ≤ (d j : ℝ) := hdlow j
    exact_mod_cast h1
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (le_max_right D₀ 1) (hdD₀ j)
  -- the degrees drop fast enough for Roth's lemma
  have hratio : ∀ j : Fin mnum, (d j.succ : ℝ) ≤ σ * (d j.castSucc : ℝ) := by
    intro j
    have hsucc : Mind * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ) := hchain j
    have hquo0 : (0 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) :=
      mul_nonneg (by positivity) (div_nonneg hD0.le (hβpos _).le)
    have heq : σ / 2 * (D / logHeight₁ (β j.castSucc))
        * (Mind * logHeight₁ (β j.castSucc)) = D := by
      rw [hMdef, show σ / 2 * (D / logHeight₁ (β j.castSucc))
          * (2 / σ * logHeight₁ (β j.castSucc))
          = σ / 2 * (2 / σ) * (D / logHeight₁ (β j.castSucc) * logHeight₁ (β j.castSucc)) from
        by ring, div_mul_cancel₀ D (hβpos _).ne', show σ / 2 * (2 / σ) = 1 from by field_simp,
        one_mul]
    have hstep : D / logHeight₁ (β j.succ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      rw [div_le_iff₀ (hβpos _)]
      calc D = σ / 2 * (D / logHeight₁ (β j.castSucc))
              * (Mind * logHeight₁ (β j.castSucc)) := heq.symm
        _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) * logHeight₁ (β j.succ) :=
            mul_le_mul_of_nonneg_left hsucc hquo0
    have hu2 : 2 / σ ≤ D / logHeight₁ (β j.castSucc) := by
      rw [div_le_div_iff₀ hσ0 (hβpos _)]
      rw [div_le_iff₀ hσ0] at hDσ
      linarith only [hDσ, hβle j.castSucc]
    have hone : (1 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      have h := mul_le_mul_of_nonneg_left hu2 (by positivity : (0 : ℝ) ≤ σ / 2)
      rwa [show σ / 2 * (2 / σ) = 1 by field_simp] at h
    calc (d j.succ : ℝ) ≤ D / logHeight₁ (β j.succ) + 1 := (hdhigh _).le
      _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) + 1 := by linarith only [hstep]
      _ ≤ σ * (D / logHeight₁ (β j.castSucc)) := by linarith only [hone]
      _ ≤ σ * (d j.castSucc : ℝ) := mul_le_mul_of_nonneg_left (hdlow _) hσ0.le
  -- the heights of the targets cost `O(δ D)` per coordinate
  have hterm : ∀ i, (tw : ℝ) * (C₁ i * (d i : ℝ)) ≤ 4 * δ * D := fun i ↦ by
    have hdi : (0 : ℝ) ≤ d i := Nat.cast_nonneg _
    calc (tw : ℝ) * (C₁ i * (d i : ℝ)) = ((tw : ℝ) * C₁ i) * (d i : ℝ) := by ring
      _ ≤ (2 * δ * logHeight₁ (β i)) * (d i : ℝ) := mul_le_mul_of_nonneg_right (hC₁le i) hdi
      _ = 2 * δ * ((d i : ℝ) * logHeight₁ (β i)) := by ring
      _ ≤ 2 * δ * (2 * D) := mul_le_mul_of_nonneg_left (hd2 i) (by positivity)
      _ = 4 * δ * D := by ring
  have hsumC₁ : (tw : ℝ) * ∑ i, C₁ i * (d i : ℝ) ≤ ((mnum : ℝ) + 1) * (4 * δ * D) := by
    rw [Finset.mul_sum]
    calc ∑ i, (tw : ℝ) * (C₁ i * (d i : ℝ)) ≤ ∑ _i : Fin (mnum + 1), 4 * δ * D :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ((mnum : ℝ) + 1) * (4 * δ * D) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  -- the height condition of Roth's lemma
  have hRothH : ∀ j, (tw : ℝ) * ∑ i, C₁ i * (d i : ℝ)
      + 4 * ((mnum : ℝ) + 1) * (d 0 : ℝ) * (tw : ℝ)
      ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) := by
    intro j
    have hd0term : (d 0 : ℝ) * (tw : ℝ) ≤ 2 * δ * D := by
      have h1 : (tw : ℝ) ≤ δ * logHeight₁ (β 0) := by
        have := mul_nonneg (by linarith only [htw1] : (0 : ℝ) ≤ (tw : ℝ)) (hHα0 0)
        linarith only [hsmall 0, this]
      calc (d 0 : ℝ) * (tw : ℝ) ≤ (d 0 : ℝ) * (δ * logHeight₁ (β 0)) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = δ * ((d 0 : ℝ) * logHeight₁ (β 0)) := by ring
        _ ≤ δ * (2 * D) := mul_le_mul_of_nonneg_left (hd2 0) hδ0.le
        _ = 2 * δ * D := by ring
    have h4 := mul_le_mul_of_nonneg_left hd0term (by positivity : (0 : ℝ) ≤ 4 * ((mnum : ℝ) + 1))
    have h5 := mul_le_mul_of_nonneg_right hδσ hD0.le
    have h3 : σ * D ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) :=
      mul_le_mul_of_nonneg_left (hdD j) hσ0.le
    linarith only [hsumC₁, h4, h5, h3]
  -- Steps I and II produce the polynomial
  obtain ⟨Q, hQβ, hQdeg, hQindex, hQheight⟩ :=
    hD₀ d (fun j ↦ le_trans (le_max_left D₀ 1) (hdD₀ j)) β hratio hRothH
  -- Steps III to V
  simp only [htgtdef] at hQindex
  have hkey := roth_key_inequality hwA α (fun j ↦ hd1 j) hQdeg hQβ hQindex hlam0 hκ0.le hD0.le
    hblocal hdD hCα1 hCα
  have hWcast : ∑ a : ↥Sinf ⊕ ↥Sfin, ((sPlaceWeight a : ℕ) : ℝ) = (Wsum : ℝ) := by
    rw [hWdef]
    push_cast
    ring
  rw [← htwdef, hWcast] at hkey
  -- the four remaining estimates
  have hsumlog : (∑ j, Real.log ((d j : ℝ) + 1)) ≤ ((mnum : ℝ) + 1) * Real.log (D + 2) := by
    calc (∑ j : Fin (mnum + 1), Real.log ((d j : ℝ) + 1))
        ≤ ∑ _j : Fin (mnum + 1), Real.log (D + 2) := by
          refine Finset.sum_le_sum fun j _ ↦ Real.log_le_log ?_ ?_
          · positivity
          · have h1 : D / logHeight₁ (β j) ≤ D := div_le_self hD0.le (hβ1 j)
            linarith only [hdhigh j, h1]
      _ = ((mnum : ℝ) + 1) * Real.log (D + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hsumCα : (∑ j, (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j)))
      ≤ ((mnum : ℝ) + 1) * (4 * rF * δ * D) := by
    calc (∑ j : Fin (mnum + 1), (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j)))
        ≤ ∑ _j : Fin (mnum + 1), 4 * rF * δ * D := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          calc (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j))
              ≤ (d j : ℝ) * (2 * rF * δ * logHeight₁ (β j)) :=
                mul_le_mul_of_nonneg_left (hlogCα j) (Nat.cast_nonneg _)
            _ = 2 * rF * δ * ((d j : ℝ) * logHeight₁ (β j)) := by ring
            _ ≤ 2 * rF * δ * (2 * D) :=
                mul_le_mul_of_nonneg_left (hd2 j) (by positivity)
            _ = 4 * rF * δ * D := by ring
      _ = ((mnum : ℝ) + 1) * (4 * rF * δ * D) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hQh : Real.log Q.mulHeight ≤ ((mnum : ℝ) + 1) * (8 * δ * D) := by
    have hle : (tw : ℝ) * ∑ i, (C₁ i + Real.log 2) * (d i : ℝ)
        ≤ 2 * ((tw : ℝ) * ∑ i, C₁ i * (d i : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hC : Real.log 2 ≤ C₁ i := by
        simp only [hC₁def]
        linarith only [hHα0 i]
      have hdi : (0 : ℝ) ≤ d i := Nat.cast_nonneg _
      have h3 := mul_le_mul_of_nonneg_left hC
        (mul_nonneg (by linarith only [htw1] : (0 : ℝ) ≤ (tw : ℝ)) hdi)
      linarith only [h3]
    linarith only [hsumC₁, hle, hQheight]
  have hsumdh : (∑ j, (d j : ℝ) * logHeight₁ (β j)) ≤ ((mnum : ℝ) + 1) * D + Hβ := by
    have hterm' : ∀ j : Fin (mnum + 1),
        (d j : ℝ) * logHeight₁ (β j) ≤ D + logHeight₁ (β j) := fun j ↦ by
      have h := mul_le_mul_of_nonneg_right (hdhigh j).le (hβpos j).le
      rwa [add_mul, div_mul_cancel₀ D (hβpos j).ne', one_mul] at h
    calc (∑ j : Fin (mnum + 1), (d j : ℝ) * logHeight₁ (β j))
        ≤ ∑ j : Fin (mnum + 1), (D + logHeight₁ (β j)) := Finset.sum_le_sum fun j _ ↦ hterm' j
      _ = ((mnum : ℝ) + 1) * D + Hβ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_fin, hHβdef]
          push_cast
          ring
  -- Step V: the comparison
  have hlhs : Θ * (((mnum : ℝ) + 1) * D)
      ≤ κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by
    have hfac : (0 : ℝ) ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) :=
      mul_nonneg hκ0.le (mul_nonneg hε4.le (mul_nonneg hm1.le hD0.le))
    have h := mul_le_mul_of_nonneg_left hlamsum hfac
    calc Θ * (((mnum : ℝ) + 1) * D)
        = κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (1 - (SA : ℝ) / N) := by
          rw [hΘdef]; ring
      _ ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (∑ a, lam a) := h
      _ = κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by ring
  have hb1 := mul_le_mul_of_nonneg_left hsumlog
    (by positivity : (0 : ℝ) ≤ (tw : ℝ) + 2 * (Wsum : ℝ))
  have hb2 := mul_le_mul_of_nonneg_left hsumCα hW0
  have hδD := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδΘ hD0.le) hm1.le
  have hDlog' := mul_lt_mul_of_pos_left hDlog hm1
  have hmH : (0 : ℝ) ≤ (mnum : ℝ) * Hβ := mul_nonneg (Nat.cast_nonneg _) hHβ0
  linarith only [hlhs, hkey, hb1, hb2, hQh, hsumdh, hδD, hDlog', hmH]

/-- **The core of Roth's proof, with moving targets** (Bombieri–Gubler 6.4.5 to 6.4.10, as 6.5.2
reads them): there is a `δ > 0` such that **no chain of `rothChainLength κ s r + 1` solutions in
one approximation class, with heights growing by the ratio `rothRatio κ s r`, has targets small
against it** — `1 + ∑ v ∈ S, h(α j v) ≤ δ h(β j)` for every member `β j`, whose own targets are
`α j`. Here `s = |S|`, `r = [F : K]`, and the class is given by its vector of exponents `λ`, with
`∑ λ ≥ 1 − s / N` for `N = rothClassSize κ s`. The number `δ` depends on `K`, `S`, `[F : ℚ]` and
`κ` and on no target; the smallness condition is in absolute heights and the ratio, which reads
the same in both normalizations, in Mathlib's relative ones. -/
theorem roth_no_moving_chain (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / rothClassSize κ (Sinf.card + Sfin.card)
        ≤ ∑ a, lam a →
      ∀ (α : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) →
          AbsoluteValue K ℝ → F)
        (β : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K),
        (∀ j, 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a))
          ≤ δ * absLogHeight₁ (β j)) →
        (∀ j : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
          rothRatio κ (Sinf.card + Sfin.card) (finrank K F) * logHeight₁ (β j.castSucc)
            ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, localApprox Sinf Sfin w (α j) a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
  obtain ⟨hε0, hε1, hε4⟩ := rothEps_spec hκ
  exact roth_no_moving_chain_aux Sinf Sfin w hwInf hwFin (by linarith) hε0 hε1 hε4
    (rothClassSize_spec hκ _).2.2 (rothChainLength_spec hκ _ _)

/-- **The core of Roth's proof** (Bombieri–Gubler 6.4.5 to 6.4.10, read as in 6.5.7): there is a
height `L` — depending on `K`, `S` and the targets — such that **no `(L, M)`-independent chain of
`rothChainLength κ s r + 1` solutions lies in one approximation class**. Here `s = |S|`,
`r = [F : K]`, `M = rothRatio κ s r` and the class is given by its vector of exponents `λ`, with
`∑ λ ≥ 1 − s / N` for `N = rothClassSize κ s`; the length, the ratio and the class size depend on
`κ`, `s` and `r` alone. Heights are Mathlib's relative ones. It is the fixed-target case of
`NumberField.roth_no_moving_chain`, with `L = [K : ℚ] (1 + ∑ v ∈ S, h(α v)) / δ`. -/
theorem roth_no_chain (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    ∃ L : ℝ, ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / rothClassSize κ (Sinf.card + Sfin.card)
        ≤ ∑ a, lam a →
      ∀ β : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K,
        L ≤ logHeight₁ (β 0) →
        (∀ j : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
          rothRatio κ (Sinf.card + Sfin.card) (finrank K F) * logHeight₁ (β j.castSucc)
            ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, localApprox Sinf Sfin w α a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
  obtain ⟨δ, hδ0, hδ⟩ := roth_no_moving_chain Sinf Sfin w hwInf hwFin hκ
  refine ⟨(totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
      / δ, fun lam hlam0 hlamsum β hβL hchain ↦
    hδ lam hlam0 hlamsum (fun _ ↦ α) β (fun j ↦ ?_) hchain⟩
  have hmono : Monotone fun j ↦ logHeight₁ (β j) :=
    Fin.monotone_iff_le_succ.mpr fun j ↦
      le_trans (le_mul_of_one_le_left (zero_le_logHeight₁ _) (one_le_rothRatio hκ _ _))
        (hchain j)
  have hLj : (totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
      / δ ≤ logHeight₁ (β j) := le_trans hβL (hmono (Fin.zero_le j))
  have htw : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
  have hfrK : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have habs : (totalWeight K : ℝ) * absLogHeight₁ (β j) = logHeight₁ (β j) := by
    rw [absLogHeight₁_eq_inv_mul, totalWeight_eq_finrank, logHeight₁_eq_log_mulHeight₁]
    field_simp
  rw [div_le_iff₀ hδ0, ← habs] at hLj
  change 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)) ≤ δ * absLogHeight₁ (β j)
  refine le_of_mul_le_mul_left ?_ htw
  calc (totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
      ≤ (totalWeight K : ℝ) * absLogHeight₁ (β j) * δ := hLj
    _ = (totalWeight K : ℝ) * (δ * absLogHeight₁ (β j)) := by ring

/-! ### Roth's theorem -/

/-- **Layer 3.2: Roth's theorem** (Bombieri–Gubler, Theorem 6.4.1). -/
theorem finite_setOf_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hκ0 : (0 : ℝ) < κ := by linarith
  -- discard the finitely many degenerate solutions
  have hbad : ({β : K | mulHeight₁ β ≤ 1}
      ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}).Finite := by
    refine Set.Finite.union (finite_setOfPred_mulHeight₁_le (K := K) 1)
      (Set.finite_iUnion fun a ↦ ?_)
    exact Set.Subsingleton.finite fun x hx y hy ↦
      (algebraMap K F).injective ((Set.mem_ofPred_eq ▸ hx).trans (Set.mem_ofPred_eq ▸ hy).symm)
  have hXinf := hinf.sdiff hbad
  set X : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}
      \ ({β : K | mulHeight₁ β ≤ 1}
        ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}) with hXdef
  have hXh : ∀ β ∈ X, 1 < mulHeight₁ β := fun β hβ ↦ by
    by_contra h
    exact hβ.2 (Set.mem_union_left _ (not_lt.mp h))
  have hXne : ∀ (a : ↥Sinf ⊕ ↥Sfin), ∀ β ∈ X, algebraMap K F β ≠ α (sPlaceAbsValue a) :=
    fun a β hβ h ↦ hβ.2 (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hXsub : ∀ β ∈ X, (∏ a, localApprox Sinf Sfin w α a β) ≤ mulHeight₁ β ^ (-κ) := by
    intro β hβ
    rw [prod_localApprox]
    exact hβ.1
  have hfpos : ∀ a, ∀ β ∈ X, 0 < localApprox Sinf Sfin w α a β := fun a β hβ ↦
    pow_pos (lt_min one_pos ((w _).pos (sub_ne_zero.mpr (hXne a β hβ)))) _
  have hfle : ∀ a, ∀ β ∈ X, localApprox Sinf Sfin w α a β ≤ 1 :=
    fun a β _ ↦ localApprox_le_one _ _ _ _ _ _
  -- the parameters `ε` and `N`
  -- the core, fed by Step 0
  obtain ⟨L, hL⟩ := roth_no_chain Sinf Sfin w hwInf hwFin α hκ
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = Sinf.card + Sfin.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  obtain ⟨lam, hlam0, hlamsum, b, -, hbind, hblocal⟩ :=
    exists_isHeightIndependent_forall_le_rpow (localApprox Sinf Sfin w α) hXinf hfpos hfle hκ0
      hXsub hXh (rothClassSize_spec hκ (Sinf.card + Sfin.card)).1 L
      (rothRatio κ (Sinf.card + Sfin.card) (finrank K F))
  rw [hcard] at hlamsum
  refine hL lam hlam0 hlamsum (fun j ↦ b j.val) (by simpa using hbind.1) (fun j ↦ ?_)
    fun j a ↦ hblocal j.val a
  simpa [Fin.val_succ, Fin.val_castSucc] using hbind.2 j.val


/-! ### Acceptance criteria -/

/-- **Conformance: the classical shape.** One infinite place and one target — Roth's theorem as it
is usually quoted, before any set of places appears. -/
example (v : InfinitePlace K) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hw : (w v.1).LiesOver v.1) (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult
      ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  have h := finite_setOf_prod_min_one_le {v} (∅ : Finset (FinitePlace K)) w
    (fun u hu ↦ by rwa [Finset.mem_singleton.mp hu])
    (fun u hu ↦ absurd hu (Finset.notMem_empty u)) α hκ
  simpa using h

omit [NumberField F] in
/-- The truncated product is at most `1`, whatever the data. -/
private theorem prod_min_one_le_one (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (α : AbsoluteValue K ℝ → F) (β : K) :
    (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ 1 := by
  have hnn : ∀ u : AbsoluteValue K ℝ, (0 : ℝ) ≤ min 1 (w u (algebraMap K F β - α u)) :=
    fun u ↦ le_min zero_le_one ((w u).nonneg _)
  have hA : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ pow_nonneg (hnn v.1) _)
      fun v _ ↦ pow_le_one₀ (hnn v.1) (min_le_left _ _)
  have hB : (∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ hnn v.1) fun v _ ↦ min_le_left _ _
  have hB0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) :=
    Finset.prod_nonneg fun v _ ↦ hnn v.1
  calc (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ 1 * 1 :=
      mul_le_mul hA hB hB0 zero_le_one
    _ = 1 := one_mul 1

/-- **The theorem bounds a nonempty set, at every `κ`.** With the target `0` at every place, `0`
is a solution: its local factors all vanish and its height is `1`. So the finiteness is not
finiteness of the empty set. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (κ : ℝ) :
    (0 : K) ∈ {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - (fun _ ↦ 0) v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - (fun _ ↦ 0) v.1))
        ≤ mulHeight₁ β ^ (-κ)} := by
  rw [Set.mem_ofPred_eq, mulHeight₁_zero, Real.one_rpow]
  exact prod_min_one_le_one Sinf Sfin w (fun _ ↦ 0) 0

/-- **Rejection test: a positive exponent is not decoration.** At `κ = 0` the right-hand side is
`1` and the truncated product is always at most `1`, so *every* element of `K` is a solution and
the set the theorem bounds is infinite. The hypothesis `2 < κ` is therefore doing work, and it is
the only hypothesis that is. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))
        ≤ mulHeight₁ β ^ (-(0 : ℝ))}.Infinite := by
  have huniv : {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))
        ≤ mulHeight₁ β ^ (-(0 : ℝ))} = Set.univ := by
    refine Set.eq_univ_of_forall fun β ↦ ?_
    rw [Set.mem_ofPred_eq, neg_zero, Real.rpow_zero]
    exact prod_min_one_le_one Sinf Sfin w α β
  rw [huniv]
  exact Set.infinite_univ

end NumberField

end
