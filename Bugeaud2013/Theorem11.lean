/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Theorem31
public import DiophantineApproximation.FactorComplexity

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Theorem 1.1 (Bugeaud 2013, §4)

**Theorem 1.1**: if `a = a₁ a₂ …` is a sequence of positive integers which is not eventually
periodic and `[0; a₁, a₂, …]` is algebraic, then `p(n, a) / n → ∞`.

The proof in §4: if `p(n, a) ≤ C n` for infinitely many `n`, the alphabet is finite, so
`q_ℓ^{1/ℓ}` is bounded, and the Schubfachprinzip gives Condition `(♠)`; Theorem 3.1 applies.

## Main results

* `Function.hasSpadeRepetitions_of_periodic`: a period `s_k` on a segment of length `w s_k`
  after position `r_k ≤ C' s_k` (`w > 1`, `s_k → ∞`) gives the repetitions of `(♠)`.
* `Nat.bddAbove_contDen_rpow`: bounded partial quotients make `q_ℓ^{1/ℓ}` bounded.
* `Nat.eventually_lt_encard_factors`: **Theorem 1.1**, `p(n, a) > C n` for every `C` and all
  large `n`, with `p(n, a)` counted in `ℕ∞`.
* `Nat.tendsto_complexity_div_atTop`: **Theorem 1.1** in the form `p(n, a) / n → ∞`, with
  `Function.complexity`, for a sequence taking finitely many values.

## Implementation notes

⚠ **The pigeonhole step is not redone.** `Function.exists_periodic_of_frequently_complexity_le`
(Adamczewski–Bugeaud 2007, §4, in `DiophantineApproximation/FactorComplexity.lean`) already turns
`p(n) ≤ C n` infinitely often into periodic segments. The paper's own case split
(`|W_n X_n| ≤ |W'_n|` or not) is replaced by that lemma's re-cut period: with period `P` on a
segment of length `L + P` after position `r`, the words `W = a₁ … a_r`, `U` of length
`min(L, P)` and `V` of length `P - min(L, P)` give the prefix `W U V U`.

⚠ **The complexity of an infinite alphabet.** `Function.complexity` is `Set.ncard`, which is
`0` on an infinite set of factors, so `p(n, a) / n → ∞` is false as written when `a` is
unbounded. The paper reads `p(n, a) = ∞` there. `Nat.eventually_lt_encard_factors` counts with
`Set.encard` and needs no finiteness; `Nat.tendsto_complexity_div_atTop` assumes it.
-/

@[expose] public section

open Filter

namespace Function

variable {α : Type*}

/-- Adjacent factors concatenate. -/
theorem factor_append_factor (x : ℕ → α) (i m n : ℕ) :
    factor x i m ++ factor x (i + m) n = factor x i (m + n) := by
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [factor, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  split_ifs with hj
  · rfl
  · congr 1; omega

/-- Adjacent factors concatenate, with the second position given. -/
theorem factor_append_factor' (x : ℕ → α) {i j m n : ℕ} (h : i + m = j) :
    factor x i m ++ factor x j n = factor x i (m + n) := by
  rw [← h, factor_append_factor]

/-- The letters of a prefix. -/
theorem getElem?_factor_zero (x : ℕ → α) {n i : ℕ} (hi : i < n) :
    (factor x 0 n)[i]? = some (x i) := by
  simp [factor, hi]

/-- The factors of `x`, read in its range. -/
theorem factors_eq_image_rangeFactorization (x : ℕ → α) (m : ℕ) :
    factors x m = List.map Subtype.val '' factors (Set.rangeFactorization x) m := by
  rw [factors, factors, ← Set.range_comp]
  congr 1
  funext i
  simp only [factor, Function.comp_apply, List.map_ofFn]
  rfl

/-- For a sequence taking finitely many values, `Function.complexity` counts the factors. -/
theorem cast_complexity_of_finite {x : ℕ → α} (hfin : (Set.range x).Finite) (m : ℕ) :
    ((complexity x m : ℕ) : ℕ∞) = (factors x m).encard := by
  have := hfin.to_subtype
  have hf := finite_factors (Set.rangeFactorization x) m
  rw [complexity, Set.Finite.cast_ncard_eq ?_]
  rw [factors_eq_image_rangeFactorization]
  exact hf.image _

/-- **The repetitions of `(♠)` from periodic segments.** If `x` has period `s k` on the segment
of length `⌈w s k⌉` after position `r k`, with `w > 1`, `r k ≤ C' s k` and `s k → ∞`, then `x`
has the repetitions `W U V U` of Condition `(♠)`. -/
theorem hasSpadeRepetitions_of_periodic {x : ℕ → α} {w C' : ℝ} (hw : 1 < w) {r s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (hs1 : ∀ k, 1 ≤ s k) (hrs : ∀ k, (r k : ℝ) ≤ C' * s k)
    (hper : ∀ k i, r k ≤ i → i + s k < r k + ⌈w * s k⌉₊ → x (i + s k) = x i) :
    HasSpadeRepetitions x := by
  set L : ℕ → ℕ := fun k ↦ min (⌈w * s k⌉₊ - s k) (s k) with hL
  set δ : ℝ := min (w - 1) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hLs : ∀ k, L k ≤ s k := fun k ↦ min_le_right _ _
  -- `U` is long: `L ≥ δ P`
  have hLδ : ∀ k, δ * s k ≤ L k := by
    intro k
    have hP : (s k : ℝ) ≤ w * s k := le_mul_of_one_le_left (by positivity) hw.le
    have hc : (s k : ℝ) ≤ ⌈w * s k⌉₊ := hP.trans (Nat.le_ceil _)
    have hsub : ((⌈w * s k⌉₊ - s k : ℕ) : ℝ) = ⌈w * s k⌉₊ - s k := by
      rw [Nat.cast_sub (by exact_mod_cast hc)]
    simp only [hL, Nat.cast_min, hsub, le_min_iff]
    constructor
    · have := Nat.le_ceil (w * s k)
      nlinarith [min_le_left (w - 1) 1, (Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
    · nlinarith [(Nat.cast_nonneg (s k) : (0 : ℝ) ≤ s k)]
  have hLpos : ∀ k, (0 : ℝ) < L k := fun k ↦
    lt_of_lt_of_le (mul_pos hδ0 (by exact_mod_cast hs1 k)) (hLδ k)
  have hLt : Tendsto L atTop atTop := by
    refine (tendsto_natCast_atTop_iff (R := ℝ)).mp ?_
    refine tendsto_atTop_mono hLδ (Tendsto.const_mul_atTop hδ0 ?_)
    exact tendsto_natCast_atTop_atTop.comp hs
  obtain ⟨φ, -, hφ⟩ := strictMono_subseq_of_tendsto_atTop hLt
  refine ⟨fun n ↦ factor x 0 (r (φ n)), fun n ↦ factor x (r (φ n)) (L (φ n)),
    fun n ↦ factor x (r (φ n) + L (φ n)) (s (φ n) - L (φ n)), fun n i hi ↦ ?_, ⟨1 / δ, ?_⟩,
    ⟨C' / δ, ?_⟩, fun _ _ h ↦ by simpa using hφ h⟩
  · set k := φ n
    have hU : factor x (r k) (L k) = factor x (r k + s k) (L k) := by
      refine factor_eq_factor_iff.mpr fun j hj ↦ (hper k (r k + j) (by omega) ?_).symm.trans ?_
      · have : L k ≤ ⌈w * s k⌉₊ - s k := min_le_left _ _
        omega
      · rw [Nat.add_right_comm]
    have heq : factor x 0 (r k) ++ factor x (r k) (L k) ++
        factor x (r k + L k) (s k - L k) ++ factor x (r k) (L k) =
        factor x 0 (r k + s k + L k) := by
      have := hLs k
      rw [factor_append_factor' x (by omega), factor_append_factor' x (by omega),
        show r k + L k + (s k - L k) = r k + s k by omega, hU, factor_append_factor' x (by omega)]
    rw [heq] at hi ⊢
    exact getElem?_factor_zero x (by simpa using hi)
  · rintro _ ⟨n, rfl⟩
    simp only [length_factor]
    rw [div_le_div_iff₀ (hLpos _) hδ0, one_mul]
    have := hLδ (φ n)
    have : ((s (φ n) - L (φ n) : ℕ) : ℝ) ≤ s (φ n) := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  · rintro _ ⟨n, rfl⟩
    simp only [length_factor]
    rw [div_le_div_iff₀ (hLpos _) hδ0]
    have h1 := hLδ (φ n)
    have h2 := hrs (φ n)
    have hC : 0 ≤ C' := by
      by_contra hneg
      have : (0 : ℝ) < s (φ n) := by exact_mod_cast hs1 (φ n)
      nlinarith [(Nat.cast_nonneg (r (φ n)) : (0 : ℝ) ≤ r (φ n))]
    nlinarith

end Function

namespace Nat

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `q_{ℓ+1} ≤ (M + 1) q_ℓ` when the partial quotients are at most `M`. -/
theorem contDen_succ_le {M : ℕ} (hM : ∀ n, a (n + 1) ≤ M) (n : ℕ) :
    contDen a (n + 1) ≤ (M + 1) * contDen a n := by
  rcases n with _ | n
  · simpa using (hM 0).trans (Nat.le_succ M)
  · rw [contDen_add_two]
    have h1 := hM (n + 1)
    have h2 := contDen_le_contDen_succ ha n
    nlinarith

/-- `q_ℓ ≤ (M + 1)^ℓ` when the partial quotients are at most `M`. -/
theorem contDen_le_pow {M : ℕ} (hM : ∀ n, a (n + 1) ≤ M) (n : ℕ) :
    contDen a n ≤ (M + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    exact (contDen_succ_le ha hM n).trans (Nat.mul_le_mul_left _ ih)

/-- **Bounded partial quotients make `q_ℓ^{1/ℓ}` bounded** (§4, from (2.1)). -/
theorem bddAbove_contDen_rpow {M : ℕ} (hM : ∀ n, a (n + 1) ≤ M) :
    BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))) := by
  refine ⟨M + 1, ?_⟩
  rintro _ ⟨ℓ, rfl⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  · calc (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ)) ≤ (((M + 1 : ℕ) : ℝ) ^ ℓ) ^ (1 / (ℓ : ℝ)) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          exact_mod_cast contDen_le_pow ha hM ℓ
      _ = M + 1 := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) hℓ.ne']
          push_cast; rfl

/-- **Theorem 1.1 (Bugeaud 2013).** If `a₁ a₂ …` is not eventually periodic and
`[0; a₁, a₂, …]` is algebraic, then for every `C` the number of factors of length `n` exceeds
`C n` for all large `n`. Factors are counted in `ℕ∞`, so that an unbounded sequence, with
infinitely many factors of each length `n ≥ 1`, is covered. -/
theorem eventually_lt_encard_factors (hp : ¬ Function.IsEventuallyPeriodic fun k ↦ a (k + 1))
    (halg : IsAlgebraic ℚ (contFrac a)) (C : ℕ) :
    ∀ᶠ n in atTop, ((C * n : ℕ) : ℕ∞) < (Function.factors (fun k ↦ a (k + 1)) n).encard := by
  set x : ℕ → ℕ := fun k ↦ a (k + 1) with hx
  by_contra hne
  have hfr : ∃ᶠ n in atTop, (Function.factors x n).encard ≤ ((C * n : ℕ) : ℕ∞) :=
    (not_eventually.mp hne).mono fun _ h ↦ not_lt.mp h
  -- the alphabet is finite
  obtain ⟨n, hn, hn1⟩ := (hfr.and_eventually (eventually_ge_atTop 1)).exists
  have hfin_n : (Function.factors x n).Finite :=
    Set.encard_lt_top_iff.mp (hn.trans_lt (WithTop.coe_lt_top _))
  have hfin : (Set.range x).Finite := by
    refine (hfin_n.image fun l ↦ l.headD 0).subset ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨Function.factor x i (m + 1), ⟨i, rfl⟩, by rw [Function.factor_succ]; rfl⟩
  have := hfin.to_subtype
  -- pass to the finite alphabet `Set.range x`
  have hcard : ∀ m, ((Function.complexity (Set.rangeFactorization x) m : ℕ) : ℕ∞) =
      (Function.factors x m).encard := by
    intro m
    rw [Function.cast_complexity_of_finite (Set.toFinite _),
      Function.factors_eq_image_rangeFactorization x,
      Set.InjOn.encard_image (List.map_injective_iff.mpr Subtype.val_injective).injOn]
  have hy' : ∃ᶠ m in atTop, (Function.complexity (Set.rangeFactorization x) m : ℝ) ≤ C * m := by
    refine hfr.mono fun m hm ↦ ?_
    rw [← hcard] at hm
    exact_mod_cast Nat.cast_le.mp hm
  obtain ⟨w, C', hw, -, r, s, hs, hs1, hrs, hper⟩ :=
    Function.exists_periodic_of_frequently_complexity_le hy'
  have hrep : Function.HasSpadeRepetitions x :=
    Function.hasSpadeRepetitions_of_periodic hw hs.tendsto_atTop hs1 hrs
      fun k i hi hiL ↦ congrArg Subtype.val (hper k i hi hiL)
  -- bounded partial quotients
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hq := bddAbove_contDen_rpow ha (M := M) fun k ↦ hM ⟨k, rfl⟩
  exact transcendental_contFrac_of_isSpade ha hq ⟨hp, hrep⟩ halg

/-- **Theorem 1.1 (Bugeaud 2013)**, `lim p(n, a) / n = +∞`, for a sequence taking finitely many
values. -/
theorem tendsto_complexity_div_atTop (hfin : (Set.range fun k ↦ a (k + 1)).Finite)
    (hp : ¬ Function.IsEventuallyPeriodic fun k ↦ a (k + 1))
    (halg : IsAlgebraic ℚ (contFrac a)) :
    Tendsto (fun n ↦ (Function.complexity (fun k ↦ a (k + 1)) n : ℝ) / n) atTop atTop := by
  refine tendsto_atTop.mpr fun b ↦ ?_
  filter_upwards [eventually_lt_encard_factors ha hp halg ⌈b⌉₊, eventually_ge_atTop 1]
    with n hn hn1
  rw [← Function.cast_complexity_of_finite hfin, Nat.cast_lt] at hn
  have hn' : ((⌈b⌉₊ * n : ℕ) : ℝ) < Function.complexity (fun k ↦ a (k + 1)) n := by
    exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [le_div_iff₀ hn0]
  push_cast at hn'
  nlinarith [Nat.le_ceil b]

end Positive

end Nat
