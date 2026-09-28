/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.BetaApproximation
public import AdamczewskiBugeaud2007.PisotSubspace
public import DiophantineApproximation.StammeringWords
public import ForMathlib.NumberTheory.PisotNumber

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Theorem 5: expansions in a Pisot or Salem base

**Theorem 5 of Adamczewski–Bugeaud 2007.** Let `β > 1` be a Pisot or a Salem number and `a` a
bounded sequence of integers satisfying Condition `(∗)_w` for some `w > 1`. Then
`α = ∑ k, a k / β ^ (k + 1)` either lies in `ℚ(β)` or is transcendental.

The proof is the paper's. A repetition `U V ^ w` with `r = |U|`, `s = |V|` gives the approximation
`|α β ^ (r + s) - α β ^ r - (P_(r + s) (β) - P_r (β))| ≪ β ^ (-(w - 1) s)` of Lemma 1
(`Real.abs_sub_le_of_periodic`). At the other infinite places the conjugates of `β` have modulus at
most `1`, so the conjugates of the digit polynomials grow at most linearly
(`Complex.norm_aeval_digitPoly_le`). The Subspace Theorem over `ℚ(β)`
(`Real.exists_finset_submodule_of_pow_pow`) then puts the points
`(β ^ (r + s), β ^ r, P_(r + s) (β) - P_r (β))` into finitely many proper subspaces, and one of them
contains infinitely many. Its equation either fixes `β ^ s`, which is impossible, or expresses
`α` in `ℚ(β)` (`Real.mem_range_algebraMap_of_forall_mem`).

## Main results

* `Real.mem_adjoin_of_isStammering`: **Theorem 5**, for a real algebraic integer `β > 1` whose
  other conjugates lie in the closed unit disc.
* `Real.mem_adjoin_or_transcendental_of_isPisot`, `Real.mem_adjoin_or_transcendental_of_isSalem`:
  Theorem 5 as printed.
* `Real.mem_range_algebraMap_of_forall_mem`: the endgame, infinitely many points in one proper
  subspace.

## Implementation notes

⚠ **Non-periodicity is not needed.** The paper's Condition `(∗)_w` includes that `a` is not
eventually periodic; Theorem 5 holds without it, since an eventually periodic `a` already gives
`α ∈ ℚ(β)`. The hypothesis here is `Function.IsStammering a`, which has no periodicity clause.

⚠ **The digits are integers, indexed from `0`**: `α = ∑ k, a k / β ^ (k + 1)` is the paper's
`∑_{k ≥ 1} a_k β ^ (-k)`. Boundedness is `BddAbove (Set.range fun k ↦ |a k|)`.

⚠ **Only the inequalities of the paper are used, not its normalization.** The conjugates of the
digit polynomial are at most `2 M (r + s)`, a polynomial loss that the exponential gain
`β ^ (-(w - 1) s)` absorbs for large `s`. So the Subspace Theorem applies to the points with `k`
large, which is enough.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §4, Theorem 5.
-/

@[expose] public section

open Filter Finset IntermediateField NumberField Polynomial

namespace Real

/-- **A polynomial is eventually below an exponential**: `A (1 + B m) ^ p ≤ q ^ m` for all large
`m`, when `q > 1`. -/
theorem eventually_mul_one_add_mul_pow_le {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 1 < q)
    (p : ℕ) : ∀ᶠ m : ℕ in atTop, A * (1 + B * m) ^ p ≤ q ^ m := by
  set D : ℝ := A * (1 + B) ^ p with hDdef
  have hD : 0 ≤ D := by positivity
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) p hq).bound
    (c := (D + 1)⁻¹) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with m hm hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq0 : 0 < q ^ m := pow_pos (by linarith) m
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos hq0] at hm
  have h1 : 1 + B * m ≤ (1 + B) * m := by nlinarith
  have h2 : (1 + B * m) ^ p ≤ (1 + B) ^ p * (m : ℝ) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 p
  calc A * (1 + B * m) ^ p ≤ A * ((1 + B) ^ p * (m : ℝ) ^ p) := mul_le_mul_of_nonneg_left h2 hA
    _ ≤ A * ((1 + B) ^ p * ((D + 1)⁻¹ * q ^ m)) := by gcongr
    _ = D / (D + 1) * q ^ m := by rw [hDdef]; field_simp
    _ ≤ q ^ m := mul_le_of_le_one_left hq0.le (div_le_one_of_le₀ (by linarith) (by linarith))

/-- **The endgame of Theorem 5.** Let `K` be a field with a map to `ℝ`, `β > 1`, and `x k` points
of `K ^ 3` mapping to `(β ^ (r k + s k), β ^ r k, Y k)` with `s` strictly increasing. If
infinitely many of them lie in one proper subspace and `α β ^ (r + s) - α β ^ r - Y` stays
bounded along them, then `α` is in the image of `K`. -/
theorem mem_range_algebraMap_of_forall_mem {K : Type*} [Field K] [Algebra K ℝ] {β α c : ℝ}
    (hβ : 1 < β) {r s : ℕ → ℕ} (hs : StrictMono s) {x : ℕ → Fin 3 → K} {Y : ℕ → ℝ}
    (h0 : ∀ k, algebraMap K ℝ (x k 0) = β ^ (r k + s k))
    (h1 : ∀ k, algebraMap K ℝ (x k 1) = β ^ r k) (h2 : ∀ k, algebraMap K ℝ (x k 2) = Y k)
    {S : Set ℕ} (hS : S.Infinite)
    (hL : ∀ k ∈ S, |α * β ^ (r k + s k) - α * β ^ r k - Y k| ≤ c)
    {V : Submodule K (Fin 3 → K)} (hV : V ≠ ⊤) (hxV : ∀ k ∈ S, x k ∈ V) :
    α ∈ Set.range (algebraMap K ℝ) := by
  classical
  have hB0 : (0 : ℝ) < β := by linarith
  obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hV) inferInstance
  set z : Fin 3 → K := fun i ↦ f (fun t ↦ if i = t then 1 else 0) with hzdef
  have hfx : ∀ y : Fin 3 → K, f y = ∑ i, y i * z i := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]
  have hz : ¬ (z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, Fin.sum_univ_three, h0, h1, h2])
  set Z : Fin 3 → ℝ := fun i ↦ algebraMap K ℝ (z i) with hZdef
  have hinj : Function.Injective (algebraMap K ℝ) := (algebraMap K ℝ).injective
  have hrel : ∀ k ∈ S, β ^ (r k + s k) * Z 0 + β ^ r k * Z 1 + Y k * Z 2 = 0 := by
    intro k hk
    have hmap : f (x k) ∈ Submodule.map f V := Submodule.mem_map_of_mem (hxV k hk)
    rw [hfV, Submodule.mem_bot, hfx, Fin.sum_univ_three] at hmap
    have h := congrArg (algebraMap K ℝ) hmap
    simp only [map_add, map_mul, map_zero, h0, h1, h2] at h
    exact h
  by_cases hz2 : z 2 = 0
  · -- the relation does not involve the third coordinate: it pins down `β ^ s`
    have hZ2 : Z 2 = 0 := by simp [hZdef, hz2]
    obtain ⟨k₁, hk₁⟩ := hS.nonempty
    obtain ⟨k₂, hk₂, hlt⟩ := hS.exists_gt k₁
    have hlin : ∀ k ∈ S, β ^ s k * Z 0 + Z 1 = 0 := by
      intro k hk
      have h := hrel k hk
      rw [hZ2, mul_zero, add_zero, pow_add] at h
      have hr : β ^ r k ≠ 0 := (pow_pos hB0 _).ne'
      have : β ^ r k * (β ^ s k * Z 0 + Z 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left hr
    have hne : β ^ s k₁ - β ^ s k₂ ≠ 0 := sub_ne_zero.mpr (pow_lt_pow_right₀ hβ (hs hlt)).ne
    have hZ0 : Z 0 = 0 := by
      have : (β ^ s k₁ - β ^ s k₂) * Z 0 = 0 := by linear_combination hlin k₁ hk₁ - hlin k₂ hk₂
      exact (mul_eq_zero.mp this).resolve_left hne
    have hZ1 : Z 1 = 0 := by linear_combination hlin k₁ hk₁ - β ^ s k₁ * hZ0
    exact (hz ⟨hinj (by rw [map_zero]; exact hZ0), hinj (by rw [map_zero]; exact hZ1),
      hz2⟩).elim
  · -- the relation determines the third coordinate, and the approximation determines `α`
    have hZ2 : Z 2 ≠ 0 := fun h ↦ hz2 (hinj (by rw [map_zero]; exact h))
    set θ : ℝ := α + Z 0 / Z 2 with hθ
    set η : ℝ := Z 1 / Z 2 - α with hη
    have hbound : ∀ k ∈ S, |θ * β ^ s k + η| ≤ |c| := by
      intro k hk
      have hr : (0 : ℝ) < β ^ r k := pow_pos hB0 _
      have hid : α * β ^ (r k + s k) - α * β ^ r k - Y k = β ^ r k * (θ * β ^ s k + η) := by
        have h := hrel k hk
        rw [hθ, hη, pow_add]
        rw [pow_add] at h
        field_simp
        linear_combination -h
      have hE := hL k hk
      rw [hid, abs_mul, abs_of_pos hr] at hE
      have hr1 : (1 : ℝ) ≤ β ^ r k := one_le_pow₀ hβ.le
      nlinarith [abs_nonneg (θ * β ^ s k + η), le_abs_self c]
    by_cases hθ0 : θ = 0
    · refine ⟨-(z 0 / z 2), ?_⟩
      rw [map_neg, map_div₀]
      change -(Z 0 / Z 2) = α
      linarith
    · obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((|c| + |η|) / |θ|) hβ
      obtain ⟨k, hk, hNk⟩ := hS.exists_gt N
      have hsk : N ≤ s k := hNk.le.trans (hs.id_le k)
      have hb1 := hbound k hk
      have hb2 : (|c| + |η|) / |θ| < β ^ s k := hN.trans_le (pow_le_pow_right₀ hβ.le hsk)
      rw [div_lt_iff₀ (abs_pos.mpr hθ0)] at hb2
      have hb3 : |θ * β ^ s k| ≤ |θ * β ^ s k + η| + |η| := by
        have := abs_sub (θ * β ^ s k + η) η
        rwa [add_sub_cancel_right] at this
      rw [abs_mul, abs_of_pos (pow_pos hB0 _)] at hb3
      linarith

/-- **The exponent bookkeeping of Theorem 5.** With `ε = min 1 ((w - 1) / (4 (C + 1)))` and
`δ = (w - 1) / (2 (C + 1))`, a polynomial loss `c₃ c₁ G ^ (4 n) ≤ β ^ (δ (r + s))` is absorbed:
`c₃ β ^ (-(⌈w s⌉ - s)) G ^ (2 n) ≤ (c₁ β ^ (r + s) G ^ (2 n)) ^ (-ε)` whenever `r ≤ C s`. -/
theorem div_pow_mul_pow_le_rpow {β w C c₁ c₃ G : ℝ} (hβ : 1 < β) (hw : 1 < w) (hC : 0 ≤ C)
    (hc₁ : 1 ≤ c₁) (hG : 1 ≤ G) {n r s : ℕ} (hrs : (r : ℝ) ≤ C * s)
    (hkey : c₃ * c₁ * G ^ (4 * n) ≤ (β ^ ((w - 1) / (2 * (C + 1)))) ^ (r + s)) :
    c₃ / β ^ (⌈w * s⌉₊ - s) * G ^ (2 * n)
      ≤ (c₁ * β ^ (r + s) * G ^ (2 * n)) ^ (-min 1 ((w - 1) / (4 * (C + 1)))) := by
  set ε := min 1 ((w - 1) / (4 * (C + 1))) with hεdef
  set δ := (w - 1) / (2 * (C + 1)) with hδdef
  set m : ℕ := r + s with hmdef
  set t : ℕ := ⌈w * s⌉₊ - s with htdef
  have hβ0 : 0 < β := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hε0 : 0 < ε := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε4 : ε ≤ (w - 1) / (4 * (C + 1)) := min_le_right _ _
  -- the exponents: `δ m + m ε ≤ t`
  have hst : s ≤ ⌈w * s⌉₊ := by
    have : (s : ℝ) ≤ w * s := le_mul_of_one_le_left (Nat.cast_nonneg _) hw.le
    exact_mod_cast this.trans (Nat.le_ceil _)
  have ht : (w - 1) * s ≤ (t : ℝ) := by
    rw [htdef, Nat.cast_sub hst]
    have := Nat.le_ceil (w * s)
    linarith
  have hm : (m : ℝ) ≤ (C + 1) * s := by
    rw [hmdef, Nat.cast_add]
    linarith
  have hexp : δ * m + m * ε ≤ t := by
    have h1 : δ * m ≤ (w - 1) / (2 * (C + 1)) * ((C + 1) * s) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg (by linarith) (by linarith))
    have h2 : m * ε ≤ (C + 1) * s * ((w - 1) / (4 * (C + 1))) :=
      mul_le_mul hm hε4 hε0.le (by positivity)
    have e1 : (w - 1) / (2 * (C + 1)) * ((C + 1) * s) = (w - 1) * s / 2 := by
      field_simp
    have e2 : (C + 1) * s * ((w - 1) / (4 * (C + 1))) = (w - 1) * s / 4 := by
      field_simp
    have hws : 0 ≤ (w - 1) * s := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  -- the bound
  have hQ : 1 ≤ c₁ * G ^ (2 * n) := one_le_mul_of_one_le_of_one_le hc₁ (one_le_pow₀ hG)
  have hQ0 : 0 < c₁ * G ^ (2 * n) := by linarith
  have hG0 : 0 < G := by linarith
  have hβm : 0 < β ^ m := pow_pos hβ0 m
  have hβt : 0 < β ^ t := pow_pos hβ0 t
  have hβε : 0 < β ^ ((m : ℝ) * ε) := Real.rpow_pos_of_pos hβ0 _
  have e1 : (c₁ * β ^ m * G ^ (2 * n)) ^ (-ε)
      = (c₁ * G ^ (2 * n)) ^ (-ε) * (β ^ ((m : ℝ) * ε))⁻¹ := by
    rw [show c₁ * β ^ m * G ^ (2 * n) = (c₁ * G ^ (2 * n)) * β ^ m by ring,
      Real.mul_rpow hQ0.le hβm.le, ← Real.rpow_natCast β m, ← Real.rpow_mul hβ0.le,
      ← Real.rpow_neg hβ0.le, neg_mul_eq_mul_neg]
  have e2 : (c₁ * G ^ (2 * n))⁻¹ ≤ (c₁ * G ^ (2 * n)) ^ (-ε) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have e3 : c₃ * c₁ * G ^ (4 * n) * β ^ ((m : ℝ) * ε) ≤ β ^ t := by
    have hk : c₃ * c₁ * G ^ (4 * n) ≤ β ^ (δ * m) := by
      rw [Real.rpow_mul hβ0.le, Real.rpow_natCast]
      exact hkey
    calc c₃ * c₁ * G ^ (4 * n) * β ^ ((m : ℝ) * ε) ≤ β ^ (δ * m) * β ^ ((m : ℝ) * ε) :=
          mul_le_mul_of_nonneg_right hk hβε.le
      _ = β ^ (δ * m + m * ε) := (Real.rpow_add hβ0 _ _).symm
      _ ≤ β ^ (t : ℝ) := Real.rpow_le_rpow_of_exponent_le hβ.le hexp
      _ = β ^ t := Real.rpow_natCast β t
  rw [e1]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right e2 (inv_nonneg.mpr hβε.le))
  have e4 : c₃ / β ^ t * G ^ (2 * n) = c₃ * c₁ * G ^ (4 * n) * β ^ ((m : ℝ) * ε) / β ^ t
      * ((c₁ * G ^ (2 * n))⁻¹ * (β ^ ((m : ℝ) * ε))⁻¹) := by
    field_simp
    ring
  rw [e4]
  exact mul_le_of_le_one_left (by positivity) ((div_le_one hβt).mpr e3)

open scoped Classical in
/-- **Theorem 5 (Adamczewski–Bugeaud 2007)**, for a real algebraic integer `β > 1` whose conjugates
other than `β` lie in the closed unit disc. If the bounded sequence of integers `a` is stammering
and `α = ∑ k, a k / β ^ (k + 1)` is algebraic, then `α ∈ ℚ(β)`. -/
theorem mem_adjoin_of_isStammering {β : ℝ} (hβ : 1 < β) (hint : IsIntegral ℤ β)
    (hconj : ∀ z ∈ (minpoly ℚ β).aroots ℂ, z ≠ (β : ℂ) → ‖z‖ ≤ 1) {a : ℕ → ℤ}
    (hbdd : BddAbove (Set.range fun k ↦ |a k|)) (hst : Function.IsStammering a)
    (halg : IsAlgebraic ℚ (∑' k, (a k : ℝ) / β ^ (k + 1))) :
    ∑' k, (a k : ℝ) / β ^ (k + 1) ∈ ℚ⟮β⟯ := by
  set α := ∑' k, (a k : ℝ) / β ^ (k + 1) with hαdef
  have hβ0 : 0 < β := by linarith
  have hintQ : IsIntegral ℚ β := hint.tower_top
  have : FiniteDimensional ℚ ℚ⟮β⟯ := adjoin.finiteDimensional hintQ
  have : NumberField ℚ⟮β⟯ := {}
  set K := ℚ⟮β⟯ with hKdef
  set b : K := AdjoinSimple.gen ℚ β with hbdef
  have hb : algebraMap K ℝ b = β := AdjoinSimple.algebraMap_gen ℚ β
  have hbint : IsIntegral ℤ b :=
    (isIntegral_algHom_iff (algebraMap K ℝ).toIntAlgHom (algebraMap K ℝ).injective).mp
      (by rw [RingHom.toIntAlgHom_apply, hb]; exact hint)
  have hb0 : b ≠ 0 := fun h ↦ hβ0.ne' (by rw [← hb, h, map_zero])
  -- the digits
  obtain ⟨M₀, hM₀⟩ := hbdd
  set M : ℝ := (M₀ : ℝ) with hMdef
  have hM : ∀ k, |(a k : ℝ)| ≤ M := fun k ↦ by
    have h : |a k| ≤ M₀ := hM₀ ⟨k, rfl⟩
    rw [hMdef, ← Int.cast_abs]
    exact_mod_cast h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the repetitions
  obtain ⟨w, hw, hsw⟩ := hst
  obtain ⟨C, hC, r, s, hs, -, hrs, hper⟩ := hsw.exists_periodic (by linarith)
  set ε : ℝ := min 1 ((w - 1) / (4 * (C + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos (by linarith) (by linarith))
  obtain ⟨T, hTp, hTmem⟩ := exists_finset_submodule_of_pow_pow hβ0.ne' hint halg hε
  set n := Fintype.card (InfinitePlace K) with hndef
  set c₁ : ℝ := 1 + 2 * (|α| + M / (β - 1)) with hc₁def
  set c₃ : ℝ := 2 * M / (β - 1) with hc₃def
  have hβ1 : 0 < β - 1 := by linarith
  have hc₁ : 1 ≤ c₁ := by
    have : 0 ≤ M / (β - 1) := div_nonneg hM0 hβ1.le
    linarith [abs_nonneg α]
  have hc₃ : 0 ≤ c₃ := div_nonneg (by linarith) hβ1.le
  have hq : 1 < β ^ ((w - 1) / (2 * (C + 1))) :=
    Real.one_lt_rpow hβ (div_pos (by linarith) (by linarith))
  have hev := eventually_mul_one_add_mul_pow_le (A := c₃ * c₁) (mul_nonneg hc₃ (by linarith))
    (by positivity : (0 : ℝ) ≤ 2 * M) hq (4 * n)
  have htend : Tendsto (fun k ↦ r k + s k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (hs.id_le k).trans (Nat.le_add_left _ _)) tendsto_id
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (htend.eventually hev)
  -- the points
  set y : ℕ → K := fun k ↦ aeval b (digitPoly a (r k + s k)) - aeval b (digitPoly a (r k))
    with hydef
  set Y : ℕ → ℝ := fun k ↦ aeval β (digitPoly a (r k + s k)) - aeval β (digitPoly a (r k))
    with hYdef
  have hY : ∀ k, algebraMap K ℝ (y k) = Y k := fun k ↦ by
    simp only [hydef, hYdef, map_sub, ← aeval_algebraMap_apply, hb]
  have hyint : ∀ k, IsIntegral ℤ (y k) := by
    have hmem : ∀ P : ℤ[X], aeval b P ∈ integralClosure ℤ K := fun P ↦
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hbint) (aeval_mem_adjoin_singleton ℤ b)
    exact fun k ↦ sub_mem (hmem _) (hmem _)
  have hL3 : ∀ k, |α * β ^ (r k + s k) - α * β ^ r k - Y k| ≤ c₃ / β ^ (⌈w * s k⌉₊ - s k) := by
    intro k
    have h := abs_sub_le_of_periodic hβ hM (hper k)
    rw [hc₃def, div_div]
    convert h using 2
    simp only [hYdef, hαdef]
    ring
  -- the other infinite places
  have hmult : ∀ v : InfinitePlace K, v.mult ≤ 2 := fun v ↦ by
    rw [InfinitePlace.mult]
    split_ifs <;> norm_num
  set G : ℕ → ℝ := fun k ↦ 1 + 2 * M * ((r k + s k : ℕ) : ℝ) with hGdef
  have hG1 : ∀ k, 1 ≤ G k := fun k ↦ by
    have : 0 ≤ 2 * M * ((r k + s k : ℕ) : ℝ) := by positivity
    simp only [hGdef]
    linarith
  have hvb : ∀ v ∈ univ.erase (adjoinPlace β), v b ≤ 1 := fun v hv ↦
    apply_gen_le_one hintQ hconj (mem_erase.mp hv).1
  have hvy : ∀ v ∈ univ.erase (adjoinPlace β), ∀ k, v (y k) ≤ G k := by
    intro v hv k
    have hnb : ‖v.embedding b‖ ≤ 1 := by rw [v.norm_embedding_eq]; exact hvb v hv
    have e : ∀ P : ℤ[X], v.embedding (aeval b P) = aeval (v.embedding b) P := fun P ↦
      (aeval_algHom_apply v.embedding.toIntAlgHom b P).symm
    rw [← v.norm_embedding_eq, hydef]
    dsimp only
    rw [map_sub, e, e]
    have h1 := Complex.norm_aeval_digitPoly_le hM hnb (r k + s k)
    have h2 := Complex.norm_aeval_digitPoly_le hM hnb (r k)
    have h3 : M * (r k : ℝ) ≤ M * ((r k + s k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right _ _) hM0
    refine (norm_sub_le _ _).trans ?_
    simp only [hGdef]
    linarith
  have hprodG : ∀ k, ∀ f : InfinitePlace K → ℝ, (∀ v, 0 ≤ f v) →
      (∀ v ∈ univ.erase (adjoinPlace β), f v ≤ G k) →
      ∏ v ∈ univ.erase (adjoinPlace β), f v ^ v.mult ≤ G k ^ (2 * n) := by
    intro k f hf0 hf
    calc ∏ v ∈ univ.erase (adjoinPlace β), f v ^ v.mult
        ≤ ∏ v ∈ univ.erase (adjoinPlace β), G k ^ 2 :=
          prod_le_prod₀ (fun v _ ↦ pow_nonneg (hf0 v) _) fun v hv ↦
            (pow_le_pow_left₀ (hf0 v) (hf v hv) _).trans (pow_le_pow_right₀ (hG1 k) (hmult v))
      _ = G k ^ (2 * (univ.erase (adjoinPlace β)).card) := by rw [prod_const, ← pow_mul,
          mul_comm]
      _ ≤ G k ^ (2 * n) := pow_le_pow_right₀ (hG1 k) (Nat.mul_le_mul_left 2
          ((card_erase_le).trans (by rw [card_univ])))
  -- the sup norms
  set x : ℕ → Fin 3 → K := fun k ↦ ![b ^ (r k + s k), b ^ r k, y k] with hxdef
  have hsupv : ∀ k, ∀ v ∈ univ.erase (adjoinPlace β), (⨆ j, v (x k j)) ≤ G k := by
    intro k v hv
    refine ciSup_le fun j ↦ ?_
    fin_cases j
    · change v (b ^ (r k + s k)) ≤ G k
      rw [map_pow]
      exact (pow_le_one₀ (apply_nonneg v b) (hvb v hv)).trans (hG1 k)
    · change v (b ^ r k) ≤ G k
      rw [map_pow]
      exact (pow_le_one₀ (apply_nonneg v b) (hvb v hv)).trans (hG1 k)
    · exact hvy v hv k
  have hsup0 : ∀ k, (⨆ j, adjoinPlace β (x k j)) ≤ c₁ * β ^ (r k + s k) := by
    intro k
    have hPm := abs_aeval_digitPoly_le hβ hM (r k + s k)
    have hPr := abs_aeval_digitPoly_le hβ hM (r k)
    have hrle : β ^ r k ≤ β ^ (r k + s k) := pow_le_pow_right₀ hβ.le (Nat.le_add_right _ _)
    have hpos : 0 < β ^ (r k + s k) := pow_pos hβ0 _
    have hc : 0 ≤ |α| + M / (β - 1) := add_nonneg (abs_nonneg _) (div_nonneg hM0 hβ1.le)
    have hpr : 0 < β ^ r k := pow_pos hβ0 _
    refine ciSup_le fun j ↦ ?_
    fin_cases j
    · change adjoinPlace β (b ^ (r k + s k)) ≤ _
      rw [adjoinPlace_apply, map_pow, hb, abs_of_pos hpos]
      nlinarith
    · change adjoinPlace β (b ^ r k) ≤ _
      rw [adjoinPlace_apply, map_pow, hb, abs_of_pos hpr]
      nlinarith
    · change adjoinPlace β (y k) ≤ _
      rw [adjoinPlace_apply, hY]
      refine (abs_sub _ _).trans ?_
      nlinarith
  have hprod : ∀ k, ∏ v : InfinitePlace K, (⨆ j, v (x k j)) ^ v.mult
      ≤ c₁ * β ^ (r k + s k) * G k ^ (2 * n) := by
    intro k
    rw [← mul_prod_erase univ _ (mem_univ (adjoinPlace β)), (isReal_adjoinPlace β).mult_eq_one,
      pow_one]
    exact mul_le_mul (hsup0 k) (hprodG k _ (fun v ↦ Real.iSup_nonneg fun j ↦ apply_nonneg v _)
      (hsupv k)) (prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun j ↦ apply_nonneg v _)
      _) (by positivity)
  have hprodpos : ∀ k, 0 < ∏ v : InfinitePlace K, (⨆ j, v (x k j)) ^ v.mult := fun k ↦
    prod_pos fun v _ ↦ pow_pos (lt_of_lt_of_le (v.pos_iff.mpr (pow_ne_zero (r k + s k) hb0))
      (le_ciSup_of_le (Finite.bddAbove_range _) 0 le_rfl)) _
  -- for large `k` the points lie in finitely many subspaces
  have hbig : ∀ k, k₀ ≤ k → ∃ V ∈ T, x k ∈ V := by
    intro k hk
    refine hTmem (r k + s k) (r k) (y k) (hyint k) ?_
    rw [hY]
    have hyv := hprodG k (fun v ↦ v (y k)) (fun v ↦ apply_nonneg v _) (fun v hv ↦ hvy v hv k)
    have hmain := div_pow_mul_pow_le_rpow hβ hw hC hc₁ (hG1 k) (n := n) (hrs k) (by
      have := hk₀ k hk
      simp only [hGdef]
      exact this)
    calc |α * β ^ (r k + s k) - α * β ^ r k - Y k|
          * ∏ v ∈ univ.erase (adjoinPlace β), v (y k) ^ v.mult
        ≤ c₃ / β ^ (⌈w * s k⌉₊ - s k) * G k ^ (2 * n) :=
          mul_le_mul (hL3 k) hyv (prod_nonneg fun v _ ↦ pow_nonneg (apply_nonneg v _) _)
            (div_nonneg hc₃ (pow_nonneg hβ0.le _))
      _ ≤ (c₁ * β ^ (r k + s k) * G k ^ (2 * n)) ^ (-ε) := hmain
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (hprodpos k) (hprod k) (by linarith)
  -- one subspace contains infinitely many of them
  have hmem : ∀ k, ∃ V ∈ T, x (k + k₀) ∈ V := fun k ↦ hbig _ (Nat.le_add_left _ _)
  choose V hVT hxV using hmem
  obtain ⟨⟨V₀, hV₀⟩, hinf⟩ := Finite.exists_infinite_fiber (fun k ↦ (⟨V k, hVT k⟩ : T))
  set S : Set ℕ := (fun k ↦ (⟨V k, hVT k⟩ : T)) ⁻¹' {⟨V₀, hV₀⟩} with hSdef
  have hS : S.Infinite := Set.infinite_coe_iff.mp hinf
  have hSV : ∀ k ∈ S, x (k + k₀) ∈ V₀ := fun k hk ↦ by
    have h : V k = V₀ := congrArg Subtype.val (Set.mem_singleton_iff.mp hk)
    rw [← h]
    exact hxV k
  obtain ⟨q, hq⟩ := mem_range_algebraMap_of_forall_mem (K := K) (c := c₃) hβ
    (r := fun k ↦ r (k + k₀)) (s := fun k ↦ s (k + k₀)) (fun i j hij ↦ hs (by omega))
    (x := fun k ↦ x (k + k₀)) (Y := fun k ↦ Y (k + k₀))
    (fun k ↦ by rw [show x (k + k₀) 0 = b ^ (r (k + k₀) + s (k + k₀)) from rfl, map_pow, hb])
    (fun k ↦ by rw [show x (k + k₀) 1 = b ^ r (k + k₀) from rfl, map_pow, hb]) (fun k ↦ hY _) hS
    (fun k _ ↦ (hL3 _).trans (div_le_self hc₃ (one_le_pow₀ hβ.le))) (hTp V₀ hV₀) hSV
  rw [← hq]
  exact q.2

/-- **Theorem 5 (Adamczewski–Bugeaud 2007) for a Pisot base**, as printed: for a bounded stammering
sequence of integers `a`, the number `∑ k, a k / β ^ (k + 1)` either lies in `ℚ(β)` or is
transcendental. -/
theorem mem_adjoin_or_transcendental_of_isPisot {β : ℝ} (hβ : IsPisot β) {a : ℕ → ℤ}
    (hbdd : BddAbove (Set.range fun k ↦ |a k|)) (hst : Function.IsStammering a) :
    ∑' k, (a k : ℝ) / β ^ (k + 1) ∈ ℚ⟮β⟯ ∨
      Transcendental ℚ (∑' k, (a k : ℝ) / β ^ (k + 1)) :=
  or_iff_not_imp_right.mpr fun h ↦
    mem_adjoin_of_isStammering hβ.1 hβ.2.1 hβ.norm_le_one hbdd hst (not_not.mp h)

/-- **Theorem 5 (Adamczewski–Bugeaud 2007) for a Salem base**, as printed. -/
theorem mem_adjoin_or_transcendental_of_isSalem {β : ℝ} (hβ : IsSalem β) {a : ℕ → ℤ}
    (hbdd : BddAbove (Set.range fun k ↦ |a k|)) (hst : Function.IsStammering a) :
    ∑' k, (a k : ℝ) / β ^ (k + 1) ∈ ℚ⟮β⟯ ∨
      Transcendental ℚ (∑' k, (a k : ℝ) / β ^ (k + 1)) :=
  or_iff_not_imp_right.mpr fun h ↦
    mem_adjoin_of_isStammering hβ.1 hβ.2.1 hβ.2.2.1 hbdd hst (not_not.mp h)

/-- The digit polynomials take their values at `β` in `ℚ(β)`. -/
theorem aeval_digitPoly_mem_adjoin (β : ℝ) (a : ℕ → ℤ) (n : ℕ) :
    aeval β (digitPoly a n) ∈ ℚ⟮β⟯ := by
  have h : aeval β (digitPoly a n)
      = algebraMap ℚ⟮β⟯ ℝ (aeval (AdjoinSimple.gen ℚ β) (digitPoly a n)) := by
    rw [← aeval_algebraMap_apply, AdjoinSimple.algebraMap_gen]
  rw [h]
  exact SetLike.coe_mem _

/-- **An eventually periodic expansion has its value in `ℚ(β)`**, for any real `β > 1` and
bounded integer digits: with period `p` from position `N` on, the tails after `N` and `N + p`
agree, and Lemma 1 solves for the value. -/
theorem tsum_mem_adjoin_of_isEventuallyPeriodic {β : ℝ} (hβ : 1 < β) {a : ℕ → ℤ}
    (hbdd : BddAbove (Set.range fun k ↦ |a k|)) (hper : Function.IsEventuallyPeriodic a) :
    ∑' k, (a k : ℝ) / β ^ (k + 1) ∈ ℚ⟮β⟯ := by
  obtain ⟨N, p, hp, hN⟩ := hper
  obtain ⟨M₀, hM₀⟩ := hbdd
  have hM : ∀ k, |(a k : ℝ)| ≤ M₀ := fun k ↦ by
    have h : |a k| ≤ M₀ := hM₀ ⟨k, rfl⟩
    rw [← Int.cast_abs]
    exact_mod_cast h
  have e1 := pow_mul_tsum_sub_aeval_digitPoly hβ hM N
  have e2 := pow_mul_tsum_sub_aeval_digitPoly hβ hM (N + p)
  have htail : ∑' j, (a (j + (N + p)) : ℝ) / β ^ (j + 1)
      = ∑' j, (a (j + N) : ℝ) / β ^ (j + 1) :=
    tsum_congr fun j ↦ by rw [show j + (N + p) = j + N + p by ring, hN _ (by omega)]
  have hden : β ^ (N + p) - β ^ N ≠ 0 :=
    (sub_pos.mpr (pow_lt_pow_right₀ hβ (by omega))).ne'
  have hα : ∑' k, (a k : ℝ) / β ^ (k + 1)
      = (aeval β (digitPoly a (N + p)) - aeval β (digitPoly a N)) / (β ^ (N + p) - β ^ N) := by
    rw [eq_div_iff hden]
    linear_combination e2 - e1 + htail
  rw [hα]
  have hβK : β ∈ ℚ⟮β⟯ := mem_adjoin_simple_self ℚ β
  exact div_mem (sub_mem (aeval_digitPoly_mem_adjoin β a _) (aeval_digitPoly_mem_adjoin β a _))
    (sub_mem (pow_mem hβK _) (pow_mem hβK _))

end Real
