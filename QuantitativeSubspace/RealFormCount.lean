/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSystemCount
public import DiophantineApproximation.LinearFormSubspaces

-- Used only inside proofs.
import ArithmeticHeights.Extension
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.RationalPlaces
import QuantitativeSubspace.Numerics
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic

/-!
# The quantitative Subspace Theorem for real forms at `∞` and at finitely many primes

The applications of the quantitative Subspace Theorem to the digits and the continued fraction
of a real algebraic number `α` all use systems of one shape: at `∞`, `n` linear forms whose
coefficients are `b₀ + b₁ α + b₂ α²` with integers `bᵢ`; at each prime `l` of a finite set `S`,
the coordinates; and integer points. This file states what such an application uses
(`Real.SubspaceBoundAt α S a`: the solutions lie in at most `K δ^{-a} (1 + log δ⁻¹)²` proper
subspaces, above a threshold linear in `δ⁻¹` and in the logarithms of the data) and
proves it with `a = 3` from the Evertse–Ferretti count
(`NumberField.exists_finset_submodule_of_efSystemThreshold_le`, `NumberField.efLargeCount_le_ef`),
with an explicit `K` (`Real.SubspaceBoundWith`, `Real.subspaceConst`).

The case `S = ∅` is what Bugeaud 2013, (6.1), uses (`Bugeaud2013/Additions/`); the case `n = 3`,
`S` the primes of the base `b`, with the forms `X₀`, `X₁`, `α X₀ - α X₁ - X₂` at `∞`, is the
quantitative form of `Real.exists_finset_submodule_of_repetition` (DA 7.4) that Bugeaud–Evertse
2008, Theorem 2.1, uses (`BugeaudEvertse2008/README.md`, BE.0). EF13's count holds for every
`n ≥ 2`, so the case `n = 2` (BE08's planes) needs no separate two-variable count.

## Main definitions

* `Real.quadVal α b`: `b₀ + b₁ α + b₂ α²`.
* `Real.SubspaceBoundWith α S a n K`: the quantitative Subspace Theorem for such forms in `n`
  variables, at `∞` and the primes of `S`, with `K δ^{-a} (1 + log δ⁻¹)²` subspaces above the
  threshold `K δ⁻¹ (1 + log B + log C + log γ⁻¹)`.
* `Real.SubspaceBoundAt α S a`: `Real.SubspaceBoundWith α S a n K` for `2 ≤ n ≤ 4` and some `K`.
* `Real.efCountConst n M`, `Real.thrConst n d s μ`, `Real.subspaceConst n d s h μ`: EF13's
  constant at `M` conjugated forms, the threshold constant, and the larger of the two, in `n`, the
  degree `d` of the field of the forms, the height `h = log H(α)` in it, the number `s` of primes
  and `μ = log 2 + ∑_{l ∈ S} log l`.

## Main results

* `Real.subspaceBoundWith_three_of_mem`: **Evertse–Ferretti 2013, with an explicit constant**:
  `Real.SubspaceBoundWith α S 3 n (Real.subspaceConst n d #S h μ)` for `2 ≤ n ≤ 4` and every Galois
  field `E ⊆ ℂ` of degree `d` containing `α`.
* `Real.subspaceBoundAt_three`: `Real.SubspaceBoundAt α S 3` for every real algebraic `α` and every
  finite set of primes `S`.
* `Real.subspaceBoundWith_three_ratCast`, `Real.subspaceBoundWith_three_zero`: the case
  `α ∈ ℚ`, with `d = 1` and `h = log H(α)`.
* `Real.SubspaceBoundWith.mono_const`, `Real.SubspaceBoundWith.mono`,
  `Real.SubspaceBoundAt.mono`: a larger constant or exponent is weaker.
* `Real.exists_normalized_places_of_mem`: the normalized system of the forms over `E`, and every
  solution above the threshold is a solution of it above its threshold; shared with the interval
  form of `QuantitativeSubspace/RealFormInterval.lean`. `Real.normalized_placeForms_of_mem` is
  the same with the forms, constants and exponents of the system written out, for a given `k`.

## Implementation notes

⚠ **The forms at `∞` are normalized here, not by the caller.** The count is for systems under
Evertse's normalization (2.4): one constant per place, at `∞` at most `|det|^{1/n}`, and at every
place an exponent equal to the normalized local degree (`1` at `∞`, `0` at a prime). The caller
gives any constant `C ≥ 1` at `∞` and a lower bound `γ` for `|det|`; the forms whose exponent is
within `τ = δ / 2n` of `1` keep their exponent, the others are multiplied by a power of `2` and
their exponent is raised by `τ`. That costs half of `δ` and a threshold linear in `log C` and
`log γ⁻¹`, and it needs one exponent at `∞` that is not within `τ` of `1`: the caller gives one
`≤ 1 - τ` (for instance one `≤ 0`, `Real.exists_le_one_sub_div_of_exists_nonpos`). At the
primes nothing is rescaled; the constant is `1`, the forms are the coordinates (determinant `1`),
and the caller's exponents must already be `≤ 0` with one `= 0`.

⚠ **The absolute values of the number field above the primes are chosen once**
(`NumberField.exists_liesOver_finitePlace`), and only their values on `ℚ` are ever used, because
the forms at the primes are the coordinates (as in DA 7.4).

This is an application of Layer Q4.3 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Module Finset Height NumberField IsDedekindDomain Polynomial

namespace Real

/-- `b₀ + b₁ α + b₂ α²`. -/
noncomputable def quadVal (α : ℝ) (b : Fin 3 → ℤ) : ℝ := b 0 + b 1 * α + b 2 * α ^ 2

/-- **A Galois number field containing `α`**, inside `ℂ`: the splitting field of the minimal
polynomial. -/
theorem exists_isGalois_mem {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ∃ E : IntermediateField ℚ ℂ, IsGalois ℚ E ∧ FiniteDimensional ℚ E ∧ (α : ℂ) ∈ E := by
  have hint : IsIntegral ℚ (α : ℂ) := (hα.algebraMap (A := ℂ)).isIntegral
  set f := minpoly ℚ (α : ℂ)
  have hsplit : IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet ℂ)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    IsSplittingField.finiteDimensional _ f
  refine ⟨IntermediateField.adjoin ℚ (f.rootSet ℂ), ?_, hfd, ?_⟩
  · exact isGalois_iff.2 ⟨inferInstance, Normal.of_isSplittingField f⟩
  · exact IntermediateField.subset_adjoin _ _
      ((mem_rootSet).2 ⟨minpoly.ne_zero hint, minpoly.aeval ℚ _⟩)

end Real

namespace Height

/-- **The affine height of an integer point** is its sup norm. -/
theorem mulHeightAff_intCast {ι : Type*} [Finite ι] {x : ι → ℤ} (hx : x ≠ 0) :
    mulHeightAff (fun i ↦ (x i : ℚ)) = ⨆ i, |(x i : ℝ)| := by
  have := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have h1 : (1 : ℝ) ≤ ⨆ i, |(x i : ℝ)| := by
    refine le_trans ?_ (Finite.le_ciSup_of_le i₀ le_rfl)
    have : (1 : ℤ) ≤ |x i₀| := Int.one_le_abs hi₀
    exact_mod_cast this
  refine le_antisymm ?_ (ciSup_le fun i ↦ ?_)
  · -- the tuple `(1, x)` is an integer tuple
    set y : Option ι → ℤ := fun o ↦ o.elim 1 x
    have hy : (fun o ↦ (y o : ℚ)) ≠ 0 := fun h ↦ by simpa [y] using congrFun h none
    have h := Rat.mulHeight_intCast_le_iSup Rat.infinitePlace hy
    have heq : (fun o : Option ι ↦ ((y o : ℤ) : ℚ)) = fun o : Option ι ↦ o.elim 1
        fun i ↦ (x i : ℚ) := by
      funext o; cases o <;> simp [y]
    rw [heq] at h
    refine h.trans (ciSup_le fun o ↦ ?_)
    cases o with
    | none => simpa [y] using h1
    | some i =>
      simp only [y, Option.elim_some, Rat.infinitePlace_apply, Rat.cast_abs, Rat.cast_intCast]
      exact Finite.le_ciSup_of_le i le_rfl
  · have h := mulHeight₁_le_mulHeightAff (fun i ↦ (x i : ℚ)) i
    rw [Rat.mulHeight₁_eq_max] at h
    refine le_trans ?_ h
    have : |(x i : ℝ)| = ((x i).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    exact_mod_cast le_max_left (((x i : ℚ)).num.natAbs) ((x i : ℚ)).den |>.trans' (by simp)

end Height

namespace NumberField

open Height

/-- **The absolute height is at most the relative one.** -/
theorem absMulHeight₁_le_mulHeight₁ {E : Type*} [Field E] [NumberField E] (y : E) :
    absMulHeight₁ y ≤ mulHeight₁ y := by
  have hd : 0 < finrank ℚ E := finrank_pos
  have h := absMulHeight₁_pow_finrank y
  have h0 : 0 ≤ absMulHeight₁ y := by
    rw [absMulHeight₁_eq]; exact Real.rpow_nonneg (mulHeight₁_nonneg y) _
  have h1 : 1 ≤ absMulHeight₁ y := by
    by_contra hlt
    push Not at hlt
    have : absMulHeight₁ y ^ finrank ℚ E < 1 := pow_lt_one₀ h0 hlt hd.ne'
    rw [h] at this
    exact absurd (one_le_mulHeight₁ y) (not_le.mpr this)
  rw [← h]
  exact le_self_pow₀ h1 hd.ne'

/-- **The height of `c₀ + c₁ β + c₂ β²`** for integers `|cᵢ| ≤ B` in a number field `E`. -/
theorem absMulHeight₁_sum_le {E : Type*} [Field E] [NumberField E] (β : E) (c : Fin 3 → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hc : ∀ m, |(c m : ℝ)| ≤ B) :
    absMulHeight₁ (∑ m : Fin 3, (c m : E) * β ^ (m : ℕ)) ≤
      3 ^ finrank ℚ E * B ^ (3 * finrank ℚ E) * mulHeight₁ β ^ 3 := by
  set d := finrank ℚ E
  set y := ∑ m : Fin 3, (c m : E) * β ^ (m : ℕ)
  refine (absMulHeight₁_le_mulHeight₁ y).trans ?_
  -- the integer coefficients
  have hint (m : Fin 3) : mulHeight₁ (c m : E) ≤ B ^ d := by
    have h := mulHeight₁_pow_finrank (K := ℚ) (L := E) ((c m : ℤ) : ℚ)
    rw [map_intCast] at h
    rw [← h, Rat.mulHeight₁_eq_max]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ d
    rw [Nat.cast_max]
    refine max_le ?_ ?_
    · have : (((c m : ℚ)).num.natAbs : ℝ) = |(c m : ℝ)| := by
        rw [Rat.num_intCast, Nat.cast_natAbs, Int.cast_abs]
      rw [this]; exact hc m
    · rw [Rat.den_intCast]; simpa using hB
  have hterm (m : Fin 3) :
      mulHeight₁ ((c m : E) * β ^ (m : ℕ)) ≤ B ^ d * mulHeight₁ β ^ (m : ℕ) := by
    calc _ ≤ mulHeight₁ (c m : E) * mulHeight₁ (β ^ (m : ℕ)) := mulHeight₁_mul_le _ _
      _ = mulHeight₁ (c m : E) * mulHeight₁ β ^ (m : ℕ) := by rw [mulHeight₁_pow]
      _ ≤ B ^ d * mulHeight₁ β ^ (m : ℕ) :=
          mul_le_mul_of_nonneg_right (hint m) (pow_nonneg (mulHeight₁_nonneg β) _)
  have hsum := mulHeight₁_sum_le (K := E) (s := (univ : Finset (Fin 3))) univ_nonempty
    (fun m ↦ (c m : E) * β ^ (m : ℕ))
  rw [totalWeight_eq_finrank, card_univ, Fintype.card_fin] at hsum
  calc mulHeight₁ y ≤ (3 : ℝ) ^ d * ∏ m : Fin 3, mulHeight₁ ((c m : E) * β ^ (m : ℕ)) := by
        exact_mod_cast hsum
    _ ≤ 3 ^ d * ∏ m : Fin 3, (B ^ d * mulHeight₁ β ^ (m : ℕ)) :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun m _ ↦ mulHeight₁_nonneg _)
          fun m _ ↦ hterm m) (by positivity)
    _ = 3 ^ d * B ^ (3 * d) * mulHeight₁ β ^ 3 := by
        simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
        ring

/-- **The threshold of Q4.2, in closed form**, for `K = ℚ`, `[E : ℚ] = d` and `s` forms over `E`.
-/
theorem domainThreshold_le_div {n d s c : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) (hd : 1 ≤ d) {δ L : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 ≤ L) :
    domainThreshold n d s (efEps d δ) (efSpread d n δ) (c * n ^ 2 * (d * L)) ≤
      ((1 + 10 * ((s + n).choose n : ℝ)) * (23 + 64 * c * L) + 60) / δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  rw [domainThreshold, domainDelta_efEps (by omega) (by omega) hδ, efSystemDelta, efSpread]
  set ch : ℝ := ((s + n).choose n : ℝ)
  have hch : 0 ≤ ch := Nat.cast_nonneg _
  -- `n! ≤ 24` and `n ≤ 4`
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfact : Real.log (n.factorial : ℝ) ≤ 23 := by
    have h24 : (n.factorial : ℝ) ≤ 24 := by
      have : n.factorial ≤ 24 := by interval_cases n <;> decide
      exact_mod_cast this
    linarith [Real.log_le_sub_one_of_pos hfpos]
  have hfact0 : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hlogn : Real.log n ≤ 3 := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- the leading factor is at most `1`
  have key : (d : ℝ) / (2 * (d * (1 + δ / n) / 2)) = 1 / (1 + δ / n) := by
    field_simp
  rw [key]
  have hA0 : 0 < 1 / (1 + δ / n) := by positivity
  have hA1 : 1 / (1 + δ / n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 0 ≤ δ / n := by positivity
    linarith
  set G := Real.log (n.factorial : ℝ) + n * (c * n ^ 2 * (d * L)) / d
  have hGeq : G = Real.log (n.factorial : ℝ) + n ^ 3 * c * L := by
    simp only [G]
    field_simp
  have hG0 : 0 ≤ G := by rw [hGeq]; positivity
  have hGle : G ≤ 23 + 64 * c * L := by
    rw [hGeq]
    have : (n : ℝ) ^ 3 ≤ 64 := by
      calc (n : ℝ) ^ 3 ≤ 4 ^ 3 := by gcongr
        _ = 64 := by norm_num
    have : (n : ℝ) ^ 3 * c * L ≤ 64 * c * L := by gcongr
    linarith
  have t2 : Real.log n / (δ / (4 * (n + δ))) ≤ 60 / δ := by
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hδ]
    nlinarith
  have t3 : ch * G / (n * (δ / (4 * (n + δ)))) ≤ 10 * ch * G / δ := by
    have hq : 0 < n * (δ / (4 * (n + δ))) := by positivity
    have h : δ ≤ 10 * (n * (δ / (4 * (n + δ)))) := by
      rw [show 10 * (n * (δ / (4 * (n + δ)))) = 10 * n * δ / (4 * (n + δ)) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    rw [div_le_div_iff₀ hq hδ]
    calc ch * G * δ ≤ ch * G * (10 * (n * (δ / (4 * (n + δ))))) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hch hG0)
      _ = 10 * ch * G * (n * (δ / (4 * (n + δ)))) := by ring
  have hGδ : G ≤ G / δ := le_div_self hG0 hδ hδ1
  calc 1 / (1 + δ / n) * (G + Real.log n / (δ / (4 * (n + δ))) +
        ch * G / (n * (δ / (4 * (n + δ)))))
      ≤ 1 * (G / δ + 60 / δ + 10 * ch * G / δ) := by
        gcongr
    _ = ((1 + 10 * ch) * G + 60) / δ := by ring
    _ ≤ ((1 + 10 * ch) * (23 + 64 * c * L) + 60) / δ := by
        gcongr

/-- **A finite place of `ℚ` is not the infinite one**: it is at most `1` at `2`. -/
theorem FinitePlace.val_ne_infinitePlace (v : FinitePlace ℚ) : v.1 ≠ Rat.infinitePlace.1 := by
  intro h
  have h1 : v ((2 : ℤ) : ℚ) ≤ 1 := v.apply_intCast_le_one 2
  have h2 : Rat.infinitePlace ((2 : ℤ) : ℚ) = 2 := by
    rw [Rat.infinitePlace_apply]; norm_num
  have : v ((2 : ℤ) : ℚ) = Rat.infinitePlace ((2 : ℤ) : ℚ) := by
    change v.1 _ = Rat.infinitePlace.1 _
    rw [h]
  linarith

end NumberField

namespace Real

open NumberField

/-- **The quantitative Subspace Theorem for forms in `1, α, α²` at `∞` and the primes of `S`, in
`n` variables, with `δ^{-a}` subspaces and the constant `K`.** For forms
`∑_k quadVal α (P i k) X_k` at `∞` with integer data `|P i k m| ≤ B` and determinant at least `γ`
in absolute value, a constant `C ≥ 1`, exponents `e i ≤ 1` at `∞`, one of them `1` and one of them
`≤ 1 - δ / 2n`, and exponents `f l i ≤ 0` at the primes `l ∈ S`, one of them `0` at each `l`, of
total sum at most `-δ`, the nonzero integer points `x` with
`|∑_k quadVal α (P i k) x_k| ≤ C |x|^{e i}` and `|x i|_l ≤ |x|^{f l i}` for all `i` and `l ∈ S`,
and `log |x| ≥ K δ⁻¹ (1 + log B + log C + log γ⁻¹)`, lie in at most `K δ^{-a} (1 + log δ⁻¹)²`
proper subspaces of `ℚⁿ`. -/
def SubspaceBoundWith (α : ℝ) (S : Finset Nat.Primes) (a : ℝ) (n : ℕ) (K : ℝ) : Prop :=
  ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (f : Nat.Primes → Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      (∀ i, e i ≤ 1) → (∃ i, e i = 1) → (∃ i, e i ≤ 1 - δ / (2 * n)) →
      (∀ l ∈ S, ∀ i, f l i ≤ 0) → (∀ l ∈ S, ∃ i, f l i = 0) →
      ∑ i, e i + ∑ l ∈ S, ∑ i, f l i ≤ -δ →
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), (#T : ℝ) ≤ K * δ⁻¹ ^ a * (1 + log δ⁻¹) ^ 2 ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        (∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤ (⨆ k, |(x k : ℝ)|) ^ f l i) →
        K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        ∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U

/-- **The quantitative Subspace Theorem for forms in `1, α, α²` at `∞` and the primes of `S`, with
`δ^{-a}` subspaces**: `Real.SubspaceBoundWith α S a n K` for `2 ≤ n ≤ 4` and some `K > 0`, which
depends on `α`, `S` and `n` only. -/
def SubspaceBoundAt (α : ℝ) (S : Finset Nat.Primes) (a : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 0 < K ∧ SubspaceBoundWith α S a n K

/-- A larger constant is a weaker statement. -/
theorem SubspaceBoundWith.mono_const {α a K K' : ℝ} {S : Finset Nat.Primes} {n : ℕ}
    (h : SubspaceBoundWith α S a n K) (hKK : K ≤ K') : SubspaceBoundWith α S a n K' := by
  intro P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  obtain ⟨T, hcard, hT, hmem⟩ := h P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  refine ⟨T, hcard.trans ?_, hT, fun x hx hsol hfin hlarge ↦ hmem x hx hsol hfin ?_⟩
  · have : 0 ≤ δ⁻¹ ^ a := Real.rpow_nonneg (inv_nonneg.2 hδ.le) a
    gcongr
  · have hΞ : 0 ≤ δ⁻¹ * (1 + log B + log C + log γ⁻¹) := by
      have := Real.log_nonneg hB
      have := Real.log_nonneg hC
      have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
      have : 0 < δ⁻¹ := inv_pos.2 hδ
      positivity
    refine le_trans ?_ hlarge
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hKK hΞ

/-- A larger exponent is a weaker statement. -/
theorem SubspaceBoundWith.mono {α a b K : ℝ} {S : Finset Nat.Primes} {n : ℕ}
    (h : SubspaceBoundWith α S a n K) (hK : 0 ≤ K) (hab : a ≤ b) : SubspaceBoundWith α S b n K := by
  intro P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  obtain ⟨T, hcard, hT, hmem⟩ := h P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  refine ⟨T, hcard.trans ?_, hT, hmem⟩
  have h1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have := Real.rpow_le_rpow_of_exponent_le h1 hab
  gcongr

/-- A larger exponent is a weaker statement. -/
theorem SubspaceBoundAt.mono {α a b : ℝ} {S : Finset Nat.Primes} (h : SubspaceBoundAt α S a)
    (hab : a ≤ b) : SubspaceBoundAt α S b := by
  intro n hn2 hn4
  obtain ⟨K, hK, hT⟩ := h n hn2 hn4
  exact ⟨K, hK, hT.mono hK.le hab⟩

/-- **EF13's constant** for `n` variables and `M` conjugated forms:
`8 · 2 · 10¹³ · 4ⁿ n¹⁴ (log 6M + 1) (log (2 log 3M) + 1)`. -/
noncomputable def efCountConst (n M : ℕ) : ℝ :=
  2 * 10 ^ 13 * 4 ^ n * (n : ℝ) ^ 14 * 8 * (Real.log (6 * M) + 1) *
    (Real.log (2 * Real.log (3 * M)) + 1)

theorem efCountConst_pos {n M : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ M) : 0 < efCountConst n M := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hl1 : 0 ≤ Real.log (6 * M) := Real.log_nonneg (by linarith)
  have hl3 : 1 ≤ Real.log (3 * M) := hlog3.trans (Real.log_le_log (by norm_num) (by linarith))
  have hl2 : 0 ≤ Real.log (2 * Real.log (3 * M)) := Real.log_nonneg (by linarith)
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold efCountConst
  positivity

/-- **EF13's count in closed form**, at `r` forms and `δ / 2`. -/
theorem efLargeCount_half_le {n d r : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hr : 1 ≤ r) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    efLargeCount n d r (δ / 2) ≤ efCountConst n (r * d) * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2 := by
  set m : ℝ := ((r * d : ℕ) : ℝ)
  have hm : 1 ≤ m := by
    have : 1 ≤ r * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    simp only [m]
    exact_mod_cast this
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hl1 : 0 ≤ Real.log (6 * m) := Real.log_nonneg (by linarith)
  have hl3 : 1 ≤ Real.log (3 * m) :=
    hlog3.trans (Real.log_le_log (by norm_num) (by linarith))
  have hl2 : 0 ≤ Real.log (2 * Real.log (3 * m)) := Real.log_nonneg (by linarith)
  set c0 : ℝ := 2 * 10 ^ 13 * 4 ^ n * (n : ℝ) ^ 14
  have hδ2 : 0 < δ / 2 := by positivity
  have h := efLargeCount_le_ef (n := n) (e := d) (r := r) hn hd hr hδ2 (by linarith)
  have hinv : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).2 hδ1)
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  -- the two logarithms
  have e1 : Real.log (3 * m / (δ / 2)) = Real.log (6 * m) + Real.log δ⁻¹ := by
    rw [← Real.log_mul (by positivity) hδi.ne']
    congr 1
    field_simp
    ring
  have e2 : Real.log (Real.log (3 * m) / (δ / 2)) =
      Real.log (2 * Real.log (3 * m)) + Real.log δ⁻¹ := by
    rw [← Real.log_mul (by positivity) hδi.ne']
    congr 1
    field_simp
  have f1 : Real.log (3 * m / (δ / 2)) ≤ (Real.log (6 * m) + 1) * (1 + Real.log δ⁻¹) := by
    rw [e1]; nlinarith
  have f2 : Real.log (Real.log (3 * m) / (δ / 2)) ≤
      (Real.log (2 * Real.log (3 * m)) + 1) * (1 + Real.log δ⁻¹) := by
    rw [e2]; nlinarith
  have f10 : 0 ≤ Real.log (3 * m / (δ / 2)) := by rw [e1]; positivity
  have hcube : c0 / (δ / 2) ^ 3 = c0 * 8 * δ⁻¹ ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    ring
  calc efLargeCount n d r (δ / 2)
      ≤ c0 / (δ / 2) ^ 3 * Real.log (3 * m / (δ / 2)) *
          Real.log (Real.log (3 * m) / (δ / 2)) := by
        simpa [m, c0] using h
    _ ≤ c0 / (δ / 2) ^ 3 * ((Real.log (6 * m) + 1) * (1 + Real.log δ⁻¹)) *
          ((Real.log (2 * Real.log (3 * m)) + 1) * (1 + Real.log δ⁻¹)) := by
        gcongr
        rw [e2]; positivity
    _ = c0 * 8 * (Real.log (6 * m) + 1) * (Real.log (2 * Real.log (3 * m)) + 1) *
          δ⁻¹ ^ (3 : ℝ) * (1 + Real.log δ⁻¹) ^ 2 := by
        rw [hcube]; ring

/-- The forms `y ↦ ∑ k, M i k y k` make up the linear map of the matrix `M`. -/
theorem pi_sumForm_eq_toLin' {F : Type*} [Field F] {n : ℕ} (M : Fin n → Fin n → F) :
    LinearMap.pi (fun i ↦ Module.Dual.sumForm (M i)) = Matrix.toLin' (Matrix.of M) := by
  ext y i
  simp [Module.Dual.sumForm_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem mult_placeQ (v : InfinitePlace ℚ) : v.mult = 1 := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace

section Forms

variable {E : Type} [Field E] (σ : E →+* ℂ)

/-- The absolute value of `E` through the embedding `σ`. -/
noncomputable def absC : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ).comp σ.injective

theorem absC_apply (z : E) : absC σ z = ‖σ z‖ := rfl

theorem absC_liesOver [CharZero E] : (absC σ).LiesOver Rat.infinitePlace.1 := by
  refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
  rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, absC_apply, eq_ratCast, map_ratCast,
    ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
  simp

variable {n : ℕ} (β : E) (lam : Fin n → ℕ) (P : Fin n → Fin n → Fin 3 → ℤ)

/-- **The scaled rows** `lam i · (P i j 0 + P i j 1 β + P i j 2 β²)` over `E`. -/
noncomputable def qRow (i j : Fin n) : E :=
  ∑ m : Fin 3, (((lam i : ℤ) * P i j m : ℤ) : E) * β ^ (m : ℕ)

/-- **The scaled forms**, the same at every place. -/
noncomputable def qForms : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E) :=
  fun _ i ↦ Module.Dual.sumForm (qRow β lam P i)

variable {σ β} {α : ℝ} (hβ : σ β = α)
include hβ

theorem σ_qRow (i j : Fin n) :
    σ (qRow β lam P i j) = (((lam i : ℝ) * quadVal α (P i j) : ℝ) : ℂ) := by
  rw [qRow]
  simp only [map_sum, map_mul, map_pow, map_intCast, hβ]
  simp only [Fin.sum_univ_three, quadVal, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one]
  push_cast
  ring

/-- **The value of a scaled form at `∞`**, at an integer point. -/
theorem absC_sumForm_qRow [CharZero E] (i : Fin n) (x : Fin n → ℤ) :
    absC σ (Module.Dual.sumForm (qRow β lam P i) fun k ↦ algebraMap ℚ E (x k : ℚ)) =
      lam i * |∑ k, quadVal α (P i k) * x k| := by
  rw [absC_apply, Module.Dual.sumForm_apply, map_sum]
  have : ∑ k, σ (qRow β lam P i k * algebraMap ℚ E (x k : ℚ)) =
      (((lam i : ℝ) * ∑ k, quadVal α (P i k) * x k : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, σ_qRow lam P hβ, eq_ratCast, map_ratCast]
    push_cast
    ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast]

/-- **The determinant of the scaled forms at `∞`.** -/
theorem absC_det_qForms :
    absC σ (LinearMap.det (LinearMap.pi fun i ↦ Module.Dual.sumForm (qRow β lam P i))) =
      |(Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)).det| := by
  rw [pi_sumForm_eq_toLin', LinearMap.det_toLin', absC_apply, RingHom.map_det]
  have : σ.mapMatrix (Matrix.of (qRow β lam P)) =
      Complex.ofRealHom.mapMatrix (Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)) := by
    ext i j
    simp [σ_qRow lam P hβ]
  rw [this, ← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]

end Forms

/-- **The scaling.** For `C ≥ 1 ≥ γ > 0` there is `k` with `C ^ n / γ ≤ 2 ^ k` and
`k log 2 ≤ 1 + n log C + log γ⁻¹`. -/
theorem exists_two_pow {C γ : ℝ} (hC : 1 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℕ) :
    ∃ k : ℕ, C ^ n / γ ≤ 2 ^ k ∧
      (k : ℝ) * Real.log 2 ≤ 1 + n * Real.log C + Real.log γ⁻¹ := by
  have hCn : 1 ≤ C ^ n / γ := by
    rw [le_div_iff₀ hγ]; nlinarith [one_le_pow₀ (n := n) hC]
  refine ⟨⌈Real.logb 2 (C ^ n / γ)⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil (Real.logb 2 (C ^ n / γ))
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)] at h
    simpa [Real.rpow_natCast] using h
  · have hlogb0 : 0 ≤ Real.logb 2 (C ^ n / γ) := Real.logb_nonneg (by norm_num) hCn
    have h := Nat.ceil_lt_add_one hlogb0
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.logb 2 (C ^ n / γ) * Real.log 2 = n * Real.log C + Real.log γ⁻¹ := by
      rw [Real.logb, div_mul_cancel₀ _ hl2.ne', Real.log_div (by positivity) hγ.ne',
        Real.log_pow, Real.log_inv]
      ring
    have hl21 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    nlinarith

/-! ### The normalization at `∞` -/

/-- **The scaling factors**: `1` on the forms whose exponent is within `δ / 2n` of `1`, `2 ^ k` on
the others. -/
noncomputable def normLam {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (k : ℕ) (i : Fin n) : ℕ :=
  if 1 - δ / (2 * n) < e i then 1 else 2 ^ k

/-- **The raised exponents**: `e i` on the forms within `δ / 2n` of `1`, `e i + δ / 2n` on the
others. -/
noncomputable def normExp {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (i : Fin n) : ℝ :=
  if 1 - δ / (2 * n) < e i then e i else e i + δ / (2 * n)

theorem normLam_pos {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (k : ℕ) (i : Fin n) :
    0 < normLam e δ k i := by
  unfold normLam
  split_ifs <;> positivity

theorem normLam_le {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (k : ℕ) (i : Fin n) :
    (normLam e δ k i : ℝ) ≤ 2 ^ k := by
  unfold normLam
  split_ifs
  · exact_mod_cast Nat.one_le_two_pow
  · push_cast; exact le_rfl

theorem normExp_le {n : ℕ} (e : Fin n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin n) :
    normExp e δ i ≤ e i + δ / (2 * n) := by
  have : 0 ≤ δ / (2 * n) := by positivity
  unfold normExp
  split_ifs <;> linarith

/-- **One exponent `≤ 0` is one exponent `≤ 1 - δ / 2n`.** -/
theorem exists_le_one_sub_div_of_exists_nonpos {n : ℕ} (hn : 2 ≤ n) {e : Fin n → ℝ} {δ : ℝ}
    (hδ1 : δ ≤ 1) (he0 : ∃ i, e i ≤ 0) : ∃ i, e i ≤ 1 - δ / (2 * n) := by
  obtain ⟨i, hi⟩ := he0
  refine ⟨i, ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : δ / (2 * n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  linarith

theorem two_pow_le_prod_normLam {n : ℕ} {e : Fin n → ℝ} {δ : ℝ}
    (he0 : ∃ i, e i ≤ 1 - δ / (2 * n)) (k : ℕ) : 2 ^ k ≤ ∏ i, normLam e δ k i := by
  obtain ⟨i, hi⟩ := he0
  have hcut : ¬ 1 - δ / (2 * n) < e i := not_lt.mpr hi
  calc 2 ^ k = normLam e δ k i := by simp [normLam, hcut]
    _ ≤ ∏ j, normLam e δ k j :=
        Finset.single_le_prod (fun j _ ↦ normLam_pos e δ k j) (mem_univ i)

theorem det_scaled {n : ℕ} (lam : Fin n → ℕ) (α : ℝ) (P : Fin n → Fin n → Fin 3 → ℤ) :
    (Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)).det =
      (∏ i, (lam i : ℝ)) * (Matrix.of fun i j ↦ quadVal α (P i j)).det := by
  have h := Matrix.det_mul_column (fun i ↦ (lam i : ℝ)) (Matrix.of fun i j ↦ quadVal α (P i j))
  simpa only [Matrix.of_apply] using h

/-- **The scaled determinant is at least `C ^ n`.** -/
theorem pow_le_det_normLam {n : ℕ} {α : ℝ} {P : Fin n → Fin n → Fin 3 → ℤ}
    {γ : ℝ} (hγ : 0 < γ) (hdet : γ ≤ |(Matrix.of fun i j ↦ quadVal α (P i j)).det|) {C : ℝ}
    {k : ℕ} (hk : C ^ n / γ ≤ 2 ^ k) {e : Fin n → ℝ} {δ : ℝ}
    (he0 : ∃ i, e i ≤ 1 - δ / (2 * n)) :
    C ^ n ≤ |(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| := by
  rw [det_scaled, abs_mul, abs_of_nonneg (by positivity)]
  have hp : (2 : ℝ) ^ k ≤ ∏ i, (normLam e δ k i : ℝ) := by
    exact_mod_cast two_pow_le_prod_normLam he0 k
  rw [div_le_iff₀ hγ] at hk
  exact hk.trans (mul_le_mul hp hdet hγ.le (by positivity))

theorem le_rpow_inv_of_pow_le {C D : ℝ} {n : ℕ} (hn : 0 < n) (hC : 0 ≤ C) (h : C ^ n ≤ D) :
    C ≤ D ^ (n : ℝ)⁻¹ :=
  calc C = (C ^ n) ^ (n : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hC hn.ne').symm
    _ ≤ D ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) h (by positivity)

/-! ### The places -/

section Places

variable {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ)

variable (E) in
/-- **An absolute value of `E` above a finite place of `ℚ`**, chosen once. -/
noncomputable def finiteAbs (v : FinitePlace ℚ) : AbsoluteValue E ℝ :=
  (NumberField.exists_liesOver_finitePlace (F := E) v).choose

theorem finiteAbs_liesOver (v : FinitePlace ℚ) : (finiteAbs E v).LiesOver v.1 :=
  (NumberField.exists_liesOver_finitePlace (F := E) v).choose_spec

open scoped Classical in
/-- **The absolute values of `E` at the places of `ℚ`**: `absC σ` at `∞`, and at a finite place
an absolute value of `E` lying over it. -/
noncomputable def placeAbs : AbsoluteValue ℚ ℝ → AbsoluteValue E ℝ := fun u ↦
  if h : ∃ v : FinitePlace ℚ, v.1 = u then finiteAbs E h.choose else absC σ

theorem placeAbs_infinitePlace : placeAbs σ Rat.infinitePlace.1 = absC σ := by
  rw [placeAbs, dite_eq_right]
  rintro ⟨v, hv⟩
  exact FinitePlace.val_ne_infinitePlace v hv

theorem placeAbs_liesOver_infinitePlace (v : InfinitePlace ℚ) :
    (placeAbs σ v.1).LiesOver v.1 := by
  rw [Subsingleton.elim v Rat.infinitePlace, placeAbs_infinitePlace]
  exact absC_liesOver σ

theorem placeAbs_liesOver_finitePlace (v : FinitePlace ℚ) :
    (placeAbs σ v.1).LiesOver v.1 := by
  have h : ∃ v' : FinitePlace ℚ, v'.1 = v.1 := ⟨v, rfl⟩
  rw [placeAbs, dite_eq_left_of_eq_true (eq_true h), Subtype.ext h.choose_spec]
  exact finiteAbs_liesOver v

variable {n : ℕ} (β : E) (lam : Fin n → ℕ) (P : Fin n → Fin n → Fin 3 → ℤ)

open scoped Classical in
/-- **The forms of the system**: the scaled forms at `∞`, the coordinates at the finite places. -/
noncomputable def placeForms : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E) := fun u ↦
  if u = Rat.infinitePlace.1 then fun i ↦ Module.Dual.sumForm (qRow β lam P i)
  else fun i ↦ LinearMap.proj i

omit [NumberField E] in
theorem placeForms_infinitePlace (v : InfinitePlace ℚ) :
    placeForms β lam P v.1 = fun i ↦ Module.Dual.sumForm (qRow β lam P i) := by
  rw [Subsingleton.elim v Rat.infinitePlace, placeForms]
  split_ifs with h
  · rfl
  · exact absurd rfl h

omit [NumberField E] in
theorem placeForms_finitePlace (v : FinitePlace ℚ) :
    placeForms β lam P v.1 = fun i ↦ LinearMap.proj i := by
  rw [placeForms]
  split_ifs with h
  · exact absurd h (FinitePlace.val_ne_infinitePlace v)
  · rfl

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {σ β} {α : ℝ} (hβ : σ β = α)

include hβ in
theorem systemValue_placeForms_inl (v : InfinitePlace ℚ)
    (i : Fin n) (x : Fin n → ℤ) :
    systemValue S (placeAbs σ) (placeForms β lam P) (.inl v) i (fun k ↦ (x k : ℚ)) =
      lam i * |∑ k, quadVal α (P i k) * x k| := by
  simp only [systemValue, systemAbs, systemMult, mult_placeQ, pow_one, systemPlace]
  rw [placeForms_infinitePlace, Subsingleton.elim v Rat.infinitePlace, placeAbs_infinitePlace]
  exact absC_sumForm_qRow lam P hβ i x

theorem systemValue_placeForms_inr (v : S) (i : Fin n) (x : Fin n → ℤ) :
    systemValue S (placeAbs σ) (placeForms β lam P) (.inr v) i (fun k ↦ (x k : ℚ)) =
      FinitePlace.mk v.1 (x i : ℚ) := by
  simp only [systemValue, systemAbs, systemMult, pow_one, systemPlace]
  rw [placeForms_finitePlace, LinearMap.proj_apply]
  have := placeAbs_liesOver_finitePlace σ (FinitePlace.mk v.1)
  rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := (FinitePlace.mk v.1).1)]
  rfl

include hβ in
theorem systemDet_placeForms :
    systemDet S (placeAbs σ) (placeForms β lam P) =
      |(Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)).det| := by
  rw [systemDet, Fintype.prod_sum_type, Fintype.prod_unique]
  have hfin : ∀ v : S, systemAbs S (placeAbs σ) (.inr v)
      (LinearMap.det (LinearMap.pi (placeForms β lam P (systemPlace S (.inr v))))) = 1 := by
    intro v
    simp only [systemAbs, systemMult, pow_one, systemPlace]
    rw [placeForms_finitePlace, LinearMap.pi_proj, LinearMap.det_id, map_one]
  rw [Fintype.prod_congr _ _ hfin, Finset.prod_const_one, mul_one]
  simp only [systemAbs, systemMult, mult_placeQ, pow_one, systemPlace]
  rw [placeForms_infinitePlace, Subsingleton.elim (default : InfinitePlace ℚ) Rat.infinitePlace,
    placeAbs_infinitePlace]
  exact absC_det_qForms lam P hβ

end Places

/-! ### The normalized system -/

section Normalized

variable {E : Type} [Field E] [NumberField E] {σ : E →+* ℂ} {β : E} {α : ℝ} (hβ : σ β = α)
  {n : ℕ} (P : Fin n → Fin n → Fin 3 → ℤ) (e : Fin n → ℝ) (δ : ℝ) (k : ℕ)
  (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (f : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ)

/-- **The exponents of the system**: the raised exponents at `∞`, the caller's at the primes. -/
noncomputable def placeExp : InfinitePlace ℚ ⊕ S → Fin n → ℝ
  | .inl _ => normExp e δ
  | .inr v => f v.1

/-- **The constants of the system**: `c₀` at `∞`, `1` at the primes. -/
noncomputable def placeConst (c₀ : ℝ) : InfinitePlace ℚ ⊕ S → ℝ
  | .inl _ => c₀
  | .inr _ => 1

omit [NumberField E] in
theorem ncard_range_le {X : Type*} (g : Fin n → X) : (Set.range g).ncard ≤ n := by
  rw [← Set.image_univ]
  refine le_trans Set.ncard_image_le ?_
  simp

include hβ in
/-- **The scaled forms at `∞` and the coordinates at the primes make up a normalized system**, of
weight `-δ / 2`, with at most `2 n` distinct forms. -/
theorem isNormalizedSystem_placeForms (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B)
    (hP : ∀ i j m, |(P i j m : ℝ)| ≤ B) {γ : ℝ} (hγ : 0 < γ)
    (hdet : γ ≤ |(Matrix.of fun i j ↦ quadVal α (P i j)).det|) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he1 : ∀ i, e i ≤ 1) (he : ∃ i, e i = 1) (hf : ∀ v ∈ S, ∀ i, f v i ≤ 0)
    (hf0 : ∀ v ∈ S, ∃ i, f v i = 0) (hsum : ∑ i, e i + ∑ v ∈ S, ∑ i, f v i ≤ -δ) :
    IsNormalizedSystem S (placeAbs σ) (placeForms β (normLam e δ k) P)
      (placeConst S
        (|(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^ (n : ℝ)⁻¹))
      (placeExp e δ S f)
      (3 ^ finrank ℚ E * (2 ^ k * B) ^ (3 * finrank ℚ E) * mulHeight₁ β ^ 3)
      (finrank ℚ E) (2 * n) (δ / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hτ : 0 < δ / (2 * n) := by positivity
  have hexp (v : InfinitePlace ℚ) : systemExponent S (.inl v) = 1 := by
    simp only [systemExponent, mult_placeQ, Module.finrank_self, Nat.cast_one, div_one]
  have hk1 : (1 : ℝ) ≤ 2 ^ k * B :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
  have hH1 : (1 : ℝ) ≤ 3 ^ finrank ℚ E * (2 ^ k * B) ^ (3 * finrank ℚ E) * mulHeight₁ β ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ hk1)) (one_le_pow₀ (one_le_mulHeight₁ β))
  exact {
    height_le := fun p i j ↦ by
      rcases p with v | v
      · change absMulHeight₁ (placeForms β (normLam e δ k) P v.1 i _) ≤ _
        rw [placeForms_infinitePlace]
        have : Module.Dual.sumForm (qRow β (normLam e δ k) P i) (Pi.basisFun E (Fin n) j) =
            qRow β (normLam e δ k) P i j := by
          simp [Pi.basisFun_apply, Pi.single_apply]
        rw [this, qRow]
        refine absMulHeight₁_sum_le β (fun m ↦ (normLam e δ k i : ℤ) * P i j m) hk1 fun m ↦ ?_
        push_cast
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul (normLam_le e δ k i) (hP i j m) (abs_nonneg _) (by positivity)
      · change absMulHeight₁ (placeForms β (normLam e δ k) P (FinitePlace.mk v.1).1 i _) ≤ _
        rw [placeForms_finitePlace]
        refine (absMulHeight₁_le_mulHeight₁ _).trans (le_trans (le_of_eq ?_) hH1)
        by_cases hij : j = i
        · simp [Pi.basisFun_apply, hij]
        · simp [Pi.basisFun_apply, Ne.symm hij]
    degree_le := fun p i j ↦ minpoly.natDegree_le _
    ncard_le := by
      have hsub : (Set.range fun q : (InfinitePlace ℚ ⊕ S) × Fin n ↦
          placeForms β (normLam e δ k) P (systemPlace S q.1) q.2) ⊆
          (Set.range fun i ↦ Module.Dual.sumForm (qRow β (normLam e δ k) P i)) ∪
            Set.range fun i : Fin n ↦ (LinearMap.proj i : Dual E (Fin n → E)) := by
        rintro _ ⟨⟨v | v, i⟩, rfl⟩
        · left
          refine ⟨i, ?_⟩
          change _ = placeForms β (normLam e δ k) P v.1 i
          rw [placeForms_infinitePlace]
        · right
          refine ⟨i, ?_⟩
          change _ = placeForms β (normLam e δ k) P (FinitePlace.mk v.1).1 i
          rw [placeForms_finitePlace]
      refine (Set.ncard_le_ncard hsub ((Set.finite_range _).union (Set.finite_range _))).trans ?_
      refine (Set.ncard_union_le _ _).trans ?_
      have := ncard_range_le fun i ↦ Module.Dual.sumForm (qRow β (normLam e δ k) P i)
      have := ncard_range_le fun i : Fin n ↦ (LinearMap.proj i : Dual E (Fin n → E))
      omega
    const_pos := fun p ↦ by
      rcases p with v | v
      · refine Real.rpow_pos_of_pos (abs_pos.2 ?_) _
        rw [det_scaled]
        refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_)
          (abs_pos.1 (hγ.trans_le hdet))
        exact Nat.cast_ne_zero.2 (normLam_pos e δ k i).ne'
      · exact one_pos
    const_le := by
      rw [systemConst, Fintype.prod_sum_type, Fintype.prod_unique]
      simp only [placeConst, Finset.prod_const_one, mul_one]
      rw [systemDet_placeForms (normLam e δ k) P S hβ, Fintype.card_fin]
    delta_pos := by positivity
    delta_le_one := by linarith
    weight_le := by
      rw [systemWeight, Fintype.sum_sum_type, Fintype.sum_unique]
      simp only [placeExp]
      rw [Finset.sum_coe_sort S (fun v ↦ ∑ i, f v i)]
      calc ∑ i, normExp e δ i + ∑ v ∈ S, ∑ i, f v i
          ≤ ∑ i, (e i + δ / (2 * n)) + ∑ v ∈ S, ∑ i, f v i := by
            gcongr with i
            exact normExp_le e hδ.le i
        _ = ∑ i, e i + ∑ v ∈ S, ∑ i, f v i + δ / 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            field_simp
            ring
        _ ≤ -(δ / 2) := by linarith
    exponent_le := fun p i ↦ by
      rcases p with v | v
      · rw [hexp]
        change normExp e δ i ≤ 1
        unfold normExp
        split_ifs with h
        · exact he1 i
        · linarith [not_lt.1 h]
      · exact hf v.1 v.2 i
    exists_exponent_eq := fun p ↦ by
      rcases p with v | v
      · obtain ⟨i, hi⟩ := he
        refine ⟨i, ?_⟩
        rw [hexp]
        have : 1 - δ / (2 * n) < e i := by rw [hi]; linarith
        change normExp e δ i = 1
        unfold normExp
        simp only [this, ↓reduceIte]
        exact hi
      · exact hf0 v.1 v.2 }

include hβ in
/-- **The solutions are solutions of the scaled system**, once `2 ^ k ≤ |x| ^ (δ / 2n)`. -/
theorem mem_systemSet_placeForms {x : Fin n → ℤ} (hx : x ≠ 0) {C c₀ : ℝ} (hC : C ≤ c₀)
    (hk : (2 : ℝ) ^ k ≤ (⨆ j, |(x j : ℝ)|) ^ (δ / (2 * n)))
    (hsol : ∀ i, |∑ j, quadVal α (P i j) * x j| ≤ C * (⨆ j, |(x j : ℝ)|) ^ e i)
    (hfin : ∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ j, |(x j : ℝ)|) ^ f v i) :
    (fun j ↦ (x j : ℚ)) ∈ systemSet S (placeAbs σ) (placeForms β (normLam e δ k) P)
      (placeConst S c₀) (placeExp e δ S f) := by
  have hX : 1 ≤ ⨆ j, |(x j : ℝ)| := by
    rw [← Height.mulHeightAff_intCast hx]
    exact one_le_mulHeightAff _
  refine ⟨fun j ↦ intCast_mem _ (x j), fun p i ↦ ?_⟩
  rw [Height.mulHeightAff_intCast hx]
  set X := ⨆ j, |(x j : ℝ)|
  rcases p with v | v
  swap
  · rw [systemValue_placeForms_inr]
    simp only [placeConst, placeExp, one_mul]
    exact hfin v.1 v.2 i
  rw [systemValue_placeForms_inl (normLam e δ k) P S hβ v i x]
  simp only [placeConst, placeExp]
  have hX0 : 0 < X := by linarith
  have hv := hsol i
  unfold normLam normExp
  by_cases h : 1 - δ / (2 * n) < e i
  · simp only [h, ↓reduceIte, Nat.cast_one, one_mul]
    exact hv.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hX0.le _))
  · simp only [h, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.rpow_add hX0]
    calc (2 : ℝ) ^ k * |∑ j, quadVal α (P i j) * x j|
        ≤ X ^ (δ / (2 * n)) * (C * X ^ e i) :=
          mul_le_mul hk hv (abs_nonneg _) (by positivity)
      _ = C * (X ^ e i * X ^ (δ / (2 * n))) := by ring
      _ ≤ c₀ * (X ^ e i * X ^ (δ / (2 * n))) := mul_le_mul_of_nonneg_right hC (by positivity)

end Normalized

/-! ### The threshold -/

/-- `log n! ≤ 23` for `n ≤ 4`. -/
theorem log_factorial_le {n : ℕ} (hn4 : n ≤ 4) : Real.log (n.factorial : ℝ) ≤ 23 := by
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h24 : (n.factorial : ℝ) ≤ 24 := by
    have : n.factorial ≤ 24 := by interval_cases n <;> decide
    exact_mod_cast this
  linarith [Real.log_le_sub_one_of_pos hfpos]

/-- **Minkowski's constant for one scalar over `ℚ`** is at least `1`: it is `2 ∏_{v ∈ S} N(v)`. -/
theorem one_le_scalarConst_rat (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    1 ≤ scalarConst ℚ S := by
  rw [scalarConst, Module.finrank_self, NumberField.discr_rat]
  have hprod : (1 : ℝ) ≤ ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) := by
    have : 1 ≤ ∏ q ∈ S, Ideal.absNorm q.asIdeal :=
      Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun q _ ↦ by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact q.ne_bot)
    exact_mod_cast this
  norm_num
  linarith

/-- The constant of the threshold, for `2 ≤ n ≤ 4` variables over a field of degree `d`, at `∞`
and `s` finite places with `μ` the logarithm of Minkowski's constant. -/
noncomputable def thrConst (n d s : ℕ) (μ : ℝ) : ℝ :=
  2 * ((1 + 10 * ((2 * n * d + n).choose n : ℝ)) * (23 + 64 * (d + d * s)) + 60) + 48 +
    2 * (8 * μ + 4 * (1 + s) * (23 + 4 * d))

/-- The constant of the threshold, for `2 ≤ n ≤ 4` variables over a field of degree `d`, at the
places `∞` and `S`. -/
noncomputable def thrConstAt (n d : ℕ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ℝ :=
  thrConst n d #S (Real.log (scalarConst ℚ S))

/-- **The threshold of the scaled system** is at most `thrConstAt n d S (1 + log H) / δ`. -/
theorem efSystemThreshold_le_thrConstAt {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {w : AbsoluteValue ℚ ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → Fin n → ℝ} {H : ℝ} {D : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D (2 * n) (δ / 2)) (hH : 1 ≤ H) (hδ1 : δ ≤ 1) :
    efSystemThreshold E S w L (2 * n) H (δ / 2) ≤
      thrConstAt n (finrank ℚ E) S * (1 + log H) / δ := by
  have hδ2 : 0 < δ / 2 := hN.delta_pos
  have hδ : 0 < δ := by linarith
  have hΛ : 0 ≤ log H := Real.log_nonneg hH
  set d := finrank ℚ E with hd
  have hd1 : 1 ≤ d := finrank_pos
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hlogn : Real.log n ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  set μ := Real.log (scalarConst ℚ S) with hμ
  have hμ0 : 0 ≤ μ := Real.log_nonneg (one_le_scalarConst_rat S)
  set ch : ℝ := ((2 * n * d + n).choose n : ℝ) with hch
  have hch0 : 0 ≤ ch := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
  have hdom : 0 ≤ (1 + 10 * ch) * (23 + 64 * ((d : ℝ) + d * #S)) + 60 := by positivity
  have hhgt : 0 ≤ 8 * μ + 4 * (1 + (#S : ℝ)) * (23 + 4 * d) := by positivity
  have h := efSystemThreshold_le hwInf hwFin hN
  refine h.trans (max_le ?_ (max_le ?_ ?_))
  · -- the domain threshold
    set c := Fintype.card (InfinitePlace E) + #(systemPlacesOver E S) with hc
    have hcd : (c : ℝ) ≤ d + d * #S := by
      have h1 : Fintype.card (InfinitePlace E) ≤ d := card_infinitePlace_le_finrank (E := E)
      have h2 := card_systemPlacesOver_le (E := E) S
      have : c ≤ d + d * #S := by
        have e : d * #S = finrank ℚ E * #S := rfl
        have e' : d = finrank ℚ E := rfl
        rw [hc]
        omega
      exact_mod_cast this
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    rw [Fintype.card_fin, ← Nat.cast_add, ← hc]
    refine (domainThreshold_le_div (s := 2 * n * d) (c := c) hn hn4 hd1 hδ2 (by linarith)
      hΛ).trans ?_
    rw [div_div_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have e1 : 23 + 64 * (c : ℝ) * log H ≤ (23 + 64 * ((d : ℝ) + d * #S)) * (1 + log H) := by
      nlinarith
    have e2 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 1 + 10 * ch)
    unfold thrConstAt thrConst
    have : (0 : ℝ) ≤ (48 + 2 * (8 * μ + 4 * (1 + #S) * (23 + 4 * d))) * (1 + log H) := by
      positivity
    nlinarith
  · -- the gap principle
    simp only [Fintype.card_fin, Module.finrank_self, Nat.cast_one, one_mul]
    rw [show 2 * (n : ℝ) / (δ / 2) * Real.log n = 4 * n * Real.log n / δ by field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have : (n : ℝ) * Real.log n ≤ 4 * 3 := mul_le_mul hn4' hlogn hlogn0 (by norm_num)
    unfold thrConstAt thrConst
    have : (0 : ℝ) ≤ (2 * ((1 + 10 * ch) * (23 + 64 * ((d : ℝ) + d * #S)) + 60) +
      2 * (8 * μ + 4 * (1 + #S) * (23 + 4 * d))) * (1 + log H) := by positivity
    nlinarith
  · -- the scalar
    have ht : ((Fintype.card (InfinitePlace ℚ) + #S : ℕ) : ℝ) = 1 + #S := by
      have : Fintype.card (InfinitePlace ℚ) = 1 := Fintype.card_unique
      push_cast [this]; ring
    rw [systemHeightThreshold, Fintype.card_fin, div_div_eq_mul_div, ht, ← hμ]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    set G := Real.log (n.factorial : ℝ) + n * (d * log H)
    have hG0 : 0 ≤ G := by
      have : 0 ≤ Real.log (n.factorial : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
      positivity
    have hG : G ≤ (23 + 4 * d) * (1 + log H) := by
      have : (n : ℝ) * (d * log H) ≤ 4 * (d * log H) :=
        mul_le_mul_of_nonneg_right hn4' (by positivity)
      nlinarith [log_factorial_le hn4]
    have htG : 4 * (1 + (#S : ℝ)) * G ≤ 4 * (1 + #S) * ((23 + 4 * d) * (1 + log H)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have hnμ : 2 * (n : ℝ) * μ ≤ 8 * μ * (1 + log H) := by nlinarith
    unfold thrConstAt thrConst
    have : (0 : ℝ) ≤ (2 * ((1 + 10 * ch) * (23 + 64 * ((d : ℝ) + d * #S)) + 60) + 48) *
      (1 + log H) := by positivity
    nlinarith

/-! ### Evertse–Ferretti -/

/-- **The constant of `Real.subspaceBoundWith_three_of_mem`**, for `n` variables, forms over a
field of degree `d` in which `α` has height `log H(α) = h` (not normalized by the degree), and `s`
finite places with `μ` the logarithm of Minkowski's constant: the larger of EF13's constant at
`2 n d` conjugated forms and the threshold constant. -/
noncomputable def subspaceConst (n d s : ℕ) (h μ : ℝ) : ℝ :=
  max (max (efCountConst n (2 * n * d)) (thrConst n d s μ * (1 + 17 * d + 3 * h) + 2 * n ^ 2)) 1

theorem one_le_subspaceConst (n d s : ℕ) (h μ : ℝ) : 1 ≤ subspaceConst n d s h μ :=
  le_max_right _ _

theorem efCountConst_le_subspaceConst (n d s : ℕ) (h μ : ℝ) :
    efCountConst n (2 * n * d) ≤ subspaceConst n d s h μ :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem thrConst_le_subspaceConst (n d s : ℕ) (h μ : ℝ) :
    thrConst n d s μ * (1 + 17 * d + 3 * h) + 2 * n ^ 2 ≤ subspaceConst n d s h μ :=
  (le_max_right _ _).trans (le_max_left _ _)

/-- **The system of `Real.exists_normalized_places_of_mem`, explicitly**: for a `k` with
`C^n / γ ≤ 2^k` and `k log 2 ≤ 1 + n log C + log γ⁻¹`, the forms `placeForms β (normLam e δ k) P`,
the constants `placeConst` and the exponents `placeExp e δ S f`. The forms and the constants depend
on `e` only through the set of `i` with `e i > 1 - δ / 2n`. -/
theorem normalized_placeForms_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (P : Fin n → Fin n → Fin 3 → ℤ) {B : ℝ}
    (hB : 1 ≤ B) (hP : ∀ i k m, |(P i k m : ℝ)| ≤ B) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdet : γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det|) {C : ℝ} (hC : 1 ≤ C)
    (e : Fin n → ℝ) (f : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (he1 : ∀ i, e i ≤ 1) (he : ∃ i, e i = 1) (he0 : ∃ i, e i ≤ 1 - δ / (2 * n))
    (hf : ∀ v ∈ S, ∀ i, f v i ≤ 0) (hf0 : ∀ v ∈ S, ∃ i, f v i = 0)
    (hsum : ∑ i, e i + ∑ v ∈ S, ∑ i, f v i ≤ -δ)
    {k : ℕ} (hk : C ^ n / γ ≤ 2 ^ k)
    (hklog : (k : ℝ) * Real.log 2 ≤ 1 + n * Real.log C + Real.log γ⁻¹) :
    IsNormalizedSystem S (placeAbs E.val.toRingHom) (placeForms ⟨α, hαE⟩ (normLam e δ k) P)
      (placeConst S
        (|(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^ (n : ℝ)⁻¹))
      (placeExp e δ S f)
      (3 ^ finrank ℚ E * (2 ^ k * B) ^ (3 * finrank ℚ E) * mulHeight₁ (⟨α, hαE⟩ : E) ^ 3)
      (finrank ℚ E) (2 * n) (δ / 2) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ f v i) →
        (thrConstAt n (finrank ℚ E) S *
            (1 + 17 * finrank ℚ E + 3 * log (mulHeight₁ (⟨α, hαE⟩ : E))) + 2 * n ^ 2) *
            δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        (fun j ↦ (x j : ℚ)) ∈ systemSet S (placeAbs E.val.toRingHom)
            (placeForms ⟨α, hαE⟩ (normLam e δ k) P)
            (placeConst S
              (|(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^ (n : ℝ)⁻¹))
            (placeExp e δ S f) ∧
          efSystemThreshold E S (placeAbs E.val.toRingHom) (placeForms ⟨α, hαE⟩ (normLam e δ k) P)
            (2 * n)
            (3 ^ finrank ℚ E * (2 ^ k * B) ^ (3 * finrank ℚ E) * mulHeight₁ (⟨α, hαE⟩ : E) ^ 3)
            (δ / 2) ≤
            log (mulHeightAff fun j ↦ (x j : ℚ)) := by
  set d := finrank ℚ E with hd
  have hd1 : 1 ≤ d := finrank_pos
  set β : E := ⟨(α : ℂ), hαE⟩
  set σ : E →+* ℂ := E.val.toRingHom
  have hβ : σ β = α := rfl
  have hwInf := placeAbs_liesOver_infinitePlace σ
  have hwFin : ∀ v ∈ S, (placeAbs σ (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1 :=
    fun v _ ↦ placeAbs_liesOver_finitePlace σ (FinitePlace.mk v)
  set Mβ := mulHeight₁ β
  have hMβ : 1 ≤ Mβ := one_le_mulHeight₁ β
  have hlM : 0 ≤ log Mβ := Real.log_nonneg hMβ
  set c₁ : ℝ := 1 + 17 * d + 3 * log Mβ with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  set M := thrConstAt n d S
  have hM0 : 0 ≤ M := by
    have := Real.log_nonneg (one_le_scalarConst_rat S)
    unfold M thrConstAt thrConst
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hN := isNormalizedSystem_placeForms hβ P e δ k S f hn hB hP hγ hdet hδ hδ1 he1 he hf hf0
    hsum
  refine ⟨hN, fun x hx hsol hfin hlarge ↦ ?_⟩
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  -- the data
  have hlB : 0 ≤ log B := Real.log_nonneg hB
  have hlC : 0 ≤ log C := Real.log_nonneg hC
  have hlγ : 0 ≤ log γ⁻¹ := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
  set Ξ := 1 + log B + log C + log γ⁻¹ with hΞ
  have hΞ1 : 1 ≤ Ξ := by linarith
  have hk' : (k : ℝ) * log 2 ≤ n * Ξ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hn1) hlγ, mul_nonneg hn0.le hlB,
      mul_nonneg (sub_nonneg.2 hn1) hlC]
  -- the point
  set X := ⨆ j, |(x j : ℝ)| with hX
  have hX1 : 1 ≤ X := by
    rw [hX, ← Height.mulHeightAff_intCast hx]
    exact one_le_mulHeightAff _
  have hX0 : 0 < X := by linarith
  have hbig : (M * c₁ + 2 * n ^ 2) * δ⁻¹ * Ξ ≤ log X := hlarge
  have hsplit : (M * c₁ + 2 * n ^ 2) * δ⁻¹ * Ξ =
      M * c₁ * δ⁻¹ * Ξ + 2 * n ^ 2 * δ⁻¹ * Ξ := by ring
  have hMc : 0 ≤ M * c₁ * δ⁻¹ * Ξ := by positivity
  have h2n : 2 * n ^ 2 * δ⁻¹ * Ξ ≤ log X := by linarith
  -- `2 ^ k ≤ |x| ^ (δ / 2n)`
  have h2k : (2 : ℝ) ^ k ≤ X ^ (δ / (2 * n)) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hX0]
    calc (k : ℝ) * log 2 ≤ n * Ξ := hk'
      _ = δ / (2 * n) * (2 * n ^ 2 * δ⁻¹ * Ξ) := by field_simp
      _ ≤ δ / (2 * n) * log X := mul_le_mul_of_nonneg_left h2n (by positivity)
  -- the constant
  have hCc : C ≤ |(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^
      (n : ℝ)⁻¹ :=
    le_rpow_inv_of_pow_le (by omega) (by linarith) (pow_le_det_normLam hγ hdet hk he0)
  -- the height of the coefficients
  set Hc : ℝ := 3 ^ d * (2 ^ k * B) ^ (3 * d) * Mβ ^ 3 with hHc
  have hkB : (1 : ℝ) ≤ 2 ^ k * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
  have hHc1 : 1 ≤ Hc := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ hkB)) (one_le_pow₀ hMβ)
  have hlogHc : 1 + log Hc ≤ c₁ * Ξ := by
    have hl3 : log 3 ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
    have hl2kB : log ((2 : ℝ) ^ k * B) = k * log 2 + log B := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
    have : log Hc = d * log 3 + (3 * d) * (k * log 2 + log B) + 3 * log Mβ := by
      rw [hHc, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, hl2kB]
      push_cast
      ring
    have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hΞ0 : 0 ≤ Ξ - 1 := sub_nonneg.2 hΞ1
    have ha : (d : ℝ) * log 3 ≤ 2 * d * Ξ := by
      have h1 := mul_le_mul_of_nonneg_left hl3 (by positivity : (0 : ℝ) ≤ d)
      have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d) hΞ0
      linarith
    have hb : 3 * (d : ℝ) * (k * log 2 + log B) ≤ 3 * d * (5 * Ξ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := mul_le_mul_of_nonneg_right hn4' (by linarith : (0 : ℝ) ≤ Ξ)
      linarith
    have hc := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hlM) hΞ0
    rw [this, hc₁]
    linarith
  have hthr := efSystemThreshold_le_thrConstAt hn hn4 hwInf hwFin hN hHc1 hδ1
  have hthr' := hthr.trans <| show M * (1 + log Hc) / δ ≤ log X by
    calc M * (1 + log Hc) / δ = M * (1 + log Hc) * δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ M * (c₁ * Ξ) * δ⁻¹ := by gcongr
      _ = M * c₁ * δ⁻¹ * Ξ := by ring
      _ ≤ log X := by
          have : 0 ≤ 2 * (n : ℝ) ^ 2 * δ⁻¹ * Ξ := by positivity
          linarith
  exact ⟨mem_systemSet_placeForms hβ P e δ k S f hx hCc h2k hsol hfin,
    by rwa [Height.mulHeightAff_intCast hx]⟩

/-- **The system of the forms in `1, α, α²` at `∞` and finitely many finite places of `ℚ`**: the
forms are taken over a Galois field `E ⊆ ℂ` containing `α`, scaled at `∞` to a normalized system
of weight `-δ / 2` with the coordinates at the primes (`Real.isNormalizedSystem_placeForms`), and
every solution above the threshold `(thrConstAt n d S (1 + 17 d + 3 log H(α)) + 2 n²) δ⁻¹ Ξ`,
`Ξ = 1 + log B + log C + log γ⁻¹`, is a solution of that system above its threshold
`efSystemThreshold`. Both `Real.subspaceBound_places_of_mem` and
`Real.subspaceInterval_places_of_mem` count these. -/
theorem exists_normalized_places_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (P : Fin n → Fin n → Fin 3 → ℤ) {B : ℝ}
    (hB : 1 ≤ B) (hP : ∀ i k m, |(P i k m : ℝ)| ≤ B) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdet : γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det|) {C : ℝ} (hC : 1 ≤ C)
    (e : Fin n → ℝ) (f : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (he1 : ∀ i, e i ≤ 1) (he : ∃ i, e i = 1) (he0 : ∃ i, e i ≤ 1 - δ / (2 * n))
    (hf : ∀ v ∈ S, ∀ i, f v i ≤ 0) (hf0 : ∀ v ∈ S, ∃ i, f v i = 0)
    (hsum : ∑ i, e i + ∑ v ∈ S, ∑ i, f v i ≤ -δ) :
    ∃ (L : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E)) (Cs : InfinitePlace ℚ ⊕ S → ℝ)
      (c : InfinitePlace ℚ ⊕ S → Fin n → ℝ) (H : ℝ),
      IsNormalizedSystem S (placeAbs E.val.toRingHom) L Cs c H (finrank ℚ E) (2 * n) (δ / 2) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ f v i) →
        (thrConstAt n (finrank ℚ E) S *
            (1 + 17 * finrank ℚ E + 3 * log (mulHeight₁ (⟨α, hαE⟩ : E))) + 2 * n ^ 2) *
            δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        (fun k ↦ (x k : ℚ)) ∈ systemSet S (placeAbs E.val.toRingHom) L Cs c ∧
          efSystemThreshold E S (placeAbs E.val.toRingHom) L (2 * n) H (δ / 2) ≤
            log (mulHeightAff fun k ↦ (x k : ℚ)) := by
  obtain ⟨k, hk, hklog⟩ := exists_two_pow hC hγ hγ1 n
  exact ⟨_, _, _, _, normalized_placeForms_of_mem E hαE hn hn4 S P hB hP hγ hγ1 hdet hC e f hδ hδ1
    he1 he he0 hf hf0 hsum hk hklog⟩

/-- **The quantitative Subspace Theorem at `∞` and finitely many finite places of `ℚ`**, with an
explicit constant, the form `Real.subspaceBoundWith_three_of_mem` is assembled from: the places
are elements of `HeightOneSpectrum (𝓞 ℚ)` and the exponents at them a function on all of them.
The forms are taken over a Galois field `E ⊆ ℂ` containing `α`
(`Real.exists_normalized_places_of_mem`). -/
theorem subspaceBound_places_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    let K := subspaceConst n (finrank ℚ E) #S (log (mulHeight₁ (⟨α, hαE⟩ : E)))
        (log (scalarConst ℚ S))
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
      ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (f : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ) (δ : ℝ),
        0 < δ → δ ≤ 1 → (∀ i, e i ≤ 1) → (∃ i, e i = 1) → (∃ i, e i ≤ 1 - δ / (2 * n)) →
        (∀ v ∈ S, ∀ i, f v i ≤ 0) → (∀ v ∈ S, ∃ i, f v i = 0) →
        ∑ i, e i + ∑ v ∈ S, ∑ i, f v i ≤ -δ →
      ∃ T : Finset (Submodule ℚ (Fin n → ℚ)),
        (#T : ℝ) ≤ K * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x : Fin n → ℤ, x ≠ 0 →
          (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
          (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ f v i) →
          K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
          ∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U := by
  intro K P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  have hwInf := placeAbs_liesOver_infinitePlace E.val.toRingHom
  have hwFin : ∀ v ∈ S, (placeAbs E.val.toRingHom (FinitePlace.mk v).1).LiesOver
      (FinitePlace.mk v).1 := fun v _ ↦ placeAbs_liesOver_finitePlace _ (FinitePlace.mk v)
  obtain ⟨L, Cs, c, H, hN, hmem⟩ := exists_normalized_places_of_mem E hαE hn hn4 S P hB hP hγ
    hγ1 hdet hC e f hδ hδ1 he1 he he0 hf hf0 hsum
  obtain ⟨T, hT, htop, hTmem⟩ :=
    exists_finset_submodule_of_efSystemThreshold_le S _ hwInf hwFin hN
  refine ⟨T, ?_, htop, fun x hx hsol hfin hlarge ↦ ?_⟩
  · rw [Fintype.card_fin] at hT
    refine hT.trans ((efLargeCount_half_le (d := finrank ℚ E) (r := 2 * n) hn finrank_pos
      (by omega) hδ hδ1).trans ?_)
    have : efCountConst n (2 * n * finrank ℚ E) ≤ K := efCountConst_le_subspaceConst ..
    have : 0 ≤ δ⁻¹ ^ (3 : ℝ) := Real.rpow_nonneg (inv_nonneg.2 hδ.le) _
    gcongr
  have hΞ : 0 ≤ δ⁻¹ * (1 + log B + log C + log γ⁻¹) := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    have : 0 < δ⁻¹ := inv_pos.2 hδ
    positivity
  obtain ⟨h1, h2⟩ := hmem x hx hsol hfin <| le_trans (by
    rw [mul_assoc, mul_assoc K]
    exact mul_le_mul_of_nonneg_right (thrConst_le_subspaceConst ..) hΞ) hlarge
  exact hTmem _ h1 h2

/-- The prime ideal of `ℤ` at a prime, as a finite place of `ℚ`. -/
noncomputable def primeIdeal (l : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.finitePlace l).maximalIdeal

theorem finitePlace_mk_primeIdeal (l : Nat.Primes) (y : ℚ) :
    FinitePlace.mk (primeIdeal l) y = ((padicNorm (l : ℕ) y : ℚ) : ℝ) := by
  rw [primeIdeal, FinitePlace.mk_maximalIdeal, Rat.finitePlace_apply]

theorem primeIdeal_injective : Function.Injective primeIdeal := by
  intro l l' h
  have : FinitePlace.mk (primeIdeal l) = FinitePlace.mk (primeIdeal l') := by rw [h]
  rw [primeIdeal, primeIdeal, FinitePlace.mk_maximalIdeal, FinitePlace.mk_maximalIdeal] at this
  exact Rat.finitePlace_injective this

theorem card_image_primeIdeal [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] (S : Finset Nat.Primes) :
    #(S.image primeIdeal) = #S :=
  card_image_of_injective S primeIdeal_injective

/-- **Minkowski's constant at the primes of `S`** is `2 ∏_{l ∈ S} l`. -/
theorem log_scalarConst_image_primeIdeal [DecidableEq (HeightOneSpectrum (𝓞 ℚ))]
    (S : Finset Nat.Primes) :
    Real.log (scalarConst ℚ (S.image primeIdeal)) = Real.log 2 + ∑ l ∈ S, Real.log (l : ℕ) := by
  have hl (l : Nat.Primes) : (0 : ℝ) < (l : ℕ) := by exact_mod_cast l.2.pos
  rw [scalarConst_rat, Finset.prod_image fun l _ l' _ h ↦ primeIdeal_injective h,
    Real.log_mul (by norm_num) (Finset.prod_ne_zero_iff.2 fun l _ ↦ by
      rw [primeIdeal, Rat.absNorm_maximalIdeal_finitePlace]; exact (hl l).ne'),
    Real.log_prod fun l _ ↦ by
      rw [primeIdeal, Rat.absNorm_maximalIdeal_finitePlace]; exact (hl l).ne']
  simp only [primeIdeal, Rat.absNorm_maximalIdeal_finitePlace]

/-- **The quantitative Subspace Theorem of Evertse–Ferretti 2013 for forms in `1, α, α²` at `∞`
and the primes of `S`, with an explicit constant**: `δ^{-3} (1 + log δ⁻¹)²` subspaces, with the
constant `Real.subspaceConst` of `n`, the degree `d` of a Galois field `E ⊆ ℂ` containing `α`, the
height `log H(α)` of `α` in `E` (`d` times the absolute logarithmic height), `#S` and
`log 2 + ∑_{l ∈ S} log l`. The forms are taken over `E`, scaled at `∞` to a normalized system of
weight `-δ / 2` with the coordinates at the primes (`Real.isNormalizedSystem_placeForms`), and
counted by `NumberField.exists_finset_submodule_of_efSystemThreshold_le`. -/
theorem subspaceBoundWith_three_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    SubspaceBoundWith α S 3 n (subspaceConst n (finrank ℚ E) #S
      (log (mulHeight₁ (⟨α, hαE⟩ : E))) (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  classical
  have hT := subspaceBound_places_of_mem E hαE hn hn4 (S.image primeIdeal)
  rw [card_image_primeIdeal, log_scalarConst_image_primeIdeal] at hT
  intro P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  set f' : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ := fun v ↦ f (Function.invFun primeIdeal v)
  have hf' (l : Nat.Primes) : f' (primeIdeal l) = f l := by
    simp only [f', Function.leftInverse_invFun primeIdeal_injective l]
  have hsum' : ∑ v ∈ S.image primeIdeal, ∑ i, f' v i = ∑ l ∈ S, ∑ i, f l i := by
    rw [Finset.sum_image fun l _ l' _ h ↦ primeIdeal_injective h]
    simp only [hf']
  obtain ⟨T, hcard, htop, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e f' δ hδ hδ1 he1 he he0
    (fun v hv ↦ by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      rw [hf']; exact hf l hl)
    (fun v hv ↦ by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      rw [hf']; exact hf0 l hl)
    (by rwa [hsum'])
  refine ⟨T, hcard, htop, fun x hx hsol hfin hlarge ↦ hmem x hx hsol (fun v hv i ↦ ?_) hlarge⟩
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
  rw [hf', finitePlace_mk_primeIdeal]
  exact hfin l hl i

/-- **The quantitative Subspace Theorem of Evertse–Ferretti 2013 for forms in `1, α, α²` at `∞`
and the primes of `S`**: `δ^{-3} (1 + log δ⁻¹)²` subspaces. The forms are taken over the Galois
closure of `α` in `ℂ` (`Real.subspaceBoundWith_three_of_mem`). -/
theorem subspaceBoundAt_three {α : ℝ} (hα : IsAlgebraic ℚ α) (S : Finset Nat.Primes) :
    SubspaceBoundAt α S 3 := by
  intro n hn hn4
  obtain ⟨E, hgal, hfd, hmem⟩ := exists_isGalois_mem hα
  have : NumberField E := { }
  exact ⟨_, zero_lt_one.trans_le (one_le_subspaceConst ..),
    subspaceBoundWith_three_of_mem E hmem S hn hn4⟩

/-- **The rational case of `Real.subspaceBoundWith_three_of_mem`**: for `α = q ∈ ℚ` the forms are
over `ℚ`, `d = 1`, and the height is `log max (|num q|, den q)`. -/
theorem subspaceBoundWith_three_ratCast (q : ℚ) (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    SubspaceBoundWith (q : ℝ) S 3 n
      (subspaceConst n 1 #S (log (mulHeight₁ q)) (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  have : NumberField (⊥ : IntermediateField ℚ ℂ) := { }
  have hq : (((q : ℝ) : ℂ)) ∈ (⊥ : IntermediateField ℚ ℂ) :=
    IntermediateField.mem_bot.2 ⟨q, by simp⟩
  have h := subspaceBoundWith_three_of_mem ⊥ hq S hn hn4
  have hβ : (⟨((q : ℝ) : ℂ), hq⟩ : (⊥ : IntermediateField ℚ ℂ)) =
      algebraMap ℚ (⊥ : IntermediateField ℚ ℂ) q := Subtype.ext (by simp)
  rwa [IntermediateField.finrank_bot, hβ, ← NumberField.mulHeight₁_pow_finrank,
    IntermediateField.finrank_bot, pow_one] at h

/-- **The case `α = 0`**: forms with integer coefficients. -/
theorem subspaceBoundWith_three_zero (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) :
    SubspaceBoundWith 0 S 3 n (subspaceConst n 1 #S 0 (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  have h := subspaceBoundWith_three_ratCast 0 S hn hn4
  rwa [Rat.cast_zero, mulHeight₁_zero, Real.log_one] at h

end Real
