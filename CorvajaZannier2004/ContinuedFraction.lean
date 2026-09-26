/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.Real.Irrational

-- Used only inside proofs.
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular

/-!
# Continued fractions of irrational numbers: complete quotients, periods, Serret's theorem

The continued fraction of an irrational `x` is read off the orbit of `x` under the Gauss map
`y ↦ 1 / fract y`: the complete quotients `xₙ` and the partial quotients `aₙ = ⌊xₙ⌋`, so that
`xₙ = aₙ + 1 / xₙ₊₁`. The period of the expansion is defined through Mathlib's
`GenContFract.of`, and computed through the complete quotients.

## Main definitions

* `Real.cfTail x n`: the `n`-th complete quotient of `x`.
* `Real.cfQuot x n`: the `n`-th partial quotient `⌊cfTail x n⌋`.
* `Real.cfPeriod x`: the length of the eventual period of the continued fraction of `x` (`0` if
  it is not eventually periodic), defined from `GenContFract.of x`.
* `Real.TailEquiv x y`: some complete quotient of `x` is one of `y`.

## Main results

* `Real.partDens_get?_of`: the partial denominators of `GenContFract.of x` are the `cfQuot x n`.
* `Real.eq_of_cfQuot_eq`: an irrational number is determined by its partial quotients.
* `Real.cfPeriod_eq_of_tailEquiv`: numbers with a common complete quotient have the same period.
* `Real.tailEquiv_mob`: **Serret's theorem** — `x` and `(a x + b) / (c x + d)`, `ad - bc = ±1`,
  have a common complete quotient.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, §3 ("Facts", p. 9);
G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, §10.11.
-/

@[expose] public section

open GenContFract Matrix
open scoped MatrixGroups

namespace Real

/-- The Gauss map `y ↦ 1 / fract y`. -/
noncomputable def gaussMap (y : ℝ) : ℝ := (Int.fract y)⁻¹

/-- The `n`-th complete quotient of the continued fraction of `x`. -/
noncomputable def cfTail (x : ℝ) (n : ℕ) : ℝ := gaussMap^[n] x

/-- The `n`-th partial quotient of the continued fraction of `x`. -/
noncomputable def cfQuot (x : ℝ) (n : ℕ) : ℤ := ⌊cfTail x n⌋

/-- **The length of the period of the continued fraction of `x`**: the least `r > 0` such that the
partial denominators of `GenContFract.of x` satisfy `aᵢ₊ᵣ = aᵢ` for all large `i`, and `0` if
there is none. -/
noncomputable def cfPeriod (x : ℝ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ ∃ N, ∀ i ≥ N,
    (GenContFract.of x).partDens.get? (i + r) = (GenContFract.of x).partDens.get? i}

/-- `r` is an eventual period of the partial quotients of `x`. -/
def IsCFPeriod (x : ℝ) (r : ℕ) : Prop :=
  0 < r ∧ ∃ N, ∀ i ≥ N, cfQuot x (i + r) = cfQuot x i

/-- Two numbers are tail equivalent if a complete quotient of the one is a complete quotient of
the other. -/
def TailEquiv (x y : ℝ) : Prop := ∃ m k, cfTail x m = cfTail y k

variable {x y z : ℝ}

@[simp] theorem cfTail_zero (x : ℝ) : cfTail x 0 = x := rfl

theorem cfTail_succ (x : ℝ) (n : ℕ) : cfTail x (n + 1) = (Int.fract (cfTail x n))⁻¹ :=
  Function.iterate_succ_apply' _ _ _

theorem cfTail_one (x : ℝ) : cfTail x 1 = (Int.fract x)⁻¹ := cfTail_succ x 0

theorem cfTail_add (x : ℝ) (m n : ℕ) : cfTail x (m + n) = cfTail (cfTail x m) n := by
  rw [cfTail, add_comm, Function.iterate_add_apply]
  rfl

theorem cfQuot_add (x : ℝ) (m n : ℕ) : cfQuot x (m + n) = cfQuot (cfTail x m) n := by
  rw [cfQuot, cfQuot, cfTail_add]

theorem _root_.Irrational.fract_ne_zero (h : Irrational y) : Int.fract y ≠ 0 := fun h0 ↦ by
  have := Int.floor_add_fract y
  rw [h0, add_zero] at this
  exact h.ne_int ⌊y⌋ this.symm

theorem _root_.Irrational.cfTail (h : Irrational x) (n : ℕ) : Irrational (cfTail x n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [cfTail_succ, Int.fract]
    exact (Irrational.sub_intCast ih _).inv

theorem one_lt_cfTail (h : Irrational x) {n : ℕ} (hn : 0 < n) : 1 < cfTail x n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, cfTail_succ]
  exact one_lt_inv₀ ((Int.fract_nonneg _).lt_of_ne' ((h.cfTail n).fract_ne_zero))
    |>.mpr (Int.fract_lt_one _)

theorem one_le_cfQuot (h : Irrational x) {n : ℕ} (hn : 0 < n) : 1 ≤ cfQuot x n :=
  Int.le_floor.mpr (by exact_mod_cast (one_lt_cfTail h hn).le)

/-- `xₙ = aₙ + 1 / xₙ₊₁`. -/
theorem cfTail_eq (x : ℝ) (n : ℕ) :
    cfTail x n = cfQuot x n + (cfTail x (n + 1))⁻¹ := by
  rw [cfTail_succ, inv_inv, cfQuot, Int.floor_add_fract]

/-- The partial denominators of Mathlib's `GenContFract.of x` are the partial quotients
`cfQuot x (n + 1)`. -/
theorem s_get?_of (h : Irrational x) (n : ℕ) :
    (GenContFract.of x).s.get? n = some ⟨1, (cfQuot x (n + 1) : ℝ)⟩ := by
  induction n generalizing x with
  | zero =>
    change (GenContFract.of x).s.head = _
    rw [of_s_head h.fract_ne_zero, cfQuot, cfTail_one]
  | succ n ih =>
    rw [of_s_succ, ← cfTail_one, ih (h.cfTail 1), ← cfQuot_add, add_comm 1 (n + 1)]

theorem partDens_get?_of (h : Irrational x) (n : ℕ) :
    (GenContFract.of x).partDens.get? n = some (cfQuot x (n + 1) : ℝ) := by
  rw [partDens, Stream'.Seq.map_get?, s_get?_of h]
  rfl

/-- **The two readings of the period agree.** -/
theorem mem_setOf_cfPeriod_iff (h : Irrational x) (r : ℕ) :
    (0 < r ∧ ∃ N, ∀ i ≥ N,
      (GenContFract.of x).partDens.get? (i + r) = (GenContFract.of x).partDens.get? i) ↔
      IsCFPeriod x r := by
  simp only [partDens_get?_of h, Option.some.injEq, Int.cast_inj, IsCFPeriod]
  refine and_congr_right fun _ ↦ ⟨fun ⟨N, hN⟩ ↦ ⟨N + 1, fun i hi ↦ ?_⟩,
    fun ⟨N, hN⟩ ↦ ⟨N, fun i hi ↦ ?_⟩⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have := hN (N + j) (Nat.le_add_right _ _)
    rwa [show N + j + r + 1 = N + 1 + j + r by ring, show N + j + 1 = N + 1 + j by ring] at this
  · have := hN (i + 1) (by omega)
    rwa [show i + 1 + r = i + r + 1 by ring] at this

theorem cfPeriod_eq_sInf (h : Irrational x) : cfPeriod x = sInf {r | IsCFPeriod x r} := by
  rw [cfPeriod]
  congr 1
  ext r
  exact mem_setOf_cfPeriod_iff h r

/-- **An irrational number is determined by its partial quotients**, by the convergence of its
continued fraction. -/
theorem eq_of_cfQuot_eq (hy : Irrational y) (hz : Irrational z)
    (h : ∀ n, cfQuot y n = cfQuot z n) : y = z := by
  have hof : GenContFract.of y = GenContFract.of z := by
    have hh : (GenContFract.of y).h = (GenContFract.of z).h := by
      rw [of_h_eq_floor, of_h_eq_floor]
      exact_mod_cast h 0
    have hs : (GenContFract.of y).s = (GenContFract.of z).s :=
      Stream'.Seq.ext fun n ↦ by rw [s_get?_of hy, s_get?_of hz, h]
    cases hY : GenContFract.of y
    cases hZ : GenContFract.of z
    rw [hY, hZ] at hh hs
    simp_all
  have hy' := of_convergence y
  rw [hof] at hy'
  exact tendsto_nhds_unique hy' (of_convergence z)

/-- **Eventual periodicity is periodicity of the complete quotients.** -/
theorem isCFPeriod_iff (h : Irrational x) (r : ℕ) :
    IsCFPeriod x r ↔ 0 < r ∧ ∃ N, cfTail x (N + r) = cfTail x N := by
  refine and_congr_right fun _ ↦ ⟨fun ⟨N, hN⟩ ↦ ⟨N, ?_⟩, fun ⟨N, hN⟩ ↦ ⟨N, fun i hi ↦ ?_⟩⟩
  · refine eq_of_cfQuot_eq (h.cfTail _) (h.cfTail _) fun n ↦ ?_
    rw [← cfQuot_add, ← cfQuot_add, show N + r + n = N + n + r by ring]
    exact hN _ (Nat.le_add_right _ _)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [show N + j + r = N + r + j by ring, cfQuot_add, hN, ← cfQuot_add]

/-! ### Tail equivalence -/

theorem TailEquiv.refl (x : ℝ) : TailEquiv x x := ⟨0, 0, rfl⟩

theorem TailEquiv.symm (h : TailEquiv x y) : TailEquiv y x :=
  let ⟨m, k, hmk⟩ := h
  ⟨k, m, hmk.symm⟩

theorem TailEquiv.trans (h₁ : TailEquiv x y) (h₂ : TailEquiv y z) : TailEquiv x z := by
  obtain ⟨m, k, h₁⟩ := h₁
  obtain ⟨m', k', h₂⟩ := h₂
  refine ⟨m + m', k' + k, ?_⟩
  rw [cfTail_add, h₁, ← cfTail_add, add_comm k m', cfTail_add, h₂, ← cfTail_add]

theorem tailEquiv_cfTail (x : ℝ) (n : ℕ) : TailEquiv (cfTail x n) x := ⟨0, n, rfl⟩

theorem IsCFPeriod.of_tailEquiv (h : TailEquiv x y) {r : ℕ} (hx : IsCFPeriod x r) :
    IsCFPeriod y r := by
  obtain ⟨m, k, hmk⟩ := h
  obtain ⟨hr, N, hN⟩ := hx
  refine ⟨hr, k + N, fun i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hq : ∀ l, cfQuot y (k + l) = cfQuot x (m + l) := fun l ↦ by
    rw [cfQuot_add, cfQuot_add, hmk]
  rw [show k + N + j + r = k + (N + j + r) by ring, show k + N + j = k + (N + j) by ring, hq, hq,
    show m + (N + j + r) = m + N + j + r by ring, show m + (N + j) = m + N + j by ring]
  exact hN _ (by omega)

/-- **Tail equivalent irrationals have the same period.** -/
theorem cfPeriod_eq_of_tailEquiv (hx : Irrational x) (hy : Irrational y) (h : TailEquiv x y) :
    cfPeriod x = cfPeriod y := by
  rw [cfPeriod_eq_sInf hx, cfPeriod_eq_sInf hy]
  congr 1
  ext r
  exact ⟨fun h' ↦ h'.of_tailEquiv h, fun h' ↦ h'.of_tailEquiv h.symm⟩

/-! ### Serret's theorem -/

theorem tailEquiv_add_one (x : ℝ) : TailEquiv (x + 1) x :=
  ⟨1, 1, by rw [cfTail_one, cfTail_one, Int.fract_add_one]⟩

theorem tailEquiv_add_intCast (x : ℝ) (n : ℤ) : TailEquiv (x + n) x :=
  ⟨1, 1, by rw [cfTail_one, cfTail_one, Int.fract_add_intCast]⟩

/-- `fract y = y - 1` for `1 < y < 2`. -/
private theorem fract_eq_sub_one {y : ℝ} (h1 : 1 < y) (h2 : y < 2) : Int.fract y = y - 1 :=
  Int.fract_eq_iff.mpr ⟨by linarith, by linarith, 1, by push_cast; ring⟩

private theorem fract_eq_self {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : Int.fract y = y :=
  Int.fract_eq_iff.mpr ⟨h0, h1, 0, by simp⟩

/-- **`-x` and `x` are tail equivalent.** -/
theorem tailEquiv_neg (hx : Irrational x) : TailEquiv (-x) x := by
  set f := Int.fract x with hf
  have hf0 : 0 < f := (Int.fract_nonneg x).lt_of_ne' hx.fract_ne_zero
  have hf1 : f < 1 := Int.fract_lt_one x
  have hneg : Int.fract (-x) = 1 - f := Int.fract_neg hx.fract_ne_zero
  have h1 : cfTail x 1 = f⁻¹ := cfTail_one x
  have h1' : cfTail (-x) 1 = (1 - f)⁻¹ := by rw [cfTail_one, hneg]
  have hx1 : 1 < cfTail x 1 := one_lt_cfTail hx one_pos
  have hne : cfTail x 1 ≠ 2 := fun h2 ↦ (hx.cfTail 1).ne_nat 2 (by rw [h2]; norm_num)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `a₁ = 1`: the second complete quotient of `-x` is `1 + x₂`
    have h2 : cfTail x 2 = (cfTail x 1 - 1)⁻¹ := by
      rw [cfTail_succ, fract_eq_sub_one hx1 hlt]
    have h2' : cfTail (-x) 1 = cfTail x 2 + 1 := by
      rw [h1', h2, h1]
      have h1f : (1 : ℝ) - f ≠ 0 := by linarith
      have e : f⁻¹ - 1 = (1 - f) / f := by field_simp
      rw [e, inv_div]
      field_simp
      ring
    refine ⟨2, 3, ?_⟩
    rw [cfTail_succ, h2', Int.fract_add_one, ← cfTail_succ]
  · -- `a₁ ≥ 2`: the third complete quotient of `-x` is `x₂`
    have hf2 : f < 1 / 2 := by
      rw [h1] at hgt
      have := (inv_lt_inv₀ (a := f⁻¹) (b := 2) (inv_pos.mpr hf0) (by norm_num)).mpr hgt
      rw [inv_inv] at this
      norm_num at this ⊢
      exact this
    have hlt2 : (1 - f)⁻¹ < 2 :=
      (inv_lt_comm₀ (a := 1 - f) (b := 2) (by linarith) (by norm_num)).mpr (by linarith)
    have hgt1 : 1 < (1 - f)⁻¹ := (one_lt_inv₀ (a := 1 - f) (by linarith)).mpr (by linarith)
    have h2' : cfTail (-x) 2 = cfTail x 1 - 1 := by
      rw [cfTail_succ, h1', fract_eq_sub_one hgt1 hlt2, h1]
      have h1f : (1 : ℝ) - f ≠ 0 := by linarith
      have e : (1 - f)⁻¹ - 1 = f / (1 - f) := by field_simp; ring
      rw [e, inv_div]
      field_simp
    refine ⟨3, 2, ?_⟩
    rw [cfTail_succ, h2', Int.fract_sub_one, ← cfTail_succ]

/-- **`1 / x` and `x` are tail equivalent.** -/
theorem tailEquiv_inv (hx : Irrational x) : TailEquiv x⁻¹ x := by
  have hpos : ∀ {y : ℝ}, Irrational y → 0 < y → TailEquiv y⁻¹ y := by
    intro y hy hy0
    have hne : y ≠ 1 := fun h1 ↦ hy.ne_nat 1 (by rw [h1]; norm_num)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨0, 1, by rw [cfTail_zero, cfTail_one, fract_eq_self hy0.le hlt]⟩
    · refine ⟨1, 0, ?_⟩
      rw [cfTail_one, fract_eq_self (inv_nonneg.mpr hy0.le) (inv_lt_one_of_one_lt₀ hgt), inv_inv,
        cfTail_zero]
  rcases lt_or_gt_of_ne (hx.ne_nat 0) with hneg | hpos'
  · have hx' : Irrational (-x) := hx.neg
    have h := hpos hx' (by simpa using hneg)
    rw [inv_neg] at h
    exact (tailEquiv_neg hx.inv).symm.trans (h.trans (tailEquiv_neg hx))
  · exact hpos hx (by exact_mod_cast hpos')

/-- The Möbius action of `SL(2, ℤ)` on the reals. -/
noncomputable def mob (g : SL(2, ℤ)) (x : ℝ) : ℝ :=
  ((g 0 0 : ℤ) * x + (g 0 1 : ℤ)) / ((g 1 0 : ℤ) * x + (g 1 1 : ℤ))

theorem mob_denom_ne_zero (g : SL(2, ℤ)) (hx : Irrational x) :
    ((g 1 0 : ℤ) : ℝ) * x + (g 1 1 : ℤ) ≠ 0 := by
  intro h0
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  by_cases hc : g 1 0 = 0
  · rw [hc, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h0
    rw [hc, h0] at hdet
    simp at hdet
  · have hc' : ((g 1 0 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have : x = -((g 1 1 : ℤ) : ℝ) / (g 1 0 : ℤ) := by
      field_simp
      linarith
    exact hx ⟨((-(g 1 1) : ℤ) : ℚ) / ((g 1 0 : ℤ) : ℚ), by rw [this]; push_cast; ring⟩

theorem mob_mul (g h : SL(2, ℤ)) (hx : Irrational x) :
    mob (g * h) x = mob g (mob h x) := by
  have hh := mob_denom_ne_zero h hx
  have hgh := mob_denom_ne_zero (g * h) hx
  have e : ∀ i j, (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := fun i j ↦ by
    rw [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  rw [e, e] at hgh
  rw [mob, mob, mob, e, e, e, e, mul_div_assoc', div_add' _ _ _ hh, mul_div_assoc',
    div_add' _ _ _ hh, div_div_div_cancel_right₀ hh]
  push_cast
  congr 1 <;> ring

theorem mob_one (x : ℝ) : mob (1 : SL(2, ℤ)) x = x := by
  simp [mob]

theorem _root_.Irrational.mob (g : SL(2, ℤ)) (hx : Irrational x) :
    Irrational (Real.mob g x) := by
  rintro ⟨q, hq⟩
  have hinv : Real.mob g⁻¹ (Real.mob g x) = x := by
    rw [← mob_mul _ _ hx, inv_mul_cancel, mob_one]
  rw [← hq] at hinv
  apply hx
  refine ⟨(((g⁻¹ 0 0 : ℤ) : ℚ) * q + (g⁻¹ 0 1 : ℤ)) / (((g⁻¹ 1 0 : ℤ) : ℚ) * q + (g⁻¹ 1 1 : ℤ)),
    ?_⟩
  rw [← hinv, Real.mob]
  push_cast
  rfl

/-- **Serret's theorem**: `x` and `(a x + b) / (c x + d)` have a common complete quotient, for
`[[a, b], [c, d]] ∈ SL(2, ℤ)`. -/
theorem tailEquiv_mob (g : SL(2, ℤ)) (hx : Irrational x) : TailEquiv (mob g x) x := by
  have hmem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g
  induction hmem using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with rfl | rfl
    · have : mob ModularGroup.S x = -x⁻¹ := by
        simp [Real.mob, ModularGroup.S, neg_div]
      rw [this]
      exact (tailEquiv_neg hx.inv).trans (tailEquiv_inv hx)
    · have : mob ModularGroup.T x = x + 1 := by
        simp [Real.mob, ModularGroup.T]
      rw [this]
      exact tailEquiv_add_one x
  | one => rw [mob_one]; exact TailEquiv.refl x
  | mul g h _ _ hg hh =>
    rw [mob_mul g h hx]
    exact (hg (hx.mob h)).trans (hh hx)
  | inv g _ hg =>
    have := hg (hx.mob g⁻¹)
    rw [← mob_mul _ _ hx, mul_inv_cancel, mob_one] at this
    exact this.symm

/-- **Serret's theorem**, for `ad - bc = ±1`. -/
theorem tailEquiv_of_det {a b c d : ℤ} (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (hx : Irrational x) : TailEquiv ((a * x + b) / (c * x + d)) x := by
  rcases hdet with h | h
  · let g : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [det_fin_two_of]; exact h⟩
    exact tailEquiv_mob g hx
  · let g : SL(2, ℤ) := ⟨!![-a, b; -c, d], by rw [det_fin_two_of]; linarith⟩
    have hmob : mob g (-x) = (a * x + b) / (c * x + d) := by
      simp [Real.mob, g]
    rw [← hmob]
    exact (tailEquiv_mob g hx.neg).trans (tailEquiv_neg hx)

/-! ### Convergents -/

/-- The numerators of the convergents, shifted by two: `cfNum x (n + 2) = pₙ`, with `p₋₂ = 0`,
`p₋₁ = 1` and `pₙ = aₙ pₙ₋₁ + pₙ₋₂`. -/
noncomputable def cfNum (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => cfQuot x n * cfNum x (n + 1) + cfNum x n

/-- The denominators of the convergents, shifted by two: `cfDen x (n + 2) = qₙ`, with `q₋₂ = 1`,
`q₋₁ = 0` and `qₙ = aₙ qₙ₋₁ + qₙ₋₂` (formula (4.2)). -/
noncomputable def cfDen (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => cfQuot x n * cfDen x (n + 1) + cfDen x n

theorem cfNum_succ_succ (x : ℝ) (n : ℕ) :
    cfNum x (n + 2) = cfQuot x n * cfNum x (n + 1) + cfNum x n := rfl

theorem cfDen_succ_succ (x : ℝ) (n : ℕ) :
    cfDen x (n + 2) = cfQuot x n * cfDen x (n + 1) + cfDen x n := rfl

/-- The determinant of consecutive convergents. -/
theorem cfNum_mul_cfDen_sub (x : ℝ) (n : ℕ) :
    cfNum x (n + 1) * cfDen x n - cfNum x n * cfDen x (n + 1) = (-1) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cfNum_succ_succ, cfDen_succ_succ, pow_succ, ← ih]
    ring

theorem cfDen_nonneg (hx : Irrational x) (n : ℕ) : 0 ≤ cfDen x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact zero_le_one
    | 1 => exact le_rfl
    | 2 => rw [cfDen_succ_succ]; simp [cfDen]
    | n + 3 =>
      rw [cfDen_succ_succ]
      exact add_nonneg (mul_nonneg (zero_le_one.trans (one_le_cfQuot hx (by omega)))
        (ih _ (by omega))) (ih _ (by omega))

theorem cfDen_le_cfDen_succ (hx : Irrational x) {n : ℕ} (hn : 1 ≤ n) :
    cfDen x n ≤ cfDen x (n + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases n with _ | n
  · simp [cfDen]
  · rw [show 1 + (n + 1) + 1 = n + 1 + 2 by ring, cfDen_succ_succ, show 1 + (n + 1) = n + 2 by ring]
    have h1 := one_le_cfQuot hx (n := n + 1) (by omega)
    have h2 := cfDen_nonneg hx (n + 2)
    have h3 := cfDen_nonneg hx (n + 1)
    nlinarith

theorem one_le_cfDen (hx : Irrational x) {n : ℕ} (hn : 2 ≤ n) : 1 ≤ cfDen x n := by
  induction n, hn using Nat.le_induction with
  | base => simp [cfDen]
  | succ n hn ih => exact ih.trans (cfDen_le_cfDen_succ hx (by omega))

/-- **The convergent identity** `x = (pₙ₋₁ xₙ + pₙ₋₂) / (qₙ₋₁ xₙ + qₙ₋₂)`. -/
theorem eq_cfNum_div_cfDen (hx : Irrational x) (n : ℕ) :
    x = (cfNum x (n + 1) * cfTail x n + cfNum x n) /
      (cfDen x (n + 1) * cfTail x n + cfDen x n) := by
  induction n with
  | zero => simp [cfNum, cfDen]
  | succ n ih =>
    have hy : cfTail x (n + 1) ≠ 0 := (zero_lt_one.trans (one_lt_cfTail hx n.succ_pos)).ne'
    change x = (cfNum x (n + 2) * cfTail x (n + 1) + cfNum x (n + 1)) /
      (cfDen x (n + 2) * cfTail x (n + 1) + cfDen x (n + 1))
    rw [cfNum_succ_succ, cfDen_succ_succ]
    refine ih.trans ?_
    rw [cfTail_eq x n]
    set y := cfTail x (n + 1)
    push_cast
    have e1 : (cfNum x (n + 1) : ℝ) * (cfQuot x n + y⁻¹) + cfNum x n =
        ((cfQuot x n * cfNum x (n + 1) + cfNum x n) * y + cfNum x (n + 1)) / y := by
      field_simp
      ring
    have e2 : (cfDen x (n + 1) : ℝ) * (cfQuot x n + y⁻¹) + cfDen x n =
        ((cfQuot x n * cfDen x (n + 1) + cfDen x n) * y + cfDen x (n + 1)) / y := by
      field_simp
      ring
    rw [e1, e2, div_div_div_cancel_right₀ hy]

theorem cfDen_mul_cfTail_add_pos (hx : Irrational x) (n : ℕ) :
    0 < (cfDen x (n + 1) : ℝ) * cfTail x n + cfDen x n := by
  rcases n with _ | n
  · simp [cfDen]
  · have h1 : (1 : ℝ) ≤ cfDen x (n + 2) := by exact_mod_cast one_le_cfDen hx (by omega)
    have h2 : (0 : ℝ) ≤ cfDen x (n + 1) := by exact_mod_cast cfDen_nonneg hx _
    have h3 := one_lt_cfTail hx (n := n + 1) n.succ_pos
    nlinarith

/-- **The error of a convergent**: `|x - pₙ/qₙ| = 1 / (qₙ (qₙ xₙ₊₁ + qₙ₋₁))`. -/
theorem abs_sub_cfNum_div_cfDen (hx : Irrational x) (n : ℕ) :
    |x - cfNum x (n + 2) / cfDen x (n + 2)| =
      1 / (cfDen x (n + 2) * (cfDen x (n + 2) * cfTail x (n + 1) + cfDen x (n + 1))) := by
  have hQ : (0 : ℝ) < cfDen x (n + 2) := by exact_mod_cast one_le_cfDen hx (le_add_self)
  have hD := cfDen_mul_cfTail_add_pos hx (n + 1)
  have hdet := cfNum_mul_cfDen_sub x (n + 1)
  have hdet' : ((cfNum x (n + 2) : ℝ) * cfDen x (n + 1) - cfNum x (n + 1) * cfDen x (n + 2)) =
      (-1) ^ (n + 1) := by exact_mod_cast hdet
  have hxe := eq_cfNum_div_cfDen hx (n + 1)
  have e : x - cfNum x (n + 2) / cfDen x (n + 2) =
      (cfNum x (n + 2) * cfTail x (n + 1) + cfNum x (n + 1)) /
        (cfDen x (n + 2) * cfTail x (n + 1) + cfDen x (n + 1)) -
        cfNum x (n + 2) / cfDen x (n + 2) := by
    rw [← hxe]
  rw [e, div_sub_div _ _ hD.ne' hQ.ne']
  have hnum : (cfNum x (n + 2) * cfTail x (n + 1) + cfNum x (n + 1)) * (cfDen x (n + 2) : ℝ) -
      (cfDen x (n + 2) * cfTail x (n + 1) + cfDen x (n + 1)) * cfNum x (n + 2) =
      -(-1) ^ (n + 1) := by
    rw [← hdet']
    ring
  rw [hnum, abs_div, abs_neg, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hD hQ), mul_comm]

/-- **Formula (4.1)**: `|pₙ/qₙ - x| ≤ 1 / (qₙ² aₙ₊₁)`. -/
theorem abs_sub_cfNum_div_cfDen_le (hx : Irrational x) (n : ℕ) :
    |x - cfNum x (n + 2) / cfDen x (n + 2)| ≤
      1 / ((cfDen x (n + 2) : ℝ) ^ 2 * cfQuot x (n + 1)) := by
  rw [abs_sub_cfNum_div_cfDen hx]
  have hQ : (0 : ℝ) < cfDen x (n + 2) := by exact_mod_cast one_le_cfDen hx (le_add_self)
  have ha : (1 : ℝ) ≤ cfQuot x (n + 1) := by exact_mod_cast one_le_cfQuot hx n.succ_pos
  have hy : (cfQuot x (n + 1) : ℝ) ≤ cfTail x (n + 1) := Int.floor_le _
  have h0 : (0 : ℝ) ≤ cfDen x (n + 1) := by exact_mod_cast cfDen_nonneg hx _
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

end Real
