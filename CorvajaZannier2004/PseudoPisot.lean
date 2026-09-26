/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Pisot and pseudo-Pisot numbers

Corvaja and Zannier call a real algebraic number `α` **pseudo-Pisot** if `|α| > 1`, all its
conjugates other than `α` have modulus `< 1`, and its trace is a rational integer. The algebraic
integers among them are the Pisot numbers up to sign. Their Main Theorem says that `δ q u` has
small distance to the nearest integer only when it is pseudo-Pisot, apart from finitely many
exceptions.

Conjugates are the complex roots of `minpoly ℚ α`, and the trace is their sum.

## Main definitions

* `IsPseudoPisot`: the predicate of Corvaja–Zannier, p. 2.
* `IsPisot`: a real algebraic integer `> 1` whose other conjugates lie in the open unit disc.

## Main results

* `aroots_minpoly_ratCast_mul`: the conjugates of `r x`, for `r ∈ ℚˣ`, are `r` times those of
  `x`.
* `exists_conjugate_ne`: an irrational algebraic number has a nonzero conjugate other than itself.
* `not_isPseudoPisot_mul_ratCast`: an irrational algebraic `x` times a large rational is never
  pseudo-Pisot.
* `isPseudoPisot_ratCast_iff`: over `ℚ`, pseudo-Pisot means `|v| > 1` and `v ∈ ℤ`.

## Implementation notes

⚠ **Conjugates are a multiset of complex numbers, and `α` is compared through the cast.** The
condition "every conjugate other than `α`" is `z ≠ (α : ℂ)`. Since `minpoly ℚ α` is separable,
`α` occurs once, so this excludes exactly one root.

⚠ **A pseudo-Pisot number need not be an algebraic integer**, which is the point of the
definition: `δ q u` with `δ`, `u` arbitrary algebraic numbers is well approximated by its trace
exactly when it is pseudo-Pisot.

## References

P. Corvaja and U. Zannier, *On the rational approximations to the powers of an algebraic number:
solution of two problems of Mahler and Mendès France*, Acta Math. **193** (2004), 175–191,
Definition on p. 2. Ported from `CITED/CorvajaZannierAlgebraic.lean` of the author's `lean-code`
corpus.
-/

@[expose] public section

open Polynomial

/-- **Pseudo-Pisot** (Corvaja–Zannier, p. 2): `|α| > 1`, `α` is algebraic, every conjugate of `α`
other than `α` itself has modulus `< 1`, and the trace, the sum of the conjugates, is a rational
integer. -/
def IsPseudoPisot (α : ℝ) : Prop :=
  1 < |α| ∧ IsAlgebraic ℚ α ∧ (∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ (α : ℂ) → ‖z‖ < 1) ∧
    ∃ n : ℤ, ((minpoly ℚ α).aroots ℂ).sum = n

/-- **A Pisot number**: a real algebraic integer `α > 1` whose conjugates other than `α` lie in
the open unit disc. Rational integers `> 1` are Pisot numbers. -/
def IsPisot (α : ℝ) : Prop :=
  1 < α ∧ IsIntegral ℤ α ∧ ∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ (α : ℂ) → ‖z‖ < 1

/-- The conjugates of `r x`, for rational `r ≠ 0`, are `r` times the conjugates of `x`, because
`minpoly ℚ (r • x) = (minpoly ℚ x).scaleRoots r`. -/
theorem aroots_minpoly_ratCast_mul {x : ℝ} (hx : IsAlgebraic ℚ x) {r : ℚ} (hr : r ≠ 0) :
    (minpoly ℚ ((r : ℝ) * x)).aroots ℂ = ((minpoly ℚ x).aroots ℂ).map fun z ↦ (r : ℂ) * z := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  have hsmul : (r : ℝ) * x = r • x := (Rat.smul_def r x).symm
  have halg : (algebraMap ℚ ℂ) r = (r : ℂ) := eq_ratCast _ r
  rw [hsmul, IsIntegrallyClosed.minpoly_smul hr hint]
  unfold Polynomial.aroots
  rw [Polynomial.map_scaleRoots _ _ _ (by rw [(minpoly.monic hint).leadingCoeff]; simp), halg]
  exact Polynomial.roots_scaleRoots _
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hr : ((r : ℚ) : ℂ) ≠ 0))

/-- The number itself is one of its conjugates. -/
theorem mem_aroots_minpoly {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (x : ℂ) ∈ (minpoly ℚ x).aroots ℂ := by
  rw [Polynomial.mem_aroots]
  refine ⟨minpoly.ne_zero hx.isIntegral, ?_⟩
  have h := Polynomial.aeval_algebraMap_apply ℂ x (minpoly ℚ x)
  rw [minpoly.aeval, map_zero] at h
  simpa using h

/-- An **irrational** algebraic real number has a conjugate other than itself, and that conjugate
is nonzero: the minimal polynomial has degree at least `2`, is separable, and has a nonzero
constant coefficient. -/
theorem exists_conjugate_ne {x : ℝ} (hx : IsAlgebraic ℚ x) (hirr : Irrational x) :
    ∃ z ∈ (minpoly ℚ x).aroots ℂ, z ≠ (x : ℂ) ∧ z ≠ 0 := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  -- degree `≥ 2`: degree `1` would make `x` rational
  have hdeg : 2 ≤ (minpoly ℚ x).natDegree := by
    by_contra h
    push Not at h
    have h1 : (minpoly ℚ x).natDegree = 1 := by
      have := minpoly.natDegree_pos hint
      omega
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    rw [eq_ratCast (algebraMap ℚ ℝ) q] at hq
    exact hirr ⟨q, hq⟩
  have hmem := mem_aroots_minpoly hx
  have hnodup : ((minpoly ℚ x).aroots ℂ).Nodup :=
    Polynomial.nodup_roots ((minpoly.irreducible hint).separable.map)
  have hcard : ((minpoly ℚ x).aroots ℂ).card = (minpoly ℚ x).natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree
  have herase : 0 < (((minpoly ℚ x).aroots ℂ).erase (x : ℂ)).card := by
    have hce : (((minpoly ℚ x).aroots ℂ).erase (x : ℂ)).card + 1 =
        ((minpoly ℚ x).aroots ℂ).card := by
      conv_rhs => rw [← Multiset.cons_erase hmem]
      rw [Multiset.card_cons]
    omega
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp herase
  have hzmem : z ∈ (minpoly ℚ x).aroots ℂ := Multiset.mem_of_mem_erase hz
  refine ⟨z, hzmem, (hnodup.mem_erase_iff.mp hz).1, ?_⟩
  -- a zero root would kill the constant coefficient
  rintro rfl
  have hc0 : (minpoly ℚ x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hirr.ne_zero
  rw [Polynomial.mem_aroots] at hzmem
  apply hc0
  have h := hzmem.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero,
    eq_ratCast (algebraMap ℚ ℂ) ((minpoly ℚ x).coeff 0)] at h
  exact_mod_cast h

/-- **An irrational algebraic number times a large rational is never pseudo-Pisot**: the
conjugate `r z`, with `z ≠ x` a conjugate of `x`, leaves the unit disc once `r ≥ |z|⁻¹`. -/
theorem not_isPseudoPisot_mul_ratCast {x : ℝ} (hx : IsAlgebraic ℚ x) (hirr : Irrational x) :
    ∃ A : ℚ, 0 < A ∧ ∀ r : ℚ, A ≤ r → ¬ IsPseudoPisot (x * r) := by
  obtain ⟨z, hzmem, hzx, hz0⟩ := exists_conjugate_ne hx hirr
  obtain ⟨A, hA⟩ := exists_rat_gt (max 1 ‖z‖⁻¹)
  have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hAz : ‖z‖⁻¹ < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
  have hA0 : (0 : ℚ) < A := by exact_mod_cast zero_lt_one.trans hA1
  refine ⟨A, hA0, fun r hAr hPP ↦ ?_⟩
  have hrpos : (0 : ℚ) < r := lt_of_lt_of_le hA0 hAr
  have hr0 : r ≠ 0 := hrpos.ne'
  obtain ⟨-, -, hconj, -⟩ := hPP
  -- the scaled conjugate is a conjugate of the scaled number …
  have hmem' : (r : ℂ) * z ∈ (minpoly ℚ (x * r)).aroots ℂ := by
    rw [mul_comm x (r : ℝ), aroots_minpoly_ratCast_mul hx hr0]
    exact Multiset.mem_map_of_mem _ hzmem
  -- … distinct from it …
  have hne' : (r : ℂ) * z ≠ ((x * r : ℝ) : ℂ) := by
    intro h
    have hrC : ((r : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    exact hzx (mul_left_cancel₀ hrC (h.trans (by push_cast; ring)))
  -- … and outside the unit disc
  have hbig : (1 : ℝ) ≤ ‖(r : ℂ) * z‖ := by
    rw [norm_mul]
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hrA : ‖z‖⁻¹ ≤ (r : ℝ) := le_trans hAz.le (by exact_mod_cast hAr)
    have hnormr : ‖((r : ℚ) : ℂ)‖ = (r : ℝ) := by
      rw [show ((r : ℚ) : ℂ) = ((r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by exact_mod_cast hrpos)]
    rw [hnormr]
    calc (1 : ℝ) = ‖z‖⁻¹ * ‖z‖ := (inv_mul_cancel₀ hnz.ne').symm
      _ ≤ (r : ℝ) * ‖z‖ := mul_le_mul_of_nonneg_right hrA hnz.le
  exact absurd (hconj _ hmem' hne') (not_lt.mpr hbig)

/-- The conjugates of a rational number are that number alone. -/
theorem aroots_minpoly_ratCast (v : ℚ) : (minpoly ℚ ((v : ℚ) : ℝ)).aroots ℂ = {(v : ℂ)} := by
  have hminp : minpoly ℚ ((v : ℚ) : ℝ) = X - C v := by
    rw [show ((v : ℚ) : ℝ) = algebraMap ℚ ℝ v from (eq_ratCast (algebraMap ℚ ℝ) v).symm]
    exact minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℝ).injective
  rw [hminp]
  have : (X - C v).aroots ℂ = (X - C (v : ℂ)).roots := by
    unfold Polynomial.aroots
    congr 1
    simp
  rw [this, Polynomial.roots_X_sub_C]

/-- **Over `ℚ`, pseudo-Pisot means `|v| > 1` and `v ∈ ℤ`**: the conjugate condition is vacuous
and the trace of a rational number is the number itself. -/
theorem isPseudoPisot_ratCast_iff (v : ℚ) :
    IsPseudoPisot (v : ℝ) ↔ 1 < |v| ∧ ∃ n : ℤ, v = n := by
  have haroots := aroots_minpoly_ratCast v
  constructor
  · rintro ⟨habs, -, -, n, hsum⟩
    refine ⟨by exact_mod_cast habs, n, ?_⟩
    rw [haroots, Multiset.sum_singleton] at hsum
    exact_mod_cast hsum
  · rintro ⟨habs, n, hn⟩
    have halg : IsAlgebraic ℚ ((v : ℚ) : ℝ) := by
      rw [show ((v : ℚ) : ℝ) = algebraMap ℚ ℝ v from (eq_ratCast (algebraMap ℚ ℝ) v).symm]
      exact isAlgebraic_algebraMap v
    refine ⟨by exact_mod_cast habs, halg, fun z hz hzne ↦ ?_, n, ?_⟩
    · rw [haroots, Multiset.mem_singleton] at hz
      exact absurd (by rw [hz]; push_cast; ring) hzne
    · rw [haroots, Multiset.sum_singleton, hn]
      push_cast
      ring

/-- The trace of an algebraic integer is a rational integer. -/
theorem exists_intCast_eq_sum_aroots {α : ℝ} (hα : IsIntegral ℤ α) :
    ∃ n : ℤ, ((minpoly ℚ α).aroots ℂ).sum = n := by
  have hmin : minpoly ℚ α = (minpoly ℤ α).map (Int.castRingHom ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hα
  have hsplit : ((minpoly ℤ α).map (algebraMap ℤ ℂ)).Splits :=
    IsAlgClosed.splits _
  refine ⟨-(minpoly ℤ α).nextCoeff, ?_⟩
  have hmon : ((minpoly ℤ α).map (algebraMap ℤ ℂ)).Monic := (minpoly.monic hα).map _
  have haroots : (minpoly ℚ α).aroots ℂ = (minpoly ℤ α).aroots ℂ := by
    rw [hmin]
    unfold Polynomial.aroots
    rw [Polynomial.map_map]
    rfl
  rw [haroots]
  unfold Polynomial.aroots
  have h := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hmon
  rw [Polynomial.nextCoeff_map (algebraMap ℤ ℂ).injective_int] at h
  rw [eq_neg_iff_add_eq_zero.mp h |> eq_neg_of_add_eq_zero_right]
  simp

/-- **A Pisot number is pseudo-Pisot.** -/
theorem IsPisot.isPseudoPisot {α : ℝ} (h : IsPisot α) : IsPseudoPisot α := by
  obtain ⟨h1, hint, hconj⟩ := h
  refine ⟨by rwa [abs_of_pos (zero_lt_one.trans h1)], ?_, hconj,
    exists_intCast_eq_sum_aroots hint⟩
  exact (hint.tower_top (A := ℚ)).isAlgebraic
