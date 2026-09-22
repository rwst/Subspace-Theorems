/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BinaryForm
public import DiophantineApproximation.RothRational

/-!
# Thue's equation

**Thue's theorem** (Thue 1909). Let `G ∈ ℤ[X, Y]` be homogeneous with at least three pairwise
non-proportional linear factors over `ℂ`, and let `m ≠ 0`. Then `G(x, y) = m` has only finitely
many solutions `(x, y) ∈ ℤ²`. It is the first Diophantine equation the roadmap solves, and the
test that Roth's theorem over `ℚ` — the classical case of Layer 3.3 — is usable as stated.

The route is the book's direct one. Write `G = g.homogenize d` (`DiophantineApproximation/
BinaryForm.lean`). If `Y` divides `G`, the equation forces `y ∣ m` and nothing more is needed.
Otherwise, for `y ≠ 0`,

```text
|m| = |G(x, y)| = |a| · |y| ^ d · ∏ r, ‖x / y - r‖ ^ μ(r)
```

over the distinct complex roots `r` of `g`. Once `|y|` is large, `x / y` is within `δ / 2` of
exactly one root `r` and at least `δ / 2` from the others, `δ` the least distance between two
roots, and the identity leaves

```text
‖x / y - r‖ ^ μ(r) · |y| ^ d ≤ C,
```

which puts `(x, y)` in the exceptional set of `r`. There are finitely many roots, and each
exceptional set is finite.

## Main results

* `Real.finite_setOf_pow_abs_sub_div_mul_pow_le`: Roth's theorem for pairs of integers,
  `|ξ - x / y| ^ μ |y| ^ e ≤ C` for finitely many `(x, y)` when `e > 2 μ`.
* `Complex.finite_setOf_norm_div_sub_pow_mul_pow_le`: the exceptional set of one algebraic
  target is finite, whatever kind of number the target is.
* `Polynomial.finite_setOf_eval_homogenize_eq`: Thue's theorem for `g.homogenize d`, with the
  hypothesis counted on the roots of `g`.
* `MvPolynomial.IsHomogeneous.finite_setOf_eval_eq`: **Thue's theorem**, with the roadmap's
  hypothesis literally — three linear forms, pairwise non-proportional, each dividing `G` over
  `ℂ`.

## Implementation notes

⚠ **Only Roth's theorem over `ℚ` at the real place is used.** The input is
`Real.finite_setOf_min_one_abs_sub_le`, Layer 3.3's classical case; no finite place and no number
field beyond `ℚ⟮ξ⟯` appears. So 3.6 is the acceptance test of the one-place rational form of
Roth's theorem, not of Ridout's — that was 3.5.

⚠ **The nearest root decides the case, and two of the three cases need no approximation
theory.** A non-real root is at distance at least `|Im r|` from every real `x / y`. A rational
root `c` has `|x / y - c| ≥ 1 / (c.den |y|)` unless `x / y = c`, and `x / y = c` makes
`G(x, y) = 0`. Only an irrational real nearest root sends the argument to Roth's theorem.

⚠ **This is not the book's reduction, and the difference is the multiplicities.**
Bombieri–Gubler first factor `G` into irreducible forms over `ℤ`, change coordinates so that
`Y ∤ G`, and use the box principle over the divisors of `m` to show that only one irreducible
factor can carry infinitely many solutions; the approximation argument then meets a separable
form only. Here it is run on `G` directly, which avoids the factorization in `ℤ[X, Y]` and the
change of coordinates, and pays with the exponent: at a nearest root of multiplicity `μ` it is
`d / μ`, not `d`. For an irrational root that is still above `2`
(`Polynomial.two_mul_count_roots_lt_natDegree`). For a rational root it can be exactly `2` —
`X ^ 2 (X ^ 2 - 2 Y ^ 2)`, the root `0`, `μ = 2`, `d = 4` — where Roth's theorem says nothing,
and Liouville's inequality with exponent `1`, which needs only `μ < d`, takes its place.

⚠ **The line at infinity costs nothing**, and replaces the book's change of coordinates. If
`Y ∣ G` then `y ∣ G(x, y) = m`, so `|y| ≤ |m|`, and `|x|` is bounded in terms of `|y|` by the size
of the roots alone. In that case the hypothesis "three linear factors" is only ever used to know
that `g` is not constant.

⚠ **What the proof uses is three zeros, not three factors.** A linear form dividing `G` over `ℂ`
vanishes at one point of `ℙ¹(ℂ)`, and non-proportional forms vanish at different points. The
statement asks for the factors because the roadmap does; the converse — a zero gives a factor —
is true and is not needed.

⚠ **`m ≠ 0` and "three" are both sharp**, and the acceptance criteria record it: Pell's equation
`x ^ 2 - 2 y ^ 2 = 1` has infinitely many solutions for a form with two linear factors, and
`x ^ 3 - x y ^ 2 = 0` has the whole line `x = 0` for a form with three. `m ≠ 0` is needed exactly
because a rational linear factor has infinitely many integer zeros.

⚠ **Nothing here is effective.** The solutions are finitely many and no bound on their size is
asserted or available: each exceptional set is finite because Roth's is, and Roth's theorem gives
no bound on the heights of its exceptions.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.2.1; A. Thue, *Über Annäherungswerte algebraischer Zahlen*, J. reine angew. Math. 135
(1909), 284–305.

This is part of Layer 3.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Polynomial

/-- A box in `ℤ²` is finite. -/
private theorem finite_setOf_abs_le (X Y : ℝ) :
    {z : ℤ × ℤ | |(z.1 : ℝ)| ≤ X ∧ |(z.2 : ℝ)| ≤ Y}.Finite := by
  refine ((Set.finite_Icc (-⌈X⌉) ⌈X⌉).prod (Set.finite_Icc (-⌈Y⌉) ⌈Y⌉)).subset ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  have hx' : |x| ≤ ⌈X⌉ := by
    have : ((|x| : ℤ) : ℝ) ≤ ⌈X⌉ := by rw [Int.cast_abs]; exact hx.trans (Int.le_ceil X)
    exact_mod_cast this
  have hy' : |y| ≤ ⌈Y⌉ := by
    have : ((|y| : ℤ) : ℝ) ≤ ⌈Y⌉ := by rw [Int.cast_abs]; exact hy.trans (Int.le_ceil Y)
    exact_mod_cast this
  exact ⟨abs_le.mp hx', abs_le.mp hy'⟩

/-- Reducing `x / y` does not increase its naive height, for any nonzero integer `y`; the
negative-denominator companion of `Rat.max_num_den_le_of_div`. -/
theorem Rat.max_num_den_le_of_div_intCast {x y : ℤ} (hy : y ≠ 0) :
    max ((x : ℚ) / y).num.natAbs ((x : ℚ) / y).den ≤ max x.natAbs y.natAbs := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have hq : (x : ℚ) / y = ((-x : ℤ) : ℚ) / ((y.natAbs : ℕ) : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      push_cast
      rw [neg_div_neg_eq]
    rw [hq]
    have := Rat.max_num_den_le_of_div (m := -x) (Int.natAbs_pos.mpr hy)
    rwa [Int.natAbs_neg] at this
  · have hq : (x : ℚ) / y = (x : ℚ) / ((y.natAbs : ℕ) : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    rw [hq]
    exact Rat.max_num_den_le_of_div (Int.natAbs_pos.mpr hy)

/-- A nonzero integer has absolute value at least `1` in `ℝ`. -/
private theorem one_le_abs_intCast {y : ℤ} (hy : y ≠ 0) : (1 : ℝ) ≤ |(y : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hy

/-- `t ^ μ ≤ K` with `μ ≠ 0` gives `t ≤ max 1 K`: a power bounds its base once the base is
at least `1`. -/
private theorem le_max_one_of_pow_le {t K : ℝ} {μ : ℕ} (hμ : μ ≠ 0) (h : t ^ μ ≤ K) :
    t ≤ max 1 K := by
  by_contra hcon
  push Not at hcon
  have h1 : 1 < t := (le_max_left _ _).trans_lt hcon
  have : t ≤ t ^ μ := le_self_pow₀ h1.le hμ
  linarith [le_max_right 1 K]


/-- **Roth's theorem for pairs of integers.** For a real algebraic irrational `ξ`, natural numbers
`μ > 0` and `e > 2 μ`, and any `C`, only finitely many `(x, y)` with `y ≠ 0` satisfy
`|ξ - x / y| ^ μ |y| ^ e ≤ C`. This is `Real.finite_setOf_min_one_abs_sub_le` at the exponent
`κ = 2 + 1 / (2 μ)`, read for unreduced fractions: the pairs over one rational `β` are finitely
many because `|ξ - β| > 0` bounds `|y|`. The exponent `e / μ` is what Thue's argument produces at
a root of multiplicity `μ`, and `e > 2 μ` is Roth's `κ > 2`. -/
theorem Real.finite_setOf_pow_abs_sub_div_mul_pow_le {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) {μ e : ℕ} (hμ : 0 < μ) (he : 2 * μ < e) (C : ℝ) :
    {z : ℤ × ℤ | z.2 ≠ 0 ∧ |ξ - (z.1 : ℝ) / z.2| ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
  set K : ℝ := max 1 C with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hCK : C ≤ K := le_max_right _ _
  set A : ℝ := |ξ| + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg ξ]
  set Y₁ : ℝ := max K (K ^ 2 * A ^ (4 * μ + 1)) with hY₁
  set κ : ℝ := 2 + 1 / (2 * μ) with hκdef
  have hμR : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hκ : 2 < κ := by rw [hκdef]; linarith [show (0 : ℝ) < 1 / (2 * μ) by positivity]
  have hκμ : κ * ((2 * μ : ℕ) : ℝ) = ((4 * μ + 1 : ℕ) : ℝ) := by
    rw [hκdef]; push_cast; field_simp; ring
  have hroth := Real.finite_setOf_min_one_abs_sub_le hξ hκ
  -- the fibre over a single rational is finite
  have hfib : ∀ β : ℚ, {z : ℤ × ℤ | z.2 ≠ 0 ∧ ((z.1 : ℚ) / z.2 = β) ∧
      |ξ - (z.1 : ℝ) / z.2| ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
    intro β
    have hD : 0 < |ξ - (β : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hirr ⟨β, h.symm⟩)
    refine (finite_setOf_abs_le (|(β : ℝ)| * (C / |ξ - (β : ℝ)| ^ μ))
      (C / |ξ - (β : ℝ)| ^ μ)).subset ?_
    rintro ⟨x, y⟩ ⟨hy, hxy, hle⟩
    have hxyR : (x : ℝ) / y = β := by rw [← hxy]; push_cast; rfl
    rw [hxyR] at hle
    have hy1 := one_le_abs_intCast hy
    have hyC : |(y : ℝ)| ≤ C / |ξ - (β : ℝ)| ^ μ := by
      rw [le_div_iff₀ (pow_pos hD μ), mul_comm]
      refine le_trans ?_ hle
      gcongr
      exact le_self_pow₀ hy1 (by omega)
    refine ⟨?_, hyC⟩
    have hx : (x : ℝ) = β * y := by
      rw [← hxyR]; field_simp
    rw [hx, abs_mul]
    gcongr
  refine ((finite_setOf_abs_le ((|ξ| + K) * Y₁) Y₁).union
    (hroth.biUnion fun β _ ↦ hfib β)).subset ?_
  rintro ⟨x, y⟩ ⟨hy, hle⟩
  change y ≠ 0 at hy
  change |ξ - (x : ℝ) / y| ^ μ * |(y : ℝ)| ^ e ≤ C at hle
  have hy1 := one_le_abs_intCast hy
  set D := |ξ - (x : ℝ) / y| with hDdef
  have hD0 : 0 ≤ D := abs_nonneg _
  have hleK : D ^ μ * |(y : ℝ)| ^ e ≤ K := hle.trans hCK
  -- first, `|x| ≤ (|ξ| + L) |y|` as soon as `D ≤ L`
  have hxA : ∀ L : ℝ, D ≤ L → |(x : ℝ)| ≤ (|ξ| + L) * |(y : ℝ)| := by
    intro L hDL
    have : |(x : ℝ) / y| ≤ |ξ| + L := by
      have := abs_sub_abs_le_abs_sub ((x : ℝ) / y) ξ
      rw [abs_sub_comm] at this
      linarith
    rwa [abs_div, div_le_iff₀ (by linarith)] at this
  by_cases hsmall : |(y : ℝ)| ≤ Y₁
  · left
    have hDK : D ≤ K := by
      refine (le_max_one_of_pow_le (μ := μ) (by omega) ?_).trans (max_le hK1 le_rfl)
      refine le_trans ?_ hleK
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hy1)
    refine ⟨(hxA K hDK).trans ?_, hsmall⟩
    exact mul_le_mul_of_nonneg_left hsmall (by linarith [abs_nonneg ξ])
  right
  push Not at hsmall
  have hYK : K ≤ Y₁ := le_max_left _ _
  have hY2 : K ^ 2 * A ^ (4 * μ + 1) ≤ Y₁ := le_max_right _ _
  have hD1 : D ≤ 1 := by
    by_contra hD1
    push Not at hD1
    have h1 : 1 ≤ D ^ μ := one_le_pow₀ hD1.le
    have h2 : |(y : ℝ)| ≤ |(y : ℝ)| ^ e := le_self_pow₀ hy1 (by omega)
    have h3 : |(y : ℝ)| ^ e ≤ D ^ μ * |(y : ℝ)| ^ e := le_mul_of_one_le_left (by positivity) h1
    linarith
  set β : ℚ := (x : ℚ) / y with hβ
  have hβR : (β : ℝ) = (x : ℝ) / y := by rw [hβ]; push_cast; rfl
  refine Set.mem_iUnion₂.mpr ⟨β, ?_, hy, rfl, hle⟩
  rw [Set.mem_ofPred_eq, hβR]
  set H : ℝ := max (β.num.natAbs : ℝ) (β.den : ℝ) with hHdef
  have hH1 : 1 ≤ H := le_max_of_le_right (by exact_mod_cast β.pos)
  have hH0 : 0 ≤ H := by linarith
  have hHle : H ≤ A * |(y : ℝ)| := by
    have h := (Nat.cast_le (α := ℝ)).mpr (Rat.max_num_den_le_of_div_intCast (x := x) hy)
    rw [Nat.cast_max, Nat.cast_max] at h
    refine h.trans (max_le ?_ ?_)
    · rw [Nat.cast_natAbs, Int.cast_abs]
      exact hxA 1 hD1
    · rw [Nat.cast_natAbs, Int.cast_abs]
      exact le_mul_of_one_le_left (abs_nonneg _) hA1
  refine (min_le_right _ _).trans ?_
  refine le_of_pow_le_pow_left₀ (n := 2 * μ) (by omega) (Real.rpow_nonneg hH0 _) ?_
  rw [← Real.rpow_mul_natCast hH0, neg_mul, hκμ, Real.rpow_neg hH0, Real.rpow_natCast,
    ← one_div, le_div_iff₀ (by positivity)]
  have hsq : (D ^ μ) ^ 2 * |(y : ℝ)| ^ (2 * e) ≤ K ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hleK 2
    rwa [mul_pow, ← pow_mul |(y : ℝ)|, mul_comm e 2] at this
  have hy2e : |(y : ℝ)| ^ (4 * μ + 1) * |(y : ℝ)| ≤ |(y : ℝ)| ^ (2 * e) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hy1 (by omega)
  have hpos : 0 < |(y : ℝ)| := by linarith
  have key : D ^ (2 * μ) * H ^ (4 * μ + 1) * |(y : ℝ)| ≤ 1 * |(y : ℝ)| := by
    calc D ^ (2 * μ) * H ^ (4 * μ + 1) * |(y : ℝ)|
        ≤ (D ^ μ) ^ 2 * (A * |(y : ℝ)|) ^ (4 * μ + 1) * |(y : ℝ)| := by
          rw [← pow_mul, mul_comm μ 2]; gcongr
      _ = ((D ^ μ) ^ 2 * (|(y : ℝ)| ^ (4 * μ + 1) * |(y : ℝ)|)) * A ^ (4 * μ + 1) := by
          rw [mul_pow]; ring
      _ ≤ ((D ^ μ) ^ 2 * |(y : ℝ)| ^ (2 * e)) * A ^ (4 * μ + 1) := by gcongr
      _ ≤ K ^ 2 * A ^ (4 * μ + 1) := by gcongr
      _ ≤ 1 * |(y : ℝ)| := by linarith
  exact le_of_mul_le_mul_right key hpos

/-- **The exceptional set of one algebraic target is finite, in every case.** For an algebraic
`r ∈ ℂ` and `0 < μ < e`, only finitely many `(x, y)` with `y ≠ 0` and `x / y ≠ r` satisfy
`‖x / y - r‖ ^ μ |y| ^ e ≤ C`, provided `2 μ < e` whenever `r` is an irrational real number.
Of the three cases only the last uses Roth's theorem: a non-real `r` stays `|Im r|` away from
every real `x / y`; a rational `r = c` has `|x / y - c| ≥ 1 / (c.den |y|)` unless `x / y = c`,
which is Liouville's inequality with exponent `1` and is why `μ < e` suffices there; and an
irrational real `r` is `Real.finite_setOf_pow_abs_sub_div_mul_pow_le`. -/
theorem Complex.finite_setOf_norm_div_sub_pow_mul_pow_le {r : ℂ} (hr : IsAlgebraic ℚ r)
    {μ e : ℕ} (hμ : 0 < μ) (he : μ < e)
    (hirr : ∀ ξ : ℝ, (ξ : ℂ) = r → Irrational ξ → 2 * μ < e) (C : ℝ) :
    {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
  -- the bound on `x` in terms of `y`, common to the two elementary cases
  have hxB : ∀ z ∈ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C},
      |(z.1 : ℝ)| ≤ (‖r‖ + max 1 C) * |(z.2 : ℝ)| := by
    rintro ⟨x, y⟩ ⟨hy, -, hle⟩
    change y ≠ 0 at hy
    change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
    have hy1 := one_le_abs_intCast hy
    have h1 : ‖(x : ℂ) / y - r‖ ≤ max 1 C := by
      refine le_max_one_of_pow_le (μ := μ) (by omega) (le_trans ?_ hle)
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hy1)
    have h2 : ‖(x : ℂ) / y‖ ≤ ‖r‖ + max 1 C := by
      have := norm_sub_norm_le ((x : ℂ) / y) r
      linarith
    have h3 : ‖(x : ℂ) / y‖ = |(x : ℝ)| / |(y : ℝ)| := by
      rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
    rw [h3, div_le_iff₀ (by linarith)] at h2
    exact h2
  have hbox : ∀ Y : ℝ, (∀ z ∈ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}, |(z.2 : ℝ)| ≤ Y) →
      {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
        ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
    intro Y hY
    refine (finite_setOf_abs_le ((‖r‖ + max 1 C) * Y) Y).subset fun z hz ↦ ⟨?_, hY z hz⟩
    refine (hxB z hz).trans (mul_le_mul_of_nonneg_left (hY z hz) ?_)
    have := le_max_left 1 C
    positivity
  by_cases him : r.im = 0
  · set ξ : ℝ := r.re with hξdef
    have hrξ : (ξ : ℂ) = r := Complex.ext (by simp [hξdef]) (by simp [him])
    have hnorm : ∀ x y : ℤ, ‖(x : ℂ) / y - r‖ = |ξ - (x : ℝ) / y| := by
      intro x y
      rw [← hrξ, abs_sub_comm, show (x : ℂ) / y - ξ = (((x : ℝ) / y - ξ : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
    by_cases hirrξ : Irrational ξ
    · -- Roth
      have hξalg : IsAlgebraic ℚ ξ := by
        obtain ⟨p, hp0, hp⟩ := hr
        refine ⟨p, hp0, ?_⟩
        rw [← hrξ] at hp
        have : (algebraMap ℝ ℂ) (Polynomial.aeval ξ p) = 0 := by
          rw [← Polynomial.aeval_algebraMap_apply]
          exact hp
        exact (algebraMap ℝ ℂ).injective (this.trans (map_zero _).symm)
      refine (Real.finite_setOf_pow_abs_sub_div_mul_pow_le hξalg hirrξ hμ
        (hirr ξ hrξ hirrξ) C).subset ?_
      rintro ⟨x, y⟩ ⟨hy, -, hle⟩
      refine ⟨hy, ?_⟩
      change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
      rwa [hnorm] at hle
    · -- a rational root: Liouville with exponent one
      obtain ⟨c, hc⟩ : ∃ c : ℚ, (c : ℝ) = ξ := by
        by_contra hcon
        exact hirrξ fun ⟨c, hc'⟩ ↦ hcon ⟨c, hc'⟩
      refine hbox (max 1 C * (c.den : ℝ) ^ μ) ?_
      rintro ⟨x, y⟩ ⟨hy, hne, hle⟩
      change y ≠ 0 at hy
      change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
      change (x : ℂ) / y ≠ r at hne
      rw [hnorm] at hle
      change |(y : ℝ)| ≤ max 1 C * (c.den : ℝ) ^ μ
      have hy1 := one_le_abs_intCast hy
      have hden : (0 : ℝ) < c.den := by exact_mod_cast c.pos
      set N : ℤ := c.num * y - x * c.den with hN
      have hN0 : N ≠ 0 := by
        intro h0
        apply hne
        rw [← hrξ, ← hc]
        have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
        have hdC : ((c.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast c.den_nz
        have h' : x * (c.den : ℤ) = c.num * y := by rw [hN] at h0; linarith
        rw [Complex.ofReal_ratCast, Rat.cast_def, ← Int.cast_natCast, div_eq_div_iff hyC hdC]
        exact_mod_cast h'
      have hid : |ξ - (x : ℝ) / y| * |(y : ℝ)| = |(N : ℝ)| / c.den := by
        have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
        have : ((c : ℝ) - (x : ℝ) / y) * y = (N : ℝ) / c.den := by
          rw [Rat.cast_def, hN]
          push_cast
          field_simp
        rw [← hc, ← abs_mul, this, abs_div, Nat.abs_cast]
      have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := one_le_abs_intCast hN0
      have hlow : (1 / (c.den : ℝ)) ^ μ * |(y : ℝ)| ≤ C := by
        refine le_trans ?_ hle
        have hsplit : |ξ - (x : ℝ) / y| ^ μ * |(y : ℝ)| ^ e =
            (|ξ - (x : ℝ) / y| * |(y : ℝ)|) ^ μ * |(y : ℝ)| ^ (e - μ) := by
          rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' he.le]
        rw [hsplit, hid]
        gcongr
        exact le_self_pow₀ hy1 (by omega)
      rw [div_pow, one_pow, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)] at hlow
      exact hlow.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · -- a non-real root: `x / y` stays `|Im r|` away from it
    have himpos : 0 < |r.im| := abs_pos.mpr him
    refine hbox (C / |r.im| ^ μ) ?_
    rintro ⟨x, y⟩ ⟨hy, -, hle⟩
    change y ≠ 0 at hy
    change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
    change |(y : ℝ)| ≤ C / |r.im| ^ μ
    have hy1 := one_le_abs_intCast hy
    have hfar : |r.im| ≤ ‖(x : ℂ) / y - r‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have : ((x : ℂ) / y - r).im = -r.im := by
        rw [Complex.sub_im]
        have : ((x : ℂ) / y).im = 0 := by
          rw [show ((x : ℂ) / y) = (((x : ℝ) / y : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
        rw [this, zero_sub]
      rw [this, abs_neg]
    rw [le_div_iff₀ (pow_pos himpos μ), mul_comm]
    refine le_trans ?_ hle
    gcongr
    exact le_self_pow₀ hy1 (by omega)

/-- **Thue's theorem, for the homogenization of a polynomial in one variable.** Let `g ∈ ℤ[X]`
have degree at most `d`, and suppose the binary form `g.homogenize d` has at least three pairwise
non-proportional linear factors over `ℂ`: `g` has at least three distinct complex roots, the
point at infinity counting as one when `deg g < d`. Then for `m ≠ 0` the equation
`G(x, y) = m` has only finitely many solutions `(x, y) ∈ ℤ²`. -/
theorem Polynomial.finite_setOf_eval_homogenize_eq {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {m : ℤ} (hm : m ≠ 0) :
    {z : ℤ × ℤ | MvPolynomial.eval ![z.1, z.2] (g.homogenize d) = m}.Finite := by
  classical
  set gc := g.map (Int.castRingHom ℂ) with hgc
  set rs := gc.roots with hrs
  set R := rs.toFinset with hR
  set n := g.natDegree with hn
  set a := g.leadingCoeff with ha
  have hg : g ≠ 0 := by
    rintro rfl
    simp only [hgc, hrs, hR, Polynomial.map_zero, roots_zero, Multiset.toFinset_zero,
      Finset.card_empty, zero_add] at hroots
    split_ifs at hroots <;> omega
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have haR : (1 : ℝ) ≤ |(a : ℝ)| := one_le_abs_intCast ha0
  have hgc0 : gc ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg
  have hcard : Multiset.card rs = n := by
    rw [hrs, splits_iff_card_roots.mp (IsAlgClosed.splits gc), hgc,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  have hsum : ∑ r ∈ R, rs.count r = n := by rw [hR, Multiset.toFinset_sum_count_eq, hcard]
  have hR2 : 2 ≤ R.card := by split_ifs at hroots <;> omega
  have hcount : ∀ r ∈ R, 0 < rs.count r := fun r hr ↦ Multiset.count_pos.mpr
    (Multiset.mem_toFinset.mp hr)
  have hnR : R.card ≤ n := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun r hr ↦ hcount r hr
  -- the identity `|G(x, y)| = |a| |y| ^ d ∏ ‖x / y - r‖ ^ μ(r)`
  have hid : ∀ x y : ℤ, y ≠ 0 → |((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℝ)| =
      |(a : ℝ)| * |(y : ℝ)| ^ d * ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by
    intro x y hy
    have h1 := congrArg norm (Polynomial.intCast_eval_homogenize hd x y hy)
    rw [eval_map_intCast_eq_prod] at h1
    rw [Complex.norm_intCast] at h1
    rw [h1, norm_mul, norm_mul, norm_pow, Complex.norm_intCast, Complex.norm_intCast,
      Complex.norm_prod]
    simp_rw [norm_pow]
    ring
  -- a first bound: `|x| ≤ B |y|`
  set Rs : ℝ := ∑ r ∈ R, ‖r‖ with hRs
  have hxbound : ∀ x y : ℤ, y ≠ 0 → MvPolynomial.eval ![x, y] (g.homogenize d) = m →
      |(x : ℝ)| ≤ (Rs + 1 + |(m : ℝ)|) * |(y : ℝ)| := by
    intro x y hy hxy
    have hy1 := one_le_abs_intCast hy
    have hidm := hid x y hy
    rw [hxy] at hidm
    have htnorm : ‖(x : ℂ) / y‖ = |(x : ℝ)| / |(y : ℝ)| := by
      rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
    suffices h : ‖(x : ℂ) / y‖ ≤ Rs + 1 + |(m : ℝ)| by
      rwa [htnorm, div_le_iff₀ (by linarith)] at h
    by_cases hsmall : ‖(x : ℂ) / y‖ ≤ Rs + 1
    · linarith [abs_nonneg (m : ℝ)]
    push Not at hsmall
    have hfac : ∀ r ∈ R, ‖(x : ℂ) / y‖ - Rs ≤ ‖(x : ℂ) / y - r‖ := by
      intro r hr
      have h1 : ‖r‖ ≤ Rs := Finset.single_le_sum (f := fun r ↦ ‖r‖)
        (fun _ _ ↦ norm_nonneg _) hr
      have h2 := norm_sub_norm_le ((x : ℂ) / y) r
      linarith
    have hP : (‖(x : ℂ) / y‖ - Rs) ^ n ≤ ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by
      rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg (by linarith) _)
        fun r hr ↦ pow_le_pow_left₀ (by linarith) (hfac r hr) _
    have hn1 : n ≠ 0 := by omega
    have hP1 : ‖(x : ℂ) / y‖ - Rs ≤ (‖(x : ℂ) / y‖ - Rs) ^ n := le_self_pow₀ (by linarith) hn1
    have hay : 1 ≤ |(a : ℝ)| * |(y : ℝ)| ^ d := one_le_mul_of_one_le_of_one_le haR
      (one_le_pow₀ hy1)
    have hPnn : 0 ≤ ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by positivity
    have : ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r ≤ |(m : ℝ)| := by
      rw [hidm]; exact le_mul_of_one_le_left hPnn hay
    linarith
  rcases lt_or_eq_of_le hd with hlt | heq
  · -- the form is divisible by `Y`, so `y ∣ m`: no approximation is needed
    have hdiv : ∀ x y : ℤ, y ∣ MvPolynomial.eval ![x, y] (g.homogenize d) := by
      intro x y
      have hsplit : g.homogenize d = MvPolynomial.X 1 * g.homogenize (d - 1) := by
        have := homogenize_mul (1 : ℤ[X]) g (m := 1) (n := d - 1) (by simp) (by omega)
        rw [one_mul, Nat.add_sub_cancel' (by omega)] at this
        rw [this, homogenize_one, pow_one]
      rw [hsplit, map_mul, MvPolynomial.eval_X]
      exact dvd_mul_right _ _
    refine (finite_setOf_abs_le ((Rs + 1 + |(m : ℝ)|) * |(m : ℝ)|) |(m : ℝ)|).subset ?_
    rintro ⟨x, y⟩ hxy
    change MvPolynomial.eval ![x, y] (g.homogenize d) = m at hxy
    have hy : y ≠ 0 := by
      rintro rfl
      rw [eval_homogenize_eq_coeff_mul_pow, coeff_eq_zero_of_natDegree_lt hlt, zero_mul] at hxy
      exact hm hxy.symm
    have hym : |(y : ℝ)| ≤ |(m : ℝ)| := by
      have h := Int.le_of_dvd (abs_pos.mpr hm) ((abs_dvd_abs _ _).mpr (hxy ▸ hdiv x y))
      rw [← Int.cast_abs, ← Int.cast_abs]
      exact_mod_cast h
    refine ⟨(hxbound x y hy hxy).trans ?_, hym⟩
    refine mul_le_mul_of_nonneg_left hym ?_
    positivity
  -- the form is not divisible by `Y`, and it has three distinct roots
  have hR3 : 3 ≤ R.card := by simp only [heq, ↓reduceIte, add_zero] at hroots; omega
  have hoff : R.offDiag.Nonempty := by
    obtain ⟨r₁, hr₁, r₂, hr₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < R.card)
    exact ⟨(r₁, r₂), Finset.mem_offDiag.mpr ⟨hr₁, hr₂, h12⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := R.offDiag.exists_min_image (fun p ↦ ‖p.1 - p.2‖) hoff
  set δ : ℝ := ‖p₀.1 - p₀.2‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp₀).2.2)
  have hδle : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → δ ≤ ‖r - r'‖ := fun r hr r' hr' h ↦
    hmin (r, r') (Finset.mem_offDiag.mpr ⟨hr, hr', h⟩)
  set δ' : ℝ := min 1 (δ / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min one_pos (by positivity)
  have hδ'1 : δ' ≤ 1 := min_le_left _ _
  set C : ℝ := |(m : ℝ)| / δ' ^ n with hCdef
  set Y₀ : ℝ := max 1 (2 * max 1 |(m : ℝ)| / δ) with hY₀def
  have hY₀1 : 1 ≤ Y₀ := le_max_left _ _
  -- the exceptional set of each root is finite
  set T : ℂ → Set (ℤ × ℤ) := fun r ↦ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
    ‖(z.1 : ℂ) / z.2 - r‖ ^ rs.count r * |(z.2 : ℝ)| ^ d ≤ C} with hTdef
  have hT : ∀ r ∈ R, (T r).Finite := by
    intro r hr
    have hrs : r ∈ rs := Multiset.mem_toFinset.mp hr
    have halg : IsAlgebraic ℚ r := by
      refine ⟨g.map (Int.castRingHom ℚ),
        (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg, ?_⟩
      have hroot : gc.IsRoot r := (mem_roots hgc0).mp hrs
      rw [aeval_def, eval₂_map]
      rw [IsRoot, hgc, eval_map] at hroot
      convert hroot using 2
      exact RingHom.ext_int _ _
    have hlt : rs.count r < d := by
      obtain ⟨r', hr', hne⟩ : ∃ r' ∈ R, r' ≠ r := by
        by_contra hcon
        push Not at hcon
        have : R.card ≤ 1 := Finset.card_le_one.mpr fun u hu v hv ↦
          (hcon u hu).trans (hcon v hv).symm
        omega
      have h2 : rs.count r + rs.count r' ≤ n := by
        rw [← hsum, ← Finset.sum_pair (f := fun r ↦ rs.count r) hne.symm]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.insert_subset hr (Finset.singleton_subset_iff.mpr hr'))
          fun _ _ _ ↦ Nat.zero_le _
      have := hcount r' hr'
      omega
    refine Complex.finite_setOf_norm_div_sub_pow_mul_pow_le halg (hcount r hr) hlt ?_ C
    intro ξ hξ hirrξ
    rw [← heq]
    refine two_mul_count_roots_lt_natDegree hg hrs ?_ (by omega)
    rintro ⟨c, hc⟩
    apply hirrξ
    refine ⟨c, ?_⟩
    have : ((c : ℝ) : ℂ) = (ξ : ℂ) := by rw [hξ, ← hc]; simp
    exact_mod_cast this
  set X₀ : ℝ := max ((Rs + 1 + |(m : ℝ)|) * Y₀) (max 1 |(m : ℝ)|) with hX₀def
  refine ((finite_setOf_abs_le X₀ Y₀).union
    ((R.finite_toSet).biUnion fun r hr ↦ hT r hr)).subset ?_
  rintro ⟨x, y⟩ hxy
  change MvPolynomial.eval ![x, y] (g.homogenize d) = m at hxy
  by_cases hy : y = 0
  · -- `a x ^ d = m`
    subst hy
    left
    rw [eval_homogenize_eq_coeff_mul_pow, ← heq] at hxy
    refine ⟨le_max_of_le_right ?_, by simpa using hY₀1.trans' zero_le_one⟩
    have hxm : |(x : ℝ)| ^ n ≤ |(m : ℝ)| := by
      rw [← hxy]
      push_cast
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (by positivity) haR
    have hn0 : n ≠ 0 := by omega
    exact le_max_one_of_pow_le hn0 hxm
  by_cases hsmall : |(y : ℝ)| ≤ Y₀
  · left
    refine ⟨le_max_of_le_left ((hxbound x y hy hxy).trans ?_), hsmall⟩
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  right
  push Not at hsmall
  have hy1 := one_le_abs_intCast hy
  have hypos : 0 < |(y : ℝ)| := by linarith
  have hidm := hid x y hy
  rw [hxy] at hidm
  set t : ℂ := (x : ℂ) / y with htdef
  set P : ℝ := ∏ r ∈ R, ‖t - r‖ ^ rs.count r with hPdef
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r₀, hr₀, hmin₀⟩ := R.exists_min_image (fun r ↦ ‖t - r‖) hRne
  set ρ : ℝ := ‖t - r₀‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  refine Set.mem_iUnion₂.mpr ⟨r₀, hr₀, hy, ?_, ?_⟩
  · -- `x / y` is not a root, since `G(x, y) = m ≠ 0`
    intro ht
    have hP0 : P = 0 := Finset.prod_eq_zero hr₀ (by
      change ‖t - r₀‖ ^ rs.count r₀ = 0
      rw [show t = r₀ from ht, sub_self, norm_zero, zero_pow (hcount r₀ hr₀).ne'])
    rw [hP0, mul_zero, abs_eq_zero, Int.cast_eq_zero] at hidm
    exact hm hidm
  change ρ ^ rs.count r₀ * |(y : ℝ)| ^ d ≤ C
  -- the nearest root is within `δ / 2`
  have hρn : ρ ^ n ≤ P := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg hρ0 _)
      fun r hr ↦ pow_le_pow_left₀ hρ0 (hmin₀ r hr) _
  have hρy : ρ * |(y : ℝ)| ≤ max 1 |(m : ℝ)| := by
    refine le_max_one_of_pow_le (μ := n) (by omega) ?_
    rw [mul_pow, heq, hidm]
    rw [← heq]
    calc ρ ^ n * |(y : ℝ)| ^ n ≤ P * |(y : ℝ)| ^ n := by gcongr
      _ = 1 * |(y : ℝ)| ^ n * P := by ring
      _ ≤ |(a : ℝ)| * |(y : ℝ)| ^ n * P := by gcongr
  have hρδ : ρ ≤ δ / 2 := by
    have h1 : 2 * max 1 |(m : ℝ)| / δ < |(y : ℝ)| := (le_max_right _ _).trans_lt hsmall
    rw [div_lt_iff₀ hδ] at h1
    have h2 : ρ * |(y : ℝ)| * 2 ≤ δ * |(y : ℝ)| := by linarith
    have h3 : (ρ * 2) * |(y : ℝ)| ≤ δ * |(y : ℝ)| := by linarith
    have := le_of_mul_le_mul_right h3 hypos
    linarith
  -- every other root is at least `δ / 2` away
  have hfar : ∀ r ∈ R.erase r₀, δ' ≤ ‖t - r‖ := by
    intro r hr
    obtain ⟨hne, hrR⟩ := Finset.mem_erase.mp hr
    have h1 := hδle r hrR r₀ hr₀ hne
    have h2 : ‖r - r₀‖ ≤ ‖t - r‖ + ‖t - r₀‖ := by
      calc ‖r - r₀‖ = ‖(t - r₀) - (t - r)‖ := by ring_nf
        _ ≤ ‖t - r₀‖ + ‖t - r‖ := norm_sub_le _ _
        _ = ‖t - r‖ + ‖t - r₀‖ := add_comm _ _
    have : δ / 2 ≤ ‖t - r‖ := by linarith
    exact (min_le_right _ _).trans this
  have hrest : δ' ^ n ≤ ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r := by
    calc δ' ^ n ≤ δ' ^ (∑ r ∈ R.erase r₀, rs.count r) := by
          refine pow_le_pow_of_le_one hδ'0.le hδ'1 ?_
          rw [← hsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ Nat.zero_le _
      _ = ∏ r ∈ R.erase r₀, δ' ^ rs.count r := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r :=
          Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg hδ'0.le _)
            fun r hr ↦ pow_le_pow_left₀ hδ'0.le (hfar r hr) _
  have hPsplit : P = ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r :=
    (Finset.mul_prod_erase R (fun r ↦ ‖t - r‖ ^ rs.count r) hr₀).symm
  rw [hCdef, le_div_iff₀ (pow_pos hδ'0 n), hidm, hPsplit]
  calc ρ ^ rs.count r₀ * |(y : ℝ)| ^ d * δ' ^ n
      ≤ ρ ^ rs.count r₀ * |(y : ℝ)| ^ d * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r := by
        gcongr
    _ = 1 * |(y : ℝ)| ^ d * (ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r) := by
        ring
    _ ≤ |(a : ℝ)| * |(y : ℝ)| ^ d *
        (ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r) := by
        gcongr

/-- **Thue's theorem** (Thue 1909; Bombieri–Gubler, Theorem 6.2.1). A homogeneous `G ∈ ℤ[X, Y]`
with at least three pairwise non-proportional linear factors over `ℂ` takes each nonzero value
`m` at only finitely many `(x, y) ∈ ℤ²`. The linear factors are `l i 0 X + l i 1 Y`, and two of
them are non-proportional when their `2 × 2` determinant is nonzero. -/
theorem MvPolynomial.IsHomogeneous.finite_setOf_eval_eq {G : MvPolynomial (Fin 2) ℤ} {d : ℕ}
    (hG : G.IsHomogeneous d)
    (hfac : ∃ l : Fin 3 → Fin 2 → ℂ, Pairwise (fun i j ↦ l i 0 * l j 1 ≠ l i 1 * l j 0) ∧
      ∀ i, (C (l i 0) * X 0 + C (l i 1) * X 1) ∣ G.map (Int.castRingHom ℂ))
    {m : ℤ} (hm : m ≠ 0) :
    {z : ℤ × ℤ | MvPolynomial.eval ![z.1, z.2] G = m}.Finite := by
  classical
  obtain ⟨l, hl, hdvd⟩ := hfac
  set g : ℤ[X] := MvPolynomial.aeval ![(Polynomial.X : ℤ[X]), 1] G with hgdef
  have hgd : g.natDegree ≤ d := hG.natDegree_aeval_X_one_le
  have hGg : G = g.homogenize d := (homogenize_eq_of_isHomogeneous hG rfl).symm
  have hGc : G.map (Int.castRingHom ℂ) = (g.map (Int.castRingHom ℂ)).homogenize d := by
    rw [hGg, homogenize_map]
  rw [hGg]
  by_cases hg : g = 0
  · convert Set.finite_empty
    ext z
    simp only [hg, homogenize_zero, map_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    exact fun h ↦ hm h.symm
  refine Polynomial.finite_setOf_eval_homogenize_eq hgd ?_ hm
  set gc := g.map (Int.castRingHom ℂ) with hgc
  have hgc0 : gc ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg
  -- each linear factor vanishes at a point of `ℙ¹(ℂ)`
  have hzero : ∀ i, MvPolynomial.eval ![-(l i 1), l i 0] (gc.homogenize d) = 0 := by
    intro i
    obtain ⟨Q, hQ⟩ := hdvd i
    rw [← hGc, hQ, map_mul]
    simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  -- a zero off the line at infinity is a root of `g`
  have hroot : ∀ i, l i 0 ≠ 0 → -(l i 1) / l i 0 ∈ gc.roots.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, mem_roots hgc0, IsRoot]
    have h := hzero i
    rw [eval_homogenize (natDegree_map_le.trans hgd) _ (by simpa using hi)] at h
    simpa [hi] using h
  -- a zero on the line at infinity means the form is divisible by `Y`
  have hinf : ∀ i, l i 0 = 0 → g.natDegree ≠ d := by
    intro i hi hdeg
    obtain ⟨j, hj⟩ : ∃ j, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
    have hi1 : l i 1 ≠ 0 := by
      intro h
      have : l i 0 * l j 1 ≠ l i 1 * l j 0 := hl hj.symm
      rw [hi, h] at this
      simp at this
    have h := hzero i
    rw [hi, eval_homogenize_eq_coeff_mul_pow] at h
    have hcoeff : gc.coeff d = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff'.mp h).1 (neg_ne_zero.mpr hi1)
    rw [hgc, Polynomial.coeff_map, ← hdeg, eq_intCast, Int.cast_eq_zero] at hcoeff
    exact hg (leadingCoeff_eq_zero.mp hcoeff)
  -- count: the zeros off the line at infinity give distinct roots
  set I := Finset.univ.filter (fun i : Fin 3 ↦ l i 0 ≠ 0) with hIdef
  have hinj : Set.InjOn (fun i ↦ -(l i 1) / l i 0) I := by
    intro i hi j hj hij
    simp only [hIdef, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    by_contra hne
    apply hl hne
    simp only at hij
    rw [div_eq_div_iff hi hj] at hij
    linear_combination hij
  have hIR : I.card ≤ gc.roots.toFinset.card :=
    Finset.card_le_card_of_injOn _ (fun i hi ↦ hroot i (Finset.mem_filter.mp hi).2) hinj
  have hIc : (Finset.univ.filter (fun i : Fin 3 ↦ ¬ l i 0 ≠ 0)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun i hi j hj ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi hj
    by_contra hne
    have : l i 0 * l j 1 ≠ l i 1 * l j 0 := hl hne
    rw [hi, hj] at this
    simp at this
  have hsplit : I.card + (Finset.univ.filter (fun i : Fin 3 ↦ ¬ l i 0 ≠ 0)).card = 3 := by
    rw [hIdef, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  split_ifs with hdeg
  · have hall : I = Finset.univ := by
      refine Finset.eq_univ_of_forall fun i ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact fun h ↦ hinf i h hdeg
    rw [hall, Finset.card_univ, Fintype.card_fin] at hIR
    omega
  · omega

/-! ### Acceptance criteria -/

/-- `X ^ n - c` has `n` distinct complex roots, because it is separable. -/
private theorem card_toFinset_roots_X_pow_sub_C {n : ℕ} (hn : n ≠ 0) {c : ℤ} (hc : c ≠ 0) :
    ((X ^ n - C c : ℤ[X]).map (Int.castRingHom ℂ)).roots.toFinset.card = n := by
  have hmap : (X ^ n - C c : ℤ[X]).map (Int.castRingHom ℂ) = X ^ n - C (c : ℂ) := by simp
  rw [hmap, Multiset.toFinset_card_of_nodup (nodup_roots (separable_X_pow_sub_C _
    (by exact_mod_cast hn) (by exact_mod_cast hc))),
    splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_X_pow_sub_C]

/-- **The classical example.** `x ^ 3 - 2 y ^ 3 = m` has finitely many solutions for every
`m ≠ 0`: the form is the homogenization of `X ^ 3 - 2`, whose three complex roots are distinct
because it is separable. -/
example {m : ℤ} (hm : m ≠ 0) : {z : ℤ × ℤ | z.1 ^ 3 - 2 * z.2 ^ 3 = m}.Finite := by
  have hdeg : (X ^ 3 - C 2 : ℤ[X]).natDegree = 3 := natDegree_X_pow_sub_C
  have h := Polynomial.finite_setOf_eval_homogenize_eq (g := X ^ 3 - C 2) (d := 3) hdeg.le
    (by rw [card_toFinset_roots_X_pow_sub_C (by norm_num) (by norm_num), hdeg]; norm_num) hm
  convert h using 3 with z
  rw [homogenize_sub, homogenize_C, homogenize_X_pow le_rfl]
  simp

/-- **The line at infinity.** `Y (X ^ 2 - 2 Y ^ 2)` has two affine roots and the root at
infinity, and `x ^ 2 y - 2 y ^ 3 = m` has finitely many solutions — through the branch that needs
no approximation at all, since `y` divides `m`. -/
example {m : ℤ} (hm : m ≠ 0) : {z : ℤ × ℤ | z.1 ^ 2 * z.2 - 2 * z.2 ^ 3 = m}.Finite := by
  have hdeg : (X ^ 2 - C 2 : ℤ[X]).natDegree = 2 := natDegree_X_pow_sub_C
  have h := Polynomial.finite_setOf_eval_homogenize_eq (g := X ^ 2 - C 2) (d := 3) (by omega)
    (by rw [card_toFinset_roots_X_pow_sub_C (by norm_num) (by norm_num), hdeg]; norm_num) hm
  convert h using 3 with z
  rw [homogenize_sub, homogenize_C, homogenize_X_pow (by norm_num)]
  simp

/-- **Rejection test: three factors cannot be lowered to two.** `X ^ 2 - 2 Y ^ 2` has two
non-proportional linear factors over `ℂ`, and Pell's equation `x ^ 2 - 2 y ^ 2 = 1` has infinitely
many solutions: those generated from `(1, 0)` by `(x, y) ↦ (3 x + 4 y, 2 x + 3 y)`. With the
classical example above, these are the two tests the roadmap sets for Layer 8.4, over `ℤ`. -/
example : ¬ {z : ℤ × ℤ | z.1 ^ 2 - 2 * z.2 ^ 2 = 1}.Finite := by
  let s : ℕ → ℤ × ℤ := fun n ↦ Nat.rec (1, 0) (fun _ p ↦ (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)) n
  have hs : ∀ n, (s n).1 ^ 2 - 2 * (s n).2 ^ 2 = 1 ∧ 1 ≤ (s n).1 ∧ 0 ≤ (s n).2 := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      change (3 * (s n).1 + 4 * (s n).2) ^ 2 - 2 * (2 * (s n).1 + 3 * (s n).2) ^ 2 = 1 ∧
        1 ≤ 3 * (s n).1 + 4 * (s n).2 ∧ 0 ≤ 2 * (s n).1 + 3 * (s n).2
      refine ⟨by linear_combination h1, by linarith, by linarith⟩
  have hmono : StrictMono fun n ↦ (s n).2 := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    change (s n).2 < 2 * (s n).1 + 3 * (s n).2
    linarith [(hs n).2.1, (hs n).2.2]
  refine Set.infinite_of_injective_forall_mem (f := s) ?_ fun n ↦ (hs n).1
  intro i j hij
  exact hmono.injective (congrArg Prod.snd hij)

/-- `X ^ 3 - X` has the three distinct complex roots `0`, `1` and `-1`, so the form
`X ^ 3 - X Y ^ 2` satisfies the hypothesis of Thue's theorem. -/
example : ((X ^ 3 - X : ℤ[X]).map (Int.castRingHom ℂ)).roots.toFinset.card = 3 := by
  have hmap : (X ^ 3 - X : ℤ[X]).map (Int.castRingHom ℂ) = X ^ 3 - X := by simp
  have h0 : (X ^ 3 - X : ℂ[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp)] at this
    simp at this
  rw [hmap]
  refine le_antisymm ?_ ?_
  · refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]
  · have hsub : ({0, 1, -1} : Finset ℂ) ⊆ (X ^ 3 - X : ℂ[X]).roots.toFinset := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rw [Multiset.mem_toFinset, mem_roots h0]
      rcases hr with rfl | rfl | rfl <;> norm_num
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]

/-- **Rejection test: `m ≠ 0` is not removable.** The form `X ^ 3 - X Y ^ 2` of the previous
example takes the value `0` at every `(0, y)`. A rational linear factor is what makes this
possible: without one, `G(x, y) = 0` forces `x = y = 0`. -/
example : ¬ {z : ℤ × ℤ | z.1 ^ 3 - z.1 * z.2 ^ 2 = 0}.Finite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ ↦ ((0 : ℤ), n)) ?_ fun n ↦ ?_
  · intro i j hij
    exact congrArg Prod.snd hij
  · simp

/-- **Thue's theorem, entered through the headline statement.** `x y (x + y) = m` has finitely
many solutions for every `m ≠ 0`: the three linear factors `X`, `Y` and `X + Y` are supplied by
hand, and their pairwise determinants are `1`, `1` and `-1`. -/
example {m : ℤ} (hm : m ≠ 0) : {z : ℤ × ℤ | z.1 * z.2 * (z.1 + z.2) = m}.Finite := by
  have hG : (MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1) :
      MvPolynomial (Fin 2) ℤ).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)).mul
      ((MvPolynomial.isHomogeneous_X _ _).add (MvPolynomial.isHomogeneous_X _ _))
  have hmap : (MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1) :
      MvPolynomial (Fin 2) ℤ).map (Int.castRingHom ℂ) =
      MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    simp
  have h := hG.finite_setOf_eval_eq ⟨![![1, 0], ![0, 1], ![1, 1]], ?_, ?_⟩ hm
  · convert h using 3
    simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro i
    rw [hmap]
    fin_cases i
    · simpa using dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · simpa using dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · simp

end
