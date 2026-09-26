/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.ContinuedFraction
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Analysis.Complex.Basic

-- Used only inside proofs.
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.Interval
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Tactic.LinearCombination

/-!
# Real quadratic irrationals and their continued fractions

The "Facts" of Corvaja–Zannier (p. 9): the continued fraction of a real quadratic irrational is
eventually periodic (Lagrange), and `α` and its conjugate `α'` have periods of the same length
(Galois, Serret).

## Main definitions

* `Real.IsQuadraticIrrational x`: `x` is irrational and a root of a nonzero rational quadratic.
* `Real.quadConj x`: the conjugate `x'` of a quadratic irrational `x`, the other root.

## Main results

* `Real.quadConj_mob`: conjugation commutes with rational Möbius maps.
* `Real.quadConj_pow`: `(xⁿ)' = x'ⁿ`.
* `Real.IsQuadraticIrrational.exists_isCFPeriod`: **Lagrange's theorem**.
* `Real.cfTail_cfPeriod_eq_self`: **Galois' theorem**, a reduced quadratic irrational
  (`x > 1`, `-1 < x' < 0`) has a purely periodic expansion.
* `Real.cfPeriod_quadConj`: `x` and `x'` have periods of the same length.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, §3 ("Facts", p. 9).
-/

@[expose] public section

open scoped MatrixGroups

namespace Real

/-- A real quadratic irrational: an irrational root of a nonzero rational quadratic. -/
def IsQuadraticIrrational (x : ℝ) : Prop :=
  Irrational x ∧ ∃ a b c : ℚ, a ≠ 0 ∧ a * x ^ 2 + b * x + c = 0

open Classical in
/-- The conjugate of a real quadratic irrational: the other root of its quadratic. It is `x` for
any other `x`. -/
noncomputable def quadConj (x : ℝ) : ℝ :=
  if h : ∃ a b c : ℚ, a ≠ 0 ∧ a * x ^ 2 + b * x + c = 0 then
    -(h.choose_spec.choose : ℝ) / h.choose - x
  else x

variable {x y : ℝ}

theorem IsQuadraticIrrational.irrational (h : IsQuadraticIrrational x) : Irrational x := h.1

/-- **Two rational quadratics sharing an irrational root are proportional.** -/
theorem div_eq_div_of_root (hx : Irrational x) {a b c a' b' c' : ℚ} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (h : a * x ^ 2 + b * x + c = 0) (h' : a' * x ^ 2 + b' * x + c' = 0) :
    b / a = b' / a' ∧ c / a = c' / a' := by
  have hlin : ((a' * b - a * b' : ℚ) : ℝ) * x + ((a' * c - a * c' : ℚ) : ℝ) = 0 := by
    push_cast
    linear_combination (a' : ℝ) * h - (a : ℝ) * h'
  have h1 : a' * b - a * b' = 0 := by
    by_contra hne
    refine hx ⟨-(a' * c - a * c') / (a' * b - a * b'), ?_⟩
    push_cast
    have hne' : ((a' * b - a * b' : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
    push_cast at hne'
    field_simp
    push_cast at hlin
    linarith
  have h2 : a' * c - a * c' = 0 := by
    rw [h1, Rat.cast_zero, zero_mul, zero_add] at hlin
    exact_mod_cast hlin
  constructor
  · rw [div_eq_div_iff ha ha']
    linarith
  · rw [div_eq_div_iff ha ha']
    linarith

/-- The conjugate through any rational quadratic of `x`. -/
theorem quadConj_eq (hx : Irrational x) {a b c : ℚ} (ha : a ≠ 0)
    (h : a * x ^ 2 + b * x + c = 0) : quadConj x = -(b : ℝ) / a - x := by
  have hex : ∃ a b c : ℚ, a ≠ 0 ∧ a * x ^ 2 + b * x + c = 0 := ⟨a, b, c, ha, h⟩
  rw [quadConj, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hne, hroot⟩ := hex.choose_spec.choose_spec.choose_spec
  have := (div_eq_div_of_root hx hne ha hroot h).1
  have : ((hex.choose_spec.choose : ℚ) : ℝ) / hex.choose = (b : ℝ) / a := by
    exact_mod_cast this
  rw [neg_div, neg_div, this]

theorem IsQuadraticIrrational.quadConj_root (hx : IsQuadraticIrrational x) {a b c : ℚ}
    (ha : a ≠ 0) (h : a * x ^ 2 + b * x + c = 0) :
    a * quadConj x ^ 2 + b * quadConj x + c = 0 := by
  rw [quadConj_eq hx.1 ha h]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  field_simp
  linear_combination (a : ℝ) * h

/-- `x` and `-b/a - x` are the two roots; `x + x' = -b/a`. -/
theorem IsQuadraticIrrational.add_quadConj (hx : IsQuadraticIrrational x) {a b c : ℚ}
    (ha : a ≠ 0) (h : a * x ^ 2 + b * x + c = 0) : x + quadConj x = -(b : ℝ) / a := by
  rw [quadConj_eq hx.1 ha h]
  ring

theorem IsQuadraticIrrational.mul_quadConj (hx : IsQuadraticIrrational x) {a b c : ℚ}
    (ha : a ≠ 0) (h : a * x ^ 2 + b * x + c = 0) : x * quadConj x = (c : ℝ) / a := by
  rw [quadConj_eq hx.1 ha h]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  field_simp
  linear_combination -h

theorem IsQuadraticIrrational.irrational_quadConj (hx : IsQuadraticIrrational x) :
    Irrational (quadConj x) := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  rw [quadConj_eq hx.1 ha h, show -(b : ℝ) / a = ((-b / a : ℚ) : ℝ) by push_cast; ring]
  exact hx.1.ratCast_sub _

theorem IsQuadraticIrrational.quadConj_ne (hx : IsQuadraticIrrational x) : quadConj x ≠ x := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  intro heq
  have hsum := hx.add_quadConj ha h
  rw [heq] at hsum
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  exact hx.1 ⟨-b / (2 * a), by push_cast; field_simp at hsum ⊢; linarith⟩

/-- A rational number is not a root of the quadratic of a quadratic irrational. -/
theorem IsQuadraticIrrational.eval_ne_zero (hx : IsQuadraticIrrational x) {a b c : ℚ}
    (ha : a ≠ 0) (h : a * x ^ 2 + b * x + c = 0) (t : ℚ) : a * t ^ 2 + b * t + c ≠ 0 := by
  intro h0
  have hfac : ((a * t ^ 2 + b * t + c : ℚ) : ℝ) = a * (t - x) * (t - quadConj x) := by
    have hs := hx.add_quadConj ha h
    have hp := hx.mul_quadConj ha h
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hb : (b : ℝ) = -a * (x + quadConj x) := by rw [hs]; field_simp
    have hc : (c : ℝ) = a * (x * quadConj x) := by rw [hp]; field_simp
    push_cast
    rw [hb, hc]
    ring
  rw [h0, Rat.cast_zero] at hfac
  rcases mul_eq_zero.mp hfac.symm with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ha (by exact_mod_cast h2)
    · exact hx.1 ⟨t, by linarith⟩
  · exact hx.irrational_quadConj ⟨t, by linarith⟩

private theorem linear_ne_zero (hx : Irrational x) {r s : ℚ} (hrs : r ≠ 0 ∨ s ≠ 0) :
    (r : ℝ) * x + s ≠ 0 := by
  intro h0
  rcases eq_or_ne r 0 with hr | hr
  · rw [hr, Rat.cast_zero, zero_mul, zero_add] at h0
    exact (hrs.resolve_left (not_not.mpr hr)) (by exact_mod_cast h0)
  · exact hx ⟨-s / r, by
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      push_cast
      field_simp
      linarith⟩

/-- **Conjugation commutes with rational Möbius maps.** -/
theorem IsQuadraticIrrational.mob {p q r s : ℚ} (hdet : p * s - q * r ≠ 0)
    (hx : IsQuadraticIrrational x) :
    IsQuadraticIrrational ((p * x + q) / (r * x + s)) ∧
      quadConj ((p * x + q) / (r * x + s)) = (p * quadConj x + q) / (r * quadConj x + s) := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  set x' := quadConj x with hx'def
  have h' := hx.quadConj_root ha h
  have hirr' := hx.irrational_quadConj
  have hne := hx.quadConj_ne
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hdet (by rw [hc.1, hc.2]; ring)
  have hd := linear_ne_zero hx.1 hrs
  have hd' := linear_ne_zero hirr' hrs
  set A := a * s ^ 2 - b * r * s + c * r ^ 2 with hA
  set B := -2 * a * s * q + b * (p * s + q * r) - 2 * c * p * r with hB
  set C := a * q ^ 2 - b * p * q + c * p ^ 2 with hC
  have hroot : ∀ t : ℝ, (r : ℝ) * t + s ≠ 0 → (a : ℝ) * t ^ 2 + b * t + c = 0 →
      (A : ℝ) * ((p * t + q) / (r * t + s)) ^ 2 + B * ((p * t + q) / (r * t + s)) + C = 0 := by
    intro t ht hft
    rw [hA, hB, hC]
    push_cast
    field_simp
    linear_combination ((p : ℝ) * s - q * r) ^ 2 * hft
  have hA0 : A ≠ 0 := by
    rcases eq_or_ne r 0 with hr | hr
    · have hs : s ≠ 0 := hrs.resolve_left (not_not.mpr hr)
      rw [hA, hr]
      simpa using mul_ne_zero ha (pow_ne_zero 2 hs)
    · have := hx.eval_ne_zero ha h (-s / r)
      intro h0
      apply this
      rw [hA] at h0
      field_simp
      linear_combination h0
  set y := (p * x + q) / (r * x + s) with hy
  set y' := (p * x' + q) / (r * x' + s) with hy'
  have hyroot := hroot x hd h
  have hy'root := hroot x' hd' h'
  have hyne : y ≠ y' := by
    intro heq
    rw [hy, hy', div_eq_div_iff hd hd'] at heq
    have : ((p * s - q * r : ℚ) : ℝ) * (x - x') = 0 := by
      push_cast
      linear_combination heq
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hdet (by exact_mod_cast h0)
    · exact hne (by linarith)
  have hyirr : Irrational y := by
    rintro ⟨t, ht⟩
    have hlin : ((p - t * r : ℚ) : ℝ) * x = ((t * s - q : ℚ) : ℝ) := by
      rw [hy, eq_div_iff hd] at ht
      push_cast
      linear_combination -ht
    rcases eq_or_ne (p - t * r) 0 with h0 | h0
    · rw [h0, Rat.cast_zero, zero_mul] at hlin
      have h1 : t * s - q = 0 := by exact_mod_cast hlin.symm
      exact hdet (by linear_combination s * h0 + r * h1)
    · exact hx.1 ⟨(t * s - q) / (p - t * r), by
        have h0' : ((p - t * r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h0
        push_cast at hlin h0' ⊢
        field_simp
        linarith⟩
  refine ⟨⟨hyirr, A, B, C, hA0, hyroot⟩, ?_⟩
  rw [quadConj_eq hyirr hA0 hyroot]
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA0
  have hsub : (A : ℝ) * (y - y') * (y + y' + B / A) = 0 := by
    field_simp
    linear_combination hyroot - hy'root
  rcases mul_eq_zero.mp hsub with h0 | h0
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hA'
    · exact absurd (sub_eq_zero.mp h1) hyne
  · rw [neg_div]
    linarith

theorem IsQuadraticIrrational.quadConj_quadConj (hx : IsQuadraticIrrational x) :
    quadConj (quadConj x) = x := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  rw [quadConj_eq hx.irrational_quadConj ha (hx.quadConj_root ha h), quadConj_eq hx.1 ha h]
  ring

theorem IsQuadraticIrrational.isQuadraticIrrational_quadConj (hx : IsQuadraticIrrational x) :
    IsQuadraticIrrational (quadConj x) := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  exact ⟨hx.irrational_quadConj, a, b, c, ha, hx.quadConj_root ha h⟩

theorem IsQuadraticIrrational.sub_intCast (hx : IsQuadraticIrrational x) (k : ℤ) :
    IsQuadraticIrrational (x - k) ∧ quadConj (x - k) = quadConj x - k := by
  have := hx.mob (p := 1) (q := -k) (r := 0) (s := 1) (by norm_num)
  simpa [sub_eq_add_neg] using this

theorem IsQuadraticIrrational.inv (hx : IsQuadraticIrrational x) :
    IsQuadraticIrrational x⁻¹ ∧ quadConj x⁻¹ = (quadConj x)⁻¹ := by
  have := hx.mob (p := 0) (q := 1) (r := 1) (s := 0) (by norm_num)
  simpa using this

theorem IsQuadraticIrrational.neg (hx : IsQuadraticIrrational x) :
    IsQuadraticIrrational (-x) ∧ quadConj (-x) = -quadConj x := by
  have := hx.mob (p := -1) (q := 0) (r := 0) (s := 1) (by norm_num)
  simpa using this

/-- The Gauss map step: `(xₙ₊₁)' = 1 / (xₙ' - aₙ)`. -/
theorem IsQuadraticIrrational.quadConj_cfTail_succ (hx : IsQuadraticIrrational x) (n : ℕ) :
    IsQuadraticIrrational (Real.cfTail x n) ∧
      quadConj (Real.cfTail x (n + 1)) = (quadConj (Real.cfTail x n) - cfQuot x n)⁻¹ := by
  induction n with
  | zero =>
    have h1 := hx.sub_intCast ⌊x⌋
    refine ⟨hx, ?_⟩
    rw [cfTail_one, Int.fract, (h1.1.inv).2, h1.2]
    rfl
  | succ n ih =>
    have h1 := ih.1.sub_intCast (cfQuot x n)
    have hn : IsQuadraticIrrational (Real.cfTail x (n + 1)) := by
      rw [cfTail_succ, Int.fract]
      exact h1.1.inv.1
    have h2 := hn.sub_intCast (cfQuot x (n + 1))
    refine ⟨hn, ?_⟩
    rw [cfTail_succ x (n + 1), Int.fract]
    exact h2.1.inv.2.trans (by rw [h2.2])

/-- **Conjugation commutes with powers.** -/
theorem IsQuadraticIrrational.quadConj_pow (hx : IsQuadraticIrrational x) {n : ℕ}
    (hn : Irrational (x ^ n)) :
    IsQuadraticIrrational (x ^ n) ∧ quadConj (x ^ n) = quadConj x ^ n := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  have hs := hx.add_quadConj ha h
  have hp := hx.mul_quadConj ha h
  have hsum : ∀ n : ℕ, ∃ σ : ℚ, x ^ n + quadConj x ^ n = σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => exact ⟨2, by norm_num⟩
      | 1 => exact ⟨-b / a, by push_cast; rw [pow_one, pow_one, hs]⟩
      | n + 2 =>
        obtain ⟨σ₁, h₁⟩ := ih (n + 1) (by omega)
        obtain ⟨σ₀, h₀⟩ := ih n (by omega)
        refine ⟨-b / a * σ₁ - c / a * σ₀, ?_⟩
        push_cast
        rw [← h₁, ← h₀, ← hs, ← hp]
        ring
  obtain ⟨σ, hσ⟩ := hsum n
  have hroot : ((1 : ℚ) : ℝ) * (x ^ n) ^ 2 + ((-σ : ℚ) : ℝ) * x ^ n +
      (((c / a) ^ n : ℚ) : ℝ) = 0 := by
    push_cast
    rw [← hσ, ← hp]
    ring
  refine ⟨⟨hn, 1, -σ, (c / a) ^ n, one_ne_zero, hroot⟩, ?_⟩
  rw [quadConj_eq hn one_ne_zero hroot]
  push_cast
  linarith

/-- A quadratic irrational is a root of an integer quadratic. -/
theorem IsQuadraticIrrational.exists_int (hx : IsQuadraticIrrational x) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * x ^ 2 + B * x + C = 0 := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  refine ⟨a.num * b.den * c.den, b.num * a.den * c.den, c.num * a.den * b.den,
    mul_ne_zero (mul_ne_zero (Rat.num_ne_zero.mpr ha) (by exact_mod_cast b.den_ne_zero))
      (by exact_mod_cast c.den_ne_zero), ?_⟩
  rw [Rat.cast_def a, Rat.cast_def b, Rat.cast_def c] at h
  have h1 : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have h2 : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have h3 : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  field_simp at h
  push_cast
  linear_combination h

/-- The roots of integer quadratics with bounded coefficients form a finite set. -/
private theorem finite_setOf_quadratic_root (L : ℕ) :
    {y : ℝ | ∃ a b c : ℤ, |a| ≤ L ∧ |b| ≤ L ∧ |c| ≤ L ∧ a ≠ 0 ∧
      (a : ℝ) * y ^ 2 + b * y + c = 0}.Finite := by
  classical
  set box := Finset.Icc (-(L : ℤ)) L
  refine (Set.Finite.biUnion (s := ((box ×ˢ box ×ˢ box : Finset (ℤ × ℤ × ℤ)) : Set (ℤ × ℤ × ℤ)))
    (Finset.finite_toSet _) (t := fun p ↦ {y : ℝ | p.1 ≠ 0 ∧
      (p.1 : ℝ) * y ^ 2 + p.2.1 * y + p.2.2 = 0}) fun p _ ↦ ?_).subset ?_
  · by_cases hp : p.1 = 0
    · simp [hp]
    · set P : Polynomial ℝ := Polynomial.C (p.1 : ℝ) * Polynomial.X ^ 2 +
        Polynomial.C (p.2.1 : ℝ) * Polynomial.X + Polynomial.C (p.2.2 : ℝ)
      have hP : P ≠ 0 := by
        intro h0
        have := congrArg (Polynomial.coeff · 2) h0
        simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
          Polynomial.coeff_C, Polynomial.coeff_zero] at this
        norm_num at this
        exact hp (by exact_mod_cast this)
      refine (Polynomial.finite_setOfPred_isRoot hP).subset fun y hy ↦ ?_
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, P, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact hy.2
  · rintro y ⟨a, b, c, ha, hb, hc, ha0, h⟩
    refine Set.mem_biUnion (x := (a, b, c)) ?_ ⟨ha0, h⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, box, Finset.mem_Icc]
    exact ⟨abs_le.mp ha, abs_le.mp hb, abs_le.mp hc⟩

/-- **Lagrange's theorem**: the continued fraction of a real quadratic irrational is eventually
periodic. The complete quotients `xₙ` are roots of integer quadratics `Aₙ X² + Bₙ X + Cₙ` of the
discriminant of `x`, whose coefficients are bounded by the approximation `|x - pₙ/qₙ| ≤ 1/qₙ²`;
so the `xₙ` take finitely many values. -/
theorem IsQuadraticIrrational.exists_isCFPeriod (hx : IsQuadraticIrrational x) :
    ∃ r, IsCFPeriod x r := by
  obtain ⟨A, B, C, hA, h⟩ := hx.exists_int
  have hq : ((A : ℚ) : ℝ) * x ^ 2 + ((B : ℚ) : ℝ) * x + ((C : ℚ) : ℝ) = 0 := by
    push_cast
    exact h
  have hA' : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  set K : ℝ := |(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)| with hK
  set An : ℕ → ℤ := fun n ↦ A * cfNum x (n + 1) ^ 2 + B * cfNum x (n + 1) * cfDen x (n + 1) +
    C * cfDen x (n + 1) ^ 2 with hAn
  set Bn : ℕ → ℤ := fun n ↦ 2 * A * cfNum x (n + 1) * cfNum x n +
    B * (cfNum x (n + 1) * cfDen x n + cfNum x n * cfDen x (n + 1)) +
    2 * C * cfDen x (n + 1) * cfDen x n with hBn
  set Cn : ℕ → ℤ := fun n ↦ A * cfNum x n ^ 2 + B * cfNum x n * cfDen x n +
    C * cfDen x n ^ 2 with hCn
  -- the complete quotients are roots
  have hroot : ∀ n, (An n : ℝ) * cfTail x n ^ 2 + Bn n * cfTail x n + Cn n = 0 := by
    intro n
    have hxe := eq_cfNum_div_cfDen hx.1 n
    have hD := (cfDen_mul_cfTail_add_pos hx.1 n).ne'
    have hxD := (eq_div_iff hD).mp hxe
    simp only [hAn, hBn, hCn]
    push_cast
    linear_combination ((cfDen x (n + 1) : ℝ) * cfTail x n + cfDen x n) ^ 2 * h -
      ((A : ℝ) * ((cfNum x (n + 1) : ℝ) * cfTail x n + cfNum x n +
        x * ((cfDen x (n + 1) : ℝ) * cfTail x n + cfDen x n)) +
        B * ((cfDen x (n + 1) : ℝ) * cfTail x n + cfDen x n)) * hxD
  -- the bound on `Aₙ`
  have hAbound : ∀ n, 1 ≤ n → |(An n : ℝ)| ≤ K := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hQ : (1 : ℝ) ≤ cfDen x (1 + m + 1) := by exact_mod_cast one_le_cfDen hx.1 (by omega)
    have happ := abs_sub_cfNum_div_cfDen_le hx.1 m
    have ha1 : (1 : ℝ) ≤ cfQuot x (m + 1) := by exact_mod_cast one_le_cfQuot hx.1 m.succ_pos
    rw [show m + 2 = 1 + m + 1 by ring] at happ
    set P : ℝ := (cfNum x (1 + m + 1) : ℝ) with hP
    set Q : ℝ := (cfDen x (1 + m + 1) : ℝ) with hQdef
    have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
    have happ' : |x - P / Q| ≤ 1 / Q ^ 2 := happ.trans (one_div_le_one_div_of_le (by positivity)
      (le_mul_of_one_le_right (by positivity) ha1))
    have hid : (An (1 + m) : ℝ) = Q ^ 2 * (P / Q - x) * (A * (P / Q + x) + B) := by
      rw [show Q ^ 2 * (P / Q - x) * (A * (P / Q + x) + B) =
        (P - Q * x) * (A * (P + Q * x) + B * Q) by field_simp]
      simp only [hAn]
      push_cast
      linear_combination Q ^ 2 * h
    have hPQ : |P / Q| ≤ |x| + 1 := by
      have : |P / Q - x| ≤ 1 := by
        rw [abs_sub_comm]
        exact happ'.trans (by rw [div_le_one (by positivity)]; nlinarith)
      calc |P / Q| = |x + (P / Q - x)| := by ring_nf
        _ ≤ |x| + |P / Q - x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    rw [hid, abs_mul, abs_mul, abs_pow, abs_of_pos hQ0, abs_sub_comm]
    have hlin : |(A : ℝ) * (P / Q + x) + B| ≤ K := by
      calc |(A : ℝ) * (P / Q + x) + B| ≤ |(A : ℝ)| * (|P / Q| + |x|) + |(B : ℝ)| := by
            refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        _ ≤ K := by
            rw [hK]
            exact add_le_add_left (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)) _
    calc Q ^ 2 * |x - P / Q| * |(A : ℝ) * (P / Q + x) + B| ≤ Q ^ 2 * (1 / Q ^ 2) * K := by
          gcongr
      _ = K := by field_simp
  have hCbound : ∀ n, 2 ≤ n → |(Cn n : ℝ)| ≤ K := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := hAbound (1 + m) (by omega)
    simp only [hAn, hCn] at this ⊢
    rwa [show 2 + m = 1 + m + 1 by ring]
  -- the discriminant is fixed
  have hdisc : ∀ n, Bn n ^ 2 - 4 * An n * Cn n = B ^ 2 - 4 * A * C := by
    intro n
    have hdet := cfNum_mul_cfDen_sub x n
    have hsq : (cfNum x (n + 1) * cfDen x n - cfNum x n * cfDen x (n + 1)) ^ 2 = 1 := by
      rw [hdet, ← pow_mul, mul_comm, pow_mul]
      simp
    simp only [hAn, hBn, hCn]
    linear_combination (B ^ 2 - 4 * A * C) * hsq
  have hBbound : ∀ n, 2 ≤ n → |(Bn n : ℝ)| ≤ |((B ^ 2 - 4 * A * C : ℤ) : ℝ)| + 4 * K ^ 2 := by
    intro n hn
    have h1 := hAbound n (by omega)
    have h2 := hCbound n hn
    have hd : ((Bn n : ℝ)) ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : ℝ) + 4 * An n * Cn n := by
      have := hdisc n
      have : ((Bn n ^ 2 - 4 * An n * Cn n : ℤ) : ℝ) = ((B ^ 2 - 4 * A * C : ℤ) : ℝ) := by
        rw [this]
      push_cast at this ⊢
      linarith
    have hB1 : |(Bn n : ℝ)| ≤ (Bn n : ℝ) ^ 2 := by
      rcases eq_or_ne (Bn n) 0 with h0 | h0
      · simp [h0]
      · have : (1 : ℝ) ≤ |(Bn n : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs h0
        rw [← sq_abs]
        nlinarith
    have hAC : 4 * (An n : ℝ) * Cn n ≤ 4 * K ^ 2 := by
      have := abs_mul (An n : ℝ) (Cn n)
      have hK0 : 0 ≤ K := (abs_nonneg _).trans h1
      nlinarith [abs_nonneg (An n : ℝ), abs_nonneg (Cn n : ℝ), le_abs_self ((An n : ℝ) * Cn n),
        mul_le_mul h1 h2 (abs_nonneg _) hK0]
    rw [hd] at hB1
    linarith [le_abs_self ((B ^ 2 - 4 * A * C : ℤ) : ℝ)]
  -- the finitely many values
  set L : ℕ := ⌈max K (|((B ^ 2 - 4 * A * C : ℤ) : ℝ)| + 4 * K ^ 2)⌉₊ with hL
  have hmaps : Set.MapsTo (cfTail x) (Set.Ici 2) {y : ℝ | ∃ a b c : ℤ, |a| ≤ L ∧ |b| ≤ L ∧
      |c| ≤ L ∧ a ≠ 0 ∧ (a : ℝ) * y ^ 2 + b * y + c = 0} := by
    intro n hn
    have hn2 : 2 ≤ n := hn
    have hle : ∀ z : ℤ, |(z : ℝ)| ≤ max K (|((B ^ 2 - 4 * A * C : ℤ) : ℝ)| + 4 * K ^ 2) →
        |z| ≤ L := fun z hz ↦ by
      have : ((|z| : ℤ) : ℝ) ≤ L := by
        rw [Int.cast_abs]
        exact hz.trans (Nat.le_ceil _)
      exact_mod_cast this
    refine ⟨An n, Bn n, Cn n, hle _ ((hAbound n (by omega)).trans (le_max_left _ _)),
      hle _ ((hBbound n hn2).trans (le_max_right _ _)),
      hle _ ((hCbound n hn2).trans (le_max_left _ _)), ?_, hroot n⟩
    -- `Aₙ ≠ 0`: `pₙ/qₙ` is not a root
    intro h0
    have hQ : (cfDen x (n + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_cfDen hx.1 (n := n + 1) (by omega))).ne'
    apply hx.eval_ne_zero hA' hq ((cfNum x (n + 1) : ℚ) / cfDen x (n + 1))
    have : ((An n : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    simp only [hAn] at this
    push_cast at this
    field_simp
    linear_combination this
  obtain ⟨m, hm, n, hn, hne, heq⟩ := (Set.Ici_infinite 2).exists_ne_map_eq_of_mapsTo hmaps
    (finite_setOf_quadratic_root L)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨n - m, (isCFPeriod_iff hx.1 _).mpr ⟨Nat.sub_pos_of_lt hlt, m, by
      rw [Nat.add_sub_cancel' hlt.le]; exact heq.symm⟩⟩
  · exact ⟨m - n, (isCFPeriod_iff hx.1 _).mpr ⟨Nat.sub_pos_of_lt hlt, n, by
      rw [Nat.add_sub_cancel' hlt.le]; exact heq⟩⟩

theorem IsQuadraticIrrational.isCFPeriod_cfPeriod (hx : IsQuadraticIrrational x) :
    IsCFPeriod x (cfPeriod x) := by
  rw [cfPeriod_eq_sInf hx.1]
  obtain ⟨r, hr⟩ := hx.exists_isCFPeriod
  exact Nat.sInf_mem (s := {r | IsCFPeriod x r}) ⟨r, hr⟩

theorem IsQuadraticIrrational.cfPeriod_pos (hx : IsQuadraticIrrational x) : 0 < cfPeriod x :=
  hx.isCFPeriod_cfPeriod.1

theorem IsQuadraticIrrational.cfPeriod_le (hx : IsQuadraticIrrational x) {r : ℕ}
    (hr : IsCFPeriod x r) : cfPeriod x ≤ r := by
  rw [cfPeriod_eq_sInf hx.1]
  exact Nat.sInf_le hr

/-! ### Reduced quadratic irrationals (Galois) -/

/-- A reduced quadratic irrational: `x > 1` and `-1 < x' < 0`. -/
def IsReduced (x : ℝ) : Prop :=
  IsQuadraticIrrational x ∧ 1 < x ∧ -1 < quadConj x ∧ quadConj x < 0

theorem IsQuadraticIrrational.tail (hx : IsQuadraticIrrational x) (n : ℕ) :
    IsQuadraticIrrational (Real.cfTail x n) :=
  (hx.quadConj_cfTail_succ n).1

/-- The Gauss map preserves reducedness. -/
theorem IsReduced.cfTail_one (hx : IsReduced x) : IsReduced (cfTail x 1) := by
  obtain ⟨hq, h1, hc1, hc0⟩ := hx
  have hstep := (hq.quadConj_cfTail_succ 0).2
  rw [cfTail_zero, zero_add] at hstep
  have ha : (1 : ℝ) ≤ cfQuot x 0 := by
    rw [cfQuot, cfTail_zero]
    exact_mod_cast Int.le_floor.mpr (by exact_mod_cast h1.le)
  refine ⟨hq.tail 1, one_lt_cfTail hq.1 one_pos, ?_, ?_⟩ <;> rw [hstep]
  · rw [lt_inv_of_neg (by norm_num) (by linarith)]
    norm_num
    linarith
  · exact inv_lt_zero.mpr (by linarith)

theorem IsReduced.tail (hx : IsReduced x) (n : ℕ) : IsReduced (Real.cfTail x n) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [show n + 1 = n + 1 from rfl, cfTail_add]
    exact ih.cfTail_one

/-- **The Gauss map is injective on reduced numbers**: the partial quotient of a reduced `x` is
determined by the conjugate of its successor. -/
theorem IsReduced.eq_of_cfTail_one_eq (hx : IsReduced x) (hy : IsReduced y)
    (h : cfTail x 1 = cfTail y 1) : x = y := by
  have hzx := (hx.1.quadConj_cfTail_succ 0).2
  have hzy := (hy.1.quadConj_cfTail_succ 0).2
  rw [cfTail_zero, zero_add, h] at hzx
  rw [cfTail_zero, zero_add] at hzy
  set z' := quadConj (cfTail y 1)
  have hz0 : z' ≠ 0 := by
    have ha : (1 : ℝ) ≤ cfQuot y 0 := by
      rw [cfQuot, cfTail_zero]
      exact_mod_cast Int.le_floor.mpr (by exact_mod_cast hy.2.1.le)
    rw [hzy]
    exact inv_ne_zero (by linarith [hy.2.2.2])
  have hxz : quadConj x = cfQuot x 0 + z'⁻¹ := by rw [hzx, inv_inv]; ring
  have hyz : quadConj y = cfQuot y 0 + z'⁻¹ := by rw [hzy, inv_inv]; ring
  have hab : cfQuot x 0 = cfQuot y 0 := by
    have h1 := hx.2.2.1
    have h2 := hx.2.2.2
    have h3 := hy.2.2.1
    have h4 := hy.2.2.2
    rw [hxz] at h1 h2
    rw [hyz] at h3 h4
    have hlt : ((cfQuot x 0 - cfQuot y 0 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hgt : (-1 : ℝ) < ((cfQuot x 0 - cfQuot y 0 : ℤ) : ℝ) := by push_cast; linarith
    have : cfQuot x 0 - cfQuot y 0 = 0 := by
      have := Int.cast_lt.mp (hlt.trans_eq (by norm_num : (1 : ℝ) = ((1 : ℤ) : ℝ)))
      have := Int.cast_lt.mp ((by norm_num : ((-1 : ℤ) : ℝ) = -1).trans_lt hgt)
      omega
    omega
  rw [← cfTail_zero x, ← cfTail_zero y, cfTail_eq x 0, cfTail_eq y 0, hab, h]

theorem IsReduced.eq_of_cfTail_eq (hx : IsReduced x) (hy : IsReduced y) {n : ℕ}
    (h : Real.cfTail x n = Real.cfTail y n) : x = y := by
  induction n generalizing x y with
  | zero => exact h
  | succ n ih =>
    refine IsReduced.eq_of_cfTail_one_eq hx hy
      (ih (IsReduced.cfTail_one hx) (IsReduced.cfTail_one hy) ?_)
    rw [← cfTail_add, ← cfTail_add, add_comm 1 n]
    exact h

/-- **Galois' theorem**: a reduced quadratic irrational has a purely periodic expansion. -/
theorem IsReduced.cfTail_eq_self (hx : IsReduced x) {r : ℕ} (hr : IsCFPeriod x r) :
    Real.cfTail x r = x := by
  obtain ⟨-, N, hN⟩ := (isCFPeriod_iff hx.1.1 r).mp hr
  refine (hx.tail r).eq_of_cfTail_eq hx (n := N) ?_
  rw [← cfTail_add, add_comm]
  exact hN

theorem one_le_cfNum (hx : Irrational x) (h1 : 1 < x) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cfNum x n := by
  have h0 : 1 ≤ cfQuot x 0 := by
    rw [cfQuot, cfTail_zero]
    exact Int.le_floor.mpr (by exact_mod_cast h1.le)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => exact le_rfl
    | 2, _ => simp [cfNum, h0]
    | n + 3, _ =>
      rw [cfNum_succ_succ]
      have h2 := ih (n + 2) (by omega) (by omega)
      have h3 : 0 ≤ cfNum x (n + 1) := zero_le_one.trans (ih (n + 1) (by omega) (by omega))
      have h4 := one_le_cfQuot hx (n := n + 1) (by omega)
      nlinarith

/-- **A purely periodic quadratic irrational `> 1` is reduced.** Its conjugate is the other root
`-p'/(q y)` of its fixed-point equation `q y² + (q' - p) y - p' = 0`, hence negative; so is the
conjugate of every complete quotient, which forces `y' > -1`. -/
theorem isReduced_of_cfTail_eq_self (hy : IsQuadraticIrrational y) (h1 : 1 < y) {r : ℕ}
    (hr : 0 < r) (h : Real.cfTail y r = y) : IsReduced y := by
  -- every complete quotient has negative conjugate
  have hneg : ∀ i, quadConj (Real.cfTail y i) < 0 := by
    intro i
    set w := Real.cfTail y i with hw
    have hwq : IsQuadraticIrrational w := hy.tail i
    have hw1 : 1 < w := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact h1
      · exact one_lt_cfTail hy.1 hi
    have hwr : Real.cfTail w r = w := by
      rw [hw, ← cfTail_add, add_comm, cfTail_add, h]
    have hfix := eq_cfNum_div_cfDen hwq.1 r
    rw [hwr] at hfix
    have hD := (cfDen_mul_cfTail_add_pos hwq.1 r)
    rw [hwr] at hD
    set P := cfNum w (r + 1)
    set P' := cfNum w r
    set Q := cfDen w (r + 1)
    set Q' := cfDen w r
    have hQ : (1 : ℤ) ≤ Q := one_le_cfDen hwq.1 (by omega)
    have hP' : (1 : ℤ) ≤ P' := one_le_cfNum hwq.1 hw1 (by omega)
    have hQ' : ((Q : ℚ)) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hQ).ne'
    have hroot : ((Q : ℚ) : ℝ) * w ^ 2 + ((Q' - P : ℚ) : ℝ) * w + ((-P' : ℚ) : ℝ) = 0 := by
      have := (eq_div_iff hD.ne').mp hfix
      push_cast
      linear_combination this
    have hprod := hwq.mul_quadConj hQ' hroot
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast zero_lt_one.trans_le hQ
    have hP'pos : (0 : ℝ) < P' := by exact_mod_cast zero_lt_one.trans_le hP'
    have hw0 : 0 < w := zero_lt_one.trans hw1
    push_cast at hprod
    by_contra hc
    push Not at hc
    have : 0 ≤ w * quadConj w := mul_nonneg hw0.le hc
    rw [hprod] at this
    have : -(P' : ℝ) / Q < 0 := div_neg_of_neg_of_pos (by linarith) hQpos
    linarith
  refine ⟨hy, h1, ?_, by simpa using hneg 0⟩
  -- `y' = 1 / ((y_{r-1})' - a_{r-1})`
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [zero_add] at h
  have hstep := (hy.quadConj_cfTail_succ r).2
  rw [h] at hstep
  have ha : (1 : ℝ) ≤ cfQuot y r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr'
    · rw [cfQuot, cfTail_zero]
      exact_mod_cast Int.le_floor.mpr (by exact_mod_cast h1.le)
    · exact_mod_cast one_le_cfQuot hy.1 hr'
  have hw := hneg r
  rw [hstep, lt_inv_of_neg (by norm_num) (by linarith)]
  norm_num
  linarith

/-! ### The conjugate has the same period -/

/-- **Fact (p. 9): `x` and `x'` have periods of the same length.** A purely periodic complete
quotient `y` of `x` is reduced; the numbers `zᵢ = -1 / yᵢ'` form the reversed cycle
(`zᵢ₊₁ = aᵢ + 1 / zᵢ`), whose period is that of `y`; and `x'` is tail equivalent to `z₀` by
Serret's theorem. -/
theorem IsQuadraticIrrational.cfPeriod_quadConj (hx : IsQuadraticIrrational x) :
    cfPeriod (quadConj x) = cfPeriod x := by
  set r := cfPeriod x with hr
  have hrp := hx.isCFPeriod_cfPeriod
  obtain ⟨hr0, N, hN⟩ := (isCFPeriod_iff hx.1 r).mp hrp
  -- a purely periodic complete quotient `y > 1`
  set y := Real.cfTail x (N + 1) with hy
  have hyq : IsQuadraticIrrational y := hx.tail _
  have hy1 : 1 < y := one_lt_cfTail hx.1 (Nat.succ_pos N)
  have hyper : Real.cfTail y r = y := by
    rw [hy, ← cfTail_add, show N + 1 + r = N + r + 1 by ring, cfTail_add, hN, ← cfTail_add]
  have hred := isReduced_of_cfTail_eq_self hyq hy1 hr0 hyper
  have hyr : cfPeriod y = r := (cfPeriod_eq_of_tailEquiv hyq.1 hx.1 (tailEquiv_cfTail x _)).trans
    hr.symm
  -- the reversed cycle
  set z : ℕ → ℝ := fun i ↦ -(quadConj (Real.cfTail y i))⁻¹ with hz
  have hzred : ∀ i, IsReduced (z i) := by
    intro i
    obtain ⟨hq, h1, hc1, hc0⟩ := hred.tail i
    have hinv := hq.isQuadraticIrrational_quadConj.inv
    have hneg := hinv.1.neg
    refine ⟨hneg.1, ?_, ?_, ?_⟩
    · simp only [hz]
      have : (quadConj (Real.cfTail y i))⁻¹ < -1 := by
        rw [inv_lt_of_neg hc0 (by norm_num)]
        norm_num
        exact hc1
      linarith
    · simp only [hz]
      rw [hneg.2, hinv.2, hq.quadConj_quadConj, neg_lt_neg_iff]
      exact inv_lt_one_of_one_lt₀ h1
    · simp only [hz]
      rw [hneg.2, hinv.2, hq.quadConj_quadConj, neg_lt_zero]
      exact inv_pos.mpr (zero_lt_one.trans h1)
  have hzstep : ∀ i, Real.cfTail (z (i + 1)) 1 = z i := by
    intro i
    have hstep := (hyq.quadConj_cfTail_succ i).2
    have hz1 := (hzred i).2.1
    have hzi : z (i + 1) = cfQuot y i + (z i)⁻¹ := by
      simp only [hz]
      rw [hstep, inv_inv, inv_neg, inv_inv]
      ring
    rw [cfTail_one, hzi, Int.fract_intCast_add, Int.fract_eq_self.mpr
      ⟨inv_nonneg.mpr (by linarith), inv_lt_one_of_one_lt₀ hz1⟩, inv_inv]
  have hzk : ∀ k i, Real.cfTail (z (i + k)) k = z i := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      rw [show k + 1 = 1 + k by ring, cfTail_add, show i + (1 + k) = i + k + 1 by ring,
        hzstep, ih]
  have hzper : ∀ i, z (i + r) = z i := by
    intro i
    simp only [hz]
    rw [add_comm, cfTail_add, hyper]
  have hzr : IsCFPeriod (z 0) r := by
    have h1 := hzk r 0
    rw [hzper 0] at h1
    exact (isCFPeriod_iff (hzred 0).1.1 r).mpr ⟨hr0, 0, by rw [zero_add, cfTail_zero]; exact h1⟩
  have hz0period : cfPeriod (z 0) = r := by
    refine le_antisymm ((hzred 0).1.cfPeriod_le hzr) ?_
    set s := cfPeriod (z 0)
    have hs := (hzred 0).1.isCFPeriod_cfPeriod
    have hself := (hzred 0).cfTail_eq_self hs
    have hzs : z 0 = z s := (hzred 0).eq_of_cfTail_eq (hzred s) (n := s) (by
      rw [hself, ← hzk s 0, zero_add])
    have hconj : quadConj (Real.cfTail y 0) = quadConj (Real.cfTail y s) := by
      simp only [hz, neg_inj, inv_inj] at hzs
      exact hzs
    have hys : Real.cfTail y s = y := by
      have := congrArg quadConj hconj
      rw [(hyq.tail 0).quadConj_quadConj, (hyq.tail s).quadConj_quadConj] at this
      exact this.symm
    rw [← hyr]
    exact hyq.cfPeriod_le ((isCFPeriod_iff hyq.1 s).mpr ⟨hs.1, 0, by rw [zero_add]; exact hys⟩)
  -- `x' = M(y')` is tail equivalent to `z₀`
  have hxy := eq_cfNum_div_cfDen hx.1 (N + 1)
  set P := cfNum x (N + 1 + 1)
  set P' := cfNum x (N + 1)
  set Q := cfDen x (N + 1 + 1)
  set Q' := cfDen x (N + 1)
  have hdet := cfNum_mul_cfDen_sub x (N + 1)
  have hdetq : (P : ℚ) * Q' - P' * Q ≠ 0 := by
    have : ((P * Q' - P' * Q : ℤ) : ℚ) = (-1) ^ (N + 1) := by rw [hdet]; push_cast; rfl
    push_cast at this
    rw [this]
    exact pow_ne_zero _ (by norm_num)
  have hmob := hyq.mob (p := P) (q := P') (r := Q) (s := Q') hdetq
  push_cast at hmob
  rw [← hy] at hxy
  rw [← hxy] at hmob
  have htx : TailEquiv (quadConj x) (quadConj y) := by
    rw [hmob.2]
    refine tailEquiv_of_det ?_ hyq.irrational_quadConj
    rw [hdet]
    rcases neg_one_pow_eq_or ℤ (N + 1) with h | h <;> rw [h] <;> simp
  have hyz : quadConj y = -(z 0)⁻¹ := by
    simp only [hz, cfTail_zero, inv_neg, inv_inv, neg_neg]
  have htz : TailEquiv (quadConj y) (z 0) := by
    rw [hyz]
    exact (tailEquiv_neg (hzred 0).1.1.inv).trans (tailEquiv_inv (hzred 0).1.1)
  rw [cfPeriod_eq_of_tailEquiv hx.irrational_quadConj (hzred 0).1.1 (htx.trans htz), hz0period]

/-! ### Integral quadratic irrationals -/

/-- **An integral quadratic irrational satisfies a monic integer quadratic**, by Gauss' lemma
for its minimal polynomial. -/
theorem IsQuadraticIrrational.exists_monic_of_isIntegral (hx : IsQuadraticIrrational x)
    (hint : IsIntegral ℤ x) : ∃ b c : ℤ, x ^ 2 + b * x + c = 0 := by
  open Polynomial in
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  have hintQ : IsIntegral ℚ x := hint.tower_top
  set p : ℚ[X] := C a * X ^ 2 + C b * X + C c with hp
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrArg (coeff · 2) h0
    simp only [hp, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at this
    norm_num at this
    exact ha this
  have hpx : aeval x p = 0 := by
    simp only [hp, map_add, map_mul, aeval_C, aeval_X_pow, aeval_X, eq_ratCast]
    exact h
  have hle : (minpoly ℚ x).natDegree ≤ 2 :=
    (natDegree_le_of_dvd (minpoly.dvd ℚ x hpx) hp0).trans natDegree_quadratic_le
  have hne1 : (minpoly ℚ x).natDegree ≠ 1 := fun h1 ↦ by
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hx.1 ⟨q, by rw [← hq, eq_ratCast]⟩
  have hpos := minpoly.natDegree_pos hintQ
  have h2 : (minpoly ℚ x).natDegree = 2 := by omega
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint,
    natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at h2
  have hmonic := minpoly.monic hint
  have hc2 : (minpoly ℤ x).coeff 2 = 1 := by
    rw [← h2]
    exact hmonic.coeff_natDegree
  have hroot := minpoly.aeval ℤ x
  rw [aeval_eq_sum_range, h2, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hc2] at hroot
  refine ⟨(minpoly ℤ x).coeff 1, (minpoly ℤ x).coeff 0, ?_⟩
  simp only [zsmul_eq_mul, pow_zero, mul_one, pow_one, Int.cast_one, one_mul] at hroot
  linear_combination hroot

/-! ### The minimal polynomial -/

section Minpoly

open Polynomial

/-- The minimal polynomial of a quadratic irrational is its monic quadratic. -/
theorem IsQuadraticIrrational.minpoly_eq (hx : IsQuadraticIrrational x) {a b c : ℚ} (ha : a ≠ 0)
    (h : a * x ^ 2 + b * x + c = 0) :
    minpoly ℚ x = C 1 * X ^ 2 + C (b / a) * X + C (c / a) := by
  set p : ℚ[X] := C 1 * X ^ 2 + C (b / a) * X + C (c / a) with hp
  have hmon : p.Monic := by
    rw [Monic, hp, leadingCoeff_quadratic one_ne_zero]
  have hdeg : p.natDegree = 2 := natDegree_quadratic one_ne_zero
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hpx : aeval x p = 0 := by
    simp only [hp, map_add, map_mul, aeval_C, aeval_X_pow, aeval_X, eq_ratCast, Rat.cast_one,
      one_mul, Rat.cast_div]
    field_simp
    linear_combination h
  have hint : IsIntegral ℚ x := ⟨p, hmon, by rw [← aeval_def]; exact hpx⟩
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd ℚ x hpx) ?_).symm
  rw [hdeg]
  have hne1 : (minpoly ℚ x).natDegree ≠ 1 := fun h1 ↦ by
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hx.1 ⟨q, by rw [← hq, eq_ratCast]⟩
  have hpos := minpoly.natDegree_pos hint
  omega

theorem IsQuadraticIrrational.isIntegral (hx : IsQuadraticIrrational x) : IsIntegral ℚ x := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  by_contra hni
  have := hx.minpoly_eq ha h
  rw [minpoly.eq_zero hni] at this
  have := congrArg (coeff · 2) this
  simp only [coeff_zero, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at this
  norm_num at this

/-- **The complex conjugates of a quadratic irrational** are `x` and `x'`. -/
theorem IsQuadraticIrrational.aroots_minpoly (hx : IsQuadraticIrrational x) :
    (minpoly ℚ x).aroots ℂ = {(x : ℂ), (quadConj x : ℂ)} := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  have hs := hx.add_quadConj ha h
  have hpr := hx.mul_quadConj ha h
  have e1 : algebraMap ℚ ℂ (b / a) = -((x : ℂ) + quadConj x) := by
    rw [eq_ratCast, ← Complex.ofReal_ratCast]
    push_cast
    rw [← Complex.ofReal_add, hs]
    push_cast
    ring
  have e2 : algebraMap ℚ ℂ (c / a) = (x : ℂ) * quadConj x := by
    rw [eq_ratCast, ← Complex.ofReal_ratCast]
    push_cast
    rw [← Complex.ofReal_mul, hpr]
    push_cast
    ring
  have hfac : (C 1 * X ^ 2 + C (b / a) * X + C (c / a) : ℚ[X]).map (algebraMap ℚ ℂ) =
      (X - C (x : ℂ)) * (X - C (quadConj x : ℂ)) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, e1, e2,
      map_one, C_neg, C_add, C_mul, Polynomial.map_one]
    ring
  rw [aroots, hx.minpoly_eq ha h, hfac, roots_mul (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
  rfl

/-- **A rational power of a quadratic irrational has rational square.** If `xⁿ = r`, the
conjugate `x'` is also a root of `Xⁿ - r`, so `|x'| = |x|`, `x' = -x` and `x² = -x x' ∈ ℚ`. -/
theorem IsQuadraticIrrational.exists_sq_eq_of_pow_eq (hx : IsQuadraticIrrational x) {n : ℕ}
    (hn : 0 < n) {r : ℚ} (hr : x ^ n = r) : ∃ s : ℚ, x ^ 2 = s := by
  obtain ⟨a, b, c, ha, h⟩ := hx.2
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨g, hg⟩ := minpoly.dvd ℚ x (p := X ^ n - C r) (by simp [hr])
  have hroot : aeval (quadConj x) (minpoly ℚ x) = 0 := by
    rw [hx.minpoly_eq ha h]
    simp only [map_add, map_mul, aeval_C, aeval_X_pow, aeval_X, eq_ratCast, Rat.cast_one,
      one_mul, Rat.cast_div]
    field_simp
    linear_combination hx.quadConj_root ha h
  have hpow : quadConj x ^ n = r := by
    have := congrArg (aeval (quadConj x)) hg
    simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast, map_mul, hroot, zero_mul] at this
    linarith
  have habs : |quadConj x| = |x| := by
    have : |quadConj x| ^ n = |x| ^ n := by rw [← abs_pow, ← abs_pow, hpow, hr]
    exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hn.ne').mp this
  rcases abs_eq_abs.mp habs with h1 | h1
  · exact absurd h1 hx.quadConj_ne
  · refine ⟨-(c / a), ?_⟩
    have := hx.mul_quadConj ha h
    rw [h1] at this
    push_cast
    linarith

end Minpoly

end Real
