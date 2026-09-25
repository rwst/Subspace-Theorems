/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SimultaneousSubspaces

-- Used only in the acceptance criteria.
import Mathlib.NumberTheory.Real.Irrational

/-!
# Schmidt's theorems on simultaneous approximation

**Layer 7.3** (Schmidt 1970; Bombieri–Gubler, Remark 7.3.4). Let `α 1, …, α n` be real algebraic
numbers with `1, α 1, …, α n` linearly independent over `ℚ`, and let `ε > 0`. Then

```text
q ^ (1 + ε) * ∏ i, ‖q * α i‖ < 1            has finitely many solutions q ≥ 1,
(∏ i, |q i|) ^ (1 + ε) * ‖∑ i, q i * α i‖ < 1   has finitely many solutions q ∈ ℤⁿ
```

the second among the `q` with no vanishing coordinate, where `‖·‖` is the distance to the
nearest integer. Both are applications of the Subspace Theorem over `ℚ` through the two systems
of forms set up in `DiophantineApproximation/SimultaneousSubspaces.lean`, and the second needs a
third statement, of independent interest, along the way: for algebraic `β 1, …, β n` with
`1, β 1, …, β n` independent over `ℚ`, only finitely many `q ∈ ℤⁿ` with no vanishing coordinate
satisfy `(∏ i, |q i|) ^ (1 + ε) * |∑ i, β i * q i| < 1`.

## Main results

* `Int.one_le_prod_abs`, `Int.iSup_abs_le_prod_abs` and `Int.finite_setOf_prod_abs_le`: the
  product of the absolute values of an integer tuple with no vanishing coordinate is at least
  one, dominates the sup norm, and is a Northcott measure of size.
* `forall_eq_zero_of_linearIndependent_option`: **linear independence of `1, β 1, …, β n` over
  `ℚ`, unfolded** into the absence of a nontrivial rational relation.
* `Real.abs_sub_round_le`: **the nearest integer is nearest**, which is what makes the
  existential over the numerator below the distance to `ℤ`.
* `Complex.finite_setOf_prod_abs_mul_norm_sum_lt` and
  `Real.finite_setOf_prod_abs_mul_abs_sum_lt`: **the linear form theorem**, over `ℂ` and `ℝ`.
* `Real.finite_setOf_prod_abs_mul_dist_lt`: **Schmidt's theorem on `∑ i, q i * α i`**.
* `Real.finite_setOf_mul_prod_dist_lt`: **Schmidt's theorem on simultaneous approximation**.

## Implementation notes

⚠ **The distance to the nearest integer is written as an existential over the numerator.**
`‖t‖` is `min p : ℤ, |t - p|`, and `Real.abs_sub_round_le` says the minimum is attained at
`round t`, so `∃ p, … |t - p| < 1` and `… ‖t‖ < 1` cut out the same set. The existential is the
form the proof wants, because the numerator *is* a coordinate of the integer point the Subspace
Theorem is applied to; the acceptance criteria record the reading with `round`.

⚠ **The product, not the sup norm, is what the exponents are read against.** For a tuple with no
vanishing coordinate `∏ i, |q i|` is at least `max i, |q i|` (`Int.iSup_abs_le_prod_abs`) and can
be very much smaller than `max i, |q i| ^ n`, so the statements below are strictly stronger than
the same inequalities with the sup norm. That is why Layer 7.1's `Rat.approxProd_projWithSum_le`,
which throws the product away, could not be reused, and why the hypothesis that no coordinate
vanishes cannot be dropped: with a vanishing coordinate the product is `0` and the inequality is
free.

⚠ **Two theorems, two inductions, and one of them feeds the other.** The linear form theorem
eliminates one variable on each exceptional subspace and recurses. The theorem on
`∑ i, q i * α i` has one variable more — the numerator — and its exceptional subspaces split in
two: a relation that does not involve the numerator eliminates one `q` and is the recursion,
while a relation that does involve it *determines* the numerator, and then the distance to `ℤ`
becomes a linear form `∑ i, q i * (α i + c i / c₀)` with algebraic coefficients, which the linear
form theorem finishes. So the second theorem consumes the first, and the two inductions are
separate.

⚠ **Simultaneous approximation needs no induction at all.** One exceptional subspace already
bounds `q`: its relation `c₀ q + ∑ i, c i p i = 0` together with `p i = q * α i - θ i`,
`|θ i| ≤ 1/2`, gives `q * (c₀ + ∑ i, c i * α i) = ∑ i, c i * θ i`, whose left factor is nonzero
*because* `1, α 1, …, α n` are independent over `ℚ`. That is the one place where the independence
hypothesis is used as a nonvanishing statement rather than as an invariant of a recursion, and it
is why this half of Layer 7.3 is the shorter one.

⚠ **A threshold is unavoidable exactly where the extra variable is.** The numerator's size is
controlled by the `α i`, not by the product, so the sup norm of the extended point is only
`≤ C * ∏ i, |q i|` with `C = ∑ i, |α i| + 2`; half of `ε` absorbs `C` once `∏ i, |q i| ≥ C`, and
below that threshold `Int.finite_setOf_prod_abs_le` counts the points. The linear form theorem
has no extra variable and needs no threshold — there the sup norm is bounded by the product
outright.

⚠ **`1, α 1, …, α n` independent over `ℚ` is Mathlib's `LinearIndependent`, indexed by
`Option ι`.** No new predicate is introduced: the statements carry
`LinearIndependent ℚ (fun o : Option ι ↦ o.elim 1 α)`, and the proofs run on the unfolded form
that `forall_eq_zero_of_linearIndependent_option` produces. Both reductions preserve it —
eliminating a variable and shifting the coefficients by rationals — and that is what makes the
inductions run.

⚠ **The base case of the linear form theorem is elementary, and the other has none.** With one
variable the Subspace Theorem is unavailable (it needs at least two) and unnecessary:
`|q| ^ (2 + ε) * ‖β‖ < 1` bounds `q` outright. The theorem on `∑ i, q i * α i` never meets that
case, because its point always carries the numerator as an extra coordinate, so `Option ι` is
nontrivial as soon as `ι` is nonempty; its only base case is the empty index type.

## References

W.M. Schmidt, *Simultaneous approximation to algebraic numbers by elements of a number field*,
Monatshefte für Mathematik **79** (1970), 55–66; *Diophantine Approximation*, Springer Lecture
Notes in Mathematics 785 (1980), Ch. VI. E. Bombieri and W. Gubler, *Heights in Diophantine
Geometry*, Cambridge University Press (2006), Remark 7.3.4.

This is part of Layer 7.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Finset Height

universe u

section Indep

variable {A : Type*} [Field A] [CharZero A] {ι : Type*} [Fintype ι]

theorem forall_eq_zero_of_linearIndependent_option {β : ι → A}
    (hβ : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : A) β)
    (c₀ : ℚ) (c : ι → ℚ) (hrel : (c₀ : A) + ∑ i, (c i : A) * β i = 0) :
    c₀ = 0 ∧ ∀ i, c i = 0 := by
  rw [Fintype.linearIndependent_iff] at hβ
  have hg : ∑ o : Option ι, (o.elim c₀ c) • (o.elim (1 : A) β) = 0 := by
    rw [Fintype.sum_option]
    simpa [Rat.smul_def] using hrel
  have h := hβ (fun o : Option ι ↦ o.elim c₀ c) hg
  exact ⟨h none, fun i ↦ h (some i)⟩

omit [CharZero A] in
theorem ne_zero_of_forall_eq_zero {β : ι → A}
    (hβ : ∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : A) + ∑ i, (c i : A) * β i = 0 → c₀ = 0 ∧ ∀ i, c i = 0)
    (i : ι) : β i ≠ 0 := by
  classical
  intro h0
  have hrel : ((0 : ℚ) : A) + ∑ t, (((if t = i then 1 else 0 : ℚ)) : A) * β t = 0 := by
    rw [Rat.cast_zero, zero_add, Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, h0, mul_zero]
    · intro t _ hti
      rw [ite_eq_right hti, Rat.cast_zero, zero_mul]
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  have h := (hβ 0 _ hrel).2 i
  rw [ite_eq_left rfl] at h
  exact one_ne_zero h

theorem forall_eq_zero_sub [DecidableEq ι] {β : ι → A}
    (hβ : ∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : A) + ∑ i, (c i : A) * β i = 0 → c₀ = 0 ∧ ∀ i, c i = 0)
    {k : ι} {d : ι → ℚ} :
    ∀ (e₀ : ℚ) (e : {i : ι // i ≠ k} → ℚ),
      (e₀ : A) + ∑ i : {i : ι // i ≠ k}, (e i : A) * (β i.1 - β k * ((d i.1 / d k : ℚ) : A)) = 0 →
        e₀ = 0 ∧ ∀ i, e i = 0 := by
  intro e₀ e hrel
  classical
  have hS : ∑ i : {i : ι // i ≠ k}, (e i : A) * (β i.1 - β k * ((d i.1 / d k : ℚ) : A))
      = (∑ i : {i : ι // i ≠ k}, (e i : A) * β i.1)
        - β k * ((∑ t : {i : ι // i ≠ k}, e t * (d t.1 / d k) : ℚ) : A) := by
    rw [Rat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Rat.cast_mul]
    ring
  rw [hS] at hrel
  set c : ι → ℚ := fun i ↦ if h : i = k then -(∑ t : {i : ι // i ≠ k}, e t * (d t.1 / d k))
    else e ⟨i, h⟩ with hc
  have hck : c k = -(∑ t : {i : ι // i ≠ k}, e t * (d t.1 / d k)) := by simp [hc]
  have hci : ∀ i : {i : ι // i ≠ k}, c i.1 = e i := fun i ↦ by simp [hc, i.2]
  have hsub : ∑ i ∈ Finset.univ.erase k, (c i : A) * β i
      = ∑ i : {i : ι // i ≠ k}, (e i : A) * β i.1 := by
    rw [Finset.sum_subtype (p := fun i ↦ i ≠ k) (Finset.univ.erase k) (fun x ↦ by simp)
      (fun i ↦ (c i : A) * β i)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hci i]
  have hexpand : (e₀ : A) + ∑ i, (c i : A) * β i = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hsub, hck, Rat.cast_neg]
    linear_combination hrel
  obtain ⟨h0, h1⟩ := hβ e₀ c hexpand
  exact ⟨h0, fun i ↦ (hci i) ▸ h1 i.1⟩

theorem forall_eq_zero_shift {β : ι → A}
    (hβ : ∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : A) + ∑ i, (c i : A) * β i = 0 → c₀ = 0 ∧ ∀ i, c i = 0)
    (r : ι → ℚ) :
    ∀ (e₀ : ℚ) (e : ι → ℚ),
      (e₀ : A) + ∑ i, (e i : A) * (β i + ((r i : ℚ) : A)) = 0 → e₀ = 0 ∧ ∀ i, e i = 0 := by
  intro e₀ e hrel
  have hS : ∑ i, (e i : A) * (β i + ((r i : ℚ) : A))
      = (∑ i, (e i : A) * β i) + ((∑ i, e i * r i : ℚ) : A) := by
    rw [Rat.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Rat.cast_mul]
    ring
  rw [hS] at hrel
  have hexpand : ((e₀ + ∑ i, e i * r i : ℚ) : A) + ∑ i, (e i : A) * β i = 0 := by
    rw [Rat.cast_add]
    linear_combination hrel
  obtain ⟨h0, h1⟩ := hβ _ e hexpand
  exact ⟨by simpa [h1] using h0, h1⟩
end Indep

namespace Int

/-- A nonzero integer has absolute value at least one, in `ℝ`. -/
theorem one_le_abs_cast {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ |(m : ℝ)| := by
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hm
  rwa [Int.cast_one, Int.cast_abs] at h2

/-- The product of the absolute values of a nowhere-vanishing integer tuple is at least one. -/
theorem one_le_prod_abs {ι : Type*} [Fintype ι] {x : ι → ℤ} (hx : ∀ i, x i ≠ 0) :
    (1 : ℝ) ≤ ∏ i, |((x i : ℤ) : ℝ)| :=
  Finset.one_le_prod₀ fun i _ ↦ Int.one_le_abs_cast (hx i)

/-- The sup norm of a nowhere-vanishing integer tuple is at most the product of the absolute
values of its coordinates: the product is the finer measure of size, and it is what Schmidt's
theorems are stated against. -/
theorem iSup_abs_le_prod_abs {ι : Type*} [Fintype ι] {x : ι → ℤ} (hx : ∀ i, x i ≠ 0) :
    (⨆ i, |((x i : ℤ) : ℝ)|) ≤ ∏ i, |((x i : ℤ) : ℝ)| := by
  classical
  refine Real.iSup_le (fun i ↦ ?_) (le_trans zero_le_one (Int.one_le_prod_abs hx))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (abs_nonneg _)
    (Finset.one_le_prod₀ fun t _ ↦ Int.one_le_abs_cast (hx t))

end Int

namespace Finset

/-- Products over `Option ι` with the `none` coordinate removed. -/
theorem prod_erase_none {M : Type*} [CommMonoid M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Option ι → M) : ∏ o ∈ Finset.univ.erase (none : Option ι), f o = ∏ i, f (some i) := by
  have h : (Finset.univ : Finset (Option ι)).erase none
      = (Finset.univ : Finset ι).map Function.Embedding.some := by
    ext o
    cases o with
    | none => simp
    | some i => simp
  rw [h, Finset.prod_map]
  rfl
end Finset

namespace Int

/-- **Northcott for the product**: only finitely many nowhere-vanishing integer tuples have the
product of the absolute values of their coordinates below a bound. -/
theorem finite_setOf_prod_abs_le {ι : Type*} [Fintype ι] (B : ℝ) :
    {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∏ i, |((q i : ℤ) : ℝ)| ≤ B}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.pi (fun _ : ι ↦ Set.finite_Icc (-⌈B⌉) ⌈B⌉)) ?_
  rintro q ⟨hne0, hle⟩
  refine Set.mem_univ_pi.2 fun i ↦ ?_
  have hi : |((q i : ℤ) : ℝ)| ≤ B := by
    refine le_trans ?_ hle
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    exact le_mul_of_one_le_right (abs_nonneg _)
      (Finset.one_le_prod₀ fun t _ ↦ Int.one_le_abs_cast (hne0 t))
  have hceil : |q i| ≤ ⌈B⌉ := by
    have h3 : |((q i : ℤ) : ℝ)| ≤ ((⌈B⌉ : ℤ) : ℝ) := hi.trans (Int.le_ceil B)
    rw [← Int.cast_abs] at h3
    exact_mod_cast h3
  simpa only [Set.mem_Icc] using abs_le.mp hceil
end Int

namespace Complex

/-- **Schmidt's linear form theorem, the induction.** -/
private theorem finite_setOf_prod_lt_aux : ∀ (n : ℕ) {ι : Type u} [Fintype ι] {β : ι → ℂ},
    (∀ i, IsAlgebraic ℚ (β i)) →
    (∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : ℂ) + ∑ i, (c i : ℂ) * β i = 0 → c₀ = 0 ∧ ∀ i, c i = 0) →
    Fintype.card ι ≤ n → ∀ {ε : ℝ}, 0 < ε →
      {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
        (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * ‖∑ i, β i * ((x i : ℤ) : ℂ)‖ < 1}.Finite := by
  intro n
  induction n with
  | zero =>
      intro ι _ β _ _ hcard ε _
      have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact Set.Finite.subset (Set.finite_singleton (fun _ ↦ (0 : ℤ)))
        fun x _ ↦ Set.mem_singleton_iff.2 (funext fun i ↦ isEmptyElim i)
  | succ n ih =>
      intro ι _ β halg hind hcard ε hε
      classical
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
      · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc0
        exact Set.Finite.subset (Set.finite_singleton (fun _ ↦ (0 : ℤ)))
          fun x _ ↦ Set.mem_singleton_iff.2 (funext fun i ↦ isEmptyElim i)
      have hβne : ∀ i, β i ≠ 0 := ne_zero_of_forall_eq_zero hind
      have hnonempty : Nonempty ι := Fintype.card_pos_iff.mp hcpos
      rcases le_or_gt (Fintype.card ι) 1 with hc1 | hc2
      · -- one variable: the inequality bounds the variable outright
        have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hc1
        obtain ⟨j⟩ := hnonempty
        refine Set.Finite.of_finite_image (f := fun x : ι → ℤ ↦ x j) ?_ ?_
        · refine Set.Finite.subset (Set.finite_Icc (-⌈‖β j‖⁻¹⌉) ⌈‖β j‖⁻¹⌉) ?_
          rintro m ⟨x, ⟨hne0, hlt⟩, rfl⟩
          have hprod : ∏ i, |((x i : ℤ) : ℝ)| = |((x j : ℤ) : ℝ)| :=
            Finset.prod_eq_single_of_mem j (Finset.mem_univ j)
              (fun b _ hb ↦ absurd (Subsingleton.elim b j) hb)
          have hsum : ∑ i, β i * ((x i : ℤ) : ℂ) = β j * ((x j : ℤ) : ℂ) :=
            Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
              (fun b _ hb ↦ absurd (Subsingleton.elim b j) hb)
          rw [hprod, hsum, norm_mul] at hlt
          have hA1 : (1 : ℝ) ≤ |((x j : ℤ) : ℝ)| := Int.one_le_abs_cast (hne0 j)
          have hpow : (1 : ℝ) ≤ |((x j : ℤ) : ℝ)| ^ (1 + ε) := by
            have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hA1
              (by linarith : (0 : ℝ) ≤ 1 + ε)
            rwa [Real.one_rpow] at h
          have hxjnorm : ‖((x j : ℤ) : ℂ)‖ = |((x j : ℤ) : ℝ)| := by simp
          rw [hxjnorm] at hlt
          have hβpos : 0 < ‖β j‖ := norm_pos_iff.mpr (hβne j)
          have hmul : ‖β j‖ * |((x j : ℤ) : ℝ)| < 1 := by
            nlinarith [mul_nonneg (norm_nonneg (β j)) (abs_nonneg (((x j : ℤ) : ℝ)))]
          have habs : |((x j : ℤ) : ℝ)| ≤ ‖β j‖⁻¹ := by
            rw [← one_div, le_div_iff₀ hβpos, mul_comm]
            exact hmul.le
          have hceil : |x j| ≤ ⌈‖β j‖⁻¹⌉ := by
            have h3 : |((x j : ℤ) : ℝ)| ≤ ((⌈‖β j‖⁻¹⌉ : ℤ) : ℝ) := habs.trans (Int.le_ceil _)
            rw [← Int.cast_abs] at h3
            exact_mod_cast h3
          simpa only [Set.mem_Icc] using abs_le.mp hceil
        · intro x _ y _ h
          funext i
          rw [Subsingleton.elim i j]
          exact h
      · -- at least two variables: the Subspace Theorem
        have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hc2
        obtain ⟨j⟩ := hnonempty
        obtain ⟨T, hTproper, hTmem⟩ :=
          Complex.exists_finset_submodule_of_norm_sum_mul_prod_le halg (hβne j) hε
        have hkey : ∀ x : ι → ℤ, (∀ i, x i ≠ 0) →
            (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * ‖∑ i, β i * ((x i : ℤ) : ℂ)‖ < 1 →
            ‖∑ k, β k * ((x k : ℤ) : ℂ)‖ * ∏ i ∈ Finset.univ.erase j, |((x i : ℤ) : ℝ)|
              ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) := by
          intro x hne0 hlt
          set P : ℝ := ∏ i, |((x i : ℤ) : ℝ)| with hP
          have hP1 : (1 : ℝ) ≤ P := Int.one_le_prod_abs hne0
          have hP0 : (0 : ℝ) < P := lt_of_lt_of_le zero_lt_one hP1
          have hpowpos : (0 : ℝ) < P ^ (1 + ε) := Real.rpow_pos_of_pos hP0 _
          have hSle : ‖∑ k, β k * ((x k : ℤ) : ℂ)‖ ≤ P ^ (-(1 + ε)) := by
            rw [Real.rpow_neg hP0.le, ← one_div, le_div_iff₀ hpowpos]
            nlinarith [hlt]
          have herase : ∏ i ∈ Finset.univ.erase j, |((x i : ℤ) : ℝ)| ≤ P := by
            rw [hP, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
            exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)
              (Int.one_le_abs_cast (hne0 j))
          have hM : (⨆ i, |((x i : ℤ) : ℝ)|) ≤ P := Int.iSup_abs_le_prod_abs hne0
          have hMpos : (0 : ℝ) < ⨆ i, |((x i : ℤ) : ℝ)| :=
            lt_of_lt_of_le zero_lt_one
              ((Int.one_le_abs_cast (hne0 j)).trans (Finite.le_ciSup_of_le j le_rfl))
          have hPP : P ^ (-(1 + ε)) * P = P ^ (-ε) := by
            nth_rewrite 2 [← Real.rpow_one P]
            rw [← Real.rpow_add hP0, show -(1 + ε) + 1 = -ε by ring]
          calc ‖∑ k, β k * ((x k : ℤ) : ℂ)‖ * ∏ i ∈ Finset.univ.erase j, |((x i : ℤ) : ℝ)|
              ≤ P ^ (-(1 + ε)) * P :=
                mul_le_mul hSle herase (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)
                  (Real.rpow_nonneg hP0.le _)
            _ = P ^ (-ε) := hPP
            _ ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) :=
                Real.rpow_le_rpow_of_nonpos hMpos hM (by linarith)
        have hx0 : ∀ x : ι → ℤ, (∀ i, x i ≠ 0) → (fun i ↦ ((x i : ℤ) : ℚ)) ≠ 0 := by
          intro x hne0 h0
          have h := congrFun h0 j
          simp only [Pi.zero_apply] at h
          exact hne0 j (by exact_mod_cast h)
        have hcover : {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
              (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * ‖∑ i, β i * ((x i : ℤ) : ℂ)‖ < 1}
            ⊆ ⋃ V ∈ (T : Set (Submodule ℚ (ι → ℚ))),
                {x : ι → ℤ | ((∀ i, x i ≠ 0) ∧
                  (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * ‖∑ i, β i * ((x i : ℤ) : ℂ)‖ < 1)
                  ∧ (fun i ↦ ((x i : ℤ) : ℚ)) ∈ V} := by
          intro x hx
          obtain ⟨V, hV, hmem⟩ := hTmem x (hx0 x hx.1) (hkey x hx.1 hx.2)
          exact Set.mem_biUnion hV ⟨hx, hmem⟩
        refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun V hV ↦ ?_) hcover
        obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
          (lt_top_iff_ne_top.mpr (hTproper V hV)) inferInstance
        set c : ι → ℚ := fun i ↦ f (fun t ↦ if i = t then 1 else 0) with hcdef
        have hfx : ∀ y : ι → ℚ, f y = ∑ i, y i * c i := by
          intro y
          rw [LinearMap.pi_apply_eq_sum_univ f y]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]
        obtain ⟨k, hck⟩ : ∃ k, c k ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, hcon])
        have hrel : ∀ x : ι → ℤ, (fun i ↦ ((x i : ℤ) : ℚ)) ∈ V →
            ∑ i, ((x i : ℤ) : ℚ) * c i = 0 := by
          intro x hxV
          have hmap : f (fun i ↦ ((x i : ℤ) : ℚ)) ∈ Submodule.map f V :=
            Submodule.mem_map_of_mem hxV
          rw [hfV, Submodule.mem_bot] at hmap
          rw [← hfx]
          exact hmap
        have hγalg : ∀ i : {i : ι // i ≠ k},
            IsAlgebraic ℚ (β i.1 - β k * ((c i.1 / c k : ℚ) : ℂ)) := fun i ↦
          (((halg i.1).isIntegral).sub
            (((halg k).isIntegral).mul isIntegral_algebraMap)).isAlgebraic
        have hγind := forall_eq_zero_sub hind (k := k) (d := c)
        have hcard' : Fintype.card {i : ι // i ≠ k} ≤ n := by
          have h1 : Fintype.card {i : ι // i ≠ k} = Fintype.card ι - 1 := by
            simp [Fintype.card_subtype_compl]
          omega
        have hckC : ((c k : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hck
        refine Set.Finite.of_finite_image (f := fun x : ι → ℤ ↦ fun i : {i : ι // i ≠ k} ↦ x i.1)
          (Set.Finite.subset (ih hγalg hγind hcard' hε) ?_) ?_
        · rintro _ ⟨x, ⟨⟨hne0, hlt⟩, hxV⟩, rfl⟩
          have hrelC : ∑ i ∈ Finset.univ.erase k, ((x i : ℤ) : ℂ) * ((c i : ℚ) : ℂ)
              = -(((x k : ℤ) : ℂ) * ((c k : ℚ) : ℂ)) := by
            have h1 : ((∑ i, ((x i : ℤ) : ℚ) * c i : ℚ) : ℂ) = 0 := by rw [hrel x hxV]; simp
            push_cast at h1
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1
            exact eq_neg_of_add_eq_zero_right h1
          have hsum : ∑ i : {i : ι // i ≠ k},
                (β i.1 - β k * ((c i.1 / c k : ℚ) : ℂ)) * ((x i.1 : ℤ) : ℂ)
              = ∑ i, β i * ((x i : ℤ) : ℂ) := by
            have hsub : ∑ i : {i : ι // i ≠ k},
                  (β i.1 - β k * ((c i.1 / c k : ℚ) : ℂ)) * ((x i.1 : ℤ) : ℂ)
                = ∑ i ∈ Finset.univ.erase k,
                    (β i - β k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ) :=
              (Finset.sum_subtype _ (fun i ↦ by simp)
                (fun i ↦ (β i - β k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ))).symm
            have hterm : ∀ i ∈ Finset.univ.erase k,
                (β i - β k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ)
                  = β i * ((x i : ℤ) : ℂ)
                    - (β k / ((c k : ℚ) : ℂ)) * (((x i : ℤ) : ℂ) * ((c i : ℚ) : ℂ)) := by
              intro i _
              push_cast
              ring
            rw [hsub, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hrelC,
              ← Finset.add_sum_erase _ (fun i ↦ β i * ((x i : ℤ) : ℂ)) (Finset.mem_univ k)]
            field_simp
            ring
          have hsubprod : ∏ i : {i : ι // i ≠ k}, |((x i.1 : ℤ) : ℝ)|
              = ∏ i ∈ Finset.univ.erase k, |((x i : ℤ) : ℝ)| :=
            (Finset.prod_subtype _ (fun t ↦ by simp) (fun i ↦ |((x i : ℤ) : ℝ)|)).symm
          have hprodle : ∏ i : {i : ι // i ≠ k}, |((x i.1 : ℤ) : ℝ)|
              ≤ ∏ i, |((x i : ℤ) : ℝ)| := by
            rw [hsubprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
            exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)
              (Int.one_le_abs_cast (hne0 k))
          refine ⟨fun i ↦ hne0 i.1, ?_⟩
          rw [hsum]
          refine lt_of_le_of_lt ?_ hlt
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact Real.rpow_le_rpow (Finset.prod_nonneg fun i _ ↦ abs_nonneg _) hprodle
            (by linarith)
        · rintro x ⟨-, hxV⟩ y ⟨-, hyV⟩ hxy
          funext i
          by_cases hik : i = k
          · rw [hik]
            have h1 := hrel x hxV
            have h2 := hrel y hyV
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1 h2
            have heq : ∑ t ∈ Finset.univ.erase k, ((x t : ℤ) : ℚ) * c t
                = ∑ t ∈ Finset.univ.erase k, ((y t : ℤ) : ℚ) * c t :=
              Finset.sum_congr rfl fun t ht ↦ by
                rw [show x t = y t from congrFun hxy ⟨t, (Finset.mem_erase.mp ht).1⟩]
            rw [heq] at h1
            have hxy' : ((x k : ℤ) : ℚ) * c k = ((y k : ℤ) : ℚ) * c k := by linarith
            exact_mod_cast mul_right_cancel₀ hck hxy'
          · exact congrFun hxy ⟨i, hik⟩

/-- **Schmidt's linear form theorem over `ℂ`.** For complex algebraic `β 1, …, β n` with
`1, β 1, …, β n` linearly independent over `ℚ` and `ε > 0`, only finitely many integer points
with no vanishing coordinate satisfy `(∏ i, |x i|) ^ (1 + ε) * ‖∑ i, β i * x i‖ < 1`. -/
theorem finite_setOf_prod_abs_mul_norm_sum_lt {ι : Type u} [Fintype ι] {β : ι → ℂ}
    (halg : ∀ i, IsAlgebraic ℚ (β i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℂ) β) {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
      (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * ‖∑ i, β i * ((x i : ℤ) : ℂ)‖ < 1}.Finite :=
  finite_setOf_prod_lt_aux (Fintype.card ι) halg
    (forall_eq_zero_of_linearIndependent_option hind) le_rfl hε

end Complex

namespace Real

/-- **Schmidt's linear form theorem over `ℝ`, the induction hypothesis form.** -/
private theorem finite_setOf_prod_lt_real_aux {ι : Type u} [Fintype ι] {β : ι → ℝ}
    (halg : ∀ i, IsAlgebraic ℚ (β i))
    (hind : ∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : ℝ) + ∑ i, (c i : ℝ) * β i = 0 → c₀ = 0 ∧ ∀ i, c i = 0)
    {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
      (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * |∑ i, β i * ((x i : ℤ) : ℝ)| < 1}.Finite := by
  have hcast : ∀ x : ι → ℤ, ∑ i, ((β i : ℝ) : ℂ) * ((x i : ℤ) : ℂ)
      = ((∑ i, β i * ((x i : ℤ) : ℝ) : ℝ) : ℂ) := by
    intro x
    push_cast
    ring
  have hindC : ∀ (c₀ : ℚ) (c : ι → ℚ),
      (c₀ : ℂ) + ∑ i, (c i : ℂ) * ((β i : ℝ) : ℂ) = 0 → c₀ = 0 ∧ ∀ i, c i = 0 := by
    intro c₀ c hrel
    refine hind c₀ c ?_
    have h : (((c₀ : ℝ) + ∑ i, (c i : ℝ) * β i : ℝ) : ℂ) = 0 := by
      rw [← hrel]
      push_cast
      ring
    exact_mod_cast h
  refine Set.Finite.subset
    (Complex.finite_setOf_prod_lt_aux (Fintype.card ι) (β := fun i ↦ ((β i : ℝ) : ℂ))
      (fun i ↦ (halg i).algebraMap) hindC le_rfl hε) ?_
  rintro x ⟨hne0, hlt⟩
  refine ⟨hne0, ?_⟩
  rw [hcast x, Complex.norm_real]
  exact hlt

open Complex in
/-- **Schmidt's theorem on linear forms, the induction.** -/
private theorem finite_setOf_dist_lt_aux : ∀ (n : ℕ) {ι : Type u} [Fintype ι] {α : ι → ℝ},
    (∀ i, IsAlgebraic ℚ (α i)) →
    (∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : ℝ) + ∑ i, (c i : ℝ) * α i = 0 → c₀ = 0 ∧ ∀ i, c i = 0) →
    Fintype.card ι ≤ n → ∀ {ε : ℝ}, 0 < ε →
      {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
        (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
          * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1}.Finite := by
  intro n
  induction n with
  | zero =>
      intro ι _ α _ _ hcard ε _
      have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact Set.Finite.subset (Set.finite_singleton (fun _ ↦ (0 : ℤ)))
        fun x _ ↦ Set.mem_singleton_iff.2 (funext fun i ↦ isEmptyElim i)
  | succ n ih =>
      intro ι _ α halg hind hcard ε hε
      classical
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
      · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc0
        exact Set.Finite.subset (Set.finite_singleton (fun _ ↦ (0 : ℤ)))
          fun x _ ↦ Set.mem_singleton_iff.2 (funext fun i ↦ isEmptyElim i)
      have hnonempty : Nonempty ι := Fintype.card_pos_iff.mp hcpos
      obtain ⟨i₀⟩ := hnonempty
      have hnt : Nontrivial (Option ι) := by
        refine Fintype.one_lt_card_iff_nontrivial.mp ?_
        simpa using hcpos
      set C : ℝ := (∑ i, |α i|) + 2 with hCdef
      have hC2 : (2 : ℝ) ≤ C := by
        have h0 : (0 : ℝ) ≤ ∑ i, |α i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
        rw [hCdef]; linarith
      set a : Option ι → ℂ := fun o ↦ o.elim (-1) (fun i ↦ ((α i : ℝ) : ℂ)) with hadef
      have haalg : ∀ o, IsAlgebraic ℚ (a o) := by
        intro o
        cases o with
        | none =>
            change IsAlgebraic ℚ (-1 : ℂ)
            exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
        | some i =>
            change IsAlgebraic ℚ (((α i : ℝ) : ℂ))
            exact (halg i).algebraMap
      have hanone : a none ≠ 0 := by
        change (-1 : ℂ) ≠ 0
        norm_num
      obtain ⟨T, hTproper, hTmem⟩ :=
        Complex.exists_finset_submodule_of_norm_sum_mul_prod_le haalg hanone
          (ε := ε / 2) (by linarith)
      have hval : ∀ (q : ι → ℤ) (p : ℤ),
          ‖∑ k, a k * ((((fun o : Option ι ↦ o.elim p q) k : ℤ)) : ℂ)‖
            = |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| := by
        intro q p
        rw [Fintype.sum_option]
        have hh : a none * ((((fun o : Option ι ↦ o.elim p q) none : ℤ)) : ℂ)
              + ∑ i, a (some i) * ((((fun o : Option ι ↦ o.elim p q) (some i) : ℤ)) : ℂ)
            = ((∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ) : ℝ) : ℂ) := by
          simp only [hadef, Option.elim_none, Option.elim_some]
          push_cast
          ring
        rw [hh, Complex.norm_real, Real.norm_eq_abs]
      have hprodpt : ∀ (q : ι → ℤ) (p : ℤ),
          ∏ o ∈ Finset.univ.erase (none : Option ι),
              |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)|
            = ∏ i, |((q i : ℤ) : ℝ)| := fun q p ↦ Finset.prod_erase_none _
      have hxne : ∀ (q : ι → ℤ) (p : ℤ), (∀ i, q i ≠ 0) →
          (fun o ↦ ((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℚ)) ≠ 0 := by
        intro q p hne0 h0
        have h := congrFun h0 (some i₀)
        simp only [Pi.zero_apply] at h
        exact hne0 i₀ (by exact_mod_cast h)
      have hkey : ∀ (q : ι → ℤ) (p : ℤ), (∀ i, q i ≠ 0) →
          C < ∏ i, |((q i : ℤ) : ℝ)| →
          (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε) * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1 →
          ‖∑ k, a k * ((((fun o : Option ι ↦ o.elim p q) k : ℤ)) : ℂ)‖
              * ∏ o ∈ Finset.univ.erase (none : Option ι),
                  |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)|
            ≤ (⨆ o, |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)|) ^ (-(ε / 2)) := by
        intro q p hne0 hPC hlt
        set P : ℝ := ∏ i, |((q i : ℤ) : ℝ)| with hP
        have hP1 : (1 : ℝ) ≤ P := Int.one_le_prod_abs hne0
        have hP0 : (0 : ℝ) < P := lt_of_lt_of_le zero_lt_one hP1
        have hqiP : ∀ i, |((q i : ℤ) : ℝ)| ≤ P := by
          intro i
          rw [hP, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
          exact le_mul_of_one_le_right (abs_nonneg _)
            (Finset.one_le_prod₀ fun t _ ↦ Int.one_le_abs_cast (hne0 t))
        have hpowpos : (0 : ℝ) < P ^ (1 + ε) := Real.rpow_pos_of_pos hP0 _
        have hpow1 : (1 : ℝ) ≤ P ^ (1 + ε) := by
          have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hP1
            (by linarith : (0 : ℝ) ≤ 1 + ε)
          rwa [Real.one_rpow] at h
        have hdle : |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| ≤ P ^ (-(1 + ε)) := by
          rw [Real.rpow_neg hP0.le, ← one_div, le_div_iff₀ hpowpos]
          nlinarith [hlt]
        have hd1 : |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| ≤ 1 := by
          nlinarith [abs_nonneg (∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ))]
        -- the sup norm of the extended point
        have hpabs : |((p : ℤ) : ℝ)| ≤ C * P := by
          have hsum : |∑ i, α i * ((q i : ℤ) : ℝ)| ≤ (∑ i, |α i|) * P := by
            calc |∑ i, α i * ((q i : ℤ) : ℝ)| ≤ ∑ i, |α i * ((q i : ℤ) : ℝ)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i, |α i| * P := by
                  refine Finset.sum_le_sum fun i _ ↦ ?_
                  rw [abs_mul]
                  exact mul_le_mul_of_nonneg_left (hqiP i) (abs_nonneg _)
              _ = (∑ i, |α i|) * P := by rw [Finset.sum_mul]
          have h1 : |((p : ℤ) : ℝ)| ≤ |∑ i, α i * ((q i : ℤ) : ℝ)| + 1 := by
            have h2 := abs_sub_abs_le_abs_sub ((p : ℤ) : ℝ) (∑ i, α i * ((q i : ℤ) : ℝ))
            rw [abs_sub_comm] at h2
            linarith [hd1]
          rw [hCdef]
          nlinarith
        have hMle : (⨆ o, |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)|) ≤ P * P := by
          refine Real.iSup_le (fun o ↦ ?_) (by positivity)
          cases o with
          | none => exact le_trans hpabs (by nlinarith)
          | some i => exact le_trans (hqiP i) (by nlinarith)
        have hMpos : (0 : ℝ) < ⨆ o, |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)| :=
          lt_of_lt_of_le zero_lt_one
            ((Int.one_le_abs_cast (hne0 i₀)).trans (Finite.le_ciSup_of_le (some i₀) le_rfl))
        have hPP : P ^ (-(1 + ε)) * P = P ^ (-ε) := by
          nth_rewrite 2 [← Real.rpow_one P]
          rw [← Real.rpow_add hP0, show -(1 + ε) + 1 = -ε by ring]
        have hsq : (P * P) ^ (-(ε / 2)) = P ^ (-ε) := by
          rw [show P * P = P ^ (2 : ℝ) by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring,
            ← Real.rpow_mul hP0.le, show (2 : ℝ) * (-(ε / 2)) = -ε by ring]
        rw [hval q p, hprodpt q p]
        calc |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| * P ≤ P ^ (-(1 + ε)) * P := by
              exact mul_le_mul_of_nonneg_right hdle hP0.le
          _ = P ^ (-ε) := hPP
          _ = (P * P) ^ (-(ε / 2)) := hsq.symm
          _ ≤ (⨆ o, |((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℝ)|) ^ (-(ε / 2)) :=
              Real.rpow_le_rpow_of_nonpos hMpos hMle (by linarith)
      -- the cover
      have hcover : {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
            (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
              * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1}
          ⊆ {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∏ i, |((q i : ℤ) : ℝ)| ≤ C}
            ∪ ⋃ V ∈ (T : Set (Submodule ℚ (Option ι → ℚ))),
                {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
                  ((∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
                      * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1)
                    ∧ (fun o ↦ ((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℚ)) ∈ V} := by
        rintro q ⟨hne0, p, hlt⟩
        by_cases hCq : ∏ i, |((q i : ℤ) : ℝ)| ≤ C
        · exact Or.inl ⟨hne0, hCq⟩
        · obtain ⟨V, hV, hmem⟩ := hTmem (fun o : Option ι ↦ o.elim p q) (hxne q p hne0)
            (hkey q p hne0 (not_le.mp hCq) hlt)
          exact Or.inr (Set.mem_biUnion hV ⟨hne0, p, hlt, hmem⟩)
      refine Set.Finite.subset (Set.Finite.union (Int.finite_setOf_prod_abs_le C)
        (Set.Finite.biUnion T.finite_toSet fun V hV ↦ ?_)) hcover
      obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
        (lt_top_iff_ne_top.mpr (hTproper V hV)) inferInstance
      set c : Option ι → ℚ := fun o ↦ f (fun t ↦ if o = t then 1 else 0) with hcdef
      have hfx : ∀ y : Option ι → ℚ, f y = ∑ o, y o * c o := by
        intro y
        rw [LinearMap.pi_apply_eq_sum_univ f y]
        exact Finset.sum_congr rfl fun o _ ↦ by rw [smul_eq_mul]
      obtain ⟨o₀, hco₀⟩ : ∃ o, c o ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, hcon])
      have hrel : ∀ y : Option ι → ℤ, (fun o ↦ ((y o : ℤ) : ℚ)) ∈ V →
          ∑ o, ((y o : ℤ) : ℚ) * c o = 0 := by
        intro y hyV
        have hmap : f (fun o ↦ ((y o : ℤ) : ℚ)) ∈ Submodule.map f V :=
          Submodule.mem_map_of_mem hyV
        rw [hfV, Submodule.mem_bot] at hmap
        rw [← hfx]
        exact hmap
      have hrelqp : ∀ (q : ι → ℤ) (p : ℤ),
          (fun o ↦ ((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℚ)) ∈ V →
          ((p : ℤ) : ℚ) * c none + ∑ i, ((q i : ℤ) : ℚ) * c (some i) = 0 := by
        intro q p hmem
        have h := hrel _ hmem
        rwa [Fintype.sum_option] at h
      by_cases hcnone : c none = 0
      · -- the relation lives among the `q` alone: one variable is eliminated
        obtain ⟨k, hck⟩ : ∃ k : ι, c (some k) ≠ 0 := by
          cases o₀ with
          | none => exact absurd hcnone hco₀
          | some k => exact ⟨k, hco₀⟩
        have hdkR : ((c (some k) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hck
        have hγalg : ∀ i : {i : ι // i ≠ k},
            IsAlgebraic ℚ (α i.1 - α k * ((c (some i.1) / c (some k) : ℚ) : ℝ)) := fun i ↦
          (((halg i.1).isIntegral).sub
            (((halg k).isIntegral).mul isIntegral_algebraMap)).isAlgebraic
        have hγind := forall_eq_zero_sub hind (k := k) (d := fun i ↦ c (some i))
        have hcard' : Fintype.card {i : ι // i ≠ k} ≤ n := by
          have h1 : Fintype.card {i : ι // i ≠ k} = Fintype.card ι - 1 := by
            simp [Fintype.card_subtype_compl]
          omega
        have hrelq : ∀ (q : ι → ℤ) (p : ℤ),
            (fun o ↦ ((((fun o : Option ι ↦ o.elim p q) o : ℤ)) : ℚ)) ∈ V →
            ∑ i, ((q i : ℤ) : ℚ) * c (some i) = 0 := by
          intro q p hmem
          have h := hrelqp q p hmem
          rwa [hcnone, mul_zero, zero_add] at h
        refine Set.Finite.of_finite_image (f := fun q : ι → ℤ ↦ fun i : {i : ι // i ≠ k} ↦ q i.1)
          (Set.Finite.subset (ih hγalg hγind hcard' hε) ?_) ?_
        · rintro _ ⟨q, ⟨hne0, p, hlt, hmem⟩, rfl⟩
          have hrq := hrelq q p hmem
          have hrelC : ∑ i ∈ Finset.univ.erase k, ((q i : ℤ) : ℝ) * ((c (some i) : ℚ) : ℝ)
              = -(((q k : ℤ) : ℝ) * ((c (some k) : ℚ) : ℝ)) := by
            have h1 : ((∑ i, ((q i : ℤ) : ℚ) * c (some i) : ℚ) : ℝ) = 0 := by rw [hrq]; simp
            push_cast at h1
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1
            exact eq_neg_of_add_eq_zero_right h1
          have hsum : ∑ i : {i : ι // i ≠ k},
                (α i.1 - α k * ((c (some i.1) / c (some k) : ℚ) : ℝ)) * ((q i.1 : ℤ) : ℝ)
              = ∑ i, α i * ((q i : ℤ) : ℝ) := by
            have hsub : ∑ i : {i : ι // i ≠ k},
                  (α i.1 - α k * ((c (some i.1) / c (some k) : ℚ) : ℝ)) * ((q i.1 : ℤ) : ℝ)
                = ∑ i ∈ Finset.univ.erase k,
                    (α i - α k * ((c (some i) / c (some k) : ℚ) : ℝ)) * ((q i : ℤ) : ℝ) :=
              (Finset.sum_subtype _ (fun i ↦ by simp)
                (fun i ↦ (α i - α k * ((c (some i) / c (some k) : ℚ) : ℝ))
                  * ((q i : ℤ) : ℝ))).symm
            have hterm : ∀ i ∈ Finset.univ.erase k,
                (α i - α k * ((c (some i) / c (some k) : ℚ) : ℝ)) * ((q i : ℤ) : ℝ)
                  = α i * ((q i : ℤ) : ℝ)
                    - (α k / ((c (some k) : ℚ) : ℝ))
                      * (((q i : ℤ) : ℝ) * ((c (some i) : ℚ) : ℝ)) := by
              intro i _
              push_cast
              ring
            rw [hsub, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hrelC,
              ← Finset.add_sum_erase _ (fun i ↦ α i * ((q i : ℤ) : ℝ)) (Finset.mem_univ k)]
            field_simp
            ring
          have hsubprod : ∏ i : {i : ι // i ≠ k}, |((q i.1 : ℤ) : ℝ)|
              = ∏ i ∈ Finset.univ.erase k, |((q i : ℤ) : ℝ)| :=
            (Finset.prod_subtype _ (fun t ↦ by simp) (fun i ↦ |((q i : ℤ) : ℝ)|)).symm
          have hprodle : ∏ i : {i : ι // i ≠ k}, |((q i.1 : ℤ) : ℝ)|
              ≤ ∏ i, |((q i : ℤ) : ℝ)| := by
            rw [hsubprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
            exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)
              (Int.one_le_abs_cast (hne0 k))
          refine ⟨fun i ↦ hne0 i.1, p, ?_⟩
          rw [hsum]
          refine lt_of_le_of_lt ?_ hlt
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (Finset.prod_nonneg fun i _ ↦ abs_nonneg _) hprodle
              (by linarith)) (abs_nonneg _)
        · rintro q ⟨-, p, -, hmemq⟩ q' ⟨-, p', -, hmemq'⟩ hqq'
          funext i
          by_cases hik : i = k
          · rw [hik]
            have h1 := hrelq q p hmemq
            have h2 := hrelq q' p' hmemq'
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1 h2
            have heq : ∑ t ∈ Finset.univ.erase k, ((q t : ℤ) : ℚ) * c (some t)
                = ∑ t ∈ Finset.univ.erase k, ((q' t : ℤ) : ℚ) * c (some t) :=
              Finset.sum_congr rfl fun t ht ↦ by
                rw [show q t = q' t from congrFun hqq' ⟨t, (Finset.mem_erase.mp ht).1⟩]
            rw [heq] at h1
            have hqq2 : ((q k : ℤ) : ℚ) * c (some k) = ((q' k : ℤ) : ℚ) * c (some k) := by
              linarith
            exact_mod_cast mul_right_cancel₀ hck hqq2
          · exact congrFun hqq' ⟨i, hik⟩
      · -- the relation determines `p`: Schmidt's linear form theorem applies
        have hβalg : ∀ i, IsAlgebraic ℚ (α i + ((c (some i) / c none : ℚ) : ℝ)) := fun i ↦
          ((halg i).isIntegral.add isIntegral_algebraMap).isAlgebraic
        have hβind := forall_eq_zero_shift hind (fun i ↦ c (some i) / c none)
        refine Set.Finite.subset (finite_setOf_prod_lt_real_aux hβalg hβind hε) ?_
        rintro q ⟨hne0, p, hlt, hmem⟩
        refine ⟨hne0, ?_⟩
        have hrq := hrelqp q p hmem
        have hpq : ∑ i, ((q i : ℤ) : ℚ) * (c (some i) / c none) = -((p : ℤ) : ℚ) := by
          have h3 : ∑ i, ((q i : ℤ) : ℚ) * (c (some i) / c none)
              = (∑ i, ((q i : ℤ) : ℚ) * c (some i)) / c none := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
          rw [h3]
          field_simp
          linarith [hrq]
        have h1 : ∑ i, ((c (some i) / c none : ℚ) : ℝ) * ((q i : ℤ) : ℝ) = -((p : ℤ) : ℝ) := by
          have h2 : ((∑ i, ((q i : ℤ) : ℚ) * (c (some i) / c none) : ℚ) : ℝ)
              = ((-((p : ℤ) : ℚ) : ℚ) : ℝ) := by rw [hpq]
          push_cast at h2
          rw [← h2]
          exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
        have hsum : ∑ i, (α i + ((c (some i) / c none : ℚ) : ℝ)) * ((q i : ℤ) : ℝ)
            = ∑ i, α i * ((q i : ℤ) : ℝ) - ((p : ℤ) : ℝ) := by
          have h4 : ∑ i, α i * ((q i : ℤ) : ℝ) - ((p : ℤ) : ℝ)
              = ∑ i, α i * ((q i : ℤ) : ℝ)
                + ∑ i, ((c (some i) / c none : ℚ) : ℝ) * ((q i : ℤ) : ℝ) := by
            rw [h1]; ring
          rw [h4, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
        rw [hsum]
        exact hlt

/-- **The nearest integer is nearest**: `round x` minimises the distance from `x` to `ℤ`. -/
theorem abs_sub_round_le (x : ℝ) (m : ℤ) : |x - ((round x : ℤ) : ℝ)| ≤ |x - (m : ℝ)| := by
  by_cases h : m = round x
  · rw [h]
  · have hne : ((round x - m : ℤ)) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have h3 : ((1 : ℤ) : ℝ) ≤ ((|round x - m| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hne
    rw [Int.cast_one, Int.cast_abs, Int.cast_sub] at h3
    have h4 := abs_sub_round x
    have h5 : |((round x : ℤ) : ℝ) - (m : ℝ)| ≤ |((round x : ℤ) : ℝ) - x| + |x - (m : ℝ)| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm ((round x : ℤ) : ℝ) x] at h5
    linarith

open Complex in
/-- **Schmidt's theorem on simultaneous approximation, with the explicit independence
hypothesis.** -/
private theorem finite_setOf_mul_prod_dist_lt_aux {ι : Type u} [Fintype ι] {α : ι → ℝ}
    (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : ∀ (c₀ : ℚ) (c : ι → ℚ), (c₀ : ℝ) + ∑ i, (c i : ℝ) * α i = 0 → c₀ = 0 ∧ ∀ i, c i = 0)
    {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ∃ p : ι → ℤ,
      ((q : ℤ) : ℝ) ^ (1 + ε) * ∏ i, |((q : ℤ) : ℝ) * α i - ((p i : ℤ) : ℝ)| < 1}.Finite := by
  classical
  set pt : ℤ → Option ι → ℤ :=
    fun q o ↦ o.elim q (fun i ↦ round (((q : ℤ) : ℝ) * α i)) with hptdef
  have hptnone : ∀ q : ℤ, pt q none = q := fun q ↦ rfl
  have hptsome : ∀ (q : ℤ) (i : ι), pt q (some i) = round (((q : ℤ) : ℝ) * α i) := fun q i ↦ rfl
  have hround : {q : ℤ | 1 ≤ q ∧ ∃ p : ι → ℤ,
        ((q : ℤ) : ℝ) ^ (1 + ε) * ∏ i, |((q : ℤ) : ℝ) * α i - ((p i : ℤ) : ℝ)| < 1}
      ⊆ {q : ℤ | 1 ≤ q ∧ ((q : ℤ) : ℝ) ^ (1 + ε)
          * ∏ i, |((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)| < 1} := by
    rintro q ⟨hq1, p, hlt⟩
    have hq0 : (0 : ℝ) ≤ ((q : ℤ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((q : ℤ) : ℝ) := by exact_mod_cast hq1
      linarith
    refine ⟨hq1, lt_of_le_of_lt ?_ hlt⟩
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq0 _)
    exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _)
      (fun i _ ↦ by rw [hptsome]; exact abs_sub_round_le _ (p i))
  refine Set.Finite.subset ?_ hround
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro q ⟨hq1, hlt⟩
    have hq1R : (1 : ℝ) ≤ ((q : ℤ) : ℝ) := by exact_mod_cast hq1
    have hpow : (1 : ℝ) ≤ ((q : ℤ) : ℝ) ^ (1 + ε) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hq1R
        (by linarith : (0 : ℝ) ≤ 1 + ε)
      rwa [Real.one_rpow] at h
    rw [Finset.prod_of_isEmpty, mul_one] at hlt
    linarith
  have hcpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hnonempty
  obtain ⟨i₀⟩ := hnonempty
  have hnt : Nontrivial (Option ι) := by
    refine Fintype.one_lt_card_iff_nontrivial.mp ?_
    simpa using hcpos
  set C : ℝ := (∑ i, |α i|) + 2 with hCdef
  have hC2 : (2 : ℝ) ≤ C := by
    have h0 : (0 : ℝ) ≤ ∑ i, |α i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    rw [hCdef]; linarith
  set a : Option ι → ℂ := fun o ↦ o.elim 0 (fun i ↦ ((α i : ℝ) : ℂ)) with hadef
  have haalg : ∀ o, IsAlgebraic ℚ (a o) := by
    intro o
    cases o with
    | none =>
        change IsAlgebraic ℚ (0 : ℂ)
        exact isAlgebraic_zero
    | some i =>
        change IsAlgebraic ℚ (((α i : ℝ) : ℂ))
        exact (halg i).algebraMap
  obtain ⟨T, hTproper, hTmem⟩ :=
    Complex.exists_finset_submodule_of_abs_mul_prod_norm_le haalg (none : Option ι)
      (ε := ε / 2) (by linarith)
  have hprodpt : ∀ q : ℤ,
      ∏ o ∈ Finset.univ.erase (none : Option ι),
          ‖a o * ((pt q none : ℤ) : ℂ) - ((pt q o : ℤ) : ℂ)‖
        = ∏ i, |((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)| := by
    intro q
    rw [Finset.prod_erase_none]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hh : a (some i) * ((pt q none : ℤ) : ℂ) - ((pt q (some i) : ℤ) : ℂ)
        = (((((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)) : ℝ) : ℂ) := by
      rw [hptnone]
      change ((α i : ℝ) : ℂ) * ((q : ℤ) : ℂ) - ((pt q (some i) : ℤ) : ℂ) = _
      push_cast
      ring
    rw [hh, Complex.norm_real, Real.norm_eq_abs]
  have hMle : ∀ q : ℤ, 1 ≤ q → C ≤ ((q : ℤ) : ℝ) →
      (⨆ o, |((pt q o : ℤ) : ℝ)|) ≤ ((q : ℤ) : ℝ) * ((q : ℤ) : ℝ) := by
    intro q hq1 hCq
    have hq1R : (1 : ℝ) ≤ ((q : ℤ) : ℝ) := by exact_mod_cast hq1
    refine Real.iSup_le (fun o ↦ ?_) (by nlinarith)
    cases o with
    | none =>
        rw [hptnone, abs_of_nonneg (by linarith)]
        nlinarith
    | some i =>
        rw [hptsome]
        have h1 : |((round (((q : ℤ) : ℝ) * α i) : ℤ) : ℝ)|
            ≤ |((q : ℤ) : ℝ) * α i| + 1 / 2 := by
          have hr := abs_sub_round (((q : ℤ) : ℝ) * α i)
          have h2 := abs_sub_abs_le_abs_sub ((round (((q : ℤ) : ℝ) * α i) : ℤ) : ℝ)
            (((q : ℤ) : ℝ) * α i)
          rw [abs_sub_comm] at h2
          linarith
        have h3 : |((q : ℤ) : ℝ) * α i| = ((q : ℤ) : ℝ) * |α i| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((q : ℤ) : ℝ))]
        have h4 : |α i| ≤ ∑ t, |α t| :=
          Finset.single_le_sum (f := fun t ↦ |α t|) (fun t _ ↦ abs_nonneg _) (Finset.mem_univ i)
        have h5 : ((q : ℤ) : ℝ) * |α i| ≤ ((q : ℤ) : ℝ) * ∑ t, |α t| :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        have h6 : ((q : ℤ) : ℝ) * C ≤ ((q : ℤ) : ℝ) * ((q : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_left hCq (by linarith)
        have h7 : ((q : ℤ) : ℝ) * C
            = ((q : ℤ) : ℝ) * (∑ t, |α t|) + 2 * ((q : ℤ) : ℝ) := by rw [hCdef]; ring
        rw [h3] at h1
        linarith
  have hkey : ∀ q : ℤ, 1 ≤ q → C ≤ ((q : ℤ) : ℝ) →
      ((q : ℤ) : ℝ) ^ (1 + ε) * ∏ i, |((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)| < 1 →
      |((pt q none : ℤ) : ℝ)| * ∏ o ∈ Finset.univ.erase (none : Option ι),
            ‖a o * ((pt q none : ℤ) : ℂ) - ((pt q o : ℤ) : ℂ)‖
        ≤ (⨆ o, |((pt q o : ℤ) : ℝ)|) ^ (-(ε / 2)) := by
    intro q hq1 hCq hlt
    have hq1R : (1 : ℝ) ≤ ((q : ℤ) : ℝ) := by exact_mod_cast hq1
    rw [hprodpt q, hptnone, abs_of_nonneg (by linarith)]
    set Q : ℝ := ((q : ℤ) : ℝ) with hQ
    set D : ℝ := ∏ i, |Q * α i - ((pt q (some i) : ℤ) : ℝ)| with hD
    have hD0 : (0 : ℝ) ≤ D := Finset.prod_nonneg fun i _ ↦ abs_nonneg _
    have hpowpos : (0 : ℝ) < Q ^ (1 + ε) := Real.rpow_pos_of_pos (by linarith) _
    have hDle : D ≤ Q ^ (-(1 + ε)) := by
      rw [Real.rpow_neg (by linarith), ← one_div, le_div_iff₀ hpowpos]
      nlinarith [hlt]
    have hQQ : Q ^ (-(1 + ε)) * Q = Q ^ (-ε) := by
      nth_rewrite 2 [← Real.rpow_one Q]
      rw [← Real.rpow_add (by linarith), show -(1 + ε) + 1 = -ε by ring]
    have hsq : (Q * Q) ^ (-(ε / 2)) = Q ^ (-ε) := by
      rw [show Q * Q = Q ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring,
        ← Real.rpow_mul (by linarith), show (2 : ℝ) * (-(ε / 2)) = -ε by ring]
    have hMpos : (0 : ℝ) < ⨆ o, |((pt q o : ℤ) : ℝ)| := by
      refine lt_of_lt_of_le zero_lt_one ?_
      refine le_trans ?_ (Finite.le_ciSup_of_le (none : Option ι) le_rfl)
      rw [hptnone, abs_of_nonneg (by linarith)]
      exact hq1R
    calc Q * D ≤ Q * Q ^ (-(1 + ε)) := mul_le_mul_of_nonneg_left hDle (by linarith)
      _ = Q ^ (-ε) := by rw [mul_comm]; exact hQQ
      _ = (Q * Q) ^ (-(ε / 2)) := hsq.symm
      _ ≤ (⨆ o, |((pt q o : ℤ) : ℝ)|) ^ (-(ε / 2)) :=
          Real.rpow_le_rpow_of_nonpos hMpos (hMle q hq1 hCq) (by linarith)
  have hxne : ∀ q : ℤ, 1 ≤ q → (fun o ↦ ((pt q o : ℤ) : ℚ)) ≠ 0 := by
    intro q hq1 h0
    have h := congrFun h0 none
    simp only [Pi.zero_apply, hptnone] at h
    have hq0 : q = 0 := by exact_mod_cast h
    omega
  have hcover : {q : ℤ | 1 ≤ q ∧ ((q : ℤ) : ℝ) ^ (1 + ε)
          * ∏ i, |((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)| < 1}
      ⊆ {q : ℤ | 1 ≤ q ∧ ((q : ℤ) : ℝ) < C}
        ∪ ⋃ V ∈ (T : Set (Submodule ℚ (Option ι → ℚ))),
            {q : ℤ | 1 ≤ q ∧ (fun o ↦ ((pt q o : ℤ) : ℚ)) ∈ V} := by
    rintro q ⟨hq1, hlt⟩
    by_cases hCq : ((q : ℤ) : ℝ) < C
    · exact Or.inl ⟨hq1, hCq⟩
    · obtain ⟨V, hV, hmem⟩ := hTmem (pt q) (hxne q hq1) (hkey q hq1 (not_lt.mp hCq) hlt)
      exact Or.inr (Set.mem_biUnion hV ⟨hq1, hmem⟩)
  refine Set.Finite.subset (Set.Finite.union ?_
    (Set.Finite.biUnion T.finite_toSet fun V hV ↦ ?_)) hcover
  · refine Set.Finite.subset (Set.finite_Icc 1 ⌈C⌉) ?_
    rintro q ⟨hq1, hqC⟩
    refine Set.mem_Icc.2 ⟨hq1, ?_⟩
    have h : ((q : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := le_trans hqC.le (Int.le_ceil C)
    exact_mod_cast h
  · obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr (hTproper V hV)) inferInstance
    set c : Option ι → ℚ := fun o ↦ f (fun t ↦ if o = t then 1 else 0) with hcdef
    have hfx : ∀ y : Option ι → ℚ, f y = ∑ o, y o * c o := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun o _ ↦ by rw [smul_eq_mul]
    obtain ⟨o₀, hco₀⟩ : ∃ o, c o ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, hcon])
    have hrelq : ∀ q : ℤ, (fun o ↦ ((pt q o : ℤ) : ℚ)) ∈ V →
        ((q : ℤ) : ℚ) * c none + ∑ i, ((pt q (some i) : ℤ) : ℚ) * c (some i) = 0 := by
      intro q hqV
      have hmap : f (fun o ↦ ((pt q o : ℤ) : ℚ)) ∈ Submodule.map f V :=
        Submodule.mem_map_of_mem hqV
      rw [hfV, Submodule.mem_bot, hfx] at hmap
      rwa [Fintype.sum_option, hptnone] at hmap
    set A : ℝ := ((c none : ℚ) : ℝ) + ∑ i, ((c (some i) : ℚ) : ℝ) * α i with hAdef
    have hA : A ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := hind (c none) (fun i ↦ c (some i)) (by rw [← hAdef]; exact h0)
      cases o₀ with
      | none => exact hco₀ h1
      | some i => exact hco₀ (h2 i)
    have hA0 : (0 : ℝ) < |A| := abs_pos.mpr hA
    set B : ℝ := (∑ i, |((c (some i) : ℚ) : ℝ)|) / |A| with hBdef
    refine Set.Finite.subset (Set.finite_Icc (-⌈B⌉) ⌈B⌉) ?_
    rintro q ⟨hq1, hqV⟩
    have hR : ((q : ℤ) : ℝ) * ((c none : ℚ) : ℝ)
        + ∑ i, ((pt q (some i) : ℤ) : ℝ) * ((c (some i) : ℚ) : ℝ) = 0 := by
      have h2 : ((((q : ℤ) : ℚ) * c none
          + ∑ i, ((pt q (some i) : ℤ) : ℚ) * c (some i) : ℚ) : ℝ) = 0 := by
        rw [hrelq q hqV]; simp
      push_cast at h2
      exact h2
    have hqA : ((q : ℤ) : ℝ) * A
        = ∑ i, ((c (some i) : ℚ) : ℝ)
            * (((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)) := by
      have hexp1 : ∑ i, ((c (some i) : ℚ) : ℝ)
            * (((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ))
          = ((q : ℤ) : ℝ) * (∑ i, ((c (some i) : ℚ) : ℝ) * α i)
            - ∑ i, ((pt q (some i) : ℤ) : ℝ) * ((c (some i) : ℚ) : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hexp1, hAdef]
      linear_combination hR
    have h1 : |((q : ℤ) : ℝ) * A| ≤ ∑ i, |((c (some i) : ℚ) : ℝ)| := by
      rw [hqA]
      calc |∑ i, ((c (some i) : ℚ) : ℝ)
              * (((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ))|
          ≤ ∑ i, |((c (some i) : ℚ) : ℝ)
              * (((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |((c (some i) : ℚ) : ℝ)| := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [abs_mul]
            have hθ : |((q : ℤ) : ℝ) * α i - ((pt q (some i) : ℤ) : ℝ)| ≤ 1 / 2 := by
              rw [hptsome]
              exact abs_sub_round _
            nlinarith [abs_nonneg (((c (some i) : ℚ) : ℝ))]
    have h2 : |((q : ℤ) : ℝ)| ≤ B := by
      rw [hBdef, le_div_iff₀ hA0]
      rw [abs_mul] at h1
      exact h1
    have hceil : |q| ≤ ⌈B⌉ := by
      have h3 : |((q : ℤ) : ℝ)| ≤ ((⌈B⌉ : ℤ) : ℝ) := h2.trans (Int.le_ceil B)
      rw [← Int.cast_abs] at h3
      exact_mod_cast h3
    simpa only [Set.mem_Icc] using abs_le.mp hceil

/-- **Schmidt's linear form theorem over `ℝ`.** For real algebraic `β 1, …, β n` with
`1, β 1, …, β n` linearly independent over `ℚ` and `ε > 0`, only finitely many integer points
with no vanishing coordinate satisfy `(∏ i, |x i|) ^ (1 + ε) * |∑ i, β i * x i| < 1`. -/
theorem finite_setOf_prod_abs_mul_abs_sum_lt {ι : Type u} [Fintype ι] {β : ι → ℝ}
    (halg : ∀ i, IsAlgebraic ℚ (β i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) β) {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | (∀ i, x i ≠ 0) ∧
      (∏ i, |((x i : ℤ) : ℝ)|) ^ (1 + ε) * |∑ i, β i * ((x i : ℤ) : ℝ)| < 1}.Finite :=
  finite_setOf_prod_lt_real_aux halg (forall_eq_zero_of_linearIndependent_option hind) hε

/-- **Layer 7.3, Schmidt's theorem on `∑ i, q i * α i`** (Schmidt 1970; Bombieri–Gubler, Remark
7.3.4). For real algebraic `α 1, …, α n` with `1, α 1, …, α n` linearly independent over `ℚ` and
`ε > 0`, only finitely many `q ∈ ℤⁿ` with no vanishing coordinate satisfy
`(∏ i, |q i|) ^ (1 + ε) * ‖∑ i, q i * α i‖ < 1`, the distance to the nearest integer being
written as an existential over the numerator. -/
theorem finite_setOf_prod_abs_mul_dist_lt {ι : Type u} [Fintype ι] {α : ι → ℝ}
    (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ ∃ p : ℤ,
      (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
        * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1}.Finite :=
  finite_setOf_dist_lt_aux (Fintype.card ι) halg
    (forall_eq_zero_of_linearIndependent_option hind) le_rfl hε

/-- **Layer 7.3, Schmidt's theorem on simultaneous approximation** (Schmidt 1970;
Bombieri–Gubler, Remark 7.3.4). For real algebraic `α 1, …, α n` with `1, α 1, …, α n` linearly
independent over `ℚ` and `ε > 0`, only finitely many `q ≥ 1` satisfy
`q ^ (1 + ε) * ∏ i, ‖q * α i‖ < 1`, the distances to the nearest integers being written as an
existential over the numerators. -/
theorem finite_setOf_mul_prod_dist_lt {ι : Type u} [Fintype ι] {α : ι → ℝ}
    (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ∃ p : ι → ℤ,
      ((q : ℤ) : ℝ) ^ (1 + ε) * ∏ i, |((q : ℤ) : ℝ) * α i - ((p i : ℤ) : ℝ)| < 1}.Finite :=
  finite_setOf_mul_prod_dist_lt_aux halg (forall_eq_zero_of_linearIndependent_option hind) hε

end Real

/-!
## Acceptance criteria
-/

namespace Real

/-- **Layer 7.3 in the shape the roadmap states it**, first statement: `q ^ (1 + ε)` times the
product of the distances from `q * α i` to the nearest integers is below `1` finitely often. -/
example {ι : Type u} [Fintype ι] {α : ι → ℝ} (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ((q : ℤ) : ℝ) ^ (1 + ε)
      * ∏ i, |((q : ℤ) : ℝ) * α i - ((round (((q : ℤ) : ℝ) * α i) : ℤ) : ℝ)| < 1}.Finite := by
  refine Set.Finite.subset (finite_setOf_mul_prod_dist_lt halg hind hε) ?_
  rintro q ⟨hq1, hlt⟩
  exact ⟨hq1, fun i ↦ round (((q : ℤ) : ℝ) * α i), hlt⟩

/-- **Layer 7.3 in the shape the roadmap states it**, second statement: the distance from
`∑ i, q i * α i` to the nearest integer, against the product of the `|q i|`. -/
example {ι : Type u} [Fintype ι] {α : ι → ℝ} (halg : ∀ i, IsAlgebraic ℚ (α i))
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) {ε : ℝ} (hε : 0 < ε) :
    {q : ι → ℤ | (∀ i, q i ≠ 0) ∧ (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
      * |∑ i, α i * ((q i : ℤ) : ℝ)
          - ((round (∑ i, α i * ((q i : ℤ) : ℝ)) : ℤ) : ℝ)| < 1}.Finite := by
  refine Set.Finite.subset (finite_setOf_prod_abs_mul_dist_lt halg hind hε) ?_
  rintro q ⟨hne0, hlt⟩
  exact ⟨hne0, round (∑ i, α i * ((q i : ℤ) : ℝ)), hlt⟩

/-- **Acceptance test: the existential over the numerator is the distance to `ℤ`.** -/
example (t : ℝ) (p : ℤ) : |t - ((round t : ℤ) : ℝ)| ≤ |t - (p : ℝ)| := abs_sub_round_le t p

/-- **Acceptance test: the hypothesis has teeth.** Linear independence of `1, α 1, …, α n` over
`ℚ` implies in particular that every `α i` is irrational, which is the `n = 1` content of the
milestone's hypothesis. -/
example {ι : Type u} [Fintype ι] {α : ι → ℝ}
    (hind : LinearIndependent ℚ fun o : Option ι ↦ o.elim (1 : ℝ) α) (i : ι) :
    Irrational (α i) := by
  classical
  rintro ⟨r, hr⟩
  have hrel : ((-r : ℚ) : ℝ) + ∑ t, (((if t = i then 1 else 0 : ℚ)) : ℝ) * α t = 0 := by
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, Rat.cast_one, one_mul, ← hr, Rat.cast_neg]
      ring
    · intro t _ hti
      rw [ite_eq_right hti, Rat.cast_zero, zero_mul]
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  have h := (forall_eq_zero_of_linearIndependent_option hind (-r) _ hrel).2 i
  rw [ite_eq_left rfl] at h
  exact one_ne_zero h

/-- **Rejection test: a vanishing coordinate makes the inequality free.** The product of the
`|q i|` is then `0`, so the left-hand side is `0` whatever the numerator, and there are
infinitely many such `q`; this is why the milestone quantifies over the `q` with no vanishing
coordinate. -/
example (α : Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    {q : Fin 2 → ℤ | ∃ p : ℤ, (∏ i, |((q i : ℤ) : ℝ)|) ^ (1 + ε)
      * |∑ i, α i * ((q i : ℤ) : ℝ) - (p : ℝ)| < 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ (![(m : ℤ), 0] : Fin 2 → ℤ)) (fun m m' hmm ↦ ?_) fun m ↦ ?_
  · have h := congrFun hmm 0
    simp only [Matrix.cons_val_zero] at h
    exact_mod_cast h
  · refine ⟨0, ?_⟩
    have hz : ∏ i, |(((![(m : ℤ), 0] : Fin 2 → ℤ) i : ℤ) : ℝ)| = 0 := by
      rw [Fin.prod_univ_two]
      simp
    rw [hz, Real.zero_rpow (ne_of_gt (by linarith)), zero_mul]
    norm_num

/-- **Rejection test: independence over `ℚ` is load-bearing.** At `α = 0` the distances all
vanish and every `q` is a solution, so the conclusion fails for a family that is not independent
with `1` — here because `α 0` is rational. -/
example {ε : ℝ} :
    {q : ℤ | 1 ≤ q ∧ ∃ p : Fin 1 → ℤ, ((q : ℤ) : ℝ) ^ (1 + ε)
      * ∏ i, |((q : ℤ) : ℝ) * (![0] : Fin 1 → ℝ) i - ((p i : ℤ) : ℝ)| < 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ ((m : ℤ) + 1)) (fun m m' hmm ↦ ?_) fun m ↦ ?_
  · have h : ((m : ℤ)) + 1 = ((m' : ℤ)) + 1 := hmm
    have h2 : ((m : ℤ)) = ((m' : ℤ)) := by omega
    exact_mod_cast h2
  · refine ⟨by omega, ![0], ?_⟩
    rw [Fin.prod_univ_one]
    simp

end Real
