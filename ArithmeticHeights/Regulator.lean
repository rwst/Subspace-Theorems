/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Hadamard
public import ArithmeticHeights.MinimaBasis
public import ArithmeticHeights.MinkowskiSecond
public import ArithmeticHeights.UnitTorsion
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The regulator and the heights of a fundamental system

Let `K` be a number field of degree `d = [K : ℚ]` and unit rank `r`, and write `h` for the
absolute logarithmic height. This file compares the regulator of `K` with the heights of a
fundamental system of units, in both directions:

```text
regulator K ≤ (2 d) ^ r * ∏ i, h (ε i)                for every fundamental system ε,
∏ i, h (ε i) ≤ (r !) ^ 2 / (2 ^ (r - 1) * d ^ r) * R  for some fundamental system ε.
```

The first is **Hadamard's inequality**. The regulator is the absolute determinant of the `r × r`
matrix of the logarithmic embeddings of the system (Mathlib's
`NumberField.Units.regOfFamily_eq_det'`); each row of that matrix has ℓ¹ norm at most
`2 d h (ε i)` by Layer 6.1; and the determinant of a square matrix is at most the product of the
ℓ¹ norms of its rows, which is Layer 3.4 in the square form `Matrix.abs_det_le_prod_sum_abs`.

The second is **Bugeaud–Győry's Lemma 1** in the case `S = S∞`, and it is where both halves of
Layer 4 are spent. Minkowski's second theorem (4.2) for `NumberField.Units.unitLattice K`, whose
covolume is the regulator, against the closed ℓ¹ unit ball of the log space, whose volume is
`2 ^ r / r !`, gives `∏ i, λ i ≤ r ! * R`; the basis of Layer 4.6 realizes the `i`-th minimum up
to `max 1 ((i + 1) / 2)` and so costs `r ! / 2 ^ (r - 1)`; and Layer 6.1 turns the ℓ¹ norm of a
lattice vector back into a height, which costs `d ^ (-r)`.

## Main results

* `NumberField.Units.regulator_le_prod_absLogHeight₁`: **Hadamard's bound**, for Mathlib's
  `fundSystem`; `NumberField.Units.regOfFamily_le_prod_absLogHeight₁` is the same bound for an
  arbitrary family and its own regulator, and
  `NumberField.Units.regulator_le_prod_absLogHeight₁_of_closure_sup_torsion_eq_top` for an
  arbitrary fundamental system. `NumberField.Units.regulator_le_prod_logHeight₁` is the relative
  form, where the constant is `2 ^ r`.
* `NumberField.Units.exists_fundSystem_prod_absLogHeight₁_le`: **a fundamental system of small
  height exists**, with the explicit constant `(r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, and
  `NumberField.Units.exists_fundSystem_regulator_le_and_prod_absLogHeight₁_le` says that one and
  the same system satisfies both bounds.
* `NumberField.Units.logBall`: the closed ℓ¹ unit ball of the log space, with
  `NumberField.Units.volume_logBall` its volume `2 ^ r / r !` and
  `NumberField.Units.prod_successiveMinimum_logBall_le` Minkowski's second theorem against it.
* `NumberField.Units.closure_sup_torsion_eq_top_of_span`: a family of units whose logarithmic
  embeddings span the unit lattice over `ℤ` is a fundamental system, and
  `NumberField.Units.regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top`: a fundamental system
  has the regulator of the field for its own regulator.
* `NumberField.Units.prod_absLogHeight₁_pos_of_closure_sup_torsion_eq_top`: no member of a
  fundamental system is a root of unity, so both bounds are bounds between positive numbers.
* `NumberField.Units.regulator_eq_one_of_rank_eq_zero`: at unit rank zero the two bounds meet and
  the regulator is `1`.

## Implementation notes

⚠ **The second statement is an existence statement and cannot be made for `fundSystem`, or for
every fundamental system.** A unimodular change of basis multiplies the heights without touching
the regulator, so no bound in the direction `∏ h (ε i) ≤ c R` can hold uniformly. The family
produced here is built from the successive minima and has nothing to do with Mathlib's
`fundSystem`. What makes it a *fundamental system* rather than merely a family of maximal rank is
that the basis of Layer 4.6 is a basis of the whole unit lattice;
`closure_sup_torsion_eq_top_of_span` is the step that turns that into
`Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤`, through the kernel of `logEmbedding`. Nor is it
a statement with unspecified constants: for a fixed `K`,
`∃ c₁ c₂ > 0, c₁ R ≤ ∏ h (ε i) ≤ c₂ R` is true of any positive numbers and says nothing.

⚠ **Hadamard's inequality is used in the ℓ¹ form, not the familiar ℓ² one.** Layer 3.4 bounds the
Gram determinant `det (A Aᵀ)` by the product of the squared ℓ² norms of the rows, and extracting a
square root of that would need `Real.sqrt`. What Layer 6.1 hands over is the **ℓ¹** norm of a row,
so the ℓ² route would pay a factor `√r` per row and then have to give it back. The square form
added to Layer 3.4 for this layer, `Matrix.abs_det_le_prod_sum_abs`, stays inside the ordered field
and needs no analysis. ⚠ The `2 d` and not `d` in the constant is Layer 6.1's factor `2` — the
price of the coordinate that `logEmbedding` drops — and not a loss in Hadamard's inequality.

⚠ **Unit rank zero is not a degenerate case to be discarded; it is where the two bounds meet.**
Mathlib's `MeasureTheory.volume_sum_rpow_le` wants a nonempty index, so `volume_logBall` does
`r = 0` by hand: the log space is a single point, the ball is all of it, and its volume is
`1 = 2 ^ 0 / 0 !`. Both bounds then read `R ≤ 1` and `1 ≤ R`, and `regulator_eq_one_of_rank_eq_zero`
falls out — a value Mathlib does not record, having only `NumberField.Units.regulator_pos`. The
truncated subtraction in `2 ^ (r - 1)` is what the constant wants: it is `1` at `r = 0` and at
`r = 1`, and `∏_{i < r} max 1 ((i + 1) / 2) = r ! / 2 ^ (r - 1)` on the nose.

⚠ **That the bounds are not vacuous comes from two different places.** Layer 6.2 puts every member
of Mathlib's `fundSystem` strictly above height one, because its logarithmic embedding is a basis
vector of the unit lattice. For an *arbitrary* fundamental system that argument is not available,
and the positivity instead comes from this layer: such a family has maximal rank, because its
regulator is the regulator of `K` and that is nonzero, and a linearly independent family has no
zero member. The acceptance criteria also check that the two constants are mutually consistent,
`1 ≤ (2 d) ^ r * (r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, which the two bounds and the positivity of the
regulator force.

## References

Y. Bugeaud and K. Győry, "Bounds for the solutions of unit equations", *Acta Arithmetica* **74**
(1996), 67–80; Lemma 1 of §3 (p. 71) is the second statement, for `S`-units, and its proof on
pp. 71–72 is the route taken here. Their `h` is the multiplicative absolute height, so their
`log h` is the `absLogHeight₁` of this file.

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
Lemma 8 (p. 135), which is Layer 4.6, and Chapter VIII, Theorem V, which is Layer 4.2.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5, where the comparison between the height of a unit and its logarithmic embedding is
Proposition 1.5.12.

This is Layer 6.3 of the `ArithmeticHeights` roadmap.
-/

public section

open Height Module NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem Real

open scoped Pointwise

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-!
### The ℓ¹ unit ball of the log space
-/

open scoped Classical in
/-- The closed ℓ¹ unit ball of `NumberField.Units.dirichletUnitTheorem.logSpace K`, the convex
body Minkowski's second theorem is applied to. -/
def logBall (K : Type*) [Field K] [NumberField K] : Set (logSpace K) :=
  {x | ∑ w, |x w| ≤ 1}

open scoped Classical in
theorem mem_logBall {x : logSpace K} : x ∈ logBall K ↔ ∑ w, |x w| ≤ 1 := Iff.rfl

open scoped Classical in
theorem convex_logBall : Convex ℝ (logBall K) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_logBall] at hx hy ⊢
  have hstep : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(a • x + b • y) w| ≤ a * |x w| + b * |y w| := fun w ↦ by
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x w) (b * y w)
  calc ∑ w, |(a • x + b • y) w| ≤ ∑ w, (a * |x w| + b * |y w|) :=
        Finset.sum_le_sum fun w _ ↦ hstep w
    _ = a * ∑ w, |x w| + b * ∑ w, |y w| := by rw [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

open scoped Classical in
theorem neg_mem_logBall {x : logSpace K} (hx : x ∈ logBall K) : -x ∈ logBall K := by
  simpa [mem_logBall] using hx

open scoped Classical in
theorem isClosed_logBall : IsClosed (logBall K) := by
  have hcont : Continuous fun x : logSpace K ↦ ∑ w, |x w| := by fun_prop
  exact isClosed_le hcont continuous_const

open scoped Classical in
theorem logBall_subset_closedBall : logBall K ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_logBall] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w ↦ ?_
  refine le_trans ?_ hx
  simpa using Finset.single_le_sum (f := fun w : {w : InfinitePlace K // w ≠ w₀} ↦ |x w|)
    (fun v _ ↦ abs_nonneg _) (Finset.mem_univ w)

open scoped Classical in
theorem isBounded_logBall : Bornology.IsBounded (logBall K) :=
  Metric.isBounded_closedBall.subset logBall_subset_closedBall

open scoped Classical in
theorem interior_logBall_nonempty : (interior (logBall K)).Nonempty := by
  classical
  set n := Fintype.card {w : InfinitePlace K // w ≠ w₀} with hn
  have hsub : Metric.ball (0 : logSpace K) (1 / (n + 1)) ⊆ logBall K := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [mem_logBall]
    have hle : ∑ w, |x w| ≤ n * ‖x‖ := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀})
        (fun w ↦ |x w|) ‖x‖ fun w _ ↦ by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm x w
      rwa [Finset.card_univ, ← hn, nsmul_eq_mul] at this
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have : (n : ℝ) * ‖x‖ ≤ n * (1 / (n + 1)) := by
      exact mul_le_mul_of_nonneg_left hx.le (Nat.cast_nonneg n)
    have hfin : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hpos]
      linarith
    linarith
  exact ⟨0, mem_interior.2 ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩⟩

open scoped Classical in
/-- A point of a dilate of the ℓ¹ ball has ℓ¹ norm at most the dilation factor. This is the form
the basis of Layer 4.6 is handed back in. -/
theorem sum_abs_le_of_mem_smul_logBall {t : ℝ} (ht : 0 ≤ t) {x : logSpace K}
    (hx : x ∈ t • logBall K) : ∑ w, |x w| ≤ t := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_logBall] at hy
  calc ∑ w, |(t • y) w| = t * ∑ w, |y w| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ ↦ by simp [abs_mul, abs_of_nonneg ht]
    _ ≤ t * 1 := by gcongr
    _ = t := mul_one t

open scoped Classical in
theorem card_ne_w₀ (K : Type*) [Field K] [NumberField K] :
    Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K := by
  classical
  rw [← NumberField.Units.finrank_eq_rank (K := K), finrank_fintype_fun_eq_card]

open scoped Classical in
/-- **The volume of the ℓ¹ unit ball of the log space is `2 ^ r / r !`.** This is Mathlib's
`MeasureTheory.volume_sum_rpow_le` at `p = 1`, with the rank-zero case — where the log space is a
single point and the ball is everything — done by hand, since that lemma wants a nonempty index. -/
theorem volume_logBall (K : Type*) [Field K] [NumberField K] :
    MeasureTheory.volume (logBall K)
      = ENNReal.ofReal (2 ^ rank K / (rank K).factorial) := by
  classical
  have hΓ2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one]
  rcases isEmpty_or_nonempty {w : InfinitePlace K // w ≠ w₀} with hE | hNE
  · have hr : rank K = 0 := by
      rw [← card_ne_w₀ K, Fintype.card_eq_zero_iff]
      infer_instance
    have huniv : logBall K = Set.univ := by
      ext x
      simp [mem_logBall]
    have hvol : MeasureTheory.volume (Set.univ : Set (logSpace K)) = 1 := by
      rw [← Set.pi_univ Set.univ, MeasureTheory.volume_pi_pi]
      simp
    rw [huniv, hvol, hr]
    norm_num
  · have hset : {x : logSpace K | (∑ w, |x w| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} = logBall K := by
      ext x
      simp [mem_logBall, Real.rpow_one]
    rw [← hset,
      MeasureTheory.volume_sum_rpow_le {w : InfinitePlace K // w ≠ w₀} (p := 1) le_rfl 1,
      card_ne_w₀ K]
    norm_num [hΓ2, Real.Gamma_nat_eq_factorial (rank K)]

open scoped Classical in
/-- **Minkowski's second theorem for the unit lattice against the ℓ¹ ball** (Layer 4.2). The
product of the successive minima of `unitLattice K` for the ℓ¹ unit ball is at most `r !` times the
regulator: the body has volume `2 ^ r / r !` and the covolume of the lattice is the regulator. -/
theorem prod_successiveMinimum_logBall_le (K : Type*) [Field K] [NumberField K] :
    (∏ i ∈ Finset.range (rank K),
        ZLattice.successiveMinimum (unitLattice K) (logBall K) i)
      ≤ (rank K).factorial * regulator K := by
  classical
  have hfac : (0 : ℝ) < (rank K).factorial := by
    exact_mod_cast (rank K).factorial_pos
  have h2 : (0 : ℝ) < 2 ^ rank K := by positivity
  have hv : (0 : ℝ) < 2 ^ rank K / (rank K).factorial := by positivity
  have hmink := ZLattice.prod_successiveMinimum_mul_measure_le (unitLattice K)
    MeasureTheory.volume convex_logBall (fun x hx ↦ neg_mem_logBall hx)
    interior_logBall_nonempty isBounded_logBall
  rw [NumberField.Units.finrank_eq_rank, volume_logBall,
    ENNReal.toReal_ofReal hv.le, ← le_div_iff₀ hv] at hmink
  refine hmink.trans (le_of_eq ?_)
  rw [regulator]
  field_simp

/-!
### The constant of Layer 4.6
-/

/-- The loss of Layer 4.6 against Layer 4.2, `∏_{i < r} max 1 ((i + 1) / 2) = r ! / 2 ^ (r − 1)`.
The `max` is `1` for `i ≤ 1` and `(i + 1) / 2` afterwards, so the product telescopes into a
factorial with one factor of `2` per index above the first. -/
theorem prod_max_one_add_one_div_two (r : ℕ) :
    ∏ i : Fin r, max 1 ((((i : ℕ) : ℝ) + 1) / 2) = (r.factorial : ℝ) / 2 ^ (r - 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_sub_one]
    rw [ih]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmax : max (1 : ℝ) (((n : ℝ) + 1) / 2) = ((n : ℝ) + 1) / 2 :=
        max_eq_right (by rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith)
      have h2 : (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [hmax, Nat.factorial_succ]
      push_cast
      rw [h2]
      have hne : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
      field_simp

/-!
### Fundamental systems
-/

/-- **A family of units whose logarithmic embeddings span the unit lattice is a fundamental
system.** The kernel of `logEmbedding` is the torsion subgroup, so a unit whose embedding is an
integer combination of the `logEmbedding (ε i)` differs from the corresponding monomial in the
`ε i` by a root of unity. -/
theorem closure_sup_torsion_eq_top_of_span {m : ℕ} (ε : Fin m → (𝓞 K)ˣ)
    (h : Submodule.span ℤ (Set.range fun i ↦ logEmbedding K (Additive.ofMul (ε i)))
        = unitLattice K) :
    Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : logEmbedding K (Additive.ofMul x) ∈ unitLattice K :=
    ⟨Additive.ofMul x, Submodule.mem_top, rfl⟩
  rw [← h, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  set y : (𝓞 K)ˣ := ∏ i, ε i ^ c i with hy
  have hlogy : logEmbedding K (Additive.ofMul y)
      = ∑ i, c i • logEmbedding K (Additive.ofMul (ε i)) := by
    rw [hy, ofMul_prod, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [ofMul_zpow, map_zsmul]
  have hmem : x * y⁻¹ ∈ torsion K := by
    rw [← logEmbedding_eq_zero_iff,
      show Additive.ofMul (x * y⁻¹) = Additive.ofMul x - Additive.ofMul y from rfl,
      map_sub, hlogy, hc, sub_self]
  have hymem : y ∈ Subgroup.closure (Set.range ε) :=
    Subgroup.prod_mem _ fun i _ ↦
      Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  have hxeq : x = y * (x * y⁻¹) := by
    rw [mul_comm y, inv_mul_cancel_right]
  rw [hxeq]
  exact Subgroup.mul_mem_sup hymem hmem

/-- **The regulator of a fundamental system is the regulator of the field.** Mathlib's
`NumberField.Units.regOfFamily_div_regulator` reads the ratio as the index of the subgroup the
family generates together with the torsion; here that index is `1`. -/
theorem regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) : regOfFamily u = regulator K := by
  have hne := regulator_ne_zero K
  have hdiv := regOfFamily_div_regulator u
  rw [h, Subgroup.index_top, Nat.cast_one] at hdiv
  field_simp at hdiv
  exact hdiv

/-- A fundamental system has maximal rank: its regulator is the regulator of the field, which is
not zero. -/
theorem isMaxRank_of_closure_sup_torsion_eq_top {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) : IsMaxRank u :=
  regOfFamily_ne_zero_iff.mp <| by
    rw [regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top h]; exact regulator_ne_zero K

/-- **No member of a fundamental system is a root of unity.** The logarithmic embeddings of a
fundamental system are linearly independent, hence nonzero, and the kernel of `logEmbedding` is
the torsion subgroup. This is Layer 6.2's `NumberField.Units.fundSystem_notMem_torsion` for an
arbitrary fundamental system. -/
theorem notMem_torsion_of_closure_sup_torsion_eq_top {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) (i : Fin (rank K)) :
    u i ∉ torsion K := fun hi ↦
  LinearIndependent.ne_zero i (isMaxRank_of_closure_sup_torsion_eq_top h)
    (logEmbedding_eq_zero_iff.mpr hi)

/-- Every member of a fundamental system has strictly positive height (Layer 6.2). -/
theorem absLogHeight₁_pos_of_closure_sup_torsion_eq_top {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) (i : Fin (rank K)) :
    0 < absLogHeight₁ ((u i : 𝓞 K) : K) :=
  absLogHeight₁_pos_of_notMem_torsion (notMem_torsion_of_closure_sup_torsion_eq_top h i)

/-- **The product of heights that the bounds below compare with the regulator is positive**, so
neither of them is vacuous. -/
theorem prod_absLogHeight₁_pos_of_closure_sup_torsion_eq_top {u : Fin (rank K) → (𝓞 K)ˣ}
    (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) :
    0 < ∏ i, absLogHeight₁ ((u i : 𝓞 K) : K) :=
  Finset.prod_pos fun i _ ↦ absLogHeight₁_pos_of_closure_sup_torsion_eq_top h i

/-!
### Hadamard's bound
-/

open scoped Classical in
/-- **Hadamard's bound for the regulator of a family of units.** -/
theorem regOfFamily_le_prod_absLogHeight₁ (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u ≤ (2 * finrank ℚ K : ℝ) ^ rank K *
      ∏ i, absLogHeight₁ ((u i : 𝓞 K) : K) := by
  classical
  set e := equivFinRank K with he
  set N : Matrix {w : InfinitePlace K // w ≠ w₀} {w : InfinitePlace K // w ≠ w₀} ℝ :=
    Matrix.of fun i ↦ logEmbedding K (Additive.ofMul (u (e.symm i))) with hN
  set M : Matrix (Fin (rank K)) (Fin (rank K)) ℝ := N.submatrix e e with hM
  have hrow : ∀ (i j : Fin (rank K)),
      M i j = logEmbedding K (Additive.ofMul (u i)) (e j) := by
    intro i j
    simp [hM, hN, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hsum : ∀ i : Fin (rank K), (∑ j, |M i j|)
      = ∑ w : {w : InfinitePlace K // w ≠ w₀}, |logEmbedding K (Additive.ofMul (u i)) w| :=
    fun i ↦ Fintype.sum_equiv e _ _ fun j ↦ by rw [hrow i j]
  calc regOfFamily u = |M.det| := by
        rw [regOfFamily_eq_det' u, hM, Matrix.det_submatrix_equiv_self]
    _ ≤ ∏ i, ∑ j, |M i j| := Matrix.abs_det_le_prod_sum_abs M
    _ ≤ ∏ i, (2 * (finrank ℚ K : ℝ) * absLogHeight₁ ((u i : 𝓞 K) : K)) := by
        refine Finset.prod_le_prod₀ (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _)
          fun i _ ↦ ?_
        rw [hsum i]
        exact sum_abs_logEmbedding_le_two_mul_finrank_mul_absLogHeight₁ (u i)
    _ = (2 * finrank ℚ K : ℝ) ^ rank K * ∏ i, absLogHeight₁ ((u i : 𝓞 K) : K) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

open scoped Classical in
/-- **Layer 6.3, Hadamard's bound.** The regulator is at most `(2 d) ^ r` times the product of the
absolute logarithmic heights of Mathlib's fundamental system. -/
theorem regulator_le_prod_absLogHeight₁ (K : Type*) [Field K] [NumberField K] :
    regulator K ≤ (2 * finrank ℚ K : ℝ) ^ rank K *
      ∏ i, absLogHeight₁ ((fundSystem K i : 𝓞 K) : K) := by
  rw [regulator_eq_regOfFamily_fundSystem]
  exact regOfFamily_le_prod_absLogHeight₁ (fundSystem K)

open scoped Classical in
/-- **Hadamard's bound for an arbitrary fundamental system.** -/
theorem regulator_le_prod_absLogHeight₁_of_closure_sup_torsion_eq_top
    {u : Fin (rank K) → (𝓞 K)ˣ} (h : Subgroup.closure (Set.range u) ⊔ torsion K = ⊤) :
    regulator K ≤ (2 * finrank ℚ K : ℝ) ^ rank K * ∏ i, absLogHeight₁ ((u i : 𝓞 K) : K) :=
  regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top h ▸ regOfFamily_le_prod_absLogHeight₁ u

open scoped Classical in
/-- **Hadamard's bound in the relative logarithmic height.** The same statement without the
degree: `logHeight₁ = d · h`, so the `d ^ r` on the right cancels the one the absolute form
carries. Layer 6.1's comparison is proved in this normalization, and the `2` here is exactly the
`2` of `NumberField.Units.sum_abs_logEmbedding_le_two_mul_logHeight₁`. -/
theorem regOfFamily_le_prod_logHeight₁ (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u ≤ 2 ^ rank K * ∏ i, logHeight₁ ((u i : 𝓞 K) : K) := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hprod : ∏ i, logHeight₁ ((u i : 𝓞 K) : K)
      = (finrank ℚ K : ℝ) ^ rank K * ∏ i, absLogHeight₁ ((u i : 𝓞 K) : K) := by
    have hi : ∀ i : Fin (rank K), logHeight₁ ((u i : 𝓞 K) : K)
        = (finrank ℚ K : ℝ) * absLogHeight₁ ((u i : 𝓞 K) : K) := fun i ↦ by
      rw [absLogHeight₁_eq, mul_div_cancel₀ _ hd]
    rw [Finset.prod_congr rfl fun i _ ↦ hi i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hprod, ← mul_assoc, ← mul_pow]
  exact regOfFamily_le_prod_absLogHeight₁ u

open scoped Classical in
/-- **Layer 6.3, Hadamard's bound in the relative logarithmic height.** -/
theorem regulator_le_prod_logHeight₁ (K : Type*) [Field K] [NumberField K] :
    regulator K ≤ 2 ^ rank K * ∏ i, logHeight₁ ((fundSystem K i : 𝓞 K) : K) := by
  rw [regulator_eq_regOfFamily_fundSystem]
  exact regOfFamily_le_prod_logHeight₁ (fundSystem K)

/-!
### A fundamental system of small height
-/

open scoped Classical in
/-- **A fundamental system of small height exists** (Bugeaud–Győry 1996, Lemma 1, in the case
`S = S∞`). -/
theorem exists_fundSystem_prod_absLogHeight₁_le (K : Type*) [Field K] [NumberField K] :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ,
      Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
        ∏ i, absLogHeight₁ ((ε i : 𝓞 K) : K) ≤
          ((rank K).factorial : ℝ) ^ 2 /
              (2 ^ (rank K - 1) * (finrank ℚ K : ℝ) ^ rank K) * regulator K := by
  classical
  have hrk : finrank ℝ (logSpace K) = rank K := NumberField.Units.finrank_eq_rank K
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))
  rw [← hrk]
  obtain ⟨b₀, hb₀⟩ := ZLattice.exists_basis_mem_smul_successiveMinimum (unitLattice K)
    convex_logBall (fun x hx ↦ neg_mem_logBall hx) interior_logBall_nonempty
    isBounded_logBall isClosed_logBall
  have hex : ∀ j : Fin (finrank ℝ (logSpace K)), ∃ u : (𝓞 K)ˣ,
      logEmbedding K (Additive.ofMul u) = ((b₀ j : unitLattice K) : logSpace K) := by
    intro j
    obtain ⟨z, -, hz⟩ := (b₀ j).2
    exact ⟨Additive.toMul z, hz⟩
  choose u₀ hu₀ using hex
  refine ⟨u₀, closure_sup_torsion_eq_top_of_span _ ?_, ?_⟩
  · have hcomp : (fun j ↦ logEmbedding K (Additive.ofMul (u₀ j)))
        = (Submodule.subtype (unitLattice K)) ∘ b₀ := funext fun j ↦ hu₀ j
    rw [hcomp, Set.range_comp, ← Submodule.map_span, b₀.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  · have hbound : ∀ j : Fin (finrank ℝ (logSpace K)),
        absLogHeight₁ ((u₀ j : 𝓞 K) : K)
          ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
              ZLattice.successiveMinimum (unitLattice K) (logBall K) j / finrank ℚ K := by
      intro j
      have hpos : 0 < ZLattice.successiveMinimum (unitLattice K) (logBall K) j :=
        ZLattice.successiveMinimum_pos (unitLattice K) convex_logBall
          (fun x hx ↦ neg_mem_logBall hx) interior_logBall_nonempty isBounded_logBall j.isLt
      have ht : (0 : ℝ) ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
          ZLattice.successiveMinimum (unitLattice K) (logBall K) j :=
        mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hpos.le
      refine (absLogHeight₁_le_sum_abs_logEmbedding_div (u₀ j)).trans ?_
      gcongr
      rw [hu₀ j]
      exact sum_abs_le_of_mem_smul_logBall ht (hb₀ j)
    have hmin : (∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
          ZLattice.successiveMinimum (unitLattice K) (logBall K) i)
        ≤ ((finrank ℝ (logSpace K)).factorial : ℝ) * regulator K := by
      rw [hrk]
      exact prod_successiveMinimum_logBall_le K
    have hminnn : (0 : ℝ) ≤ ∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
        ZLattice.successiveMinimum (unitLattice K) (logBall K) i := by
      refine Finset.prod_nonneg fun i hi ↦ ?_
      exact (ZLattice.successiveMinimum_pos (unitLattice K) convex_logBall
        (fun x hx ↦ neg_mem_logBall hx) interior_logBall_nonempty isBounded_logBall
        (Finset.mem_range.1 hi)).le
    have hfacnn : (0 : ℝ) ≤ ((finrank ℝ (logSpace K)).factorial : ℝ) /
        2 ^ (finrank ℝ (logSpace K) - 1) := by positivity
    calc ∏ j, absLogHeight₁ ((u₀ j : 𝓞 K) : K)
        ≤ ∏ j : Fin (finrank ℝ (logSpace K)), (max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
            ZLattice.successiveMinimum (unitLattice K) (logBall K) j / finrank ℚ K) :=
          Finset.prod_le_prod₀ (fun j _ ↦ absLogHeight₁_nonneg _) fun j _ ↦ hbound j
      _ = (((finrank ℝ (logSpace K)).factorial : ℝ) / 2 ^ (finrank ℝ (logSpace K) - 1)) *
            (∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
              ZLattice.successiveMinimum (unitLattice K) (logBall K) i) /
            (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, prod_max_one_add_one_div_two,
            Fin.prod_univ_eq_prod_range]
      _ ≤ (((finrank ℝ (logSpace K)).factorial : ℝ) / 2 ^ (finrank ℝ (logSpace K) - 1)) *
            (((finrank ℝ (logSpace K)).factorial : ℝ) * regulator K) /
            (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K) := by
          gcongr
      _ = ((finrank ℝ (logSpace K)).factorial : ℝ) ^ 2 /
            (2 ^ (finrank ℝ (logSpace K) - 1) *
              (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K)) * regulator K := by
          field_simp

open scoped Classical in
/-- **Layer 6.3, both halves for one and the same system.** The fundamental system of
`NumberField.Units.exists_fundSystem_prod_absLogHeight₁_le` also satisfies Hadamard's bound, so the
product of its heights and the regulator determine each other up to the two explicit constants. -/
theorem exists_fundSystem_regulator_le_and_prod_absLogHeight₁_le
    (K : Type*) [Field K] [NumberField K] :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ,
      Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
        regulator K ≤ (2 * finrank ℚ K : ℝ) ^ rank K * ∏ i, absLogHeight₁ ((ε i : 𝓞 K) : K) ∧
        ∏ i, absLogHeight₁ ((ε i : 𝓞 K) : K) ≤
          ((rank K).factorial : ℝ) ^ 2 /
              (2 ^ (rank K - 1) * (finrank ℚ K : ℝ) ^ rank K) * regulator K := by
  obtain ⟨ε, hε, hprod⟩ := exists_fundSystem_prod_absLogHeight₁_le K
  exact ⟨ε, hε, regulator_le_prod_absLogHeight₁_of_closure_sup_torsion_eq_top hε, hprod⟩

open scoped Classical in
/-- **At unit rank zero the two bounds meet, and the regulator is `1`.** Both sides of both
inequalities are empty products, so Hadamard's bound reads `R ≤ 1` and the reduced system reads
`1 ≤ R`. Mathlib records `NumberField.Units.regulator_pos` but not this value. -/
theorem regulator_eq_one_of_rank_eq_zero (K : Type*) [Field K] [NumberField K]
    (h : rank K = 0) : regulator K = 1 := by
  have : IsEmpty (Fin (rank K)) := by simp [h]
  have hup : regulator K ≤ 1 := by
    have hthis := regulator_le_prod_absLogHeight₁ K
    rwa [Finset.univ_eq_empty, Finset.prod_empty, mul_one, h, pow_zero] at hthis
  have hlow : (1 : ℝ) ≤ regulator K := by
    obtain ⟨ε, -, hprod⟩ := exists_fundSystem_prod_absLogHeight₁_le K
    rw [Finset.univ_eq_empty, Finset.prod_empty, h] at hprod
    norm_num at hprod
    exact hprod
  linarith

/-!
### Acceptance criteria
-/

section Examples

open scoped Classical in
/-- **The bound is not vacuous.** Layer 6.2 puts every member of a fundamental system strictly
above height one, so the product Hadamard's inequality bounds the regulator by is positive. -/
example : 0 < ∏ i, absLogHeight₁ ((fundSystem K i : 𝓞 K) : K) ∧
    regulator K ≤ (2 * finrank ℚ K : ℝ) ^ rank K *
      ∏ i, absLogHeight₁ ((fundSystem K i : 𝓞 K) : K) :=
  ⟨prod_absLogHeight₁_fundSystem_pos K, regulator_le_prod_absLogHeight₁ K⟩

/-- **Conformance with Mathlib.** Mathlib's `NumberField.Units.regulator_eq_regOfFamily_fundSystem`
is the case of `NumberField.Units.regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top` at
Mathlib's own fundamental system; the two proofs are independent, one through the index of the
subgroup generated and one through the basis of the unit lattice. -/
example : regOfFamily (fundSystem K) = regulator K :=
  regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top (closure_fundSystem_sup_torsion_eq_top K)

open scoped Classical in
/-- **The two constants are consistent.** A bound `R ≤ A · P` together with `P ≤ c · R` forces
`1 ≤ A · c`, since the regulator is positive; if the two constants of this layer had been computed
wrongly in the same direction, this would fail. -/
example : (1 : ℝ) ≤ (2 * finrank ℚ K : ℝ) ^ rank K *
    (((rank K).factorial : ℝ) ^ 2 / (2 ^ (rank K - 1) * (finrank ℚ K : ℝ) ^ rank K)) := by
  obtain ⟨ε, -, hle, hge⟩ := exists_fundSystem_regulator_le_and_prod_absLogHeight₁_le K
  have hR := regulator_pos K
  have hA : (0 : ℝ) ≤ (2 * finrank ℚ K : ℝ) ^ rank K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hge hA]

end Examples

end NumberField.Units

end
