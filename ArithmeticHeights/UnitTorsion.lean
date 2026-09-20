/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Kronecker
public import ArithmeticHeights.UnitHeight

/-!
# Units of height one

A unit of the ring of integers of a number field has height `1` exactly when it is a root of
unity, that is, exactly when it lies in `NumberField.Units.torsion K`. This is the
height-theoretic description of the torsion subgroup, and the form in which Kronecker's theorem
of Layer 1.4 is usually applied.

The proof is Layer 6.1 and nothing else. By `NumberField.Units.two_mul_logHeight₁_eq_sum_abs`,
twice the height of a unit is `∑ w | ∞, |mult w * log (w u)|`, a sum of non-negative terms; it
vanishes exactly when every term does, which is exactly Mathlib's `NumberField.Units.mem_torsion`.
Layer 1.4 gives a second proof, recorded at the end of the file.

The last section records what Layer 6.3 needs: a unit outside the torsion subgroup has height
**strictly** above `1`, so every member of Mathlib's `fundSystem` does, and the product of the
heights of a fundamental system is positive.

## Main results

* `NumberField.Units.absMulHeight₁_eq_one_iff_mem_torsion`: the milestone, `H(u) = 1 ↔ u` is
  torsion, with the relative and logarithmic forms
  `NumberField.Units.mulHeight₁_eq_one_iff_mem_torsion`,
  `NumberField.Units.logHeight₁_eq_zero_iff_mem_torsion` and
  `NumberField.Units.absLogHeight₁_eq_zero_iff_mem_torsion` beside it.
* `NumberField.Units.logHeight₁_eq_zero_iff_forall_infinitePlace`: the step that does the work —
  a unit has height `1` exactly when every infinite place sends it to `1`.
* `NumberField.Units.logHeight₁_eq_zero_iff_logEmbedding_eq_zero`: the height of a unit vanishes
  exactly when its logarithmic embedding does, so `logHeight₁` and `logEmbedding` have the same
  kernel.
* `NumberField.Units.setOf_absMulHeight₁_eq_one`: the units of height one are precisely the
  torsion subgroup, as sets.
* `NumberField.Units.one_lt_absMulHeight₁_of_notMem_torsion` and its logarithmic forms: the gap
  above `1` is strict off the torsion subgroup.
* `NumberField.RingOfIntegers.absMulHeight₁_eq_one_iff_isOfFinOrder` and
  `NumberField.RingOfIntegers.isUnit_of_absMulHeight₁_eq_one`: the unit hypothesis costs nothing,
  since a nonzero algebraic integer of height one is a root of unity and hence a unit.
* `NumberField.Units.fundSystem_notMem_torsion` and
  `NumberField.Units.absLogHeight₁_fundSystem_pos`: the heights appearing in Layer 6.3's bounds
  are positive, so `NumberField.Units.prod_absLogHeight₁_fundSystem_pos`.

## Implementation notes

⚠ **The route the roadmap pins is not the shortest one.** The milestone asks for this "from
Kronecker (1.4) and `logEmbedding_ker`", and both work, but neither is on the critical path.
Layer 6.1 already writes `2 h(u)` as a sum of absolute values over the infinite places, and a sum
of non-negative reals vanishes exactly when each term does; `Mathlib`'s
`NumberField.Units.mem_torsion` is *verbatim* the resulting condition `∀ w, w u = 1`. The proof
below is three lines and mentions no Mahler measure and no kernel. The Layer 1.4 route is kept as
an acceptance criterion at the end of the file, where it confirms that the two agree.

⚠ **`logEmbedding_ker` would be the long way round.** Mathlib derives
`NumberField.Units.logEmbedding_eq_zero_iff`, and hence `logEmbedding_ker`, *from* `mem_torsion`;
using it here would go through `mem_torsion` twice. What the embedding does buy is the statement
`NumberField.Units.logHeight₁_eq_zero_iff_logEmbedding_eq_zero`, which is the useful direction of
the comparison for Layer 6.3 — it says the two functions on `(𝓞 K)ˣ` that Layer 6.1 compares
vanish together, which the two-sided comparison alone does not give, since a comparison with a
factor `2` says nothing about the point where both sides are `0`.

⚠ **Kronecker's theorem is genuinely used, but not Layer 1.4's.** Mathlib's `mem_torsion` rests on
`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`, which is Kronecker's theorem for algebraic
integers. Layer 1.4 proves a strictly more general statement — every algebraic number, in any
field of characteristic zero, through the Mahler measure — and the unit case does not need that
generality. Where Layer 1.4 *is* used is in dropping the unit hypothesis: the two
`NumberField.RingOfIntegers` statements above run over all of `𝓞 K`, and they are what shows the
hypothesis to be no restriction, since a nonzero algebraic integer of height one is a unit.

⚠ **The milestone is stated in the absolute height and proved in the relative one.** The passage
between them is `NumberField.absLogHeight₁_eq`, the Layer 0.3 lemma that Layer 6.1 had to add:
division by `[K : ℚ]` is injective on the value `0`, which is all that is needed here, but it is
the same lemma that turns Layer 6.1's comparison into the shape Layer 6.3 consumes.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5; Kronecker's theorem is their Theorem 1.5.9, and the description of the units of height one
is the case of it that Dirichlet's unit theorem consumes.

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Graduate Texts in
Mathematics **201**, Springer (2000), Corollary B.2.3.1.

This is Layer 6.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Height Module NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A nonzero algebraic integer has height `1` exactly when it is a root of unity.** This is
Kronecker's theorem of Layer 1.4 restricted to `𝓞 K`, and it says that the unit hypothesis in
`NumberField.Units.absMulHeight₁_eq_one_iff_mem_torsion` costs nothing: an algebraic integer of
height `1` is a unit whether or not it was assumed to be one. -/
theorem RingOfIntegers.absMulHeight₁_eq_one_iff_isOfFinOrder {x : 𝓞 K} (hx : x ≠ 0) :
    absMulHeight₁ (x : K) = 1 ↔ IsOfFinOrder x := by
  have hint : IsIntegral ℚ ((x : K)) := Algebra.IsIntegral.isIntegral _
  have hx0 : (x : K) ≠ 0 := fun h ↦ hx (RingOfIntegers.coe_injective (by simpa using h))
  rw [absMulHeight₁_eq_one_iff hint, or_iff_right hx0, isOfFinOrder_iff_pow_eq_one]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact RingOfIntegers.coe_injective (by simpa using h)
  · simpa using congrArg (fun y : 𝓞 K ↦ (y : K)) h

/-- **A nonzero algebraic integer of height one is a unit.** -/
theorem RingOfIntegers.isUnit_of_absMulHeight₁_eq_one {x : 𝓞 K} (hx : x ≠ 0)
    (h : absMulHeight₁ (x : K) = 1) : IsUnit x :=
  ((RingOfIntegers.absMulHeight₁_eq_one_iff_isOfFinOrder hx).mp h).isUnit

namespace Units

/-- **A unit has height `1` exactly when every infinite place sends it to `1`.** This is the step
that does the work: by Layer 6.1, twice the height is the sum of the absolute values of the
weighted logarithms over the infinite places, and a sum of non-negative reals vanishes exactly
when each of its terms does. -/
theorem logHeight₁_eq_zero_iff_forall_infinitePlace (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K) = 0 ↔ ∀ w : InfinitePlace K, w ((u : 𝓞 K) : K) = 1 := by
  have hzero : logHeight₁ ((u : 𝓞 K) : K) = 0 ↔ 2 * logHeight₁ ((u : 𝓞 K) : K) = 0 := by
    constructor <;> intro h <;> linarith
  rw [hzero, two_mul_logHeight₁_eq_sum_abs u,
    Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ abs_nonneg _]
  simp only [Finset.mem_univ, forall_const, abs_eq_zero]
  exact forall_congr' fun w ↦ mult_log_place_eq_zero

/-- **Units of height one, Layer 6.2**, in the relative logarithmic height: a unit has height
`0` exactly when it is a root of unity. -/
theorem logHeight₁_eq_zero_iff_mem_torsion (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K) = 0 ↔ u ∈ torsion K :=
  (logHeight₁_eq_zero_iff_forall_infinitePlace u).trans (mem_torsion K).symm

/-- **Units of height one, Layer 6.2**, in the relative multiplicative height. -/
theorem mulHeight₁_eq_one_iff_mem_torsion (u : (𝓞 K)ˣ) :
    mulHeight₁ ((u : 𝓞 K) : K) = 1 ↔ u ∈ torsion K := by
  rw [← logHeight₁_eq_zero_iff_mem_torsion, logHeight₁_eq_log_mulHeight₁]
  exact ⟨fun h ↦ by rw [h, Real.log_one],
    Real.eq_one_of_pos_of_log_eq_zero (mulHeight₁_pos ((u : 𝓞 K) : K))⟩

/-- **Units of height one, Layer 6.2**, in the absolute logarithmic height. -/
theorem absLogHeight₁_eq_zero_iff_mem_torsion (u : (𝓞 K)ˣ) :
    absLogHeight₁ ((u : 𝓞 K) : K) = 0 ↔ u ∈ torsion K := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [absLogHeight₁_eq, div_eq_zero_iff, or_iff_left hd, logHeight₁_eq_zero_iff_mem_torsion]

/-- **Units of height one** (Bombieri–Gubler 1.5.9; Hindry–Silverman B.2.3.1). A unit of the ring
of integers of a number field has absolute multiplicative height `1` exactly when it is a root of
unity, that is, exactly when it lies in the torsion subgroup. This is Layer 6.2 of the
`ArithmeticHeights` roadmap. -/
theorem absMulHeight₁_eq_one_iff_mem_torsion (u : (𝓞 K)ˣ) :
    absMulHeight₁ ((u : 𝓞 K) : K) = 1 ↔ u ∈ torsion K := by
  rw [← absLogHeight₁_eq_zero_iff_mem_torsion]
  exact ⟨fun h ↦ by rw [absLogHeight₁, h, Real.log_one],
    Real.eq_one_of_pos_of_log_eq_zero
      (zero_lt_one.trans_le (one_le_absMulHeight₁ ((u : 𝓞 K) : K)))⟩

/-- **The height and the logarithmic embedding vanish together.** Layer 6.1 compares the two up to
a factor of `2`, which says nothing about their common zero set; this does. -/
theorem logHeight₁_eq_zero_iff_logEmbedding_eq_zero (u : (𝓞 K)ˣ) :
    logHeight₁ ((u : 𝓞 K) : K) = 0 ↔ logEmbedding K (Additive.ofMul u) = 0 :=
  (logHeight₁_eq_zero_iff_mem_torsion u).trans logEmbedding_eq_zero_iff.symm

/-- The units of height one are precisely the torsion subgroup, as sets. -/
theorem setOf_absMulHeight₁_eq_one (K : Type*) [Field K] [NumberField K] :
    {u : (𝓞 K)ˣ | absMulHeight₁ ((u : 𝓞 K) : K) = 1} = torsion K :=
  Set.ext fun u ↦ absMulHeight₁_eq_one_iff_mem_torsion u

/-- A unit of height one is a root of unity of order dividing `torsionOrder K`: the exponent is
uniform over all of them. -/
theorem pow_torsionOrder_eq_one_of_absMulHeight₁_eq_one {u : (𝓞 K)ˣ}
    (hu : absMulHeight₁ ((u : 𝓞 K) : K) = 1) : u ^ torsionOrder K = 1 :=
  pow_torsionOrder_eq_one K ((absMulHeight₁_eq_one_iff_mem_torsion u).mp hu)

section Gap

/-- **Off the torsion subgroup the height is strictly positive**, in the relative logarithmic
height. -/
theorem logHeight₁_pos_of_notMem_torsion {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    0 < logHeight₁ ((u : 𝓞 K) : K) :=
  lt_of_le_of_ne (zero_le_logHeight₁ ((u : 𝓞 K) : K))
    fun h ↦ hu ((logHeight₁_eq_zero_iff_mem_torsion u).mp h.symm)

/-- **Off the torsion subgroup the height is strictly positive**, in the absolute logarithmic
height. This is the positivity Layer 6.3 needs to know that its bounds are not vacuous. -/
theorem absLogHeight₁_pos_of_notMem_torsion {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    0 < absLogHeight₁ ((u : 𝓞 K) : K) :=
  lt_of_le_of_ne (absLogHeight₁_nonneg ((u : 𝓞 K) : K))
    fun h ↦ hu ((absLogHeight₁_eq_zero_iff_mem_torsion u).mp h.symm)

/-- **Off the torsion subgroup the height is strictly above `1`**, in the absolute multiplicative
height. -/
theorem one_lt_absMulHeight₁_of_notMem_torsion {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    1 < absMulHeight₁ ((u : 𝓞 K) : K) :=
  lt_of_le_of_ne (one_le_absMulHeight₁ ((u : 𝓞 K) : K))
    fun h ↦ hu ((absMulHeight₁_eq_one_iff_mem_torsion u).mp h.symm)

/-- **No member of a fundamental system is a root of unity**: its logarithmic embedding is a basis
vector of the unit lattice, and a basis vector is not zero. -/
theorem fundSystem_notMem_torsion (i : Fin (rank K)) : fundSystem K i ∉ torsion K := by
  intro h
  have hz : logEmbedding K (Additive.ofMul (fundSystem K i)) = 0 :=
    logEmbedding_eq_zero_iff.mpr h
  rw [logEmbedding_fundSystem] at hz
  exact Basis.ne_zero (basisUnitLattice K) i (Submodule.coe_eq_zero.mp hz)

/-- The absolute logarithmic heights appearing in Layer 6.3's bounds are positive. -/
theorem absLogHeight₁_fundSystem_pos (i : Fin (rank K)) :
    0 < absLogHeight₁ ((fundSystem K i : 𝓞 K) : K) :=
  absLogHeight₁_pos_of_notMem_torsion (fundSystem_notMem_torsion i)

/-- The multiplicative form of `NumberField.Units.absLogHeight₁_fundSystem_pos`. -/
theorem one_lt_absMulHeight₁_fundSystem (i : Fin (rank K)) :
    1 < absMulHeight₁ ((fundSystem K i : 𝓞 K) : K) :=
  one_lt_absMulHeight₁_of_notMem_torsion (fundSystem_notMem_torsion i)

/-- The product of the heights of a fundamental system is positive, so Layer 6.3's Hadamard bound
`regulator K ≤ (2 d) ^ r * ∏ h (ε i)` is a bound by a positive number. -/
theorem prod_absLogHeight₁_fundSystem_pos (K : Type*) [Field K] [NumberField K] :
    0 < ∏ i, absLogHeight₁ ((fundSystem K i : 𝓞 K) : K) :=
  Finset.prod_pos fun i _ ↦ absLogHeight₁_fundSystem_pos i

end Gap

section Examples

/-!
### Acceptance criteria

The milestone asks for the statement "from Kronecker (1.4) and `logEmbedding_ker`". Neither is
needed for the proof above, so both are checked here instead: the Layer 1.4 route gives the same
theorem, and Mathlib's finiteness of the torsion subgroup — the statement `logEmbedding_ker` is
used for — is the `B = 0` case of Layer 6.1's finiteness of the units of bounded height.
-/

/-- **Acceptance criterion: the Layer 1.4 route gives the same theorem.** Kronecker's theorem
says an algebraic number has height `1` exactly when it is zero or a root of unity; a unit is
never zero, and `(𝓞 K)ˣ → K` is injective, so the root-of-unity clause transports to finite
order in the unit group. This is the roadmap's stated route, and it agrees with
`NumberField.Units.absMulHeight₁_eq_one_iff_mem_torsion`. -/
example (u : (𝓞 K)ˣ) : absMulHeight₁ ((u : 𝓞 K) : K) = 1 ↔ u ∈ torsion K := by
  have hint : IsIntegral ℚ ((u : 𝓞 K) : K) := Algebra.IsIntegral.isIntegral _
  have hcoe : ∀ n : ℕ, ((u : 𝓞 K) : K) ^ n = 1 ↔ u ^ n = 1 := fun n ↦
    ⟨fun h ↦ coe_injective K (by simpa using h),
      fun h ↦ by simpa using congrArg (fun v : (𝓞 K)ˣ ↦ ((v : 𝓞 K) : K)) h⟩
  rw [absMulHeight₁_eq_one_iff hint, or_iff_right (coe_ne_zero u), torsion,
    CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  exact exists_congr fun n ↦ and_congr_right fun _ ↦ hcoe n

/-- **Acceptance criterion: the torsion subgroup is finite because Northcott's theorem says so.**
Mathlib proves this from `Embeddings.finite_of_norm_le`; here it is the `B = 0` case of Layer
6.1's `NumberField.Units.finite_setOf_logHeight₁_le` together with Layer 6.2. -/
example : (torsion K : Set (𝓞 K)ˣ).Finite := by
  refine (finite_setOf_logHeight₁_le (K := K) 0).subset fun u hu ↦ ?_
  simp only [Set.mem_ofPred_eq]
  exact le_of_eq ((logHeight₁_eq_zero_iff_mem_torsion u).mpr hu)

/-- **Acceptance criterion: the statement is about the subgroup and not about `1`.** The unit
`-1` has height one in every number field, and is not `1`. -/
example : absMulHeight₁ (((-1 : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 ∧ (-1 : (𝓞 K)ˣ) ≠ 1 := by
  refine ⟨(absMulHeight₁_eq_one_iff_mem_torsion _).mpr ?_, fun h ↦ ?_⟩
  · exact (CommGroup.mem_torsion _).mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, neg_one_sq⟩)
  · have hK := congrArg (fun v : (𝓞 K)ˣ ↦ ((v : 𝓞 K) : K)) h
    simp only [Units.val_neg, Units.val_one, map_neg, map_one] at hK
    exact absurd hK (by norm_num)

end Examples

end Units

end NumberField
