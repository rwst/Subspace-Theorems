/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.Order.Northcott

import Mathlib.NumberTheory.Height.NumberField

/-!
# The Northcott property on projective space

`Mathlib/NumberTheory/Height/Northcott.lean` records as its own TODO the `Northcott` instances
for `Projectivization.mulHeight` and `Projectivization.logHeight`. This file supplies them, in
the generality that file works in: a field `K` carrying a family of admissible absolute values
and having the Northcott property for `Height.mulHeight₁`. Over a number field that hypothesis is
Mathlib's `NumberField.finite_setOfPred_mulHeight₁_le`, so the instances apply there with no
further input.

## Main results

* `Height.mulHeight₁_div_le_mulHeight`: the height of a ratio of two coordinates of a tuple is at
  most the height of the tuple. This is the one arithmetic ingredient the instances need.
* `Projectivization.exists_rep_apply_eq_one_of_ne_zero`: at any coordinate where a point of
  `Projectivization K (ι → K)` does not vanish there is a representative with that coordinate
  equal to `1`, whose coordinates are then the ratios of the coordinates of any representative,
  with `Projectivization.exists_rep_apply_eq_one` the form that leaves the index unnamed. No
  heights appear in either; they are statements about projective space.
* `Projectivization.finite_setOfPred_mulHeight_le` and
  `Projectivization.finite_setOfPred_logHeight_le`, with the instances
  `Projectivization.instNorthcottMulHeight` and `Projectivization.instNorthcottLogHeight` that
  are the point of the file.

## Implementation notes

⚠ There is no `Northcott` instance for `Height.mulHeight` on `ι → K`, and none is to be stated:
`Height.mulHeight_smul_eq_mulHeight` puts the whole line `Kˣ • x` at a single height, so
`{x : ι → K | Height.mulHeight x ≤ B}` is infinite as soon as `1 ≤ B` and `ι` is nonempty. This
is refuted among the examples at the end of the file. Northcott is a property of the projective
height, which is why the roadmap asks for these instances and not for one on tuples.

The roadmap proposes a different route — a representative with coordinates in `𝓞 K` generating
an ideal whose absolute norm is bounded by the height, and
`NumberField.absNorm_mul_finprod_finitePlace_eq_one` for the finite part of the height. That
route is not taken. Normalizing a coordinate to `1` reduces the statement to Mathlib's Northcott
property for `mulHeight₁` with `mulHeight₁_div_le_mulHeight` as the only step; it needs no ring
of integers, no ideal norm and no class group, and — the substantive gain — it proves the
instances over any field with `Northcott (Height.mulHeight₁ (K := K))` rather than only over a
number field. The hypothesis cannot be dropped further: by Bombieri–Gubler's Remark 2.4.10 a
general field with a product formula carries Weil heights but not the Northcott property.

The normalization is what `Height.mulHeight_comp_le` is for: with `v i₀ = 1`, the pair
`![v i, v i₀]` is `v ∘ ![i, i₀]`, a reindexing of `v` along a map of index types, so its height
is at most that of `v`. Everything else is finiteness bookkeeping — a bounded-height projective
point lies in the image of a finite set of normalized tuples.

## References

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Theorem B.2.3. Its second statement — for a fixed number field `k`, the set
`{P ∈ ℙⁿ(k) | H_k(P) ≤ B}` is finite — is what is proved here, and the argument is theirs:
normalize one coordinate to `1`, then bound the height of every coordinate by the height of the
point. The same statement is Bombieri–Gubler, *Heights in Diophantine Geometry*, Cambridge
University Press (2006), Theorem 2.4.9 for `X = ℙⁿ` and degree bound `1`. The varying-degree form
of both, which is the theorem the literature calls Northcott's, is Layer 1.3 of the roadmap and
needs the Mahler-measure bridge of Layer 1.2; it is not this statement.

This is Layer 1.1 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Height

/-- The pair of coordinates `(x i, x j)` of a tuple is that tuple reindexed along `![i, j]`. Both
bounds below are `Height.mulHeight_comp_le` read through this identification. -/
private lemma pair_eq_comp {α ι : Type*} (x : ι → α) (i j : ι) : ![x i, x j] = x ∘ ![i, j] := by
  funext k
  fin_cases k <;> rfl

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- The multiplicative height of a ratio of two coordinates of a tuple is at most the
multiplicative height of the tuple.

This is the inequality Northcott's property on projective space rests on: the ratios `x i / x j`
are the affine coordinates of the projective point `x` represents, and there are finitely many
elements of bounded height. -/
lemma mulHeight₁_div_le_mulHeight (x : ι → K) (i j : ι) :
    mulHeight₁ (x i / x j) ≤ mulHeight x := by
  rw [mulHeight₁_div_eq_mulHeight, pair_eq_comp]
  exact mulHeight_comp_le _ x

/-- The logarithmic form of `Height.mulHeight₁_div_le_mulHeight`. -/
lemma logHeight₁_div_le_logHeight (x : ι → K) (i j : ι) :
    logHeight₁ (x i / x j) ≤ logHeight x := by
  rw [logHeight₁_div_eq_logHeight, pair_eq_comp]
  exact logHeight_comp_le _ x

end Height

namespace Projectivization

open Height

section Rep

variable {K : Type*} [Field K] {ι : Type*}

/-- **Normalizing a chosen nonzero coordinate to `1`.** Dividing a representative by a coordinate
that does not vanish gives a representative whose coordinates are the ratios `rep j / rep i`, and
those do not depend on the representative chosen. This is the affine normalization of a projective
point; it carries no arithmetic.

The index is an input, not an output: Kronecker's theorem of Layer 1.4 ranges over every pair of
coordinates, so it needs the normalization at each nonvanishing coordinate in turn. -/
lemma exists_rep_apply_eq_one_of_ne_zero (x : Projectivization K (ι → K)) {i : ι}
    (hi : x.rep i ≠ 0) :
    ∃ (v : ι → K) (hv : v ≠ 0), v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧ mk K v hv = x := by
  refine ⟨(x.rep i)⁻¹ • x.rep, smul_ne_zero (inv_ne_zero hi) x.rep_nonzero,
    inv_mul_cancel₀ hi, fun j ↦ (div_eq_inv_mul _ _).symm, ?_⟩
  conv_rhs => rw [← x.mk_rep]
  exact (mk_eq_mk_iff' K _ _ _ x.rep_nonzero).mpr ⟨_, rfl⟩

/-- A point of `Projectivization K (ι → K)` has a representative one of whose coordinates is `1`:
apply `Projectivization.exists_rep_apply_eq_one_of_ne_zero` at a coordinate where the point does
not vanish. Layer 1.3 consumes it in this form, the index being immaterial there. -/
lemma exists_rep_apply_eq_one (x : Projectivization K (ι → K)) :
    ∃ (v : ι → K) (hv : v ≠ 0) (i : ι), v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧
      mk K v hv = x :=
  let ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  let ⟨v, hv, h1, hratio, hmk⟩ := exists_rep_apply_eq_one_of_ne_zero x hi
  ⟨v, hv, i, h1, hratio, hmk⟩

end Rep

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]
variable [Northcott (mulHeight₁ (K := K))]

/-- **The Northcott property on projective space.** Over a field whose elements of bounded height
are finite in number, the points of `Projectivization K (ι → K)` of bounded multiplicative height
are finite in number.

Over a number field this is Hindry–Silverman, Theorem B.2.3; the hypothesis is then Mathlib's
`NumberField.finite_setOfPred_mulHeight₁_le`. -/
theorem finite_setOfPred_mulHeight_le (B : ℝ) :
    {x : Projectivization K (ι → K) | mulHeight x ≤ B}.Finite := by
  have hpi : {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B}.Finite :=
    (Set.Finite.pi fun _ : ι ↦ Northcott.finite_le (h := mulHeight₁ (K := K)) B).subset
      fun v hv i _ ↦ hv i
  have hsub : (Subtype.val ⁻¹' {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B} :
      Set {w : ι → K // w ≠ 0}).Finite :=
    hpi.preimage Subtype.val_injective.injOn
  refine (hsub.image (mk' K)).subset ?_
  rintro x hx
  obtain ⟨v, hv, i₀, hi₀, -, rfl⟩ := exists_rep_apply_eq_one x
  refine ⟨⟨v, hv⟩, fun i ↦ ?_, rfl⟩
  have h := mulHeight₁_div_le_mulHeight v i i₀
  rw [hi₀, div_one] at h
  exact h.trans (by rwa [← mulHeight_mk hv])

/-- The `Northcott` instance for the projective multiplicative height, which
`Mathlib/NumberTheory/Height/Northcott.lean` asks for. -/
instance instNorthcottMulHeight : Northcott (mulHeight (K := K) (ι := ι)) where
  finite_le := finite_setOfPred_mulHeight_le

/-- The `Northcott` instance for the projective logarithmic height, deduced from the
multiplicative one exactly as Mathlib deduces `Northcott (logHeight₁ (K := K))` from
`Northcott (mulHeight₁ (K := K))`. -/
instance instNorthcottLogHeight : Northcott (logHeight (K := K) (ι := ι)) := by
  rw [show logHeight (K := K) (ι := ι) = Real.log ∘ mulHeight from
    funext logHeight_eq_log_mulHeight]
  exact Northcott.comp_of_bddAbove _ _ fun B ↦
    bddAbove_def.mpr ⟨Real.exp B, fun _ ↦ Real.le_exp_of_log_le⟩

/-- The logarithmic form of `Projectivization.finite_setOfPred_mulHeight_le`. -/
theorem finite_setOfPred_logHeight_le (B : ℝ) :
    {x : Projectivization K (ι → K) | logHeight x ≤ B}.Finite :=
  Northcott.finite_le B

/-!
### Worked examples

The acceptance criteria the roadmap attaches to this layer: that the statement is about the
projective height and not about tuples, and that it is not vacuous.
-/

section Examples

/-- **Rejection test.** `{x : Fin 2 → ℚ | Height.mulHeight x ≤ 1}` is infinite: it contains
`c • ![1, 1]` for every `c ≠ 0`, all of height `1` by `Height.mulHeight_smul_eq_mulHeight`. So no
`Northcott` instance for `Height.mulHeight` on tuples can exist, and the instances above, which
are for the projective height, are the strongest form of the statement. -/
example : {x : Fin 2 → ℚ | Height.mulHeight x ≤ 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ ((n : ℚ) + 1) • (1 : Fin 2 → ℚ)) (fun m n h ↦ ?_) fun n ↦ ?_
  · simpa using congrFun h 0
  · have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    simp [Height.mulHeight_smul_eq_mulHeight _ hn]

/-- **Acceptance test.** The instances are not vacuous: `Projectivization ℚ (Fin 2 → ℚ)` is
itself infinite — it contains `[n : 1]` for every `n` — so cutting it down by a height bound is a
statement about the height. -/
example : (Set.univ : Set (Projectivization ℚ (Fin 2 → ℚ))).Infinite := by
  have hne (n : ℕ) : ![(n : ℚ), 1] ≠ 0 := by simp
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ mk ℚ ![(n : ℚ), 1] (hne n)) (fun m n h ↦ ?_) fun _ ↦ Set.mem_univ _
  rw [mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h1 : a = 1 := by simpa using congrFun ha 1
  subst h1
  have h0 : (n : ℚ) = m := by simpa using congrFun ha 0
  exact_mod_cast h0.symm

/-- **Conformance.** The roadmap pins the instances over a number field; they are the special
case of the above in which the Northcott hypothesis comes from
`NumberField.finite_setOfPred_mulHeight₁_le`. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] :
    Northcott (mulHeight (K := K) (ι := ι)) ∧ Northcott (logHeight (K := K) (ι := ι)) :=
  ⟨inferInstance, inferInstance⟩

end Examples

end Projectivization

end
