/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.MahlerMeasure

import ArithmeticHeights.Northcott
import ArithmeticHeights.NorthcottTheorem
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Kronecker's theorem

**An algebraic number has absolute height one exactly when it is zero or a root of unity.** The
height measures how complicated an algebraic number is, and Kronecker's theorem says that the
numbers of least complexity are the obvious ones.

The proof is the Mahler-measure bridge of Layer 1.2 read as an equation rather than as a bound.
The primitive integer minimal polynomial `f` of an algebraic number `x` of height `1` has
`M(f) = H(x) ^ deg f = 1`, and Mathlib's `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` says that
every nonzero complex root of such an `f` is a root of unity.

## Main results

* `NumberField.absMulHeight₁_eq_one_iff`, over any field of characteristic zero, with
  `NumberField.absLogHeight₁_eq_zero_iff` its logarithmic form.
* `NumberField.absMulHeight_eq_one_of_forall_eq_zero_or_pow_eq_one`: a tuple each of whose
  coordinates is zero or a root of unity has absolute height `1`. This is the converse half of the
  projective statement, and the only part of it that is not immediate.
* `Projectivization.absMulHeight_eq_one_iff`: the projective form, for a field all of whose
  elements are algebraic — a point of `ℙⁿ` has height `1` exactly when every ratio of two of its
  coordinates is zero or a root of unity. Its logarithmic form is
  `Projectivization.absLogHeight_eq_zero_iff`.

## Implementation notes

The hard direction needs a complex root, and `x` is an element of an arbitrary field of
characteristic zero. The bridge is that `ℚ⟮x⟯` is a number field, so `IsAlgClosed.lift` embeds it
in `ℂ`; a field homomorphism is injective, so the conclusion `(φ x) ^ n = 1` comes back as
`x ^ n = 1`. Only a ring homomorphism is used, not the `ℚ`-algebra structure of the embedding —
the statement being proved is not about conjugates.

The easy direction is `NumberField.absMulHeight₁_pow` of Layer 0: a root of unity has a power of
height `1`, and a height is at least `1`, so the height is `1`. Layer 1.3 proves the same thing a
second way, from `Polynomial.cyclotomic_mahlerMeasure_eq_one`, where it is what refutes dropping
the degree bound from Northcott's theorem.

⚠ The algebraicity hypothesis is not decorative: `absMulHeight₁` takes the junk value `1` on every
transcendental element, so the statement without it is false. This is refuted among the examples
at the end of the file.

On the projective form, the degree of a point is not what is bounded — nothing is bounded — but
the same choice as in Layer 1.3 is made about how a projective point is described: by its
**ratios** `rep i / rep j`, which do not depend on the representative, so no field of definition
of a projective point has to be introduced. The converse direction is where the work is. Normalize
a coordinate to `1`; every coordinate of that representative is then a ratio, hence zero or a root
of unity; the orders of finitely many roots of unity have a common multiple `N`; and the tuple
`x ^ N` has every coordinate `0` or `1`, so it is its own square. Its height is therefore its own
square and at least `1`, hence `1`, and `absMulHeight x ^ N = 1` gives the same for `x`.

Kronecker's theorem is often stated as the corollary that a nonzero algebraic **integer** all of
whose conjugates lie in the closed unit disc is a root of unity. That is already Mathlib's
`NumberField.Embeddings.pow_eq_one_of_norm_le_one`, and is not restated here; it is one of the
ingredients of the Mahler-measure statement this file consumes.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.5.9. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
GTM 201 (2000), Corollary B.2.3.1, which is the projective statement proved here. Both deduce it
from Northcott's theorem applied to the orbit `{x ^ n}`, which is recorded among the examples
below as a second proof of the hard direction.

This is Layer 1.4 of the `ArithmeticHeights` roadmap.
-/

public section

open IntermediateField Module NumberField Polynomial

namespace NumberField

variable {K : Type*} [Field K] [CharZero K]

/-- **Kronecker's theorem.** An algebraic number has absolute multiplicative height `1` exactly
when it is zero or a root of unity.

The algebraicity hypothesis is not decorative: the height takes the junk value `1` on every
transcendental element. See the examples at the end of the file. -/
theorem absMulHeight₁_eq_one_iff {x : K} (hx : IsIntegral ℚ x) :
    absMulHeight₁ x = 1 ↔ x = 0 ∨ ∃ n, 0 < n ∧ x ^ n = 1 := by
  constructor
  · intro h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl rfl
    refine Or.inr ?_
    obtain ⟨f, hf, -, hroot, hM⟩ := exists_isPrimitive_absMulHeight₁_pow_natDegree hx
    rw [h, one_pow] at hM
    have hfd : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
    have halg : Algebra.IsAlgebraic ℚ ℚ⟮x⟯ := Algebra.IsAlgebraic.of_finite ℚ _
    let ψ : ℚ⟮x⟯ →+* ℂ := (IsAlgClosed.lift : ℚ⟮x⟯ →ₐ[ℚ] ℂ).toRingHom
    let y : ℚ⟮x⟯ := AdjoinSimple.gen ℚ x
    have hy : algebraMap ℚ⟮x⟯ K y = x := AdjoinSimple.algebraMap_gen ℚ x
    have hy0 : y ≠ 0 := fun h0 ↦ hx0 (by rw [← hy, h0, map_zero])
    have hay : aeval y f = 0 := by
      have hc : (algebraMap ℚ⟮x⟯ K).comp (algebraMap ℤ ℚ⟮x⟯) = algebraMap ℤ K :=
        Subsingleton.elim _ _
      apply FaithfulSMul.algebraMap_injective ℚ⟮x⟯ K
      rw [map_zero, aeval_def, hom_eval₂, hc, ← aeval_def, hy, hroot]
    have haz : aeval (ψ y) f = 0 := by
      have hc : ψ.comp (algebraMap ℤ ℚ⟮x⟯) = algebraMap ℤ ℂ := Subsingleton.elim _ _
      rw [aeval_def, ← hc, ← hom_eval₂, ← aeval_def, hay, map_zero]
    have hz0 : ψ y ≠ 0 := fun h0 ↦ hy0 ((map_eq_zero_iff ψ ψ.injective).mp h0)
    have hmem : ψ y ∈ f.aroots ℂ := mem_aroots.mpr ⟨hf.ne_zero, haz⟩
    obtain ⟨n, hn, hzn⟩ := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one hM.symm hz0 hmem
    have hyn : y ^ n = 1 := ψ.injective (by rw [map_pow, hzn, map_one])
    exact ⟨n, hn, by rw [← hy, ← map_pow, hyn, map_one]⟩
  · rintro (rfl | ⟨n, hn, hxn⟩)
    · exact absMulHeight₁_zero
    · have hp := absMulHeight₁_pow hx n
      rw [hxn, absMulHeight₁_one] at hp
      refine le_antisymm (not_lt.mp fun hlt ↦ ?_) (one_le_absMulHeight₁ x)
      exact absurd hp.symm (one_lt_pow₀ hlt hn.ne').ne'

/-- The logarithmic form of `NumberField.absMulHeight₁_eq_one_iff`: an algebraic number has
absolute logarithmic height `0` exactly when it is zero or a root of unity. -/
theorem absLogHeight₁_eq_zero_iff {x : K} (hx : IsIntegral ℚ x) :
    absLogHeight₁ x = 0 ↔ x = 0 ∨ ∃ n, 0 < n ∧ x ^ n = 1 := by
  rw [← absMulHeight₁_eq_one_iff hx]
  exact ⟨Real.eq_one_of_pos_of_log_eq_zero (zero_lt_one.trans_le (one_le_absMulHeight₁ x)),
    fun h ↦ by rw [absLogHeight₁, h, Real.log_one]⟩

variable {ι : Type*} [Finite ι]

/-- **A tuple of roots of unity and zeros has absolute height `1`.** This is the converse half of
Kronecker's theorem on projective space.

The orders of the nonzero coordinates have a common multiple `N`; the coordinates of `x ^ N` are
then all `0` or `1`, so `x ^ N` is its own square, and a height that is its own square and at
least `1` is `1`. -/
theorem absMulHeight_eq_one_of_forall_eq_zero_or_pow_eq_one {x : ι → K}
    (hx : ∀ i, IsIntegral ℚ (x i)) (h : ∀ i, x i = 0 ∨ ∃ n, 0 < n ∧ x i ^ n = 1) :
    absMulHeight x = 1 := by
  classical
  have key : ∀ i, ∃ m : ℕ, 0 < m ∧ (x i = 0 ∨ x i ^ m = 1) := by
    intro i
    rcases h i with h0 | ⟨n, hn, hn1⟩
    exacts [⟨1, one_pos, Or.inl h0⟩, ⟨n, hn, Or.inr hn1⟩]
  choose m hm hm1 using key
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧ ∀ i, x i = 0 ∨ x i ^ N = 1 := by
    refine ⟨∏ i, m i, Finset.prod_pos fun i _ ↦ hm i, fun i ↦ ?_⟩
    rcases hm1 i with h0 | h1
    · exact Or.inl h0
    · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
      exact Or.inr (by rw [hk, pow_mul, h1, one_pow])
  have hxN : ∀ i, (x ^ N) i = 0 ∨ (x ^ N) i = 1 := fun i ↦ by
    rw [Pi.pow_apply]
    rcases hN i with h0 | h1
    exacts [Or.inl (by rw [h0, zero_pow hNpos.ne']), Or.inr h1]
  have hsq : (x ^ N) ^ 2 = x ^ N := funext fun i ↦ by
    rw [Pi.pow_apply]
    rcases hxN i with h0 | h1
    exacts [by rw [h0, zero_pow two_ne_zero], by rw [h1, one_pow]]
  have hpow : absMulHeight (x ^ N) = absMulHeight (x ^ N) * absMulHeight (x ^ N) := by
    conv_lhs => rw [← hsq]
    rw [absMulHeight_pow (fun i ↦ by rw [Pi.pow_apply]; exact (hx i).pow N) 2, pow_two]
  have hone : absMulHeight x ^ N = 1 := by
    rw [← absMulHeight_pow hx N]
    exact (mul_left_cancel₀ (absMulHeight_ne_zero _) ((mul_one _).trans hpow)).symm
  refine le_antisymm (not_lt.mp fun hlt ↦ ?_) (one_le_absMulHeight x)
  exact absurd hone (one_lt_pow₀ hlt hNpos.ne').ne'

/-- The logarithmic form of
`NumberField.absMulHeight_eq_one_of_forall_eq_zero_or_pow_eq_one`. -/
theorem absLogHeight_eq_zero_of_forall_eq_zero_or_pow_eq_one {x : ι → K}
    (hx : ∀ i, IsIntegral ℚ (x i)) (h : ∀ i, x i = 0 ∨ ∃ n, 0 < n ∧ x i ^ n = 1) :
    absLogHeight x = 0 := by
  rw [absLogHeight, absMulHeight_eq_one_of_forall_eq_zero_or_pow_eq_one hx h, Real.log_one]

end NumberField

namespace Projectivization

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Finite ι]

/-- **Kronecker's theorem on projective space** (Hindry–Silverman, Corollary B.2.3.1). A point of
`ℙ(ι → K)` has absolute height `1` exactly when every ratio of two of its coordinates is zero or a
root of unity.

The ratios `rep i / rep j` do not depend on the representative, so the condition is a condition on
the point. -/
theorem absMulHeight_eq_one_iff (P : Projectivization K (ι → K)) :
    absMulHeight P = 1 ↔
      ∀ i j, P.rep i / P.rep j = 0 ∨ ∃ n, 0 < n ∧ (P.rep i / P.rep j) ^ n = 1 := by
  have hint : ∀ y : K, IsIntegral ℚ y := fun y ↦ (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  constructor
  · intro h i j
    rcases eq_or_ne (P.rep j) 0 with hj | hj
    · exact Or.inl (by rw [hj, div_zero])
    obtain ⟨v, hv, hvj, hratio, hmk⟩ := exists_rep_apply_eq_one_of_ne_zero P hj
    have hP : NumberField.absMulHeight v = 1 := by rw [← absMulHeight_mk hv, hmk, h]
    have hle : NumberField.absMulHeight₁ (v i) ≤ 1 :=
      hP ▸ NumberField.absMulHeight₁_le_absMulHeight (fun _ ↦ hint _) hvj i
    rw [← hratio i]
    exact (NumberField.absMulHeight₁_eq_one_iff (hint _)).mp
      (le_antisymm hle (NumberField.one_le_absMulHeight₁ _))
  · intro h
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp P.rep_nonzero
    obtain ⟨v, hv, -, hratio, hmk⟩ := exists_rep_apply_eq_one_of_ne_zero P hi₀
    rw [← hmk, absMulHeight_mk]
    exact NumberField.absMulHeight_eq_one_of_forall_eq_zero_or_pow_eq_one (fun _ ↦ hint _)
      fun k ↦ by rw [hratio k]; exact h k i₀

/-- The logarithmic form of `Projectivization.absMulHeight_eq_one_iff`. -/
theorem absLogHeight_eq_zero_iff (P : Projectivization K (ι → K)) :
    absLogHeight P = 0 ↔
      ∀ i j, P.rep i / P.rep j = 0 ∨ ∃ n, 0 < n ∧ (P.rep i / P.rep j) ^ n = 1 := by
  rw [← absMulHeight_eq_one_iff, absLogHeight_eq_log_absMulHeight]
  exact ⟨Real.eq_one_of_pos_of_log_eq_zero (absMulHeight_pos P), fun h ↦ by rw [h, Real.log_one]⟩

end Projectivization

/-!
### Worked examples

The acceptance criteria the roadmap attaches to this layer: that the theorem is not vacuous on
either side, that the algebraicity hypothesis is needed, and that the second route to it — through
Northcott's theorem of Layer 1.3, applied to the orbit `{x ^ n}` — gives the same conclusion.
-/

section Examples

/-- **Acceptance test.** A primitive fifth root of unity has absolute height `1`. -/
example : absMulHeight₁ (Complex.exp (2 * Real.pi * Complex.I / 5)) = 1 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 := by
    exact_mod_cast Complex.isPrimitiveRoot_exp 5 (by norm_num)
  exact (absMulHeight₁_eq_one_iff (hprim.isIntegral (by norm_num)).tower_top).mpr
    (Or.inr ⟨5, by norm_num, hprim.pow_eq_one⟩)

/-- **Rejection test: the algebraicity hypothesis cannot be dropped.** A transcendental element
has absolute height `1` by the junk value, while it is neither zero nor a root of unity — both of
those are integral over `ℚ`. Over any field of characteristic zero with a transcendental element,
Kronecker's theorem without the hypothesis is therefore false. -/
example {K : Type*} [Field K] [CharZero K] {x : K} (hx : ¬ IsIntegral ℚ x) :
    absMulHeight₁ x = 1 ∧ ¬ (x = 0 ∨ ∃ n, 0 < n ∧ x ^ n = 1) := by
  refine ⟨?_, ?_⟩
  · rw [← absMulHeight_eq_absMulHeight₁,
      absMulHeight_eq_one_of_not_isIntegral fun h ↦ hx (by simpa using h 0)]
  · rintro (rfl | ⟨n, hn, hn1⟩)
    · exact hx isIntegral_zero
    · exact hx (IsIntegral.of_pow hn (hn1 ▸ isIntegral_one))

/-- **Acceptance test: the two routes agree.** Northcott's theorem of Layer 1.3 proves the hard
direction a second way, and without any mention of `ℂ`. The orbit `{x ^ n}` of an algebraic number
of height `1` has height `1` throughout, by `NumberField.absMulHeight₁_pow`, and degree at most
that of `x`, since `ℚ⟮x ^ n⟯ ≤ ℚ⟮x⟯`; so it is finite, so two of its members coincide, and a
nontrivial relation `x ^ a = x ^ b` in a field says that `x` is a root of unity. -/
example {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x) (hx0 : x ≠ 0)
    (h : absMulHeight₁ x = 1) : ∃ n, 0 < n ∧ x ^ n = 1 := by
  have hfd : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
  have hD : ∀ n : ℕ, finrank ℚ ℚ⟮x ^ n⟯ ≤ finrank ℚ ℚ⟮x⟯ := fun n ↦
    finrank_le_of_le_right (adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self ℚ x) n))
  have hfin : (Set.range fun n : ℕ ↦ x ^ n).Finite := by
    refine (finite_setOfPred_absMulHeight₁_le_of_finrank_le 1 (finrank ℚ ℚ⟮x⟯)).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨hx.pow n, by rw [absMulHeight₁_pow hx, h, one_pow], hD n⟩
  have key : ∀ a b : ℕ, a < b → x ^ a = x ^ b → ∃ k, 0 < k ∧ x ^ k = 1 := by
    refine fun a b hab h' ↦ ⟨b - a, Nat.sub_pos_of_lt hab, mul_left_cancel₀ (pow_ne_zero a hx0) ?_⟩
    rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab.le, ← h']
  obtain ⟨a, b, hab, hne⟩ :=
    Function.not_injective_iff.mp fun hinj ↦ Set.infinite_range_of_injective hinj hfin
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' hab, key b a h' hab.symm]

/-- **Conformance.** The roadmap pins the statement over `ℂ`; it is the special case of the
above. -/
example {x : ℂ} (hx : IsIntegral ℚ x) :
    NumberField.absMulHeight₁ x = 1 ↔ x = 0 ∨ ∃ n, 0 < n ∧ x ^ n = 1 :=
  NumberField.absMulHeight₁_eq_one_iff hx

end Examples

end
