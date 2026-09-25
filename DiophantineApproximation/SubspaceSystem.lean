/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Affine
public import DiophantineApproximation.AffineProd
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.Height.NumberField

-- Used only inside proofs.
import DiophantineApproximation.FundamentalInequality
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.SubspaceAffine
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- Used only by the acceptance criteria.
import ArithmeticHeights.Absolute
import DiophantineApproximation.RationalPlaces

/-!
# Systems of inequalities: the form the quantitative Subspace Theorem counts

**Layer 9.1.** Let `K` be a number field, `S` a finite set of primes of `𝓞 K`, `F / K` a finite
extension, `w v` an absolute value of `F` over each place `v` of `K`, and `L v i` linear forms over
`F`, all as in the affine Subspace Theorem (Layer 6.4). The quantitative theory (Evertse, "On the
Quantitative Subspace Theorem", §2) does not count the solutions of the product inequality of 6.4
but those of a **system**

```text
|L v i (x)|_v  ≤  C v · H(x) ^ (c v i)      for every place v of S∞ ∪ S and every i,
```

in `x` with `S`-integral coordinates, where `H` is the **affine** height (`ArithmeticHeights` 0.5).
The places of the system are indexed by `InfinitePlace K ⊕ S`, and at an infinite place the local
value is `w v (·) ^ mult v`, as in `NumberField.affineProd`. Evertse's absolute values are the
`[K : ℚ]`-th roots of these and his height is the `[K : ℚ]`-th root of `mulHeightAff`, so **the
exponents `c v i` are the same numbers in both normalizations**, and only the constants change,
`C v` here being his `C v ^ [K : ℚ]`.

The two directions of "the product inequality is equivalent to finitely many systems" are
`NumberField.affineProd_le_of_mem_systemSet` — the product of the inequalities of a system is the
product inequality, with the weight `∑ c v i` as its exponent — and
`NumberField.exists_finset_forall_exists_mem_systemSet`: for `δ > 0` there are finitely many
exponent systems, each of weight at most `-δ / 2`, such that for **any** positive constants every
`S`-integral solution of `affineProd ≤ H(x) ^ (-δ)` of large enough height satisfies one of them.
Evertse's Theorem A, the Subspace Theorem for one system of weight `< 0`, is then 6.4
(`NumberField.exists_finset_submodule_of_systemWeight_neg`).

Evertse's **normalization** (2.4) is `NumberField.IsNormalizedSystem`: coefficients of height at
most `H` and degree at most `D` over `K`, at most `R` distinct forms, `∏ C v` at most
`∏ |det L v|_v ^ (1 / n)`, weight at most `-δ` with `0 < δ ≤ 1`, and `max_i c v i` equal to the
normalized local degree `s(v)` — `mult v / [K : ℚ]` at the infinite places and `0` at the finite
ones. Under it the product of a system is **Schmidt's normalized inequality**
`|L₁(x) ⋯ Lₙ(x)| ≤ |det| · H(x) ^ (-δ)` (`NumberField.affineProd_le_systemDet_mul_rpow`). A
solution is **large** (`NumberField.IsLargeSolution`) if its absolute affine height is at least
`max (2 H) (n ^ (2 n / δ))`.

## Main definitions

* `NumberField.systemPlace`, `NumberField.systemAbs`, `NumberField.systemValue`: the places of a
  system, the local size at each, and the value of a form there.
* `NumberField.systemSet`: the solutions of a system, `S`-integrality included.
* `NumberField.systemWeight`, `NumberField.systemConst`, `NumberField.systemDet`,
  `NumberField.systemExponent`: `∑ c v i`, `∏ C v`, `∏ |det L v|_v` and `s(v)`.
* `NumberField.IsNormalizedSystem`: Evertse's normalization (2.4).
* `NumberField.IsLargeSolution`: the large solutions.

## Main results

* `NumberField.affineProd_eq_prod_systemValue`: the affine quantity of 6.4 is the product of the
  local values of a system.
* `NumberField.affineProd_le_of_mem_systemSet`: a solution of a system satisfies the product
  inequality with exponent the weight.
* `NumberField.affineProd_le_systemDet_mul_rpow`: under the normalization, Schmidt's inequality.
* `NumberField.exists_finset_submodule_of_systemWeight_neg`: **Evertse's Theorem A**.
* `NumberField.exists_systemValue_le_mul_mulHeightAff`: every local value is at most a constant
  times the affine height.
* `NumberField.exists_finset_forall_exists_mem_systemSet`: **the reduction to finitely many
  systems** (Evertse, §2, "by an elementary combinatorial argument").

## Implementation notes

⚠ **The reduction is stated against the affine height, and then it needs no unit.** Evertse's
product inequality (2.2) has `H(x)` affine on the right; 6.4 has the projective height, which is
at most the affine one, so (2.2) implies 6.4's inequality but not conversely. Against the affine
height every local value is at most `A · H(x)` — a coordinate is at most the height at every place
— so the exponents `log |L v i x|_v / log H(x)` are bounded above by `2` for large `H(x)`, with no
normalization of `x`, no fundamental inequality and no independence of the forms. That is the
difference from Layer 5.1, which measured against the projective height and had to move `x` by an
`S`-unit first.

⚠ **The exponents are not bounded below, and need not be.** A form may vanish at `x`, and a value
may be as small as it likes. The reduction clamps every exponent below at `-M` with
`M = 2 · #(places × forms) + δ + 1`: if some exponent is clamped, the others are at most `2` and the
weight is at most `-δ` anyway, and if none is, the weight is the logarithm of the product. So
**vanishing forms need no separate case**, unlike 5.1's classes, which had to leave the kernels to
6.2.

⚠ **The constants are free, and the normalization of the exponents is not.** The exponent grid does
not depend on the constants, and for any `C v > 0` the level `Q₀` absorbs them; choosing
`C v = |det L v|_v ^ (1 / n)` meets the third condition of (2.4) with equality. The last condition,
`max_i c v i = s(v)`, is **not** produced and cannot be without moving the point: at a finite
place `v ∈ S` it asks `|L v i x|_v ≤ C v` for every `i`, and the `S`-integral points `p ^ (-k) · y`
violate it for every constant. It is a condition on the representative of the projective point,
achieved by an `S`-unit (5.1's Lemma 7.5.4 with the weights `s(v)`), and it is what the gap
principle (9.2) uses, through `c v i ≤ s(v)`.

⚠ **Theorem A needs `[Nontrivial ι]` and a strict weight.** For `n = 1` the only proper subspace is
`0` and the system `|x| ≤ H(x) ^ (-1)` over `ℚ` has the solution `1`; that is the rejection test
below. The small solutions — of affine height below `(∏ C v) ^ (2 n / κ)` for weight `-κ` — are
finite in number by Northcott, because the affine height of a tuple bounds the height of every
coordinate, and each contributes its own line; the large ones satisfy 6.4's inequality with
exponent `κ / 2`.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240; J. Math. Sci. **171** (2010), 824–837 (arXiv:1008.2268), §2, systems (2.3) and
normalization (2.4).

W. M. Schmidt, *The subspace theorem in Diophantine approximations*, Compositio Math. **69**
(1989), 121–173.

This is Layer 9.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The places of a system**: the infinite places of `K` and the finite places of the primes of
`S`, as absolute values of `K`. -/
noncomputable def systemPlace (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ S → AbsoluteValue K ℝ
  | .inl v => v.1
  | .inr v => (FinitePlace.mk v.1).1

/-- The multiplicity of a place of a system: `mult v` at an infinite place, `1` at a finite one. -/
noncomputable def systemMult (S : Finset (HeightOneSpectrum (𝓞 K))) : InfinitePlace K ⊕ S → ℕ
  | .inl v => v.mult
  | .inr _ => 1

/-- **The local size at a place of a system**, in Mathlib's normalization: `w v (a) ^ mult v`, so
that the product over the places of a system is the product formula's. -/
noncomputable def systemAbs (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (p : InfinitePlace K ⊕ S) (a : F) : ℝ :=
  w (systemPlace S p) a ^ systemMult S p

/-- **The value of the `i`-th form of a system at `x`**, measured at the place `p`. -/
noncomputable def systemValue (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (p : InfinitePlace K ⊕ S) (i : ι) (x : ι → K) : ℝ :=
  systemAbs S w p (L (systemPlace S p) i fun j ↦ algebraMap K F (x j))

/-- **The solutions of a system of inequalities** (Evertse's (2.3)): the points with `S`-integral
coordinates at which every form is at most `C p · H(x) ^ (c p i)` at every place of the system,
`H` being the affine height. -/
def systemSet (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (C : InfinitePlace K ⊕ S → ℝ)
    (c : InfinitePlace K ⊕ S → ι → ℝ) : Set (ι → K) :=
  {x | (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
    ∀ p i, systemValue S w L p i x ≤ C p * mulHeightAff x ^ c p i}

/-- **The weight of a system**, `∑ c v i` over the places and the forms. -/
noncomputable def systemWeight {S : Finset (HeightOneSpectrum (𝓞 K))}
    (c : InfinitePlace K ⊕ S → ι → ℝ) : ℝ :=
  ∑ p, ∑ i, c p i

/-- The product of the constants of a system. -/
noncomputable def systemConst {S : Finset (HeightOneSpectrum (𝓞 K))}
    (C : InfinitePlace K ⊕ S → ℝ) : ℝ :=
  ∏ p, C p

/-- **The determinant product** `∏ |det L v|_v` over the places of a system, the right-hand side
of Schmidt's normalized inequality. -/
noncomputable def systemDet (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) :
    ℝ :=
  ∏ p, systemAbs S w p (LinearMap.det (LinearMap.pi (L (systemPlace S p))))

/-- **The normalized local degree** `s(v)`: `mult v / [K : ℚ]` at an infinite place and `0` at a
finite one. The values at the infinite places sum to `1`. -/
noncomputable def systemExponent (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ S → ℝ
  | .inl v => v.mult / finrank ℚ K
  | .inr _ => 0

/-- **Evertse's normalization (2.4)** of a system, with parameters `H` (heights of the
coefficients), `D` (their degrees over `K`), `R` (the number of distinct forms) and `δ`. The last
two fields together say `max_i c p i = s(p)`. -/
structure IsNormalizedSystem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (C : InfinitePlace K ⊕ S → ℝ) (c : InfinitePlace K ⊕ S → ι → ℝ) (H : ℝ) (D R : ℕ)
    (δ : ℝ) : Prop where
  /-- The coefficients have absolute height at most `H`. -/
  height_le : ∀ p i j, absMulHeight₁ (L (systemPlace S p) i (Pi.basisFun F ι j)) ≤ H
  /-- The coefficients have degree at most `D` over `K`. -/
  degree_le : ∀ p i j, (minpoly K (L (systemPlace S p) i (Pi.basisFun F ι j))).natDegree ≤ D
  /-- At most `R` distinct forms occur. -/
  ncard_le : (Set.range fun q : (InfinitePlace K ⊕ S) × ι ↦ L (systemPlace S q.1) q.2).ncard ≤ R
  /-- The constants are positive. -/
  const_pos : ∀ p, 0 < C p
  /-- The product of the constants is at most `(∏ |det L v|_v) ^ (1 / n)`. -/
  const_le : systemConst C ≤ systemDet S w L ^ (Fintype.card ι : ℝ)⁻¹
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  /-- The weight is at most `-δ`. -/
  weight_le : systemWeight c ≤ -δ
  /-- No exponent exceeds the normalized local degree. -/
  exponent_le : ∀ p i, c p i ≤ systemExponent S p
  /-- Some exponent at every place attains it. -/
  exists_exponent_eq : ∀ p, ∃ i, c p i = systemExponent S p

/-- **A large solution** (Evertse, Theorem B): its absolute affine height `H(x) ^ (1 / [K : ℚ])`
is at least `max (2 H) (n ^ (2 n / δ))`. The quantitative Subspace Theorem counts the subspaces
of these separately from the rest (Layers 9.3 and 9.4). -/
def IsLargeSolution (H δ : ℝ) (x : ι → K) : Prop :=
  max (2 * H) ((Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ)) ≤
    mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)

omit [NumberField F] [Fintype ι] in
theorem systemValue_nonneg (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (p : InfinitePlace K ⊕ S) (i : ι) (x : ι → K) : 0 ≤ systemValue S w L p i x :=
  pow_nonneg (apply_nonneg _ _) _

omit [NumberField F] in
/-- **The affine quantity of 6.4 is the product of the local values of a system.** -/
theorem affineProd_eq_prod_systemValue (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) : affineProd S w L x = ∏ p, ∏ i, systemValue S w L p i x := by
  rw [affineProd, Fintype.prod_sum_type, ← Finset.prod_coe_sort S]
  congr 1
  · exact Finset.prod_congr rfl fun v _ ↦ by rw [← Finset.prod_pow]; rfl
  · exact Finset.prod_congr rfl fun v _ ↦ Finset.prod_congr rfl fun i _ ↦ (pow_one _).symm

omit [NumberField F] in
/-- **A solution of a system satisfies the product inequality**, with the product of the constants
to the power `n` in front and the weight as the exponent. This is the easy direction of the
equivalence between the product inequality and finitely many systems. -/
theorem affineProd_le_of_mem_systemSet {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ}
    {x : ι → K} (hx : x ∈ systemSet S w L C c) :
    affineProd S w L x ≤ systemConst C ^ Fintype.card ι * mulHeightAff x ^ systemWeight c := by
  have hH := mulHeightAff_pos x
  rw [affineProd_eq_prod_systemValue]
  calc ∏ p, ∏ i, systemValue S w L p i x ≤ ∏ p, ∏ i, (C p * mulHeightAff x ^ c p i) :=
        Finset.prod_le_prod₀ (fun p _ ↦ Finset.prod_nonneg fun i _ ↦ systemValue_nonneg ..)
          fun p _ ↦ Finset.prod_le_prod₀ (fun i _ ↦ systemValue_nonneg ..) fun i _ ↦ hx.2 p i
    _ = systemConst C ^ Fintype.card ι * mulHeightAff x ^ systemWeight c := by
        rw [systemConst, systemWeight, Real.rpow_sum_of_pos hH, ← Finset.prod_pow,
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p _ ↦ ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Real.rpow_sum_of_pos hH]

/-- **Under Evertse's normalization a system implies Schmidt's normalized inequality**
`|L₁(x) ⋯ Lₙ(x)| ≤ |det| · H(x) ^ (-δ)`, the form in which Schmidt's quantitative theorem of 1989
is stated. -/
theorem affineProd_le_systemDet_mul_rpow [Nonempty ι] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {C : InfinitePlace K ⊕ S → ℝ} {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {x : ι → K} (hx : x ∈ systemSet S w L C c) :
    affineProd S w L x ≤ systemDet S w L * mulHeightAff x ^ (-δ) := by
  have hdet0 : 0 ≤ systemDet S w L := Finset.prod_nonneg fun p _ ↦ pow_nonneg (apply_nonneg _ _) _
  have hC0 : 0 ≤ systemConst C := Finset.prod_nonneg fun p _ ↦ (hN.const_pos p).le
  have hN0 : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : systemConst C ^ Fintype.card ι ≤ systemDet S w L :=
    calc systemConst C ^ Fintype.card ι
        ≤ (systemDet S w L ^ (Fintype.card ι : ℝ)⁻¹) ^ Fintype.card ι :=
          pow_le_pow_left₀ hC0 hN.const_le _
      _ = systemDet S w L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hdet0, inv_mul_cancel₀ hN0, Real.rpow_one]
  have h3 : mulHeightAff x ^ systemWeight c ≤ mulHeightAff x ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_mulHeightAff x) hN.weight_le
  exact (affineProd_le_of_mem_systemSet hx).trans
    (mul_le_mul h2 h3 (Real.rpow_nonneg (mulHeightAff_pos x).le _) hdet0)

open scoped Classical in
/-- **Evertse's Theorem A: the Subspace Theorem for a system.** The nonzero solutions of a system
of negative weight lie in finitely many proper subspaces of `Kⁿ`. The solutions of large affine
height satisfy the product inequality of 6.4 with half the weight as exponent; the others are
finite in number by Northcott, and each spans a line. -/
theorem exists_finset_submodule_of_systemWeight_neg [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {C : InfinitePlace K ⊕ S → ℝ} (hC : ∀ p, 0 ≤ C p) {c : InfinitePlace K ⊕ S → ι → ℝ}
    (hc : systemWeight c < 0) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c, x ≠ 0 → ∃ W ∈ T, x ∈ W := by
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : ℝ, 0 < κ ∧ systemWeight c = -κ := ⟨-systemWeight c, by linarith,
    by ring⟩
  set A : ℝ := systemConst C ^ Fintype.card ι with hAdef
  have hA0 : 0 ≤ A := pow_nonneg (Finset.prod_nonneg fun p _ ↦ hC p) _
  obtain ⟨T₁, hT₁, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le S w hwInf hwFin
    L hLInf hLFin (half_pos hκ0)
  set B : ℝ := max 1 (A ^ (2 / κ)) with hB
  have hfin : {x : ι → K | mulHeightAff x ≤ B}.Finite :=
    (Set.Finite.pi (t := fun _ : ι ↦ {a : K | mulHeight₁ a ≤ B})
      fun _ ↦ NumberField.finite_setOfPred_mulHeight₁_le K B).subset
      fun x hx j _ ↦ (mulHeight₁_le_mulHeightAff x j).trans hx
  refine ⟨T₁ ∪ hfin.toFinset.image fun x ↦ K ∙ x, fun W hW ↦ ?_, fun x hx hx0 ↦ ?_⟩
  · rcases Finset.mem_union.1 hW with hW | hW
    · exact hT₁ W hW
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hW
    intro htop
    have h1 : finrank K (K ∙ x) ≤ 1 := by
      rcases eq_or_ne x 0 with rfl | hx
      · rw [Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]; exact zero_le_one
      · exact (finrank_span_singleton hx).le
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    exact absurd h1 (not_le.2 Fintype.one_lt_card)
  by_cases hsmall : mulHeightAff x ≤ B
  · exact ⟨K ∙ x, Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hfin.mem_toFinset.2 hsmall,
      rfl⟩), Submodule.mem_span_singleton_self x⟩
  push Not at hsmall
  have hHpos : 0 < mulHeightAff x := mulHeightAff_pos x
  have hAle : A ≤ mulHeightAff x ^ (κ / 2) :=
    calc A = (A ^ (2 / κ)) ^ (κ / 2) := by
          rw [← Real.rpow_mul hA0, div_mul_div_comm, mul_comm 2 κ, div_self (by positivity),
            Real.rpow_one]
      _ ≤ mulHeightAff x ^ (κ / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _)
          ((le_max_right _ _).trans hsmall.le) (by positivity)
  obtain ⟨W, hW, hxW⟩ := hcov x hx0 hx.1 <|
    calc affineProd S w L x ≤ A * mulHeightAff x ^ systemWeight c :=
          affineProd_le_of_mem_systemSet hx
      _ ≤ mulHeightAff x ^ (κ / 2) * mulHeightAff x ^ (-κ) := by
          rw [hκ]; exact mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg hHpos.le _)
      _ = mulHeightAff x ^ (-(κ / 2)) := by rw [← Real.rpow_add hHpos]; congr 1; ring
      _ ≤ mulHeight x ^ (-(κ / 2)) :=
          Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (one_le_mulHeight x))
            (mulHeight_le_mulHeightAff x) (by linarith)
  exact ⟨W, Finset.mem_union_left _ hW, hxW⟩

omit [Fintype ι] in
/-- **A coordinate is at most the affine height at every place of a system**, counted with its
multiplicity. -/
theorem systemPlace_pow_le_mulHeightAff [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : InfinitePlace K ⊕ S) (x : ι → K) (j : ι) :
    systemPlace S p (x j) ^ systemMult S p ≤ mulHeightAff x := by
  refine le_trans ?_ (mulHeight₁_le_mulHeightAff x j)
  rcases p with v | v
  · change v (x j) ^ v.mult ≤ mulHeight₁ (x j)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, map_zero, zero_pow InfinitePlace.mult_ne_zero]; exact zero_le_one.trans
        (one_le_mulHeight₁ _)
    · have := prod_apply_le_mulHeight₁ {v} (∅ : Finset (FinitePlace K)) h
      rwa [Finset.prod_singleton, Finset.prod_empty, mul_one] at this
  · change FinitePlace.mk v.1 (x j) ^ 1 ≤ mulHeight₁ (x j)
    rw [pow_one]
    exact (le_max_left _ _).trans ((FinitePlace.mk v.1).max_apply_one_le_mulHeight₁ (x j))

omit [NumberField K] in
theorem systemMult_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) (p : InfinitePlace K ⊕ S) :
    systemMult S p ≠ 0 := by
  rcases p with v | v
  · exact InfinitePlace.mult_ne_zero
  · exact one_ne_zero

omit [Fintype ι] in
open scoped Classical in
/-- **Every local value of a system is at most a constant times the affine height.** A form is a
combination of the coordinates and each coordinate is at most the height at every place; no
independence of the forms and no integrality of the point is used. -/
theorem exists_systemValue_le_mul_mulHeightAff [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ p i (x : ι → K), systemValue S w L p i x ≤ A * mulHeightAff x := by
  have := Fintype.ofFinite ι
  set b : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ (∑ j, w (systemPlace S p)
    (L (systemPlace S p) i fun k ↦ if j = k then 1 else 0)) ^ systemMult S p with hb
  have hb0 : ∀ p i, 0 ≤ b p i := fun p i ↦
    pow_nonneg (Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _) _
  have hlies : ∀ p : InfinitePlace K ⊕ S, (w (systemPlace S p)).LiesOver (systemPlace S p) := by
    rintro (v | v)
    · exact hwInf v
    · exact hwFin v.1 v.2
  refine ⟨1 + ∑ p, ∑ i, b p i, le_add_of_nonneg_right (Finset.sum_nonneg fun p _ ↦
    Finset.sum_nonneg fun i _ ↦ hb0 p i), fun p i x ↦ ?_⟩
  have hbA : b p i ≤ 1 + ∑ p, ∑ i, b p i := by
    refine le_add_of_nonneg_of_le zero_le_one ?_
    exact (Finset.single_le_sum (fun i _ ↦ hb0 p i) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun p ↦ ∑ i, b p i)
        (fun p _ ↦ Finset.sum_nonneg fun i _ ↦ hb0 p i) (Finset.mem_univ p))
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hbA (mulHeightAff_pos x).le)
  have := hlies p
  set m := systemMult S p with hm
  have hm0 : m ≠ 0 := systemMult_ne_zero S p
  set Q := mulHeightAff x with hQ
  have hQ0 : 0 ≤ Q := (mulHeightAff_pos x).le
  set T : ℝ := Q ^ (m⁻¹ : ℝ) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0 _
  have hcoord : ∀ j, w (systemPlace S p) (algebraMap K F (x j)) ≤ T := fun j ↦ by
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := systemPlace S p)]
    refine (pow_le_pow_iff_left₀ (apply_nonneg _ _) hT0 hm0).1 ?_
    rw [hT, Real.rpow_inv_natCast_pow hQ0 hm0]
    exact systemPlace_pow_le_mulHeightAff S p x j
  have hsum : w (systemPlace S p) (L (systemPlace S p) i fun j ↦ algebraMap K F (x j)) ≤
      T * ∑ j, w (systemPlace S p) (L (systemPlace S p) i fun k ↦ if j = k then 1 else 0) := by
    rw [LinearMap.pi_apply_eq_sum_univ, Finset.mul_sum]
    refine (AbsoluteValue.sum_le _ _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [smul_eq_mul, map_mul]
    exact mul_le_mul_of_nonneg_right (hcoord j) (apply_nonneg _ _)
  calc systemValue S w L p i x
      ≤ (T * ∑ j, w (systemPlace S p)
          (L (systemPlace S p) i fun k ↦ if j = k then 1 else 0)) ^ m :=
        pow_le_pow_left₀ (apply_nonneg _ _) hsum _
    _ = b p i * Q := by rw [mul_pow, hT, Real.rpow_inv_natCast_pow hQ0 hm0, mul_comm]

omit [NumberField K] in
private theorem rpow_div_log_eq {Q a : ℝ} (hQ : 1 < Q) (ha : 0 < a) :
    Q ^ (Real.log a / Real.log Q) = a := by
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ (Real.log_pos hQ).ne',
    Real.exp_log ha]

open scoped Classical in
/-- **The reduction to finitely many systems** (Evertse, §2). For `δ > 0` there are finitely many
exponent systems `c`, each of weight at most `-δ / 2`, such that for any positive constants `C`
there is a level `Q₀` above which every `S`-integral solution of the product inequality
`affineProd ≤ H(x) ^ (-δ)` satisfies the system `(C, c)` for one of them. With 6.4 or
`NumberField.affineProd_le_of_mem_systemSet` in the other direction, the product inequality and
the systems are equivalent. The exponents are the logarithms of the local values over
`log H(x)`, clamped below and rounded up on a grid of mesh `1 / m`. -/
theorem exists_finset_forall_exists_mem_systemSet (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ 𝒞 : Finset (InfinitePlace K ⊕ S → ι → ℝ), (∀ c ∈ 𝒞, systemWeight c ≤ -δ / 2) ∧
      ∀ C : InfinitePlace K ⊕ S → ℝ, (∀ p, 0 < C p) → ∃ Q₀ : ℝ, ∀ x : ι → K,
        (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        affineProd S w L x ≤ mulHeightAff x ^ (-δ) → Q₀ ≤ mulHeightAff x →
        ∃ c ∈ 𝒞, x ∈ systemSet S w L C c := by
  obtain ⟨A, hA1, hA⟩ := exists_systemValue_le_mul_mulHeightAff S w hwInf hwFin L
  set P : ℕ := Fintype.card ((InfinitePlace K ⊕ S) × ι) with hP
  set M : ℝ := 2 * P + δ + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 * P / δ + 1 < m := exists_nat_gt _
  have hPδ : 0 ≤ 4 * (P : ℝ) / δ := by positivity
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hPm : 2 * (P : ℝ) / m ≤ δ / 2 := by
    rw [div_le_iff₀ hm0]
    have := (div_lt_iff₀ hδ).1 (lt_of_le_of_lt (le_add_of_nonneg_right zero_le_one) hm)
    linarith
  set G : Finset ℝ := (Finset.Icc (-⌈M * m⌉) (3 * (m : ℤ))).image fun k : ℤ ↦ (k : ℝ) / m
    with hG
  set 𝒞' : Set (InfinitePlace K ⊕ S → ι → ℝ) :=
    {c | (∀ p i, c p i ∈ G) ∧ systemWeight c ≤ -δ / 2} with h𝒞'
  have h𝒞 : 𝒞'.Finite := by
    refine (Set.Finite.pi (t := fun _ ↦ Set.univ.pi fun _ : ι ↦ (G : Set ℝ))
      fun _ ↦ Set.Finite.pi fun _ ↦ G.finite_toSet).subset fun c hc ↦ ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact hc.1
  refine ⟨h𝒞.toFinset, fun c hc ↦ (h𝒞.mem_toFinset.1 hc).2, fun C hC ↦ ?_⟩
  refine ⟨max 2 (A + ∑ p, (C p)⁻¹ ^ m), fun x hxS happ hQ ↦ ?_⟩
  set Q := mulHeightAff x with hQdef
  have hCi : ∀ p, 0 ≤ (C p)⁻¹ := fun p ↦ inv_nonneg.2 (hC p).le
  have hsum0 : 0 ≤ ∑ p, (C p)⁻¹ ^ m := Finset.sum_nonneg fun p _ ↦ pow_nonneg (hCi p) _
  have hQ1 : 1 < Q := by linarith [le_max_left 2 (A + ∑ p, (C p)⁻¹ ^ m)]
  have hQ0 : 0 < Q := by linarith
  have hQA : A ≤ Q := by linarith [le_max_right 2 (A + ∑ p, (C p)⁻¹ ^ m)]
  have hQC : ∀ p, (C p)⁻¹ ≤ Q ^ ((m : ℝ)⁻¹) := fun p ↦ by
    have h : (C p)⁻¹ ^ m ≤ Q := by
      refine le_trans ?_ (le_trans (le_max_right _ _) hQ)
      refine le_add_of_nonneg_of_le (by linarith) ?_
      exact Finset.single_le_sum (fun p _ ↦ pow_nonneg (hCi p) _) (Finset.mem_univ p)
    have hm' : m ≠ 0 := by rintro rfl; norm_num at hm1
    calc (C p)⁻¹ = ((C p)⁻¹ ^ m) ^ ((m : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (hCi p) hm').symm
      _ ≤ Q ^ ((m : ℝ)⁻¹) := Real.rpow_le_rpow (pow_nonneg (hCi p) _) h (by positivity)
  have hq : 0 < Real.log Q := Real.log_pos hQ1
  set V : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ systemValue S w L p i x with hV
  have hV0 : ∀ p i, 0 ≤ V p i := fun p i ↦ systemValue_nonneg ..
  set t : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦
    if V p i = 0 then -M else max (Real.log (V p i) / Real.log Q) (-M) with ht
  set c : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ ((⌈m * t p i⌉ : ℝ) + 1) / m with hc
  have hlog2 : ∀ p i, V p i ≠ 0 → Real.log (V p i) / Real.log Q ≤ 2 := fun p i h ↦ by
    rw [div_le_iff₀ hq, ← Real.log_rpow hQ0, Real.rpow_two]
    refine Real.log_le_log ((hV0 p i).lt_of_ne' h) ?_
    calc V p i ≤ A * Q := hA p i x
      _ ≤ Q ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hQA hQ0.le
  have ht_ge : ∀ p i, -M ≤ t p i := fun p i ↦ by
    simp only [ht]; split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have ht_le : ∀ p i, t p i ≤ 2 := fun p i ↦ by
    simp only [ht]; split_ifs with h
    · linarith
    · exact max_le (hlog2 p i h) (by linarith)
  have hc_ge : ∀ p i, t p i + 1 / m ≤ c p i := fun p i ↦ by
    simp only [hc]
    rw [le_div_iff₀ hm0, add_mul, one_div_mul_cancel hm0.ne', mul_comm]
    linarith [Int.le_ceil (m * t p i)]
  have hc_le : ∀ p i, c p i ≤ t p i + 2 / m := fun p i ↦ by
    simp only [hc]
    rw [div_le_iff₀ hm0, add_mul, div_mul_cancel₀ _ hm0.ne', mul_comm (t p i)]
    linarith [Int.ceil_lt_add_one (m * t p i)]
  refine ⟨c, h𝒞.mem_toFinset.2 ⟨fun p i ↦ ?_, ?_⟩, hxS, fun p i ↦ ?_⟩
  · -- the exponents lie on the grid
    refine Finset.mem_image.2 ⟨⌈m * t p i⌉ + 1, Finset.mem_Icc.2 ⟨?_, ?_⟩, by push_cast; rfl⟩
    · have h1 := Int.le_ceil (M * m)
      have h2 := Int.le_ceil (m * t p i)
      have h3 : -(M * m) ≤ m * t p i := by nlinarith [ht_ge p i]
      have : ((-⌈M * m⌉ : ℤ) : ℝ) < ((⌈m * t p i⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
    · have h1 : ⌈(m : ℝ) * t p i⌉ ≤ 2 * (m : ℤ) :=
        Int.ceil_le.2 (by push_cast; nlinarith [ht_le p i])
      have h2 : (1 : ℤ) ≤ m := by exact_mod_cast hm1
      linarith
  · -- the weight
    have hsum_t : ∑ q : (InfinitePlace K ⊕ S) × ι, t q.1 q.2 ≤ -δ := by
      by_cases hex : ∃ q : (InfinitePlace K ⊕ S) × ι, t q.1 q.2 = -M
      · obtain ⟨q₀, hq₀⟩ := hex
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q₀), hq₀]
        have h1 : ∑ q ∈ Finset.univ.erase q₀, t q.1 q.2 ≤ (Finset.univ.erase q₀).card • 2 :=
          Finset.sum_le_card_nsmul _ _ _ fun q _ ↦ ht_le q.1 q.2
        have h2 : ((Finset.univ.erase q₀).card : ℝ) ≤ P := by
          exact_mod_cast (Finset.card_erase_le).trans (Finset.card_univ).le
        rw [nsmul_eq_mul] at h1
        linarith
      · push Not at hex
        have hVne : ∀ q : (InfinitePlace K ⊕ S) × ι, V q.1 q.2 ≠ 0 := fun q h ↦
          hex q (by simp only [ht, h, ↓reduceIte])
        have hteq : ∀ q : (InfinitePlace K ⊕ S) × ι,
            t q.1 q.2 = Real.log (V q.1 q.2) / Real.log Q := fun q ↦ by
          have h := hex q
          simp only [ht, hVne q, ↓reduceIte] at h ⊢
          rcases le_total (Real.log (V q.1 q.2) / Real.log Q) (-M) with h' | h'
          · exact absurd (max_eq_right h') h
          · exact max_eq_left h'
        have hprod : affineProd S w L x = ∏ q : (InfinitePlace K ⊕ S) × ι, V q.1 q.2 := by
          rw [affineProd_eq_prod_systemValue, ← Fintype.prod_prod_type']
        have hpos : 0 < affineProd S w L x := by
          rw [hprod]; exact Finset.prod_pos fun q _ ↦ (hV0 q.1 q.2).lt_of_ne' (hVne q)
        have hlog : Real.log (affineProd S w L x) ≤ -δ * Real.log Q := by
          rw [← Real.log_rpow hQ0]; exact Real.log_le_log hpos happ
        rw [Finset.sum_congr rfl fun q _ ↦ hteq q, ← Finset.sum_div, div_le_iff₀ hq,
          ← Real.log_prod fun q _ ↦ hVne q, ← hprod]
        exact hlog
    have hsum_c : systemWeight c ≤ ∑ q : (InfinitePlace K ⊕ S) × ι, t q.1 q.2 + P * (2 / m) := by
      rw [systemWeight, ← Fintype.sum_prod_type', hP, ← Finset.card_univ, ← nsmul_eq_mul,
        ← Finset.sum_const, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun q _ ↦ hc_le q.1 q.2
    have : (P : ℝ) * (2 / m) = 2 * P / m := by ring
    linarith
  · -- the inequalities of the system
    change V p i ≤ C p * Q ^ c p i
    rcases eq_or_ne (V p i) 0 with h | h
    · rw [h]; exact mul_nonneg (hC p).le (Real.rpow_nonneg hQ0.le _)
    have hVpos : 0 < V p i := (hV0 p i).lt_of_ne' h
    have hte : Real.log (V p i) / Real.log Q ≤ t p i := by
      simp only [ht, h, ↓reduceIte]; exact le_max_left _ _
    have h1 : 1 ≤ C p * Q ^ ((m : ℝ)⁻¹) := by
      rw [← mul_inv_cancel₀ (hC p).ne']
      exact mul_le_mul_of_nonneg_left (hQC p) (hC p).le
    calc V p i ≤ (C p * Q ^ ((m : ℝ)⁻¹)) * V p i := le_mul_of_one_le_left hVpos.le h1
      _ = C p * Q ^ (Real.log (V p i) / Real.log Q + 1 / m) := by
          rw [Real.rpow_add hQ0, rpow_div_log_eq hQ1 hVpos, one_div]; ring
      _ ≤ C p * Q ^ c p i := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith [hc_ge p i])) (hC p).le

/-!
### Acceptance criteria

Over `ℚ` with `S = ∅`: Evertse's normalization is satisfiable, by the coordinate forms of `ℚ²`
with exponents `(1, -2)`; that system has infinitely many solutions, all on one line, so Theorem A
is not about finiteness; for `n = 1` Theorem A fails, so `[Nontrivial ι]` is load-bearing; and
with `S = {2}` a system of weight `0` has the solutions `(2 ^ k, 1)`, no two on a proper subspace,
so the strict inequality is load-bearing.
-/

section Tests

/-- The coordinate forms of `ℚⁿ`, the same at every place. -/
private noncomputable def coordForms (n : ℕ) : AbsoluteValue ℚ ℝ → Fin n → Dual ℚ (Fin n → ℚ) :=
  fun _ i ↦ LinearMap.proj i

/-- The exponents `(1, -2)` at every place. -/
private def coordExps : InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) → Fin 2 → ℝ :=
  fun _ ↦ ![1, -2]

private theorem mult_rat (v : InfinitePlace ℚ) : v.mult = 1 := by
  rw [Subsingleton.elim v Rat.infinitePlace]; exact Rat.isReal_infinitePlace.mult_eq_one

private theorem notMem_empty' (v : ↥(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) : False :=
  Finset.notMem_empty _ v.2

/-- **Acceptance test.** Evertse's normalization (2.4) is satisfiable: the coordinate forms of
`ℚ²` with constants `1` and exponents `(1, -2)` satisfy it with `H = 1`, `D = 1`, `R = 2` and
`δ = 1`. -/
private theorem coord_isNormalized :
    IsNormalizedSystem (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun v ↦ v) (coordForms 2)
      (fun _ ↦ 1) coordExps 1 1 2 1 where
  height_le p i j := by
    have h : Pi.single (M := fun _ ↦ ℚ) j 1 i = 0 ∨ Pi.single (M := fun _ ↦ ℚ) j 1 i = 1 := by
      rw [Pi.single_apply]; split_ifs <;> simp
    simp only [coordForms, LinearMap.proj_apply, Pi.basisFun_apply]
    rcases h with h | h <;> rw [h]
    · rw [absMulHeight₁_zero]
    · rw [absMulHeight₁_one]
  degree_le p i j := by rw [minpoly.eq_X_sub_C']; simp
  ncard_le := by
    classical
    have hsub : (Set.range fun q : (InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) ×
        Fin 2 ↦ coordForms 2 (systemPlace ∅ q.1) q.2) ⊆
        ((Finset.univ.image fun i : Fin 2 ↦ (LinearMap.proj i : Dual ℚ (Fin 2 → ℚ))) :
          Set (Dual ℚ (Fin 2 → ℚ))) := by
      rintro _ ⟨q, rfl⟩
      simp [coordForms]
    refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le.trans (by simp)
  const_pos _ := one_pos
  const_le := by
    have hdet : systemDet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun v ↦ v) (coordForms 2) = 1 :=
      Finset.prod_eq_one fun p _ ↦ by
        change systemPlace ∅ p (LinearMap.det (LinearMap.pi fun i : Fin 2 ↦
          (LinearMap.proj i : (Fin 2 → ℚ) →ₗ[ℚ] ℚ))) ^ _ = 1
        rw [LinearMap.pi_proj, LinearMap.det_id, map_one, one_pow]
    rw [hdet, Real.one_rpow]
    exact (Finset.prod_const_one).le
  delta_pos := one_pos
  delta_le_one := le_rfl
  weight_le := by
    have hcard : (1 : ℝ) ≤ Fintype.card
        (InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) := by
      exact_mod_cast Fintype.card_pos
    simp only [systemWeight, coordExps, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  exponent_le p i := by
    rcases p with v | v
    · simp only [systemExponent, mult_rat, Module.finrank_self]
      fin_cases i <;> norm_num [coordExps]
    · exact (notMem_empty' v).elim
  exists_exponent_eq p := by
    rcases p with v | v
    · exact ⟨0, by simp [systemExponent, coordExps]⟩
    · exact (notMem_empty' v).elim

/-- **Acceptance test.** The normalized system above has the infinitely many solutions `(k, 0)`,
`k ∈ ℤ` — every one on the line `x₂ = 0`, as Theorem A says. -/
example (k : ℤ) : ![(k : ℚ), 0] ∈ systemSet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (fun v ↦ v) (coordForms 2) (fun _ ↦ 1) coordExps := by
  refine ⟨fun j ↦ ?_, fun p i ↦ ?_⟩
  · fin_cases j
    · exact intCast_mem _ k
    · exact zero_mem _
  rcases p with v | v
  · fin_cases i
    · have h := systemPlace_pow_le_mulHeightAff (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
        (.inl v) ![(k : ℚ), 0] 0
      simpa [systemValue, systemAbs, systemMult, systemPlace, coordForms, coordExps] using h
    · simp only [systemValue, systemAbs, coordForms, LinearMap.proj_apply]
      simp [systemMult, Real.rpow_nonneg (mulHeightAff_pos _).le]
  · exact (notMem_empty' v).elim

/-- **Rejection test.** For `n = 1` Theorem A is false: the system `|x| ≤ H(x) ^ (-1)` over `ℚ`
has weight `-1` and the nonzero solution `1`, which lies in no proper subspace of `ℚ¹`. So
`[Nontrivial ι]` in `NumberField.exists_finset_submodule_of_systemWeight_neg` is load-bearing. -/
example : systemWeight (fun _ _ ↦ -1 :
      InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) → Fin 1 → ℝ) < 0 ∧
    ¬ ∃ T : Finset (Submodule ℚ (Fin 1 → ℚ)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x ∈ systemSet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun v ↦ v) (coordForms 1)
        (fun _ ↦ 1) (fun _ _ ↦ -1), x ≠ 0 → ∃ W ∈ T, x ∈ W := by
  refine ⟨?_, ?_⟩
  · have hcard : (1 : ℝ) ≤ Fintype.card
        (InfinitePlace ℚ ⊕ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) := by
      exact_mod_cast Fintype.card_pos
    simp only [systemWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
      nsmul_eq_mul]
    linarith
  rintro ⟨T, hT, hcov⟩
  have h1 : (1 : Fin 1 → ℚ) = ![1] := by ext i; fin_cases i; rfl
  have hmem : (1 : Fin 1 → ℚ) ∈ systemSet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun v ↦ v)
      (coordForms 1) (fun _ ↦ 1) (fun _ _ ↦ -1) := by
    refine ⟨fun j ↦ one_mem _, fun p i ↦ ?_⟩
    rw [h1, mulHeightAff_fin_one, mulHeight₁_one, Real.one_rpow, mul_one]
    simp [systemValue, systemAbs, coordForms]
  obtain ⟨W, hW, h1W⟩ := hcov 1 hmem one_ne_zero
  refine hT W hW (eq_top_iff.2 fun y _ ↦ ?_)
  have : y = y 0 • (1 : Fin 1 → ℚ) := by ext i; fin_cases i; simp
  rw [this]
  exact W.smul_mem _ h1W

/-- The prime `2`. -/
private def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `2` of `𝓞 ℚ`. -/
private noncomputable def primeTwo : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.finitePlace twoPrime).maximalIdeal

private theorem mk_primeTwo_two : FinitePlace.mk primeTwo 2 = 1 / 2 := by
  rw [primeTwo, FinitePlace.mk_maximalIdeal, Rat.finitePlace_apply]
  have : padicNorm 2 (2 : ℚ) = 2⁻¹ := by exact_mod_cast padicNorm.padicNorm_p one_lt_two
  change ((padicNorm 2 (2 : ℚ) : ℚ) : ℝ) = 1 / 2
  rw [this]
  norm_num

/-- The exponents `(1, 0)` at the infinite place and `(-1, 0)` at `2`: weight `0`. -/
private def twoExps : InfinitePlace ℚ ⊕ ({primeTwo} : Finset (HeightOneSpectrum (𝓞 ℚ))) →
    Fin 2 → ℝ
  | .inl _ => ![1, 0]
  | .inr _ => ![-1, 0]

/-- The affine height of `(2 ^ k, 1)` is at most `2 ^ k`. -/
private theorem mulHeightAff_two_pow_le (k : ℕ) :
    mulHeightAff ![(2 : ℚ) ^ k, 1] ≤ 2 ^ k := by
  set y : Option (Fin 2) → ℤ := fun o ↦ o.elim 1 ![2 ^ k, 1] with hy
  have hgcd : Finset.univ.gcd y = 1 := by
    have h : Finset.univ.gcd y ∣ 1 := Finset.gcd_dvd (Finset.mem_univ none)
    rcases Int.isUnit_iff.1 (isUnit_of_dvd_one h) with h1 | h1
    · exact h1
    · have h2 := Finset.normalize_gcd (s := Finset.univ) (f := y)
      rw [h1, Int.normalize_of_nonpos (by norm_num)] at h2
      norm_num at h2
  have hcomp : (fun o : Option (Fin 2) ↦ o.elim 1 ![(2 : ℚ) ^ k, 1]) = ((↑) : ℤ → ℚ) ∘ y := by
    ext o; rcases o with _ | i
    · simp [hy]
    · fin_cases i <;> simp [hy]
  rw [mulHeightAff, hcomp, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd]
  have : (⨆ o, |y o|) ≤ 2 ^ k := ciSup_le fun o ↦ by
    rcases o with _ | i
    · simp [hy, one_le_pow₀ (one_le_two : (1 : ℤ) ≤ 2)]
    · fin_cases i
      · simp [hy]
      · simp [hy, one_le_pow₀ (one_le_two : (1 : ℤ) ≤ 2)]
  exact_mod_cast this

/-- **Rejection test.** A strict weight is needed in Theorem A: over `ℚ` with `S = {2}`, the
coordinate forms with exponents `(1, 0)` at `∞` and `(-1, 0)` at `2` have weight `0`, and the
points `(2 ^ k, 1)` all solve the system, but no proper subspace of `ℚ²` contains two of them. -/
example : systemWeight twoExps = 0 ∧
    ¬ ∃ T : Finset (Submodule ℚ (Fin 2 → ℚ)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x ∈ systemSet {primeTwo} (fun v ↦ v) (coordForms 2) (fun _ ↦ 1) twoExps, x ≠ 0 →
        ∃ W ∈ T, x ∈ W := by
  refine ⟨?_, ?_⟩
  · simp only [systemWeight, Fintype.sum_sum_type, twoExps, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_unique, one_smul]
    norm_num
  rintro ⟨T, hT, hcov⟩
  set x : ℕ → Fin 2 → ℚ := fun k ↦ ![(2 : ℚ) ^ k, 1] with hx
  have hmem : ∀ k, x k ∈ systemSet {primeTwo} (fun v ↦ v) (coordForms 2) (fun _ ↦ 1) twoExps := by
    intro k
    refine ⟨fun j ↦ ?_, fun p i ↦ ?_⟩
    · fin_cases j
      · have h2 : ((2 : ℤ) : ℚ) ∈ ((({primeTwo} : Finset (HeightOneSpectrum (𝓞 ℚ))) :
            Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) := intCast_mem _ 2
        rw [Int.cast_ofNat] at h2
        exact pow_mem h2 k
      · exact one_mem _
    have hH1 := one_le_mulHeightAff (x k)
    rcases p with v | v
    · fin_cases i
      · have h := systemPlace_pow_le_mulHeightAff {primeTwo} (.inl v) (x k) 0
        simpa [systemValue, systemAbs, systemMult, systemPlace, coordForms, twoExps] using h
      · simp [systemValue, systemAbs, systemMult, systemPlace, coordForms, twoExps, hx]
    · obtain ⟨P, hP⟩ := v
      obtain rfl : P = primeTwo := Finset.mem_singleton.1 hP
      fin_cases i
      · simp only [systemValue, systemAbs, systemMult, systemPlace, coordForms, twoExps, hx,
          LinearMap.proj_apply, pow_one, one_mul]
        change FinitePlace.mk primeTwo (algebraMap ℚ ℚ (2 ^ k)) ≤ mulHeightAff (x k) ^ (-1 : ℝ)
        rw [Algebra.algebraMap_self, RingHom.id_apply, map_pow, mk_primeTwo_two,
          Real.rpow_neg_one, one_div, inv_pow]
        exact inv_anti₀ (by positivity) (mulHeightAff_two_pow_le k)
      · simp [systemValue, systemAbs, systemMult, systemPlace, coordForms, twoExps, hx]
  have hx0 : ∀ k, x k ≠ 0 := fun k h ↦ by simpa [hx] using congrFun h 1
  choose W hW hxW using fun k ↦ hcov (x k) (hmem k) (hx0 k)
  obtain ⟨k, j, hkj, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ ↦ (⟨W k, hW k⟩ : T))
  have hWj : W j = W k := congrArg Subtype.val heq.symm
  have hxj : x j ∈ W k := hWj ▸ hxW j
  have hne : (2 : ℚ) ^ k - 2 ^ j ≠ 0 := sub_ne_zero.2 fun h ↦
    hkj (Nat.pow_right_injective le_rfl (by exact_mod_cast h))
  have he0 : (![1, 0] : Fin 2 → ℚ) ∈ W k := by
    have : ![1, 0] = ((2 : ℚ) ^ k - 2 ^ j)⁻¹ • (x k - x j) := by
      ext i; fin_cases i <;> simp [hx, inv_mul_cancel₀ hne]
    rw [this]; exact (W k).smul_mem _ ((W k).sub_mem (hxW k) hxj)
  have he1 : (![0, 1] : Fin 2 → ℚ) ∈ W k := by
    have : ![0, 1] = x k - (2 : ℚ) ^ k • ![1, 0] := by ext i; fin_cases i <;> simp [hx]
    rw [this]; exact (W k).sub_mem (hxW k) ((W k).smul_mem _ he0)
  refine hT (W k) (hW k) (eq_top_iff.2 fun y _ ↦ ?_)
  have : y = y 0 • ![1, 0] + y 1 • ![0, 1] := by ext i; fin_cases i <;> simp
  rw [this]
  exact (W k).add_mem ((W k).smul_mem _ he0) ((W k).smul_mem _ he1)

end Tests

end NumberField
