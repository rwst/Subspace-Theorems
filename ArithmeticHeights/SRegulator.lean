/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnitTheorem
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The `S`-logarithmic embedding and the `S`-regulator

Let `K` be a number field and `S` a finite set of finite places, carried as a `Finset` of
height-one primes of `𝓞 K`. The `S`-logarithmic embedding sends an `S`-unit `x` to its vector of
local logarithms

```text
(mult w · log (w x))_{w | ∞, w ≠ w₀}   together with   (log |x|_v)_{v ∈ S},
```

one coordinate for every infinite place except the distinguished one `w₀` and one for every place
of `S`. The coordinate at `w₀` is not lost: the product formula for `S`-units says the full vector
sums to zero, so it is minus the sum of the ones that are kept. This file proves that the image is
a full `ℤ`-lattice in `ℝ^{r₁ + r₂ - 1 + |S|}`, and defines the `S`-regulator as its covolume, so
that `S = ∅` gives back `NumberField.Units.regulator`.

The two halves of "full lattice" are the two halves of Layer 6.1 read for `S`-units.
*Discreteness* is Northcott's theorem: by Layer 6.4 the height of an `S`-unit is carried by the
infinite places and `S`, so a bounded embedding means a bounded height, and there are finitely
many elements of `K` of bounded height. *Spanning* is Mathlib's `unitLattice_span_eq_top` for the
infinite coordinates together with, for each place of `S`, the `S`-unit produced from the class
group in `ArithmeticHeights/SUnitTheorem.lean`.

## Main results

* `NumberField.SUnit.logEmbedding`: the `S`-logarithmic embedding, with
  `NumberField.SUnit.logEmbedding_unitOfUnits` saying that on a unit of `𝓞 K` it is Dirichlet's.
* `NumberField.SUnit.sum_mult_mul_log_add_sum_log`: the product formula for an `S`-unit, and
  `NumberField.SUnit.sum_logEmbedding_eq`, the coordinate the embedding drops.
* `NumberField.SUnit.two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum`: **the `S`-analogue
  of Layer 6.1**, an identity and not an inequality, with the two-sided comparison
  `NumberField.SUnit.sum_abs_logEmbedding_le_two_mul_logHeight₁`,
  `NumberField.SUnit.logHeight₁_le_sum_abs_logEmbedding` and their supremum-norm forms beside it.
* `NumberField.SUnit.unitLattice`, `NumberField.SUnit.unitLattice_inter_ball_finite` and
  `NumberField.SUnit.unitLattice_span_eq_top`: the `S`-unit lattice is discrete and spans, so it
  is a full `ℤ`-lattice; `NumberField.SUnit.finrank_unitLattice` reads off its rank.
* `NumberField.SUnit.regulator`: **the `S`-regulator**, with `NumberField.SUnit.regulator_pos` and
  `NumberField.SUnit.regulator_empty`, which is `NumberField.Units.regulator`.

## Implementation notes

⚠ **The product formula is where the `S`-unit hypothesis becomes load-bearing.** Layer 6.4 found
that the height display needs only the `S`-integer condition `|x|_v ≤ 1` away from `S`. The
additive identity `NumberField.SUnit.sum_mult_mul_log_add_sum_log` needs `|x|_v = 1` there, since
the places outside `S` have to contribute `0` and not merely something non-positive. The rejection
test at the end of the file runs `x = 2` with `S = ∅`, an `∅`-integer that is not an `∅`-unit, and
the sum comes out `[K : ℚ] · log 2`.

⚠ **Discreteness is Northcott's theorem, and nothing else.** Mathlib proves the discreteness of
its unit lattice from `NumberField.Embeddings.finite_of_norm_le`, by hand. Layer 6.1 recorded as
an acceptance criterion that this discreteness *is* Northcott's theorem seen through the height,
and deliberately did not use it as a proof because Mathlib already had one. For `S`-units Mathlib
has nothing, and that reading becomes the proof: `NumberField.SUnit.logHeight₁_le_card_mul_norm_
logEmbedding` turns a bounded embedding into a bounded height and
`NumberField.finite_setOfPred_logHeight₁_le` finishes.

⚠ **The spanning half needs no second Dirichlet argument.** The hard half of Dirichlet's theorem
enters once, as Mathlib's `unitLattice_span_eq_top`, and covers the infinite coordinates; the
coordinates over `S` are covered by `Set.exists_mem_unit_finitePlace`, one `S`-unit per place of
`S`, which comes from the finiteness of the class group. So the two inputs of Layer 6.5 —
Dirichlet's theorem and the class number — are consumed once each here, exactly as they are in the
rank computation of `ArithmeticHeights/SUnitTheorem.lean`.

⚠ **The rank of the lattice is computed a second time here, and the agreement is a real check.**
`NumberField.SUnit.finrank_unitLattice` gets `r₁ + r₂ - 1 + |S|` as the real dimension of the
space the lattice fills, by `ZLattice.rank`; `Set.unit_finrank_numberField` gets the same number
from the class group and Dirichlet's theorem, with no analysis in sight. Neither proof uses the
other, and the acceptance criteria check that they agree.

⚠ **`S = ∅` recovers `NumberField.Units.regulator`, but not definitionally.** The roadmap asks
for a definitional recovery and there is none to be had: the index type of the `S`-logarithmic
space is `{w // w ≠ w₀} ⊕ ↥S`, and `α ⊕ Empty` is not `α`. Any indexing that keeps the two kinds
of place apart — which the display of Layer 6.4 forces — has the same obstruction.
`NumberField.SUnit.regulator_empty` is therefore a theorem, proved by transporting the covolume
along the measure-preserving linear equivalence `NumberField.SUnit.emptyEquiv` with Mathlib's
`ZLattice.covolume_comap`.

⚠ **The embedding is defined on `Kˣ` and then restricted.** `NumberField.SUnit.logHom` is the map
on all of `Kˣ`; `NumberField.SUnit.logEmbedding` is its composite with the inclusion of the
`S`-units. Defining it directly on the subgroup makes the additivity proof carry the subgroup
coercion through every rewrite, and the elaborator times out on it.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.5.13 and §1.5.10.

This is Layer 6.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Height IsDedekindDomain MeasureTheory Module NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem Real

namespace NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

/-- The `S`-logarithmic space: one real coordinate for every infinite place except the
distinguished one, and one for every place of `S`. -/
abbrev logSpace : Type _ := ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S) → ℝ

/-- The `S`-logarithmic coordinates of a nonzero element of `K`. -/
@[expose] noncomputable def logHom : Additive Kˣ →+ logSpace S :=
  AddMonoidHom.mk'
    (fun x => Sum.elim (fun w => (w.1.mult : ℝ) * Real.log (w.1 ((x.toMul : Kˣ) : K)))
      (fun v => Real.log (FinitePlace.mk v.1 ((x.toMul : Kˣ) : K))))
    (fun x y => by
      have hx : (x.toMul : Kˣ).val ≠ 0 := Units.ne_zero _
      have hy : (y.toMul : Kˣ).val ≠ 0 := Units.ne_zero _
      funext i
      cases i with
      | inl w =>
        simp only [Sum.elim_inl, Pi.add_apply]
        rw [show ((x + y).toMul : Kˣ) = (x.toMul : Kˣ) * (y.toMul : Kˣ) from rfl,
          Units.val_mul, map_mul,
          Real.log_mul (InfinitePlace.pos_iff.mpr hx).ne' (InfinitePlace.pos_iff.mpr hy).ne',
          mul_add]
      | inr v =>
        simp only [Sum.elim_inr, Pi.add_apply]
        rw [show ((x + y).toMul : Kˣ) = (x.toMul : Kˣ) * (y.toMul : Kˣ) from rfl,
          Units.val_mul, map_mul,
          Real.log_mul (FinitePlace.pos_iff.mpr hx).ne' (FinitePlace.pos_iff.mpr hy).ne'])

/-- **The `S`-logarithmic embedding of the `S`-units.** -/
@[expose] noncomputable def logEmbedding :
    Additive ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K) →+ logSpace S :=
  (logHom S).comp
    (MonoidHom.toAdditive ((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K).subtype)

variable {S}

@[simp]
theorem logEmbedding_apply_inl
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K))
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    logEmbedding S (Additive.ofMul x) (Sum.inl w)
      = (w.1.mult : ℝ) * Real.log (w.1 ((x : Kˣ) : K)) := rfl

@[simp]
theorem logEmbedding_apply_inr
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K))
    (v : ↥S) :
    logEmbedding S (Additive.ofMul x) (Sum.inr v)
      = Real.log (FinitePlace.mk v.1 ((x : Kˣ) : K)) := rfl

/-- **On a unit of `𝓞 K` the `S`-logarithmic embedding is Dirichlet's**, extended by zero over
the places of `S`. -/
theorem logEmbedding_unitOfUnits (u : (𝓞 K)ˣ) :
    logEmbedding S
        (Additive.ofMul ((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits u))
      = Sum.elim (Units.logEmbedding K (Additive.ofMul u)) 0 := by
  funext i
  cases i with
  | inl w =>
    rw [logEmbedding_apply_inl, Sum.elim_inl,
      Units.dirichletUnitTheorem.logEmbedding_component]
    rfl
  | inr v =>
    rw [logEmbedding_apply_inr, Sum.elim_inr, Pi.zero_apply,
      show FinitePlace.mk v.1
          (((((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits u) :
            ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) : Kˣ) : K)
        = FinitePlace.mk v.1 ((u : 𝓞 K) : K) from rfl,
      NumberField.FinitePlace.apply_units_eq_one _ u, Real.log_one]

/-!
### The product formula for `S`-units
-/

/-- **The finite part of the product formula, for an `S`-unit**, is a product over `S` alone.
This is where the `S`-unit hypothesis is used and the `S`-integer hypothesis of Layer 6.4 would
not do: the factor at a place outside `S` has to be `1`, not merely at most `1`. -/
theorem finprod_apply_eq_prod
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    ∏ᶠ w : FinitePlace K, w ((x : Kˣ) : K)
      = ∏ v ∈ S, FinitePlace.mk v ((x : Kˣ) : K) := by
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  rw [← finprod_mem_univ, finprod_mem_inter_mulSupport_eq' _ Set.univ
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) ?_, finprod_mem_coe_finset]
  intro v hv
  simp only [Set.mem_univ, true_iff]
  by_contra hvS
  exact hv ((FinitePlace.mk_apply_eq_one_iff v _).mpr (x.2 v hvS))

/-- **The product formula for an `S`-unit.** The weighted logarithms over the infinite places and
the logarithms over the places of `S` sum to zero: every other place contributes `1`. -/
theorem sum_mult_mul_log_add_sum_log
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((x : Kˣ) : K)))
      + ∑ v ∈ S, Real.log (FinitePlace.mk v ((x : Kˣ) : K)) = 0 := by
  have hx : (((x : Kˣ) : K)) ≠ 0 := Units.ne_zero _
  have key := NumberField.prod_abs_eq_one hx
  rw [finprod_apply_eq_prod x] at key
  have h1 : (∏ w : InfinitePlace K, w ((x : Kˣ) : K) ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.mpr hx).ne'
  have h2 : (∏ v ∈ S, FinitePlace.mk v ((x : Kˣ) : K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => (FinitePlace.pos_iff.mpr hx).ne'
  have hlog := congrArg Real.log key
  rw [Real.log_mul h1 h2, Real.log_one,
    Real.log_prod (fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.mpr hx).ne'),
    Real.log_prod (fun v _ => (FinitePlace.pos_iff.mpr hx).ne')] at hlog
  simpa only [Real.log_pow] using hlog

/-!
### The height of an `S`-unit in the coordinates of the `S`-logarithmic embedding
-/

/-- The height of an `S`-unit as a sum over the infinite places and the places of `S`, Layer
6.4's display in the `Finset` form this layer uses. -/
theorem logHeight₁_eq_sum (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    logHeight₁ ((x : Kˣ) : K)
      = (∑ w : InfinitePlace K, (w.mult : ℝ) * log⁺ (w ((x : Kˣ) : K)))
        + ∑ v ∈ S, log⁺ (FinitePlace.mk v ((x : Kˣ) : K)) := by
  rw [NumberField.logHeight₁_eq_of_mem_integer _ (Set.mem_integer_of_mem_unit x.2),
    finsum_mem_coe_finset]

/-- A nonnegative weight may be moved inside a positive part. -/
private theorem mul_posLog_eq_posPart {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    c * log⁺ t = (c * Real.log t)⁺ := by
  rw [posLog_apply, posPart_def, mul_max_of_nonneg _ _ hc, mul_zero, max_comm]

/-- `2 * a⁺ = |a| + a`. -/
private theorem two_mul_posPart (a : ℝ) : 2 * a⁺ = |a| + a := by
  rw [posPart_def]
  rcases le_total 0 a with h | h
  · rw [sup_eq_left.mpr h, abs_of_nonneg h]; ring
  · rw [sup_eq_right.mpr h, abs_of_nonpos h]; ring

/-- **Twice the height of an `S`-unit is the ℓ¹ norm of its vector of local logarithms**, taken
over *all* the infinite places and the places of `S`. The positive parts alone give the height,
and the product formula says the vector sums to `0`, so the negative parts repeat them. -/
theorem two_mul_logHeight₁_eq_sum_abs
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    2 * logHeight₁ ((x : Kˣ) : K)
      = (∑ w : InfinitePlace K, |(w.mult : ℝ) * Real.log (w ((x : Kˣ) : K))|)
        + ∑ v ∈ S, |Real.log (FinitePlace.mk v ((x : Kˣ) : K))| := by
  have hinf : ∀ w : InfinitePlace K,
      2 * ((w.mult : ℝ) * log⁺ (w ((x : Kˣ) : K)))
        = |(w.mult : ℝ) * Real.log (w ((x : Kˣ) : K))|
          + (w.mult : ℝ) * Real.log (w ((x : Kˣ) : K)) := fun w => by
    rw [mul_posLog_eq_posPart (Nat.cast_nonneg w.mult), two_mul_posPart]
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      2 * log⁺ (FinitePlace.mk v ((x : Kˣ) : K))
        = |Real.log (FinitePlace.mk v ((x : Kˣ) : K))|
          + Real.log (FinitePlace.mk v ((x : Kˣ) : K)) := fun v => by
    rw [show log⁺ (FinitePlace.mk v ((x : Kˣ) : K))
        = 1 * log⁺ (FinitePlace.mk v ((x : Kˣ) : K)) from (one_mul _).symm,
      mul_posLog_eq_posPart zero_le_one, two_mul_posPart, one_mul]
  rw [logHeight₁_eq_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_congr rfl fun w _ => hinf w, Finset.sum_congr rfl fun v _ => hfin v,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hzero := sum_mult_mul_log_add_sum_log x
  linarith

/-!
### The `S`-analogue of Layer 6.1

The embedding drops the coordinate at the distinguished infinite place `w₀`; by the product
formula above that coordinate is minus the sum of the ones it keeps, which is how it re-enters
every statement below.
-/

open scoped Classical in
/-- The coordinate the `S`-logarithmic embedding drops, recovered from the ones it keeps. This is
the `S`-analogue of Mathlib's `sum_logEmbedding_component`. -/
theorem sum_logEmbedding_eq
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    ∑ i, logEmbedding S (Additive.ofMul x) i
      = -((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ ((x : Kˣ) : K)) := by
  rw [Fintype.sum_sum_type]
  simp only [logEmbedding_apply_inl, logEmbedding_apply_inr]
  rw [Finset.sum_coe_sort S (fun v => Real.log (FinitePlace.mk v ((x : Kˣ) : K)))]
  have h := sum_mult_mul_log_add_sum_log x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)] at h
  linarith

open scoped Classical in
/-- **Twice the height of an `S`-unit, through the `S`-logarithmic embedding.** The ℓ¹ norm of the
coordinates the embedding keeps, plus the absolute value of their sum — which is the size of the
coordinate it drops. This is the `S`-analogue of Layer 6.1's
`NumberField.Units.two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum`. -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    2 * logHeight₁ ((x : Kˣ) : K)
      = (∑ i, |logEmbedding S (Additive.ofMul x) i|)
        + |∑ i, logEmbedding S (Additive.ofMul x) i| := by
  rw [two_mul_logHeight₁_eq_sum_abs, Fintype.sum_sum_type]
  simp only [logEmbedding_apply_inl, logEmbedding_apply_inr]
  rw [Finset.sum_coe_sort S (fun v => |Real.log (FinitePlace.mk v ((x : Kˣ) : K))|),
    sum_logEmbedding_eq, neg_mul, abs_neg,
    Fintype.sum_eq_add_sum_subtype_ne
      (fun w : InfinitePlace K => |(w.mult : ℝ) * Real.log (w ((x : Kˣ) : K))|)
      (w₀ : InfinitePlace K)]
  ring

open scoped Classical in
/-- Half of the two-sided comparison: the ℓ¹ norm of the `S`-logarithmic embedding is at most
twice the height. -/
theorem sum_abs_logEmbedding_le_two_mul_logHeight₁
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    (∑ i, |logEmbedding S (Additive.ofMul x) i|) ≤ 2 * logHeight₁ ((x : Kˣ) : K) := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum]
  linarith [abs_nonneg (∑ i, logEmbedding S (Additive.ofMul x) i)]

open scoped Classical in
/-- The other half: the height is at most the ℓ¹ norm of the `S`-logarithmic embedding, the
dropped coordinate being bounded by the triangle inequality against the ones that are kept. -/
theorem logHeight₁_le_sum_abs_logEmbedding
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    logHeight₁ ((x : Kˣ) : K) ≤ ∑ i, |logEmbedding S (Additive.ofMul x) i| := by
  have htri := Finset.abs_sum_le_sum_abs
    (fun i => logEmbedding S (Additive.ofMul x) i) Finset.univ
  have h := two_mul_logHeight₁_eq_sum_abs_logEmbedding_add_abs_sum x
  linarith

open scoped Classical in
/-- The supremum norm of the `S`-logarithmic embedding — the norm of `SUnit.logSpace S` as a `Pi`
type, and the one whose balls the discreteness statement uses — is at most twice the height. -/
theorem norm_logEmbedding_le_two_mul_logHeight₁
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    ‖logEmbedding S (Additive.ofMul x)‖ ≤ 2 * logHeight₁ ((x : Kˣ) : K) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine le_trans ?_ (sum_abs_logEmbedding_le_two_mul_logHeight₁ x)
  exact Finset.single_le_sum (f := fun i => |logEmbedding S (Additive.ofMul x) i|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ i)

open scoped Classical in
/-- Conversely the height is at most the number of coordinates times the supremum norm. -/
theorem logHeight₁_le_card_mul_norm_logEmbedding
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    logHeight₁ ((x : Kˣ) : K)
      ≤ (Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S) : ℝ)
          * ‖logEmbedding S (Additive.ofMul x)‖ := by
  refine (logHeight₁_le_sum_abs_logEmbedding x).trans ?_
  have h := Finset.sum_le_card_nsmul
    (Finset.univ : Finset ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S))
    (fun i => |logEmbedding S (Additive.ofMul x) i|) ‖logEmbedding S (Additive.ofMul x)‖
    fun i _ => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (logEmbedding S (Additive.ofMul x)) i
  rwa [Finset.card_univ, nsmul_eq_mul] at h

/-!
### The `S`-unit lattice
-/

/-- **The `S`-unit lattice**, the image of the `S`-logarithmic embedding. -/
noncomputable def unitLattice (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Submodule ℤ (logSpace S) :=
  Submodule.map (logEmbedding S).toIntLinearMap ⊤

/-- Membership in the `S`-unit lattice: being the `S`-logarithmic embedding of an `S`-unit. -/
theorem mem_unitLattice_iff {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    {z : logSpace S} : z ∈ unitLattice S ↔ ∃ x, logEmbedding S x = z := by
  rw [unitLattice, Submodule.map_top]
  rfl

/-- **A set of `S`-units of bounded height is finite**, by Northcott's theorem restricted along
the injection of the `S`-units into `K`. -/
theorem finite_setOf_logHeight₁_le (B : ℝ) :
    {x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K) |
      logHeight₁ ((x : Kˣ) : K) ≤ B}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K) =>
      ((x : Kˣ) : K)) ?_ ?_
  · exact (NumberField.finite_setOfPred_logHeight₁_le K B).subset
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  · exact Set.injOn_of_injective fun a b h => Subtype.ext (Units.ext h)

open scoped Classical in
/-- **The `S`-unit lattice meets every ball in a finite set**, which is its discreteness. This is
Northcott's theorem seen through the comparison above, and it is the `S`-analogue of Mathlib's
`unitLattice_inter_ball_finite`. -/
theorem unitLattice_inter_ball_finite (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r : ℝ) :
    ((unitLattice S : Set (logSpace S)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_ge r 0
  · convert! Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  refine ((finite_setOf_logHeight₁_le
    ((Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S) : ℝ) * r)).image
      (fun x => logEmbedding S (Additive.ofMul x))).subset ?_
  rintro z ⟨⟨y, -, rfl⟩, hz⟩
  refine ⟨Additive.toMul y, ?_, rfl⟩
  refine (logHeight₁_le_card_mul_norm_logEmbedding (Additive.toMul y)).trans ?_
  have hnorm : ‖logEmbedding S (Additive.ofMul (Additive.toMul y))‖ ≤ r :=
    mem_closedBall_zero_iff.mp hz
  have hcard : (0 : ℝ) ≤ (Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S) : ℝ) :=
    Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left hnorm hcard

open scoped Classical in
instance instDiscrete_unitLattice
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    DiscreteTopology (unitLattice S) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert! unitLattice_inter_ball_finite S 1
    ext z
    refine ⟨?_, fun ⟨h1, h2⟩ => ⟨⟨z, h1⟩, h2, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact ⟨Subtype.mem y, hy⟩

/-!
### The `S`-unit lattice spans

The image of Dirichlet's unit lattice spans the infinite coordinates, and the generator supplied
by `Set.exists_unitValuation_apply_ne_zero` at each place of `S` supplies the remaining ones.
-/

/-- Dirichlet's logarithmic space inside the `S`-logarithmic space, by zero over `S`. -/
@[expose] def inlₗ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) →ₗ[ℝ] logSpace S where
  toFun a := Sum.elim a 0
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

/-- The coordinates over `S` inside the `S`-logarithmic space, by zero over the infinite
places. -/
@[expose] def inrₗ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (↥S → ℝ) →ₗ[ℝ] logSpace S where
  toFun b := Sum.elim 0 b
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

private theorem inlₗ_mem_span (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (a : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    inlₗ S a ∈ Submodule.span ℝ (unitLattice S : Set (logSpace S)) := by
  have hmap : (inlₗ S) '' (Units.unitLattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ))
      ⊆ (unitLattice S : Set (logSpace S)) := by
    rintro _ ⟨z, ⟨u, -, rfl⟩, rfl⟩
    refine ⟨Additive.ofMul
        ((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits (Additive.toMul u)),
      trivial, ?_⟩
    have h := logEmbedding_unitOfUnits (S := S) (Additive.toMul u)
    exact h
  have hle : Submodule.map (inlₗ S)
        (Submodule.span ℝ (Units.unitLattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ)))
      ≤ Submodule.span ℝ (unitLattice S : Set (logSpace S)) := by
    rw [← Submodule.span_image]
    exact Submodule.span_mono hmap
  rw [NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top] at hle
  exact hle ⟨a, trivial, rfl⟩

open scoped Classical in
private theorem inrₗ_single_mem_span (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (v₀ : ↥S) :
    inrₗ S (Pi.single v₀ 1) ∈ Submodule.span ℝ (unitLattice S : Set (logSpace S)) := by
  obtain ⟨y, hy0, hy⟩ :=
    Set.exists_mem_unit_finitePlace (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
      ⟨v₀.1, Finset.mem_coe.mpr v₀.2⟩
  set c : ℝ := Real.log (FinitePlace.mk (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    ((y : Kˣ) : K)) with hc
  have hcne : c ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (FinitePlace.pos_iff.mpr (Units.ne_zero _)) hy0
  have hsplit : inrₗ S (Pi.single v₀ c)
      = logEmbedding S (Additive.ofMul y)
        - inlₗ S (fun w => logEmbedding S (Additive.ofMul y) (Sum.inl w)) := by
    funext i
    cases i with
    | inl w =>
      simp only [inrₗ, inlₗ, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Pi.sub_apply,
        Pi.zero_apply, sub_self]
    | inr v =>
      simp only [inrₗ, inlₗ, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Pi.sub_apply,
        Pi.zero_apply, sub_zero, logEmbedding_apply_inr]
      by_cases hv : v = v₀
      · subst hv; rw [Pi.single_eq_same, hc]
      · rw [Pi.single_eq_of_ne hv,
          hy ⟨v.1, Finset.mem_coe.mpr v.2⟩ (fun h => hv (Subtype.ext (congrArg Subtype.val h))),
          Real.log_one]
  have hmem : logEmbedding S (Additive.ofMul y)
      ∈ Submodule.span ℝ (unitLattice S : Set (logSpace S)) :=
    Submodule.subset_span ⟨Additive.ofMul y, trivial, rfl⟩
  have hdiff : inrₗ S (Pi.single v₀ c)
      ∈ Submodule.span ℝ (unitLattice S : Set (logSpace S)) := by
    rw [hsplit]
    exact Submodule.sub_mem _ hmem (inlₗ_mem_span S _)
  have hsm := Submodule.smul_mem _ c⁻¹ hdiff
  rwa [← LinearMap.map_smul, show c⁻¹ • (Pi.single v₀ c : ↥S → ℝ) = Pi.single v₀ 1 by
    rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hcne]] at hsm

open scoped Classical in
/-- **The `S`-unit lattice spans the `S`-logarithmic space over `ℝ`.** -/
theorem unitLattice_span_eq_top (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Submodule.span ℝ (unitLattice S : Set (logSpace S)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hsplit : f = inlₗ S (fun w => f (Sum.inl w)) + inrₗ S (fun v => f (Sum.inr v)) := by
    funext i; cases i <;> simp [inlₗ, inrₗ]
  have hB : ∀ b : ↥S → ℝ, inrₗ S b ∈ Submodule.span ℝ (unitLattice S : Set (logSpace S)) := by
    intro b
    have hb : b = ∑ v : ↥S, b v • Pi.single v 1 := by
      funext v
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hb, map_sum]
    refine Submodule.sum_mem _ fun v _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (inrₗ_single_mem_span S v)
  rw [hsplit]
  exact Submodule.add_mem _ (inlₗ_mem_span S _) (hB _)

/-!
### The `S`-regulator
-/

open scoped Classical in
instance instZLattice_unitLattice (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    IsZLattice ℝ (unitLattice S) where
  span_top := unitLattice_span_eq_top S

open scoped Classical in
/-- The dimension of the `S`-logarithmic space. -/
theorem finrank_logSpace (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    finrank ℝ (logSpace S) = NumberField.Units.rank K + S.card := by
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K :=
    (Module.finrank_fintype_fun_eq_card (R := ℝ)).symm.trans (NumberField.Units.finrank_eq_rank K)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_coe, hcard]

open scoped Classical in
/-- **The `S`-unit lattice has rank `r₁ + r₂ - 1 + |S|`.** ⚠ This is a second, independent
computation of that rank: here it is the real dimension of the space the lattice is full in,
while `Set.unit_finrank_numberField` computes it from the class group and Dirichlet's theorem.
The acceptance criteria at the end of the file check that the two agree. -/
theorem finrank_unitLattice (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    finrank ℤ (unitLattice S) = NumberField.Units.rank K + S.card := by
  rw [ZLattice.rank ℝ, finrank_logSpace]

open scoped Classical in
/-- **The `S`-regulator of a number field**, the covolume of the `S`-unit lattice. At `S = ∅` it
is `NumberField.Units.regulator`; see `NumberField.SUnit.regulator_empty`. -/
noncomputable def regulator (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : ℝ :=
  ZLattice.covolume (unitLattice S)

open scoped Classical in
theorem regulator_pos (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    0 < regulator S :=
  ZLattice.covolume_pos _ _

open scoped Classical in
theorem regulator_ne_zero (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    regulator S ≠ 0 :=
  (regulator_pos S).ne'

/-!
### `S = ∅` is Dirichlet's regulator
-/

open scoped Classical in
/-- At `S = ∅` the `S`-logarithmic space is Dirichlet's, up to the empty summand. ⚠ This
identification is a theorem and not a definitional unfolding; see the implementation notes. -/
@[expose] noncomputable def emptyEquiv :
    ({w : InfinitePlace K // w ≠ w₀} → ℝ)
      ≃L[ℝ] logSpace (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun a => Sum.elim a 0
      map_add' := fun a b => by funext i; cases i <;> simp
      map_smul' := fun c a => by funext i; cases i <;> simp
      invFun := fun g w => g (Sum.inl w)
      left_inv := fun a => rfl
      right_inv := fun g => by
        funext i
        cases i with
        | inl w => rfl
        | inr v => exact absurd v.2 (Finset.notMem_empty _) }

open scoped Classical in
@[simp] theorem emptyEquiv_apply (a : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    emptyEquiv a = Sum.elim a 0 := rfl

open scoped Classical in
theorem measurePreserving_emptyEquiv :
    MeasurePreserving (emptyEquiv (K := K)) volume volume := by
  have h := MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : ({w : InfinitePlace K // w ≠ w₀} ⊕
      ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) => ℝ)
    (Equiv.sumEmpty {w : InfinitePlace K // w ≠ w₀}
      ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))).symm
  have hfun : (emptyEquiv (K := K) : ({w : InfinitePlace K // w ≠ w₀} → ℝ) →
      logSpace (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))))
      = ⇑(MeasurableEquiv.piCongrLeft
        (fun _ : ({w : InfinitePlace K // w ≠ w₀} ⊕
          ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) => ℝ)
        (Equiv.sumEmpty {w : InfinitePlace K // w ≠ w₀}
          ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))).symm) := by
    funext a i
    rw [MeasurableEquiv.coe_piCongrLeft]
    cases i with
    | inl w =>
      exact (Equiv.piCongrLeft_apply_apply
        (fun _ : ({w : InfinitePlace K // w ≠ w₀} ⊕
          ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) => ℝ)
        (Equiv.sumEmpty {w : InfinitePlace K // w ≠ w₀}
          ↥(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))).symm a w).symm
    | inr v => exact absurd v.2 (Finset.notMem_empty _)
  rw [hfun]
  exact h

open scoped Classical in
/-- Under the identification of the two logarithmic spaces, the `∅`-unit lattice is Dirichlet's
unit lattice. -/
theorem comap_unitLattice_empty :
    ZLattice.comap ℝ (unitLattice (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))))
        (emptyEquiv (K := K)).toLinearMap
      = NumberField.Units.unitLattice K := by
  ext a
  rw [ZLattice.comap, Submodule.mem_comap]
  change Sum.elim a 0 ∈ unitLattice (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    ↔ a ∈ NumberField.Units.unitLattice K
  constructor
  · rintro ⟨z, -, hz⟩
    have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        v.valuation K (((Additive.toMul z : ↥((↑(∅ :
          Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
          : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) : Kˣ) : K) = 1 :=
      fun v => (Additive.toMul z).2 v (by simp)
    obtain ⟨u, hu⟩ := Set.mem_unit_empty_iff.mp fun v _ => hall v
    have hz' : (↑(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
        : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits u = Additive.toMul z :=
      Subtype.ext (Units.ext hu)
    have h := logEmbedding_unitOfUnits
      (S := (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) u
    rw [hz'] at h
    refine ⟨Additive.ofMul u, trivial, ?_⟩
    funext w
    have hw := congrFun (h.symm.trans hz) (Sum.inl w)
    rw [Sum.elim_inl, Sum.elim_inl] at hw
    exact hw
  · rintro ⟨u, -, rfl⟩
    refine ⟨Additive.ofMul ((↑(∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
      : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits (Additive.toMul u)),
      trivial, ?_⟩
    exact logEmbedding_unitOfUnits
      (S := (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) (Additive.toMul u)

open scoped Classical in
/-- **`S = ∅` recovers Dirichlet's regulator.** -/
theorem regulator_empty :
    regulator (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
      = NumberField.Units.regulator K := by
  rw [regulator, ← ZLattice.covolume_comap _ _ volume measurePreserving_emptyEquiv,
    comap_unitLattice_empty]
  rfl

/-!
### Acceptance criteria
-/

section Examples

open scoped Classical in
/-- **The two computations of the rank agree.** `NumberField.SUnit.finrank_unitLattice` reads the
rank off the real dimension of the space the lattice fills; `Set.unit_finrank_numberField` reads
it off the class group and Dirichlet's theorem. Neither proof uses the other. -/
example (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    finrank ℤ (unitLattice S)
      = finrank ℤ (Additive ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) := by
  rw [finrank_unitLattice, Set.unit_finrank_numberField _ S.finite_toSet]
  congr 1
  simp

open scoped Classical in
/-- **Conformance with Layer 6.1 and with Mathlib.** At `S = ∅` the `S`-regulator is Dirichlet's
regulator. -/
example : regulator (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    = NumberField.Units.regulator K := regulator_empty

open scoped Classical in
/-- **Acceptance test: the comparison is two-sided and its two halves are compatible.** Both
bounds hold at once, so the height and the embedding of an `S`-unit are comparable in both
directions. -/
example (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ↥((S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    ‖logEmbedding S (Additive.ofMul x)‖ ≤ 2 * logHeight₁ ((x : Kˣ) : K) ∧
      logHeight₁ ((x : Kˣ) : K)
        ≤ (Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S) : ℝ)
            * ‖logEmbedding S (Additive.ofMul x)‖ :=
  ⟨norm_logEmbedding_le_two_mul_logHeight₁ x, logHeight₁_le_card_mul_norm_logEmbedding x⟩

/-- **Rejection test: the `S`-unit hypothesis is load-bearing in the product formula.** Layer
6.4's height display asks only that `x` be an `S`-integer, and `2` is an `∅`-integer; but the
additive identity `NumberField.SUnit.sum_mult_mul_log_add_sum_log` fails for it, the left-hand
side being `[K : ℚ] · log 2`. What the display can absorb into a `max (·) 1` the product formula
cannot. -/
example : (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((2 : ℚ) : K)))
    + ∑ v ∈ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))),
        Real.log (FinitePlace.mk v ((2 : ℚ) : K)) ≠ 0 := by
  have hd : 0 < finrank ℚ K := Module.finrank_pos
  have htwo : ∀ w : InfinitePlace K, w ((2 : ℚ) : K) = 2 := fun w => by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have hsum : (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((2 : ℚ) : K)))
      = (finrank ℚ K : ℝ) * Real.log 2 := by
    calc (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((2 : ℚ) : K)))
        = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log 2 :=
          Finset.sum_congr rfl fun w _ => by rw [htwo w]
      _ = (∑ w : InfinitePlace K, (w.mult : ℝ)) * Real.log 2 := by rw [Finset.sum_mul]
      _ = (finrank ℚ K : ℝ) * Real.log 2 := by
          rw [← Nat.cast_sum, ← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  rw [Finset.sum_empty, add_zero, hsum]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') (Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num) (by norm_num))

end Examples

end NumberField.SUnit
