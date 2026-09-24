/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Affine
public import ArithmeticHeights.SRegulator
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.LinearAlgebra.Dual.Defs

-- Used only inside proofs.
import ArithmeticHeights.LinearForm
import ArithmeticHeights.SUnit
import DiophantineApproximation.FundamentalInequality
import DiophantineApproximation.RationalPlaces
import DiophantineApproximation.SAdicHeight

/-!
# Unit normalization: the reductions of the Subspace Theorem

Three reductions put every solution of the Subspace inequality over a number field `K` into a
normal form, before the approximation classes of `SubspaceReduction.lean` sort it.

*Projective to affine* (Bombieri–Gubler, Theorem 7.2.6). Every finite set `S₀` of finite places
is contained in a finite `S₀'` such that every nonzero point of `Kⁿ⁺¹` has a scalar multiple whose
local sup norms are `1` at every finite place outside `S₀'` — a **primitive** point — and the
height of a primitive point is the product of its local sup norms over the infinite places and
`S₀'`. This is Layer 0.3 (Proposition 5.3.6 and the primitive multiple over a principal ring of
`S`-integers) read in the language of `NumberField.FinitePlace`.

*Unit normalization* (Lemma 7.5.4). There is a constant `C₀` depending only on `K` and `S₀` such
that every primitive `x` has an `S₀`-unit multiple `u • x` with
`h(x) ≤ h_aff(u • x) ≤ h(x) + C₀`, the affine height being `ArithmeticHeights` 0.5's. The input is
that the `S₀`-logarithmic image of the `S₀`-units is a full lattice in the trace-zero hyperplane
(`ArithmeticHeights` 6.5): every trace-zero vector is within a bounded distance of it.

*Bounded local factors* (Corollary 7.5.5). For any forms `L v i` the unit can be chosen so that
every `h(L v i (u • x))`, at the infinite places and the places of `S₀`, is at most
`h(x) + C₁`; and then, by the fundamental inequality (Layer 0.4), every nonzero value satisfies
`|mult v · log v (L v i (u • x))| ≤ h(x) + C₁` — the book's (7.19).

## Main results

* `NumberField.SUnit.exists_forall_abs_log_sub_le` and
  `NumberField.exists_forall_abs_log_apply_sub_le`: the `S`-unit lattice is cocompact in the
  trace-zero hyperplane.
* `NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one`: the height of a primitive point.
* `NumberField.logHeightAff_le_sum_posLog`: the affine height of an `S₀`-integral point.
* `NumberField.exists_finset_superset_forall_exists_iSup_eq_one`: Theorem 7.2.6's enlargement.
* `NumberField.exists_forall_logHeightAff_smul_le`: Lemma 7.5.4.
* `NumberField.InfinitePlace.abs_mult_mul_log_le_logHeight₁` and
  `NumberField.FinitePlace.abs_log_le_logHeight₁`: the fundamental inequality at one place, the
  book's (7.19).
* `NumberField.exists_forall_logHeight₁_apply_smul_le`: Corollary 7.5.5.

## Implementation notes

⚠ **Primitivity is stated through the places, not through ideals.** A point `x` is primitive for
`Sfin` when `⨆ i, v (x i) = 1` at every finite place `v ∉ Sfin`. Layer 0.3 states it as
"the coordinates are `S`-integers generating the unit ideal", over `HeightOneSpectrum`; only the
consequence at the places is used, and it is the form in which `approxDomain` is written.

⚠ **The unit is balanced, not placed at one coordinate.** The book takes one coordinate
`x 0 ≠ 0` and asks `|u x 0|_v ≥ e^(-C)` at every `v ∈ S`. Here the target of the lattice
approximation is the trace-zero vector `(mult v / D) h(x) - mult v log |x|_v`, with `D` the
number of places of `S` counted with multiplicity: then `mult v log |u x|_v ≤ (mult v / D) h(x) + R`
at every place of `S` at once, and summing the positive parts gives `h_aff(u x) ≤ h(x) + R #S`
with no case distinction and no distinguished place.

⚠ **The constant of Lemma 7.5.4 depends only on `K` and `S₀`**, as the book says, and not on
`n`: the statement quantifies over the index type after the constant.

⚠ **Corollary 7.5.5 needs no independence of the forms.** The book compares
`h_aff(L v (x))` with `h_aff(x)` in both directions, which uses the independence of `L v`. Only
one direction is needed: the height of the single number `L v i x` is at most the affine height
of `x` plus a constant (`ArithmeticHeights` 0.5, `Height.logHeight₁_sum_mul_le`), and the
fundamental inequality bounds `|log v (L v i x)|` by that height from both sides.

⚠ **Three acceptance tests.** Over `ℚ` with `S₀` the `2`-adic place, the one-point tuples `(2 ^ k)`
are primitive, of projective height `1` and affine height `2 ^ k`: without the unit, Lemma 7.5.4
fails for every constant. Over `ℚ` with `S₀ = ∅`, the point `(2, 2)` is not primitive, and its
height `1` is not the product `2` of its sup norms at the infinite place: the height identity
needs primitivity. And at the `2`-adic place of `ℚ`, `|log |2|₂| = log H(2)`: the bound (7.19) is
sharp.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.6, Lemma 7.5.4 and Corollary 7.5.5.

This is Layer 5.1 (first half) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open scoped Real

namespace NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The `S`-unit lattice is cocompact in the trace-zero hyperplane.** There is `R` such that for
every vector `(a, b)` of the infinite places and the places of `S` with coordinate sum `0` there
is an `S`-unit whose weighted logarithms are within `R` of it, coordinate by coordinate. The
coordinates away from the distinguished infinite place are those of the lattice point nearest in
a fundamental domain of `NumberField.SUnit.unitLattice`, the coordinate at it is minus their sum by
the product formula. -/
theorem exists_forall_abs_log_sub_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (a : InfinitePlace K → ℝ) (b : S → ℝ), ∑ w, a w + ∑ v, b v = 0 →
      ∃ u : ↥((S : Set (HeightOneSpectrum (𝓞 K))).unit K),
        (∀ w : InfinitePlace K, |(w.mult : ℝ) * Real.log (w ((u : Kˣ) : K)) - a w| ≤ R) ∧
        ∀ v : S, |Real.log (FinitePlace.mk v.1 ((u : Kˣ) : K)) - b v| ≤ R := by
  set Λ := unitLattice S
  let b₀ := Module.Free.chooseBasis ℤ Λ
  let B := b₀.ofZLatticeBasis ℝ Λ
  set R₀ : ℝ := ∑ i, ‖B i‖ with hR₀
  have hR₀0 : 0 ≤ R₀ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  set M : ℕ := Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ ↥S)
  refine ⟨(M + 1) * R₀, by positivity, fun a b hab ↦ ?_⟩
  set t : logSpace S := Sum.elim (fun w ↦ a w.1) b with ht
  have hmem : (ZSpan.floor B t : logSpace S) ∈ Λ := by
    have h := (ZSpan.floor B t).2
    have hs : Submodule.span ℤ (Set.range B) = Λ := b₀.ofZLatticeBasis_span ℝ Λ
    exact hs.le h
  obtain ⟨u, hu⟩ := mem_unitLattice_iff.1 hmem
  set ℓ : logSpace S := (ZSpan.floor B t : logSpace S)
  have hdist : ∀ j, |t j - ℓ j| ≤ R₀ := by
    intro j
    have h1 : ‖t - ℓ‖ ≤ R₀ := by
      have := ZSpan.norm_fract_le B t
      rwa [ZSpan.fract_apply] at this
    have h2 := norm_le_pi_norm (t - ℓ) j
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h2
    linarith
  refine ⟨Additive.toMul u, fun w ↦ ?_, fun v ↦ ?_⟩
  · have hle : R₀ ≤ (M + 1) * R₀ := le_mul_of_one_le_left hR₀0 (by norm_cast; omega)
    by_cases hw : w = w₀
    · subst hw
      have hsum := sum_logEmbedding_eq (S := S) (Additive.toMul u)
      simp only [ofMul_toMul] at hsum
      have hu' : (logEmbedding S u : logSpace S) = ℓ := hu
      rw [hu'] at hsum
      have hsplit : a w₀ = -∑ j, t j := by
        rw [Fintype.sum_sum_type, ht]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hab
        linarith
      have hsum' : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (((Additive.toMul u :
          ↥((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) : Kˣ) : K)) = -∑ j, ℓ j := by
        rw [hsum]; ring
      rw [hsum', hsplit]
      have : |∑ j, (t j - ℓ j)| ≤ M * R₀ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun j _ ↦ hdist j).trans ?_
        simp [M]
      rw [Finset.sum_sub_distrib] at this
      rw [show -∑ j, ℓ j - -∑ j, t j = ∑ j, t j - ∑ j, ℓ j by ring]
      nlinarith
    · have := hdist (Sum.inl ⟨w, hw⟩)
      rw [← hu] at this
      change |a w - logEmbedding S (Additive.ofMul (Additive.toMul u)) (Sum.inl ⟨w, hw⟩)| ≤ R₀
        at this
      rw [abs_sub_comm, logEmbedding_apply_inl] at this
      linarith
  · have := hdist (Sum.inr v)
    rw [← hu] at this
    change |b v - logEmbedding S (Additive.ofMul (Additive.toMul u)) (Sum.inr v)| ≤ R₀ at this
    rw [abs_sub_comm, logEmbedding_apply_inr] at this
    linarith [this, le_mul_of_one_le_left hR₀0 (by norm_cast; omega : (1:ℝ) ≤ M + 1)]


end NumberField.SUnit

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The `S`-unit lattice is cocompact in the trace-zero hyperplane**, for a finite set of finite
places given as `NumberField.FinitePlace`s: an element `u ≠ 0` with `v u = 1` off `Sfin` whose
weighted logarithms are within `R` of any prescribed trace-zero vector. -/
theorem exists_forall_abs_log_apply_sub_le (Sfin : Finset (FinitePlace K)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (a : InfinitePlace K → ℝ) (b : FinitePlace K → ℝ),
      ∑ w, a w + ∑ v ∈ Sfin, b v = 0 →
      ∃ u : K, u ≠ 0 ∧ (∀ v : FinitePlace K, v ∉ Sfin → v u = 1) ∧
        (∀ w : InfinitePlace K, |(w.mult : ℝ) * Real.log (w u) - a w| ≤ R) ∧
        ∀ v ∈ Sfin, |Real.log (v u) - b v| ≤ R := by
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := Sfin.image FinitePlace.maximalIdeal with hS
  have hmemS : ∀ v : FinitePlace K, v.maximalIdeal ∈ S ↔ v ∈ Sfin := by
    intro v
    rw [hS, Finset.mem_image]
    refine ⟨fun ⟨w, hw, hwv⟩ ↦ ?_, fun h ↦ ⟨v, h, rfl⟩⟩
    rwa [← FinitePlace.mk_maximalIdeal v, ← hwv, FinitePlace.mk_maximalIdeal]
  obtain ⟨R, hR0, hR⟩ := SUnit.exists_forall_abs_log_sub_le S
  refine ⟨R, hR0, fun a b hab ↦ ?_⟩
  have hsum : ∑ v : S, b (FinitePlace.mk v.1) = ∑ v ∈ Sfin, b v := by
    rw [Finset.sum_coe_sort S (fun p ↦ b (FinitePlace.mk p)), hS,
      Finset.sum_image fun v _ w _ h ↦ by
        rw [← FinitePlace.mk_maximalIdeal v, h, FinitePlace.mk_maximalIdeal]]
    simp [FinitePlace.mk_maximalIdeal]
  obtain ⟨u, hinf, hfin⟩ := hR a (fun v ↦ b (FinitePlace.mk v.1)) (by rw [hsum]; exact hab)
  refine ⟨((u : Kˣ) : K), Units.ne_zero _, fun v hv ↦ ?_, hinf, fun v hv ↦ ?_⟩
  · have h := (Set.mem_unit_iff_finitePlace _ (u : Kˣ)).1 u.2 v.maximalIdeal
      (by simpa [hmemS] using hv)
    rwa [FinitePlace.mk_maximalIdeal] at h
  · have h := hfin ⟨v.maximalIdeal, (hmemS v).2 hv⟩
    simpa [FinitePlace.mk_maximalIdeal] using h


variable {ι : Type*}

/-!
### Primitive points
-/

/-- **The height of a primitive point is the product of its local sup norms over the infinite
places and `Sfin`.** Bombieri–Gubler, Theorem 7.2.6; the `FinitePlace` form of Layer 0.3's
`NumberField.mulHeight_eq_prod_of_isPrimitive`. -/
theorem mulHeight_eq_prod_of_forall_iSup_eq_one {Sfin : Finset (FinitePlace K)} {x : ι → K}
    (hx : x ≠ 0) (h : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) :
    mulHeight x = (∏ w : InfinitePlace K, (⨆ i, w (x i)) ^ w.mult) * ∏ v ∈ Sfin, ⨆ i, v (x i) := by
  rw [NumberField.mulHeight_eq hx]
  congr 1
  exact finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
    by_contra hvS
    exact hv (h v hvS)

/-- **The affine height of an `Sfin`-integral point** is at most the sum of the positive parts of
the logarithms of its local sup norms over the infinite places, weighted, and `Sfin`: the
appended coordinate `1` contributes nothing at a place where the sup norm exceeds `1`, and makes
the local factor `1` at the places outside `Sfin`. -/
theorem logHeightAff_le_sum_posLog [Finite ι] {Sfin : Finset (FinitePlace K)} {x : ι → K}
    (h : ∀ v : FinitePlace K, v ∉ Sfin → ∀ i, v (x i) ≤ 1) :
    logHeightAff x ≤ ∑ w : InfinitePlace K, w.mult * log⁺ (⨆ i, w (x i)) +
      ∑ v ∈ Sfin, log⁺ (⨆ i, v (x i)) := by
  set z : Option ι → K := fun o ↦ o.elim 1 x with hz
  have hbdd : ∀ f : Option ι → ℝ, BddAbove (Set.range f) := fun f ↦ Finite.bddAbove_range f
  have hone : ∀ v : AbsoluteValue K ℝ, 1 ≤ ⨆ o, v (z o) := fun v ↦
    le_ciSup_of_le (hbdd _) none (by simp [hz])
  have honeI : ∀ w : InfinitePlace K, 1 ≤ ⨆ o, w (z o) := fun w ↦ hone w.1
  have honeF : ∀ v : FinitePlace K, 1 ≤ ⨆ o, v (z o) := fun v ↦ hone v.1
  have hle : ∀ v : AbsoluteValue K ℝ, (⨆ o, v (z o)) ≤ max 1 (⨆ i, v (x i)) := by
    intro v
    refine ciSup_le fun o ↦ ?_
    cases o with
    | none => simp [hz]
    | some i =>
      exact le_max_of_le_right (le_ciSup_of_le (Finite.bddAbove_range _) i le_rfl)
  have hfin : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ o, v (z o) = 1 := by
    intro v hv
    refine le_antisymm (ciSup_le fun o ↦ ?_) (hone v.1)
    cases o with
    | none => simp [hz]
    | some i => exact h v hv i
  have hlog : ∀ v : AbsoluteValue K ℝ, Real.log (⨆ o, v (z o)) ≤ log⁺ (⨆ i, v (x i)) := by
    intro v
    rw [Real.posLog_eq_log_max_one (Real.iSup_nonneg fun i ↦ v.nonneg _)]
    exact Real.log_le_log (by linarith [hone v]) (hle v)
  rw [logHeightAff_eq_log_mulHeightAff, mulHeightAff,
    mulHeight_eq_prod_of_forall_iSup_eq_one (optionElim_one_ne_zero x) hfin,
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun w _ ↦ pow_ne_zero _ (by linarith [honeI w]))
      (Finset.prod_ne_zero_iff.2 fun v _ ↦ by linarith [honeF v]),
    Real.log_prod (fun w _ ↦ pow_ne_zero _ (by linarith [honeI w])),
    Real.log_prod (fun v _ ↦ by linarith [honeF v])]
  simp only [Real.log_pow]
  gcongr with w _ v _
  · exact hlog w.1
  · exact hlog v.1

/-- **Bombieri–Gubler, Theorem 7.2.6, the enlargement.** Every finite set of finite places is
contained in a finite `Sfin'` such that every nonzero point, of any finite dimension, has a
scalar multiple that is primitive for `Sfin'`. The enlargement makes the ring of
`Sfin'`-integers principal (Proposition 5.3.6, Layer 0.3). -/
theorem exists_finset_superset_forall_exists_iSup_eq_one (Sfin : Finset (FinitePlace K)) :
    ∃ Sfin' : Finset (FinitePlace K), Sfin ⊆ Sfin' ∧
      ∀ {ι : Type*} [Finite ι] (x : ι → K), x ≠ 0 →
        ∃ t : K, t ≠ 0 ∧ ∀ v : FinitePlace K, v ∉ Sfin' → ⨆ i, v ((t • x) i) = 1 := by
  classical
  obtain ⟨T, hST, hTfin, hTprin⟩ := exists_finite_superset_isPrincipalIdealRing
    ((Sfin.image FinitePlace.maximalIdeal : Finset _) : Set (HeightOneSpectrum (𝓞 K)))
    (Finset.finite_toSet _)
  refine ⟨hTfin.toFinset.image FinitePlace.mk, fun v hv ↦ ?_, fun {ι} _ x hx ↦ ?_⟩
  · refine Finset.mem_image.2 ⟨v.maximalIdeal, hTfin.mem_toFinset.2 (hST ?_),
      FinitePlace.mk_maximalIdeal v⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hv)
  have : IsPrincipalIdealRing ↥(T.integer K) := hTprin
  obtain ⟨c, hc0, hprim⟩ := exists_isPrimitive_mul T hx
  refine ⟨c, hc0, fun v hv ↦ ?_⟩
  have hvT : v.maximalIdeal ∉ hTfin.toFinset := fun h ↦
    hv (Finset.mem_image.2 ⟨_, h, FinitePlace.mk_maximalIdeal v⟩)
  have h := iSup_mk_eq_one_of_isPrimitive hTfin.toFinset (by rwa [hTfin.coe_toFinset]) hvT
  simpa [FinitePlace.mk_maximalIdeal] using h

/-!
### Lemma 7.5.4
-/

omit [NumberField K] in
private theorem mul_posLog_le {m t B : ℝ} (hB : 0 ≤ B) (h : m * Real.log t ≤ B) :
    m * log⁺ t ≤ B := by
  change m * max 0 (Real.log t) ≤ B
  rcases le_total (Real.log t) 0 with ht | ht
  · rw [max_eq_left ht, mul_zero]; exact hB
  · rwa [max_eq_right ht]

/-- **Bombieri–Gubler, Lemma 7.5.4.** There is a constant `C`, depending only on `K` and `Sfin`,
such that every primitive point `x` has a multiple `u • x` by an `Sfin`-unit `u` whose affine
height exceeds the height of `x` by at most `C`. -/
theorem exists_forall_logHeightAff_smul_le (Sfin : Finset (FinitePlace K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Finite ι] (x : ι → K), x ≠ 0 →
      (∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) →
      ∃ u : K, u ≠ 0 ∧ (∀ v : FinitePlace K, v ∉ Sfin → v u = 1) ∧
        logHeight x ≤ logHeightAff (u • x) ∧ logHeightAff (u • x) ≤ logHeight x + C := by
  obtain ⟨R, hR0, hR⟩ := exists_forall_abs_log_apply_sub_le Sfin
  refine ⟨R * (Fintype.card (InfinitePlace K) + Sfin.card), by positivity, ?_⟩
  intro ι _ x hx hprim
  have _i : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ i, v (x i) := fun v ↦
    lt_of_lt_of_le (v.pos hi₀) (le_ciSup_of_le (Finite.bddAbove_range _) i₀ le_rfl)
  set h : ℝ := logHeight x with hh
  have hh0 : 0 ≤ h := logHeight_nonneg x
  have hH : h = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (⨆ i, w (x i)) +
      ∑ v ∈ Sfin, Real.log (⨆ i, v (x i)) := by
    rw [hh, logHeight_eq_log_mulHeight, mulHeight_eq_prod_of_forall_iSup_eq_one hx hprim,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun w _ ↦ pow_ne_zero _ (hpos w.1).ne')
        (Finset.prod_ne_zero_iff.2 fun v _ ↦ (hpos v.1).ne'),
      Real.log_prod (fun w _ ↦ pow_ne_zero _ (hpos w.1).ne'),
      Real.log_prod (fun v _ ↦ (hpos v.1).ne')]
    simp only [Real.log_pow]
  set D : ℝ := ∑ w : InfinitePlace K, (w.mult : ℝ) + Sfin.card with hD
  have hD0 : 0 < D := by
    have : (0 : ℝ) < ∑ w : InfinitePlace K, (w.mult : ℝ) :=
      Finset.sum_pos (fun w _ ↦ by exact_mod_cast w.mult_pos) Finset.univ_nonempty
    positivity
  set a : InfinitePlace K → ℝ := fun w ↦ w.mult / D * h - w.mult * Real.log (⨆ i, w (x i))
  set b : FinitePlace K → ℝ := fun v ↦ h / D - Real.log (⨆ i, v (x i))
  have hab : ∑ w, a w + ∑ v ∈ Sfin, b v = 0 := by
    simp only [a, b, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.sum_div]
    have : (∑ w : InfinitePlace K, (w.mult : ℝ)) / D * h + Sfin.card * (h / D) = h := by
      field_simp
      ring
    linarith
  obtain ⟨u, hu0, huS, hinf, hfin⟩ := hR a b hab
  refine ⟨u, hu0, huS, ?_, ?_⟩
  · rw [hh, ← logHeight_smul_eq_logHeight x hu0]
    exact logHeight_le_logHeightAff _
  have hsup : ∀ v : AbsoluteValue K ℝ, (⨆ i, v ((u • x) i)) = v u * ⨆ i, v (x i) := by
    intro v
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact (Real.mul_iSup_of_nonneg (v.nonneg u) _).symm
  have hsupI : ∀ w : InfinitePlace K, (⨆ i, w ((u • x) i)) = w u * ⨆ i, w (x i) :=
    fun w ↦ hsup w.1
  have hsupF : ∀ v : FinitePlace K, (⨆ i, v ((u • x) i)) = v u * ⨆ i, v (x i) :=
    fun v ↦ hsup v.1
  have hposI : ∀ w : InfinitePlace K, 0 < ⨆ i, w (x i) := fun w ↦ hpos w.1
  have hposF : ∀ v : FinitePlace K, 0 < ⨆ i, v (x i) := fun v ↦ hpos v.1
  have hint : ∀ v : FinitePlace K, v ∉ Sfin → ∀ i, v ((u • x) i) ≤ 1 := by
    intro v hv i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, huS v hv, one_mul, ← hprim v hv]
    exact le_ciSup_of_le (Finite.bddAbove_range _) i le_rfl
  refine (logHeightAff_le_sum_posLog hint).trans ?_
  have hI : ∀ w : InfinitePlace K, (w.mult : ℝ) * log⁺ (⨆ i, w ((u • x) i)) ≤
      w.mult / D * h + R := by
    intro w
    refine mul_posLog_le (by positivity) ?_
    rw [hsupI w]
    have hw := hinf w
    rw [abs_le] at hw
    have : Real.log (w u * ⨆ i, w (x i)) = Real.log (w u) + Real.log (⨆ i, w (x i)) :=
      Real.log_mul (w.pos_iff.2 hu0).ne' (hposI w).ne'
    rw [this]
    simp only [a] at hw
    linarith
  have hF : ∀ v ∈ Sfin, log⁺ (⨆ i, v ((u • x) i)) ≤ h / D + R := by
    intro v hv
    have := mul_posLog_le (m := 1) (by positivity) (t := ⨆ i, v ((u • x) i))
      (B := h / D + R) ?_
    · simpa using this
    rw [hsupF v, one_mul]
    have hw := hfin v hv
    rw [abs_le] at hw
    have : Real.log (v u * ⨆ i, v (x i)) = Real.log (v u) + Real.log (⨆ i, v (x i)) :=
      Real.log_mul (FinitePlace.pos_iff.2 hu0).ne' (hposF v).ne'
    rw [this]
    simp only [b] at hw
    linarith
  calc ∑ w : InfinitePlace K, (w.mult : ℝ) * log⁺ (⨆ i, w ((u • x) i)) +
        ∑ v ∈ Sfin, log⁺ (⨆ i, v ((u • x) i))
      ≤ ∑ w : InfinitePlace K, ((w.mult : ℝ) / D * h + R) + ∑ v ∈ Sfin, (h / D + R) :=
        add_le_add (Finset.sum_le_sum fun w _ ↦ hI w) (Finset.sum_le_sum hF)
    _ = h + R * (Fintype.card (InfinitePlace K) + Sfin.card) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        rw [← Finset.sum_mul, ← Finset.sum_div]
        have : (∑ w : InfinitePlace K, (w.mult : ℝ)) / D * h + Sfin.card * (h / D) = h := by
          field_simp
          ring
        linarith

/-!
### Corollary 7.5.5
-/

/-- **The fundamental inequality at one infinite place**, in the form of Bombieri–Gubler's
(7.19): the weighted logarithm of the value of a nonzero number at one place is at most its
height in absolute value. -/
theorem InfinitePlace.abs_mult_mul_log_le_logHeight₁ (w : InfinitePlace K) {α : K} (hα : α ≠ 0) :
    |(w.mult : ℝ) * Real.log (w α)| ≤ logHeight₁ α := by
  have key : ∀ β : K, β ≠ 0 → (w.mult : ℝ) * Real.log (w β) ≤ logHeight₁ β := by
    intro β hβ
    have h := prod_apply_le_mulHeight₁ {w} ∅ hβ
    simp only [Finset.prod_singleton, Finset.prod_empty, mul_one] at h
    rw [logHeight₁_eq_log_mulHeight₁, ← Real.log_pow]
    exact Real.log_le_log (pow_pos (w.pos_iff.2 hβ) _) h
  rw [abs_le]
  refine ⟨?_, key α hα⟩
  have h := key α⁻¹ (inv_ne_zero hα)
  rw [map_inv₀, Real.log_inv, logHeight₁_inv] at h
  linarith

/-- **The fundamental inequality at one finite place**, in the form of Bombieri–Gubler's
(7.19). -/
theorem FinitePlace.abs_log_le_logHeight₁ (v : FinitePlace K) {α : K} (hα : α ≠ 0) :
    |Real.log (v α)| ≤ logHeight₁ α := by
  have key : ∀ β : K, β ≠ 0 → Real.log (v β) ≤ logHeight₁ β := by
    intro β hβ
    have h := prod_apply_le_mulHeight₁ ∅ {v} hβ
    simp only [Finset.prod_singleton, Finset.prod_empty, one_mul] at h
    rw [logHeight₁_eq_log_mulHeight₁]
    exact Real.log_le_log (FinitePlace.pos_iff.2 hβ) h
  rw [abs_le]
  refine ⟨?_, key α hα⟩
  have h := key α⁻¹ (inv_ne_zero hα)
  rw [map_inv₀, Real.log_inv, logHeight₁_inv] at h
  linarith

omit [NumberField K] in
/-- A form on `Kⁱ` is the sum of its coefficients times the coordinates, the coefficients being
its values at `Pi.basisFun K ι j`. -/
theorem _root_.LinearMap.apply_eq_sum_mul_basisFun [Fintype ι] (l : (ι → K) →ₗ[K] K)
    (y : ι → K) : l y = ∑ j, l (Pi.basisFun K ι j) * y j := by
  conv_lhs => rw [← (Pi.basisFun K ι).sum_repr y]
  simp [map_sum, mul_comm]

/-- **Bombieri–Gubler, Corollary 7.5.5.** For any forms `L v i` there is a constant `C` such that
every primitive point `x` has a multiple `u • x` by an `Sfin`-unit whose form values at the
infinite places and the places of `Sfin` have height at most `h(x) + C`. With the fundamental
inequality at one place this is the book's (7.19). -/
theorem exists_forall_logHeight₁_apply_smul_le [Finite ι] (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → K, x ≠ 0 →
      (∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (x i) = 1) →
      ∃ u : K, u ≠ 0 ∧ (∀ v : FinitePlace K, v ∉ Sfin → v u = 1) ∧
        (∀ (w : InfinitePlace K) (i : ι), logHeight₁ (L w.1 i (u • x)) ≤ logHeight x + C) ∧
        ∀ v ∈ Sfin, ∀ i : ι, logHeight₁ (L v.1 i (u • x)) ≤ logHeight x + C := by
  let _i : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C₀, hC₀, h₀⟩ := exists_forall_logHeightAff_smul_le Sfin
  set A : ℝ := ∑ w : InfinitePlace K, ∑ i, logHeightAff (fun j ↦ L w.1 i (Pi.basisFun K ι j)) +
    ∑ v ∈ Sfin, ∑ i, logHeightAff (fun j ↦ L v.1 i (Pi.basisFun K ι j)) with hA
  have hA0 : ∀ l : Module.Dual K (ι → K), 0 ≤ logHeightAff (fun j ↦ l (Pi.basisFun K ι j)) :=
    fun l ↦ logHeightAff_nonneg _
  have hAI : ∀ (w : InfinitePlace K) i, logHeightAff (fun j ↦ L w.1 i (Pi.basisFun K ι j)) ≤ A := by
    intro w i
    refine le_trans ?_ (le_add_of_nonneg_right (Finset.sum_nonneg fun v _ ↦
      Finset.sum_nonneg fun i _ ↦ hA0 _))
    refine le_trans ?_ (Finset.single_le_sum (fun w _ ↦ Finset.sum_nonneg fun i _ ↦ hA0 _)
      (Finset.mem_univ w))
    exact Finset.single_le_sum (fun i _ ↦ hA0 _) (Finset.mem_univ i)
  have hAF : ∀ v ∈ Sfin, ∀ i, logHeightAff (fun j ↦ L v.1 i (Pi.basisFun K ι j)) ≤ A := by
    intro v hv i
    refine le_trans ?_ (le_add_of_nonneg_left (Finset.sum_nonneg fun w _ ↦
      Finset.sum_nonneg fun i _ ↦ hA0 _))
    refine le_trans ?_ (Finset.single_le_sum (fun v _ ↦ Finset.sum_nonneg fun i _ ↦ hA0 _) hv)
    exact Finset.single_le_sum (fun i _ ↦ hA0 _) (Finset.mem_univ i)
  have hA00 : 0 ≤ A := add_nonneg (Finset.sum_nonneg fun w _ ↦ Finset.sum_nonneg fun i _ ↦ hA0 _)
    (Finset.sum_nonneg fun v _ ↦ Finset.sum_nonneg fun i _ ↦ hA0 _)
  set B : ℝ := totalWeight K * Real.log (Fintype.card ι) with hB
  have hB0 : 0 ≤ B := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [hB]
    · exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
  refine ⟨B + A + C₀, by positivity, fun x hx hprim ↦ ?_⟩
  have hι : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hx
    exact ⟨i⟩
  obtain ⟨u, hu0, huS, -, hle⟩ := h₀ x hx hprim
  have key : ∀ l : Module.Dual K (ι → K), logHeightAff (fun j ↦ l (Pi.basisFun K ι j)) ≤ A →
      logHeight₁ (l (u • x)) ≤ logHeight x + (B + A + C₀) := by
    intro l hl
    rw [LinearMap.apply_eq_sum_mul_basisFun]
    have h := logHeight₁_sum_mul_le (fun j ↦ l (Pi.basisFun K ι j)) (u • x)
    rw [Nat.card_eq_fintype_card] at h
    linarith
  exact ⟨u, hu0, huS, fun w i ↦ key _ (hAI w i), fun v hv i ↦ key _ (hAF v hv i)⟩

end NumberField

section Tests

open NumberField

/-- Away from the `2`-adic place, `2` is a unit of `ℚ`. -/
private theorem Rat.finitePlace_apply_two_of_ne {v : FinitePlace ℚ}
    (hv : v ≠ Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)) : v 2 = 1 := by
  obtain ⟨q, hq, hvq⟩ := Rat.exists_prime_padic_eq v
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hv (Subtype.ext (hvq.trans (Rat.finitePlace_val ⟨2, Nat.prime_two⟩).symm))
  rw [FinitePlace.coe_apply, hvq, AbsoluteValue.padic_eq_padicNorm]
  have : padicNorm q (2 : ℕ) = 1 := (padicNorm.nat_eq_one_iff 2).2 fun h ↦
    hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 h)
  exact_mod_cast this

/-- **Rejection: Lemma 7.5.4 needs the unit.** Over `ℚ` with `S₀` the `2`-adic place, the
one-point tuple `(2 ^ k)` is primitive, of projective height `1` and of affine height `2 ^ k`: no
constant bounds the affine height of a primitive point by its height without the multiple
`u • x`, here `u = 2 ^ (-k)`. -/
example (C : ℝ) : ∃ x : Fin 1 → ℚ, x ≠ 0 ∧
    (∀ v : FinitePlace ℚ,
      v ∉ ({Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)} : Finset (FinitePlace ℚ)) →
      ⨆ i, v (x i) = 1) ∧
    Height.logHeight x + C < Height.logHeightAff x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (C / Real.log 2)
  refine ⟨![((2 ^ k : ℕ) : ℚ)], by simp, fun v hv ↦ ?_, ?_⟩
  · rw [ciSup_unique]
    have h2 := Rat.finitePlace_apply_two_of_ne (Finset.notMem_singleton.1 hv)
    simp [map_pow, h2]
  · rw [Height.logHeight_eq_zero_of_subsingleton, Height.logHeightAff_fin_one,
      Rat.logHeight₁_natCast, Nat.cast_pow, Real.log_pow, zero_add]
    have := (div_lt_iff₀ (Real.log_pos one_lt_two)).1 hk
    push_cast
    linarith

/-- **Rejection: the height identity needs primitivity.** Over `ℚ` with `S₀ = ∅`, the point
`(2, 2)` has height `1`, while the product of its local sup norms over the infinite places and
`S₀` is `2`: the `2`-adic place, where the point is not primitive, is missing. -/
example : Height.mulHeight (![2, 2] : Fin 2 → ℚ) <
    (∏ w : InfinitePlace ℚ, (⨆ i, w ((![2, 2] : Fin 2 → ℚ) i)) ^ w.mult) *
      ∏ v ∈ (∅ : Finset (FinitePlace ℚ)), ⨆ i, v ((![2, 2] : Fin 2 → ℚ) i) := by
  have h1 : (![2, 2] : Fin 2 → ℚ) = (2 : ℚ) • (1 : Fin 2 → ℚ) := by
    ext i; fin_cases i <;> simp
  have h2 : ∀ w : InfinitePlace ℚ, (⨆ i, w ((![2, 2] : Fin 2 → ℚ) i)) = 2 := by
    intro w
    have hw : ∀ i : Fin 2, w ((![2, 2] : Fin 2 → ℚ) i) = 2 := by
      intro i
      rw [Subsingleton.elim w Rat.infinitePlace]
      fin_cases i <;> simp [Rat.infinitePlace_apply]
    simp only [hw, ciSup_const]
  rw [h1, Height.mulHeight_smul_eq_mulHeight _ two_ne_zero, Height.mulHeight_one, ← h1,
    Finset.prod_empty, mul_one]
  simp only [h2]
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace]
  exact one_lt_pow₀ one_lt_two Rat.infinitePlace.mult_ne_zero

/-- **Conformance: (7.19) is sharp.** At the `2`-adic place of `ℚ`, `|log |2|₂| = log H(2)`. -/
example : |Real.log (Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes) 2)| =
    Height.logHeight₁ (2 : ℚ) := by
  have hv : Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes) (2 : ℚ) =
      ((padicNorm 2 (2 : ℚ) : ℚ) : ℝ) := Rat.finitePlace_apply _ 2
  rw [hv]
  have h1 : padicNorm 2 (2 : ℚ) = 2⁻¹ := by
    have := padicNorm.padicNorm_p_of_prime (p := 2)
    exact_mod_cast this
  have h2 : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
    have := Rat.logHeight₁_natCast 2
    exact_mod_cast this
  rw [h1, h2]
  push_cast
  rw [Real.log_inv, abs_neg, abs_of_pos (Real.log_pos one_lt_two)]

end Tests
