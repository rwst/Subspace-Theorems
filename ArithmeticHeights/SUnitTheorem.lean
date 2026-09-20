/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnit
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# The `S`-unit theorem

Let `K` be a number field and `S` a finite set of finite places, carried as Mathlib carries it, as
a set of height-one primes of `𝓞 K`. Dirichlet's `S`-unit theorem says that the group `S.unit K`
of `S`-units is finitely generated of rank `r₁ + r₂ - 1 + |S|`, with the roots of unity of `K` for
its torsion subgroup. This file proves it, in the form and under the name of mathlib4#40791:

```text
finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S.
```

The route is the short exact sequence

```text
1 → (𝓞 K)ˣ → S.unit K → ⊕_{v ∈ S} ℤ
```

whose first map is the inclusion and whose second is `x ↦ (ord_v x)_{v ∈ S}`. The kernel of the
second map is the image of the first — that is Layer 6.4's `S = ∅` statement — and its image has
finite index in `⊕_{v ∈ S} ℤ`, because the class of a prime `v` has finite order in the class
group, so a power of `v` is principal and its generator is an `S`-unit whose valuation is
concentrated at `v`. Rank-nullity over `ℤ` then adds the two ranks.

Beside the rank statement the file carries the usable form, in the shape of Mathlib's
`NumberField.Units.exist_unique_eq_mul_prod`: a fundamental system of `Units.rank K + |S|`
`S`-units such that every `S`-unit is uniquely a root of unity times a product of their integer
powers.

## Main results

* `Set.unitValuation`: the map `S.unit K → ⊕_{v ∈ S} ℤ` of the sequence above, with
  `Set.range_unitOfUnitsₗ` identifying its kernel with the units of `𝓞 K`.
* `Set.finrank_range_unitValuationₗ`: its image has rank `|S|`, from the class group.
* `Set.unit_moduleFinite` and `Set.unit_fg`: the `S`-units are finitely generated. This is one of
  the two open TODOs of Mathlib's `Mathlib/RingTheory/DedekindDomain/SInteger.lean`.
* `Set.unit_finrank_numberField`: **the `S`-unit theorem**, `finrank ℤ (Additive (S.unit K))
  = Units.rank K + Nat.card S`, the other of those two TODOs.
* `Set.exists_unit_fundSystem` and `Set.exists_unit_fundSystem'`: a fundamental system of
  `S`-units, with the decomposition of an arbitrary `S`-unit unique in the exponents alone and
  then in the pair (root of unity, exponents).

## Implementation notes

⚠ **The class group enters only through "some power of a prime ideal is principal", and the class
number is never named.** What the proof needs of `v` is a single `S`-unit whose valuation is
nonzero at `v` and zero at every other prime, and the class of `v` having finite order in
`ClassGroup (𝓞 K)` — which is all the finiteness of the class group is used for — produces one:
a generator of `v ^ orderOf [v]`. The *size* of that valuation is never computed, so
`FractionalIdeal.count` and the factorization API of
`Mathlib/RingTheory/DedekindDomain/Factorization.lean` do not appear, and neither does the class
number.

⚠ **The sequence is not exhibited as short exact, and its cokernel is not embedded in the class
group.** The usual proof identifies `⊕_{v ∈ S} ℤ / image` with a subgroup of the class group and
reads off that the index is finite. Rank-nullity over `ℤ` needs much less: it needs the quotient
to have rank zero, that is, to be a torsion module, and that follows from a nonzero multiple of
each basis vector lying in the image. The index is never computed, and the sequence is never
shown to split.

⚠ **The kernel of the valuation map is Layer 6.4's `S = ∅` statement.** An `S`-unit with trivial
valuation at every place of `S` has trivial valuation at every place, and `Set.mem_unit_empty_iff`
then says it is a unit of `𝓞 K`. So the left-hand end of the sequence costs nothing here, and
`NumberField.Units.finrank_eq` — Mathlib's Dirichlet theorem — supplies its rank.

⚠ **`S` must be finite, and the failure for infinite `S` is not a technicality.** For infinite
`S` the `S`-unit group has infinite rank, so `finrank` reads `0`, while `Nat.card S` also reads
`0` and the right-hand side is `Units.rank K`: the statement is false as soon as `K` has positive
unit rank. `hS` is therefore used twice, once to give `↥S` a `Fintype` for `⊕_{v ∈ S} ℤ` and once
to make `Nat.card S` the rank of that module.

⚠ **The fundamental system is built from the torsion *submodule*, not from a group quotient.**
Mathlib's Dirichlet theorem goes through `(𝓞 K)ˣ ⧸ torsion K` as a quotient *group*, which forces
`QuotientGroup`, `MonoidHom.toAdditive` and `AddMonoidHom.toMultiplicativeRight` into every
statement. Quotienting the `ℤ`-module `Additive (S.unit K)` by `Submodule.torsion ℤ` instead keeps
everything linear: the quotient is finitely generated and torsion-free, hence free over the
principal ideal domain `ℤ` by `Module.free_of_finite_type_torsion_free'`, and
`finrank_quotient_eq_of_le_torsion` says quotienting did not change the rank. The torsion subgroup
of `S.unit K` is never shown to be finite, and the roots of unity of `K` are never mentioned.

⚠ **The uniqueness the milestone asks for is the weaker of the two available.** It asks that the
exponent vector be unique; the root of unity is then determined by it, so the pair is unique as
well. `Set.exists_unit_fundSystem` carries the milestone's shape and
`Set.exists_unit_fundSystem'` the pair form, in the shape of Mathlib's
`NumberField.Units.exist_unique_eq_mul_prod`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.5.13, where the rank is stated as `|S| - 1` in the convention that `S` contains the
archimedean places.

The statement, the carrier `Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))` and the name
`Set.unit_finrank_numberField` follow mathlib4#40791.

This is Layer 6.5 of the `ArithmeticHeights` roadmap.
-/

public section

open IsDedekindDomain Module
open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

/-!
### The valuation map on the `S`-units

The right-hand map of the sequence: an `S`-unit is sent to its vector of valuations at the places
of `S`. Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` is the valuation of a
*unit* of `K`, with values in `Multiplicative ℤ` rather than in `ℤᵐ⁰`, which is what makes this an
additive map.
-/

/-- **The valuation map on the `S`-units**, `x ↦ (ord_v x)_{v ∈ S}`. Mathlib's
`Mathlib/RingTheory/DedekindDomain/SInteger.lean` records as a TODO that the `S`-units are the
kernel of a map to a product; this is that map, and `Set.range_unitOfUnitsₗ` is that statement. -/
@[expose] noncomputable def _root_.Set.unitValuation : Additive ↥(S.unit K) →+ (↥S → ℤ) :=
  AddMonoidHom.mk'
    (fun x v => Multiplicative.toAdd ((v : HeightOneSpectrum (𝓞 K)).valuationOfNeZero
      ((Additive.toMul x : ↥(S.unit K)) : Kˣ)))
    (fun x y => by funext v; simp [map_mul])

theorem _root_.Set.unitValuation_apply (x : ↥(S.unit K)) (v : ↥S) :
    S.unitValuation (Additive.ofMul x) v =
      Multiplicative.toAdd ((v : HeightOneSpectrum (𝓞 K)).valuationOfNeZero (x : Kˣ)) := rfl

/-- A coordinate of the valuation map vanishes exactly where the adic valuation is trivial. -/
theorem _root_.Set.unitValuation_apply_eq_zero_iff (x : ↥(S.unit K)) (v : ↥S) :
    S.unitValuation (Additive.ofMul x) v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuation K ((x : Kˣ) : K) = 1 := by
  have h : S.unitValuation (Additive.ofMul x) v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuationOfNeZero (x : Kˣ) = 1 := Iff.rfl
  rw [h, ← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one]

/-- The valuation map, as a `ℤ`-linear map, which is the form every rank statement needs. -/
@[expose] noncomputable def _root_.Set.unitValuationₗ : Additive ↥(S.unit K) →ₗ[ℤ] (↥S → ℤ) :=
  (S.unitValuation).toIntLinearMap

/-!
### The kernel: the units of `𝓞 K`
-/

/-- **A unit of `𝓞 K` is an `S`-unit**, by Layer 6.4's `NumberField.Units.valuation_eq_one`. -/
@[expose] noncomputable def _root_.Set.unitOfUnits : (𝓞 K)ˣ →* ↥(S.unit K) :=
  MonoidHom.codRestrict (Units.map (algebraMap (𝓞 K) K : (𝓞 K) →* K)) (S.unit K)
    fun u _ _ => NumberField.Units.valuation_eq_one _ u

@[simp]
theorem _root_.Set.unitOfUnits_apply (u : (𝓞 K)ˣ) :
    ((S.unitOfUnits u : ↥(S.unit K)) : Kˣ)
      = Units.map (algebraMap (𝓞 K) K : (𝓞 K) →* K) u := rfl

theorem _root_.Set.unitOfUnits_injective : Function.Injective (S.unitOfUnits) := by
  intro u u' h
  have hK := congrArg (fun y => ((y : ↥(S.unit K)) : Kˣ)) h
  simp only [Set.unitOfUnits_apply] at hK
  exact Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K) hK

/-- The inclusion of the units of `𝓞 K` into the `S`-units, as a `ℤ`-linear map. -/
noncomputable def _root_.Set.unitOfUnitsₗ : Additive (𝓞 K)ˣ →ₗ[ℤ] Additive ↥(S.unit K) :=
  (MonoidHom.toAdditive (S.unitOfUnits)).toIntLinearMap

theorem _root_.Set.unitOfUnitsₗ_injective : Function.Injective (S.unitOfUnitsₗ) :=
  fun _ _ h => S.unitOfUnits_injective h

/-- **The sequence is exact at the `S`-units**: an `S`-unit whose valuations vanish on `S` is a
unit of `𝓞 K`, and conversely. This is Layer 6.4's `Set.mem_unit_empty_iff` in the form the rank
computation uses. -/
theorem _root_.Set.range_unitOfUnitsₗ :
    LinearMap.range (S.unitOfUnitsₗ) = LinearMap.ker (S.unitValuationₗ) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨u, rfl⟩
    funext v
    exact (S.unitValuation_apply_eq_zero_iff _ v).mpr
      (NumberField.Units.valuation_eq_one _ (Additive.toMul u))
  · intro hx
    have hall : ∀ v : HeightOneSpectrum (𝓞 K),
        v.valuation K ((((Additive.toMul x : ↥(S.unit K)) : Kˣ) : K)) = 1 := by
      intro v
      by_cases hv : v ∈ S
      · exact (S.unitValuation_apply_eq_zero_iff _ ⟨v, hv⟩).mp (congrFun hx ⟨v, hv⟩)
      · exact (Additive.toMul x).2 v hv
    obtain ⟨u, hu⟩ := Set.mem_unit_empty_iff.mp fun v _ => hall v
    exact ⟨Additive.ofMul u, Additive.toMul.injective (Subtype.ext (Units.ext hu))⟩

/-- The kernel of the valuation map, as a `ℤ`-module, is the unit group of `𝓞 K`. -/
noncomputable def _root_.Set.unitKerEquiv :
    Additive (𝓞 K)ˣ ≃ₗ[ℤ] ↥(LinearMap.ker (S.unitValuationₗ)) :=
  (LinearEquiv.ofInjective _ S.unitOfUnitsₗ_injective).trans
    (LinearEquiv.ofEq _ _ S.range_unitOfUnitsₗ)

/-- **The left-hand rank of the sequence is Dirichlet's**, by `NumberField.Units.finrank_eq`. -/
theorem _root_.Set.finrank_ker_unitValuationₗ :
    finrank ℤ ↥(LinearMap.ker (S.unitValuationₗ)) = NumberField.Units.rank K := by
  rw [← LinearEquiv.finrank_eq S.unitKerEquiv, NumberField.Units.finrank_eq]

/-!
### The image: finite index in `⊕_{v ∈ S} ℤ`
-/

/-- **A power of a prime ideal is principal, and its generator lies in that prime and in no
other.** The class of `v` in `ClassGroup (𝓞 K)` has finite order because the class group is
finite, so `v ^ orderOf [v]` is principal; a generator `a` of it lies in `v` because the exponent
is positive, and in no other prime `w`, because `w` is prime and `v ^ n ≤ w` would force the
maximal ideals `v` and `w` to be equal. ⚠ The exponent of `a` at `v` is never computed: only that
it is nonzero. -/
private theorem exists_generator (v₀ : HeightOneSpectrum (𝓞 K)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a ∈ v₀.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v₀ → a ∉ w.asIdeal := by
  have hI0 : v₀.asIdeal ≠ 0 := v₀.ne_bot
  have hImem : v₀.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI0
  set c := ClassGroup.mk0 (⟨v₀.asIdeal, hImem⟩ : (Ideal (𝓞 K))⁰) with hc
  have hpos : 0 < orderOf c := orderOf_pos c
  have hprin : (v₀.asIdeal ^ orderOf c).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hImem (orderOf c)), ← SubmonoidClass.mk_pow, map_pow]
    exact pow_orderOf_eq_one c
  obtain ⟨a, ha⟩ := hprin
  have hpowne : v₀.asIdeal ^ orderOf c ≠ ⊥ := pow_ne_zero _ hI0
  have hane : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.mpr rfl] at ha
    exact hpowne ha
  refine ⟨a, hane, ?_, ?_⟩
  · have hle : (𝓞 K ∙ a) ≤ v₀.asIdeal := by
      rw [← ha]; exact Ideal.pow_le_self hpos.ne'
    exact hle (Submodule.mem_span_singleton_self a)
  · intro w hw hmem
    have hle : v₀.asIdeal ^ orderOf c ≤ w.asIdeal := by
      rw [ha]; exact (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
    exact hw (HeightOneSpectrum.ext
      (v₀.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le hle))).symm

/-- **Every place of `S` supports an `S`-unit alone**: for `v₀ ∈ S` there is an `S`-unit whose
valuation is nonzero at `v₀` and zero at every other place of `S`. This is the whole use the proof
makes of the finiteness of the class group. -/
theorem _root_.Set.exists_unitValuation_apply_ne_zero (v₀ : ↥S) :
    ∃ y : Additive ↥(S.unit K), S.unitValuation y v₀ ≠ 0 ∧
      ∀ v : ↥S, v ≠ v₀ → S.unitValuation y v = 0 := by
  obtain ⟨a, hane, hmem, hnot⟩ := exists_generator (K := K) (v₀ : HeightOneSpectrum (𝓞 K))
  have hK : algebraMap (𝓞 K) K a ≠ 0 :=
    fun h => hane ((injective_iff_map_eq_zero _).mp
      (FaithfulSMul.algebraMap_injective (𝓞 K) K) a h)
  have hx : (Units.mk0 (algebraMap (𝓞 K) K a) hK) ∈ S.unit K := fun w hw =>
    (HeightOneSpectrum.valuation_eq_one_iff_notMem _).mpr (hnot w fun h => hw (h ▸ v₀.2))
  refine ⟨Additive.ofMul ⟨_, hx⟩, ?_, ?_⟩
  · rw [Ne, S.unitValuation_apply_eq_zero_iff ⟨_, hx⟩ v₀]
    exact fun h => ((HeightOneSpectrum.valuation_eq_one_iff_notMem _).mp h) hmem
  · intro v hv
    rw [S.unitValuation_apply_eq_zero_iff ⟨_, hx⟩ v]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).mpr
      (hnot v fun h => hv (Subtype.ext h))

/-- **Every place of `S` supports an `S`-unit alone, read at the finite places.** This is
`Set.exists_unitValuation_apply_ne_zero` through Layer 6.4's dictionary, and it is the form Layer
6.5's spanning argument for the `S`-unit lattice consumes. -/
theorem _root_.Set.exists_mem_unit_finitePlace (v₀ : ↥S) :
    ∃ y : ↥(S.unit K),
      NumberField.FinitePlace.mk (v₀ : HeightOneSpectrum (𝓞 K)) ((y : Kˣ) : K) ≠ 1 ∧
      ∀ v : ↥S, v ≠ v₀ →
        NumberField.FinitePlace.mk (v : HeightOneSpectrum (𝓞 K)) ((y : Kˣ) : K) = 1 := by
  obtain ⟨y, hy0, hy⟩ := S.exists_unitValuation_apply_ne_zero v₀
  refine ⟨Additive.toMul y, ?_, ?_⟩
  · exact fun h => hy0 ((S.unitValuation_apply_eq_zero_iff _ v₀).mpr
      ((FinitePlace.mk_apply_eq_one_iff _ _).mp h))
  · exact fun v hv => (FinitePlace.mk_apply_eq_one_iff _ _).mpr
      ((S.unitValuation_apply_eq_zero_iff _ v).mp (hy v hv))

/-- **The image of the valuation map has rank `|S|`.** A nonzero multiple of each basis vector of
`⊕_{v ∈ S} ℤ` lies in the image, so the quotient is a torsion module and has rank `0`; the index
of the image is never computed. -/
theorem _root_.Set.finrank_range_unitValuationₗ (hS : S.Finite) :
    finrank ℤ ↥(LinearMap.range (S.unitValuationₗ)) = Nat.card S := by
  classical
  have := hS.fintype
  choose y hy0 hy using S.exists_unitValuation_apply_ne_zero
  set c : ↥S → ℤ := fun v => S.unitValuation (y v) v with hcdef
  have hC : (∏ v, c v) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hy0 v
  have hmem : ∀ z : ↥S → ℤ, (∏ v, c v) • z ∈ LinearMap.range (S.unitValuationₗ) := by
    intro z
    have key : (∏ v, c v) • z
        = ∑ v : ↥S, ((∏ u ∈ Finset.univ.erase v, c u) * z v) • (S.unitValuationₗ (y v)) := by
      funext w
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single w]
      · rw [show S.unitValuationₗ (y w) w = c w from rfl, mul_assoc, mul_comm (z w) (c w),
          ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
      · intro v _ hvw
        rw [show S.unitValuationₗ (y v) w = S.unitValuation (y v) w from rfl,
          hy v w (Ne.symm hvw), mul_zero]
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [key]
    exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hrank : Module.rank ℤ ((↥S → ℤ) ⧸ LinearMap.range (S.unitValuationₗ)) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    refine ⟨∏ v, c v, hC, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H z => exact (Submodule.Quotient.mk_eq_zero _).mpr (hmem z)
  have hq : finrank ℤ ((↥S → ℤ) ⧸ LinearMap.range (S.unitValuationₗ)) = 0 := by
    simp [Module.finrank, hrank]
  have key := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.range (S.unitValuationₗ))
  rw [hq, zero_add, Module.finrank_fintype_fun_eq_card] at key
  rw [Nat.card_eq_fintype_card]
  exact key

/-!
### The `S`-unit theorem
-/

/-- **The `S`-units are finitely generated as a `ℤ`-module.** The kernel of the valuation map is
`(𝓞 K)ˣ`, finitely generated by Dirichlet, and the quotient by it is a submodule of
`⊕_{v ∈ S} ℤ`, finitely generated because `ℤ` is noetherian. -/
theorem _root_.Set.unit_moduleFinite (hS : S.Finite) :
    Module.Finite ℤ (Additive ↥(S.unit K)) := by
  have := hS.fintype
  have h1 : Module.Finite ℤ ↥(LinearMap.ker (S.unitValuationₗ)) :=
    Module.Finite.equiv S.unitKerEquiv
  have h2 : Module.Finite ℤ ((Additive ↥(S.unit K)) ⧸ LinearMap.ker (S.unitValuationₗ)) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (S.unitValuationₗ)).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (S.unitValuationₗ))

/-- **The `S`-unit group is finitely generated.** This is one of the two open TODOs of Mathlib's
`Mathlib/RingTheory/DedekindDomain/SInteger.lean`. -/
theorem _root_.Set.unit_fg (hS : S.Finite) : Group.FG ↥(S.unit K) := by
  rw [GroupFG.iff_add_fg, ← Module.Finite.iff_addGroup_fg]
  exact S.unit_moduleFinite hS

/-- **Dirichlet's `S`-unit theorem.** For a finite set `S` of finite places of a number field `K`,
the group of `S`-units has `ℤ`-rank `r₁ + r₂ - 1 + |S|`. `S = ∅` recovers Dirichlet's unit
theorem, `NumberField.Units.finrank_eq`, which is also what the proof consumes at the left-hand
end of the sequence. -/
theorem _root_.Set.unit_finrank_numberField (hS : S.Finite) :
    finrank ℤ (Additive ↥(S.unit K)) = NumberField.Units.rank K + Nat.card S := by
  have := hS.fintype
  have hfin := S.unit_moduleFinite hS
  have key := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker (S.unitValuationₗ))
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (S.unitValuationₗ)),
    S.finrank_range_unitValuationₗ hS, S.finrank_ker_unitValuationₗ] at key
  omega

/-!
### A fundamental system of `S`-units
-/

/-- Torsion in a commutative group and torsion in the `ℤ`-module it becomes are the same thing.
⚠ Mathlib has `Submodule.torsion_int` for the subgroups but not this membership form. -/
theorem _root_.Submodule.ofMul_mem_torsion_int_iff {G : Type*} [CommGroup G] {g : G} :
    Additive.ofMul g ∈ Submodule.torsion ℤ (Additive G) ↔ g ∈ CommGroup.torsion G := by
  rw [← Submodule.mem_toAddSubgroup, Submodule.torsion_int, AddCommGroup.mem_torsion,
    isOfFinAddOrder_ofMul_iff, CommGroup.mem_torsion]

/-- **A fundamental system of `S`-units.** There are `Units.rank K + |S|` of them, and every
`S`-unit is a root of unity times a product of their integer powers, with the exponents uniquely
determined. This is the `S`-analogue of Mathlib's
`NumberField.Units.exist_unique_eq_mul_prod`; see `Set.exists_unit_fundSystem'` for the form in
which the root of unity is unique as well. -/
theorem _root_.Set.exists_unit_fundSystem (hS : S.Finite) :
    ∃ ε : Fin (NumberField.Units.rank K + Nat.card S) → ↥(S.unit K),
      ∀ x : ↥(S.unit K), ∃! e : Fin (NumberField.Units.rank K + Nat.card S) → ℤ,
        ∃ ζ ∈ CommGroup.torsion ↥(S.unit K), x = ζ * ∏ i, ε i ^ e i := by
  classical
  have hfin := S.unit_moduleFinite hS
  have hrank : finrank ℤ ((Additive ↥(S.unit K)) ⧸ Submodule.torsion ℤ (Additive ↥(S.unit K)))
      = NumberField.Units.rank K + Nat.card S := by
    rw [finrank_quotient_eq_of_le_torsion (le_refl _), S.unit_finrank_numberField hS]
  let b : Basis (Fin (NumberField.Units.rank K + Nat.card S)) ℤ
      ((Additive ↥(S.unit K)) ⧸ Submodule.torsion ℤ (Additive ↥(S.unit K))) :=
    Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, hrank, Fintype.card_fin]))
  choose m hm using fun i => Submodule.mkQ_surjective
    (Submodule.torsion ℤ (Additive ↥(S.unit K))) (b i)
  have hzero : ∀ g : ↥(S.unit K), g ∈ CommGroup.torsion ↥(S.unit K) →
      (Submodule.torsion ℤ (Additive ↥(S.unit K))).mkQ (Additive.ofMul g) = 0 := fun g hg => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.ofMul_mem_torsion_int_iff.mpr hg
  refine ⟨fun i => Additive.toMul (m i), fun x => ?_⟩
  have hprod : ∀ e : Fin (NumberField.Units.rank K + Nat.card S) → ℤ,
      (Submodule.torsion ℤ (Additive ↥(S.unit K))).mkQ
        (Additive.ofMul (∏ i, (Additive.toMul (m i)) ^ e i)) = ∑ i, e i • b i := by
    intro e
    rw [ofMul_prod, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [ofMul_zpow, map_zsmul, ofMul_toMul, hm]
  refine ⟨b.repr ((Submodule.torsion ℤ (Additive ↥(S.unit K))).mkQ (Additive.ofMul x)), ?_, ?_⟩
  · refine ⟨x * (∏ i, (Additive.toMul (m i)) ^
      (b.repr ((Submodule.torsion ℤ (Additive ↥(S.unit K))).mkQ (Additive.ofMul x)) i))⁻¹, ?_, ?_⟩
    · rw [← Submodule.ofMul_mem_torsion_int_iff, ofMul_mul, ofMul_inv,
        ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_add, map_neg, hprod,
        b.sum_repr, add_neg_cancel]
    · rw [inv_mul_cancel_right]
  · rintro e ⟨ζ, hζ, hx⟩
    have key : (Submodule.torsion ℤ (Additive ↥(S.unit K))).mkQ (Additive.ofMul x)
        = ∑ i, e i • b i := by
      rw [hx, ofMul_mul, map_add, hprod, hzero ζ hζ, zero_add]
    rw [key, b.repr_sum_self]

/-- **A fundamental system of `S`-units, with the pair unique.** The root of unity is determined
by the exponents, so `Set.exists_unit_fundSystem` upgrades to the shape of Mathlib's
`NumberField.Units.exist_unique_eq_mul_prod`. -/
theorem _root_.Set.exists_unit_fundSystem' (hS : S.Finite) :
    ∃ ε : Fin (NumberField.Units.rank K + Nat.card S) → ↥(S.unit K),
      ∀ x : ↥(S.unit K),
        ∃! ζe : CommGroup.torsion ↥(S.unit K) ×
            (Fin (NumberField.Units.rank K + Nat.card S) → ℤ),
          x = (ζe.1 : ↥(S.unit K)) * ∏ i, ε i ^ ζe.2 i := by
  obtain ⟨ε, hε⟩ := S.exists_unit_fundSystem hS
  refine ⟨ε, fun x => ?_⟩
  obtain ⟨e, ⟨ζ, hζ, hx⟩, huniq⟩ := hε x
  refine ⟨⟨⟨ζ, hζ⟩, e⟩, hx, ?_⟩
  rintro ⟨⟨ζ', hζ'⟩, e'⟩ hx'
  have he' : e' = e := huniq e' ⟨ζ', hζ', hx'⟩
  subst he'
  have hzz : (ζ' : ↥(S.unit K)) = ζ := mul_right_cancel (hx'.symm.trans hx)
  simp [hzz]

/-!
### Acceptance criteria
-/

section Examples

variable {K : Type*} [Field K] [NumberField K]

/-- **Conformance with Dirichlet's unit theorem.** At `S = ∅` the rank formula is Mathlib's
`NumberField.Units.finrank_eq`, which is also what the proof consumes at the left-hand end of the
sequence. -/
example :
    finrank ℤ (Additive ↥((∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K))
      = NumberField.Units.rank K := by
  rw [Set.unit_finrank_numberField _ Set.finite_empty]
  simp

/-- **Conformance with Mathlib.** At `S = ∅` the inclusion of `(𝓞 K)ˣ` into the `S`-units is
onto, which is `IsDedekindDomain.integer_empty` and `Set.unitEquivUnitsInteger` read on
elements. -/
example (x : ↥((∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unit K)) :
    ∃ u : (𝓞 K)ˣ, (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).unitOfUnits u = x := by
  obtain ⟨u, hu⟩ := Set.mem_unit_empty_iff.mp x.2
  exact ⟨u, Subtype.ext (Units.ext hu)⟩

/-- **Acceptance test: each new place raises the rank by exactly one.** This is the content of the
formula that no amount of bookkeeping supplies: the `S`-units gain one free generator per place,
and never two, because the image of the valuation map is of finite index and not merely of
positive rank. -/
example (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    finrank ℤ (Additive ↥((insert v S).unit K))
      = finrank ℤ (Additive ↥(S.unit K)) + 1 := by
  rw [Set.unit_finrank_numberField _ (hS.insert v), Set.unit_finrank_numberField _ hS,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hv hS, add_assoc]

/-- **Acceptance test: the `S`-units are finitely generated as a group.** Mathlib's
`Mathlib/RingTheory/DedekindDomain/SInteger.lean` records this as an open TODO beside the `S`-unit
theorem itself. -/
example (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Group.FG ↥(S.unit K) := S.unit_fg hS

end Examples

end NumberField
