/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnitTheorem
public import Mathlib.RingTheory.DedekindDomain.SInteger

-- Used only inside proofs.
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Localization.Ideal

/-!
# The `S`-integers of a number field are a localization, and are principal for large `S`

Let `K` be a number field and `S` a finite set of finite places, carried as Mathlib carries it, as
a set of height-one primes of `𝓞 K`. Mathlib defines the `S`-integers `S.integer K` by the adic
valuations away from `S` and proves nothing about the ring they form. This file identifies that
ring: it is the localization of `𝓞 K` at the multiplicative set of elements *supported in `S`*,

```text
S.integerSubmonoid = {a : 𝓞 K | a ≠ 0 ∧ ∀ v ∉ S, a ∉ v},
```

hence a Dedekind domain; and it proves Bombieri–Gubler's Proposition 5.3.6, that **every finite
`S` is contained in a finite `S'` for which `S'.integer K` is a principal ideal domain**.

Both rest on the same one-line consequence of the finiteness of the class group that
`ArithmeticHeights/SUnitTheorem.lean` isolates — `NumberField.exists_mem_asIdeal_iff_eq`, a
nonzero algebraic integer lying in a given prime and in no other. It supplies the denominators
that make `S.integer K` a localization, and, applied to a representative of each ideal class, the
finitely many extra places that kill the class group.

## Main definitions

* `Set.integerSubmonoid`: the multiplicative set of elements of `𝓞 K` supported in `S`, i.e. the
  nonzero elements lying in no prime outside `S`.

## Main results

* `NumberField.isLocalization_integer`: for finite `S`, `S.integer K` is the localization of
  `𝓞 K` at `S.integerSubmonoid`.
* `NumberField.isDedekindDomain_integer`: hence a Dedekind domain.
* `NumberField.exists_finite_superset_isPrincipalIdealRing`: **Bombieri–Gubler, Proposition
  5.3.6.** Every finite `S` is contained in a finite `S'` with `S'.integer K` a principal ideal
  domain.
* `NumberField.exists_mem_integerSubmonoid`: the surjectivity half of the localization, stated on
  its own because it is what clears denominators: an element of `K` integral away from `S` becomes
  an algebraic integer after multiplication by an element supported in `S`.

## Implementation notes

⚠ **The exponents are chosen place by place, and the arithmetic is done in `ℤ`.** For `z` integral
away from `S` the denominator produced by `NumberField.exists_mem_integerSubmonoid` is
`∏_{v ∈ S} π_v ^ k_v` with `π_v` the element supported at `v` alone and `k_v` large enough to
absorb the pole of `z` at `v`. Comparing `k_v` with that pole is an inequality in `ℤᵐ⁰`, which is
awkward; the file therefore moves to `Kˣ` and to
`IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero`, whose values lie in `Multiplicative ℤ`, so
that every comparison becomes linear arithmetic over `ℤ` and `omega` closes it. ⚠ That
normalisation is Mathlib's and is the *negative* of the usual order: an element of `𝓞 K` has
non-positive value and a uniformizer has value `-1`.

⚠ **The principal ideal theorem uses no Dedekind theory of `S'.integer K`.** Only three things
enter: an ideal of a localization is the extension of its contraction
(`IsLocalization.map_under`); the extension of an ideal containing an element of the multiplicative
set is the unit ideal; and, for each ideal class of `𝓞 K`, a representative `I` whose product with
a suitable ideal is principal. Choosing one representative per class and enlarging `S` by the
finitely many primes containing a chosen nonzero element of each makes every one of those
representatives extend to the unit ideal, and the contraction of an arbitrary ideal then becomes
principal after multiplication by one of them. `NumberField.isDedekindDomain_integer` is proved
because consumers will want it, not because the argument needs it.

⚠ **No power of an ideal is taken, and the class number never appears.** The usual proof of
Proposition 5.3.6 factors a representative ideal into primes and adjoins those primes. Here it is
enough to adjoin the primes containing *one* nonzero element of the representative — the set
`{w | g ∈ w}` is finite by `Ideal.finite_factors` — because `g ∈ I` already forces the extension
of `I` to be everything.

⚠ **`S` must be finite for the localization, and is not needed for the primitive-multiple
statement.** Finiteness is used exactly once, to form the finite product of denominators; the
theorem `NumberField.exists_finite_superset_isPrincipalIdealRing` then produces a finite `S'`
because a finite union of finite sets is finite.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 5.3.6, where the `S`-integers are enlarged to a principal ideal domain, and §1.5.10,
where the `S`-integers are introduced.

This is Layer 0.3 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-!
### The multiplicative set of elements supported in `S`
-/

/-- **The elements of `𝓞 K` supported in `S`**: the nonzero algebraic integers lying in no prime
outside `S`. These are exactly the elements of `𝓞 K` that become units in the `S`-integers, and
`S.integer K` is the localization of `𝓞 K` at them. -/
def _root_.Set.integerSubmonoid : Submonoid (𝓞 K) where
  carrier := {a | a ≠ 0 ∧ ∀ v ∉ S, a ∉ v.asIdeal}
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    exact ⟨mul_ne_zero ha0 hb0, fun v hv hmem ↦
      (v.isPrime.mem_or_mem hmem).elim (ha v hv) (hb v hv)⟩
  one_mem' := ⟨one_ne_zero, fun v _ h ↦ v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩

theorem _root_.Set.mem_integerSubmonoid {a : 𝓞 K} :
    a ∈ S.integerSubmonoid ↔ a ≠ 0 ∧ ∀ v ∉ S, a ∉ v.asIdeal := Iff.rfl

theorem _root_.Set.integerSubmonoid_le_nonZeroDivisors : S.integerSubmonoid ≤ (𝓞 K)⁰ :=
  fun _ ha ↦ mem_nonZeroDivisors_of_ne_zero ha.1

/-!
### The additive form of the adic valuation

Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` takes values in
`Multiplicative ℤ`, so that `Multiplicative.toAdd` of it is an ordinary integer. Every comparison
in the denominator construction below is then linear arithmetic. ⚠ The sign is Mathlib's: an
algebraic integer has non-positive value.
-/

variable {S}

/-- The additive `v`-adic valuation of a nonzero element of `K`, in Mathlib's normalisation: an
algebraic integer has non-positive value and a uniformizer has value `-1`. -/
private noncomputable def ord (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : ℤ :=
  Multiplicative.toAdd (v.valuationOfNeZero x)

private theorem ord_mul (v : HeightOneSpectrum (𝓞 K)) (x y : Kˣ) :
    ord v (x * y) = ord v x + ord v y := by
  simp only [ord, map_mul]
  rfl

private theorem ord_pow (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) (n : ℕ) :
    ord v (x ^ n) = n * ord v x := by
  simp only [ord, map_pow]
  simp

private theorem valuation_le_one_iff_ord (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuation K (x : K) ≤ 1 ↔ ord v x ≤ 0 := by
  rw [← v.valuationOfNeZero_eq x, ← WithZero.coe_one, WithZero.coe_le_coe]
  rfl

private theorem valuation_eq_one_iff_ord (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuation K (x : K) = 1 ↔ ord v x = 0 := by
  rw [← v.valuationOfNeZero_eq x, ← WithZero.coe_one, WithZero.coe_inj]
  rfl

private theorem valuation_lt_one_iff_ord (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuation K (x : K) < 1 ↔ ord v x < 0 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, valuation_le_one_iff_ord,
    ne_eq, ne_eq, valuation_eq_one_iff_ord]

/-!
### Clearing denominators
-/

variable (S)

/-- **An element of `K` integral away from `S` becomes an algebraic integer after multiplication
by an element supported in `S`.** This is the surjectivity half of
`NumberField.isLocalization_integer`, and the only place the finiteness of `S` is used. -/
theorem exists_mem_integerSubmonoid (hS : S.Finite) {z : K} (hz : ∀ v ∉ S, v.valuation K z ≤ 1) :
    ∃ m : 𝓞 K, m ∈ S.integerSubmonoid ∧
      ∃ a : 𝓞 K, z * algebraMap (𝓞 K) K m = algebraMap (𝓞 K) K a := by
  classical
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨1, one_mem _, 0, by simp⟩
  choose π hπ0 hπ using exists_mem_asIdeal_iff_eq (K := K)
  have hπK : ∀ v, algebraMap (𝓞 K) K (π v) ≠ 0 := fun v ↦ by
    simpa using (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr (hπ0 v)
  set T := hS.toFinset with hT
  set k : HeightOneSpectrum (𝓞 K) → ℕ := fun v ↦ (ord v (Units.mk0 z hz0)).toNat with hk
  set m : 𝓞 K := ∏ v ∈ T, π v ^ k v with hm
  have hprod : ∀ (U : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K)),
      w ∉ U → (∏ v ∈ U, π v ^ k v) ∉ w.asIdeal := by
    intro U w hw
    have : (∏ v ∈ U, π v ^ k v) ∈ Ideal.primeCompl w.asIdeal :=
      Submonoid.prod_mem _ fun v hv ↦
        pow_mem (show π v ∉ w.asIdeal from fun h ↦ hw ((hπ v w).mp h ▸ hv)) _
    exact this
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero _ (hπ0 v)
  have hmS : ∀ w ∉ S, m ∉ w.asIdeal := fun w hw ↦ hprod T w (by simpa [hT] using hw)
  refine ⟨m, ⟨hm0, hmS⟩, ?_⟩
  have hint : ∀ w : HeightOneSpectrum (𝓞 K),
      w.valuation K (z * algebraMap (𝓞 K) K m) ≤ 1 := fun w ↦ ?_
  · obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
      (z * algebraMap (𝓞 K) K m) hint
    exact ⟨a, ha.symm⟩
  by_cases hwS : w ∈ S
  · have hwT : w ∈ T := by simpa [hT] using hwS
    set m' : 𝓞 K := ∏ v ∈ T.erase w, π v ^ k v with hm'
    have hm'mem : m' ∉ w.asIdeal := hprod _ w (Finset.notMem_erase w T)
    have hm'0 : m' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero _ (hπ0 v)
    have hm'K : algebraMap (𝓞 K) K m' ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hm'0
    have hsplit : π w ^ k w * m' = m := Finset.mul_prod_erase T (fun v ↦ π v ^ k v) hwT
    set uz := Units.mk0 z hz0
    set up := Units.mk0 (algebraMap (𝓞 K) K (π w)) (hπK w)
    set um' := Units.mk0 (algebraMap (𝓞 K) K m') hm'K
    have hcast : z * algebraMap (𝓞 K) K m = ((uz * up ^ k w * um' : Kˣ) : K) := by
      rw [← hsplit]
      push_cast [Units.val_mul, Units.val_pow_eq_pow_val]
      simp only [uz, up, um', Units.val_mk0]
      ring
    rw [hcast, valuation_le_one_iff_ord, ord_mul, ord_mul, ord_pow]
    have hup : ord w up ≤ -1 := by
      have h1 : w.valuation K ((up : Kˣ) : K) < 1 := by
        simp only [up, Units.val_mk0]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w (π w)).mpr ((hπ w w).mpr rfl)
      rw [valuation_lt_one_iff_ord] at h1
      omega
    have hum' : ord w um' = 0 := by
      rw [← valuation_eq_one_iff_ord]
      simpa [um'] using (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w).mpr hm'mem
    have hkz : ord w uz ≤ (k w : ℤ) := by
      simp only [hk, uz]
      exact Int.self_le_toNat _
    have := mul_le_mul_of_nonneg_left hup (Int.natCast_nonneg (k w))
    omega
  · rw [map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w).mpr (hmS w hwS),
      mul_one]
    exact hz w hwS

/-!
### The `S`-integers as a localization
-/

theorem coe_algebraMap_integer (a : 𝓞 K) :
    ((algebraMap (𝓞 K) ↥(S.integer K) a : ↥(S.integer K)) : K) = algebraMap (𝓞 K) K a := rfl

/-- **An element supported in `S` is a unit of the `S`-integers.** -/
theorem isUnit_algebraMap_integer {a : 𝓞 K} (ha : a ∈ S.integerSubmonoid) :
    IsUnit (algebraMap (𝓞 K) ↥(S.integer K) a) := by
  have h0 : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr ha.1
  have hinv : (algebraMap (𝓞 K) K a)⁻¹ ∈ S.integer K := fun v hv ↦ by
    rw [map_inv₀, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v).mpr (ha.2 v hv),
      inv_one]
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by
    simpa [coe_algebraMap_integer] using mul_inv_cancel₀ h0))

/-- **The `S`-integers are the localization of `𝓞 K` at the elements supported in `S`.** -/
theorem isLocalization_integer (hS : S.Finite) :
    IsLocalization S.integerSubmonoid ↥(S.integer K) := by
  refine (_root_.isLocalization_iff _ _).mpr ⟨fun m ↦ isUnit_algebraMap_integer S m.2, fun z ↦ ?_,
    ?_⟩
  · obtain ⟨m, hm, a, ha⟩ := exists_mem_integerSubmonoid S hS (z := (z : K)) z.2
    exact ⟨⟨a, ⟨m, hm⟩⟩, Subtype.ext (by simpa [coe_algebraMap_integer] using ha)⟩
  · intro x y h
    refine ⟨1, congrArg _ (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)⟩
    simpa [coe_algebraMap_integer] using congrArg (fun t : ↥(S.integer K) ↦ (t : K)) h

/-- **The `S`-integers are a Dedekind domain**, being a localization of one. -/
theorem isDedekindDomain_integer (hS : S.Finite) : IsDedekindDomain ↥(S.integer K) :=
  haveI := isLocalization_integer S hS
  IsLocalization.isDedekindDomain (𝓞 K) S.integerSubmonoid_le_nonZeroDivisors _

/-!
### Enlarging `S` to make the `S`-integers principal
-/

/-- Only finitely many primes contain a given nonzero algebraic integer. This is
`Ideal.finite_factors` for a principal ideal. -/
theorem finite_setOf_mem_asIdeal {g : 𝓞 K} (hg : g ≠ 0) :
    {w : HeightOneSpectrum (𝓞 K) | g ∈ w.asIdeal}.Finite := by
  have h : {w : HeightOneSpectrum (𝓞 K) | g ∈ w.asIdeal}
      = {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ Ideal.span {g}} := by
    ext w
    simp only [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  rw [h]
  exact Ideal.finite_factors (by simpa using hg)

/-- **Bombieri–Gubler, Proposition 5.3.6.** Every finite set of finite places of a number field is
contained in a finite set for which the ring of `S`-integers is a principal ideal domain. The
extra places are the primes containing a chosen nonzero element of a chosen representative of each
ideal class, finitely many because the class group is finite. -/
theorem exists_finite_superset_isPrincipalIdealRing (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) :
    ∃ S' : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧ S'.Finite ∧
      IsPrincipalIdealRing ↥(S'.integer K) := by
  classical
  choose I hI using (ClassGroup.mk0_surjective (R := 𝓞 K))
  have hIne : ∀ c : ClassGroup (𝓞 K), (I c : Ideal (𝓞 K)) ≠ ⊥ := fun c ↦
    nonZeroDivisors.ne_zero (I c).2
  choose g hgmem hgne using fun c : ClassGroup (𝓞 K) ↦
    Submodule.exists_mem_ne_zero_of_ne_bot (p := (I c : Ideal (𝓞 K))) (hIne c)
  set T : Set (HeightOneSpectrum (𝓞 K)) :=
    ⋃ c : ClassGroup (𝓞 K), {w | g c ∈ w.asIdeal} with hT
  have hTfin : T.Finite := Set.finite_iUnion fun c ↦ finite_setOf_mem_asIdeal (hgne c)
  set S' : Set (HeightOneSpectrum (𝓞 K)) := S ∪ T with hS'def
  have hS'fin : S'.Finite := hS.union hTfin
  refine ⟨S', Set.subset_union_left, hS'fin, ?_⟩
  have := isLocalization_integer S' hS'fin
  set f := algebraMap (𝓞 K) ↥(S'.integer K) with hf
  have hgM : ∀ c, g c ∈ S'.integerSubmonoid := fun c ↦
    ⟨hgne c, fun w hw hmem ↦ hw (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨c, hmem⟩))⟩
  have hmapI : ∀ c, Ideal.map f (I c : Ideal (𝓞 K)) = ⊤ := fun c ↦
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f (hgmem c))
      (isUnit_algebraMap_integer S' (hgM c))
  constructor
  intro 𝔞
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · exact ⟨0, by simp⟩
  obtain ⟨z, hz𝔞, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := 𝔞) h𝔞
  obtain ⟨⟨a, m⟩, hzm⟩ := IsLocalization.surj (M := S'.integerSubmonoid) z
  set J := 𝔞.under (𝓞 K) with hJdef
  have haJ : a ∈ J := by
    rw [hJdef, Ideal.mem_under, ← hzm]
    exact Ideal.mul_mem_right _ _ hz𝔞
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hzm
    exact hz0 ((mul_eq_zero.mp hzm).resolve_right
      (IsUnit.ne_zero (IsLocalization.map_units ↥(S'.integer K) m)))
  have hJne : J ≠ ⊥ := fun h ↦ ha0 (by simpa [h] using haJ)
  have hJmem : J ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hJne
  set c := (ClassGroup.mk0 (⟨J, hJmem⟩ : (Ideal (𝓞 K))⁰))⁻¹ with hc
  have hprin : (J * (I c : Ideal (𝓞 K))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (Submonoid.mul_mem _ hJmem (I c).2)]
    have he : (⟨J * (I c : Ideal (𝓞 K)), Submonoid.mul_mem _ hJmem (I c).2⟩ :
        (Ideal (𝓞 K))⁰) = (⟨J, hJmem⟩ : (Ideal (𝓞 K))⁰) * I c := rfl
    rw [he, map_mul, hI c, hc, mul_inv_cancel]
  obtain ⟨b, hb⟩ := hprin
  refine ⟨⟨f b, ?_⟩⟩
  calc 𝔞 = Ideal.map f J := (IsLocalization.map_under (M := S'.integerSubmonoid) _ 𝔞).symm
    _ = Ideal.map f J * ⊤ := (Ideal.mul_top _).symm
    _ = Ideal.map f J * Ideal.map f (I c : Ideal (𝓞 K)) := by rw [hmapI c]
    _ = Ideal.map f (J * (I c : Ideal (𝓞 K))) := (Ideal.map_mul f _ _).symm
    _ = Ideal.map f (Ideal.span {b}) := by rw [hb]
    _ = _ := by rw [Ideal.map_span, Set.image_singleton]

/-! ### Acceptance criteria -/

/-- **Conformance with `IsDedekindDomain.integer_univ`.** At `S = univ` the `S`-integers are all
of `K` and the multiplicative set is every nonzero element of `𝓞 K`, so the localization
statement is `K = Frac (𝓞 K)`. -/
example : (Set.univ : Set (HeightOneSpectrum (𝓞 K))).integerSubmonoid = (𝓞 K)⁰ := by
  ext a
  simp [Set.mem_integerSubmonoid]

/-- **Rejection test: `a ≠ 0` in `Set.integerSubmonoid` is not implied by the rest.** As soon as
some prime lies outside `S` the condition `∀ v ∉ S, a ∉ v` forces `a ≠ 0`; at `S = univ` it is
vacuous, so without the nonvanishing clause the carrier would contain `0` and the localization at
it would be the zero ring, not `K`. -/
example (v₀ : HeightOneSpectrum (𝓞 K)) (hv₀ : v₀ ∉ S) {a : 𝓞 K} (h : ∀ v ∉ S, a ∉ v.asIdeal) :
    a ≠ 0 := fun h0 ↦ h v₀ hv₀ (h0 ▸ Submodule.zero_mem _)

example : ∀ v ∉ (Set.univ : Set (HeightOneSpectrum (𝓞 K))), (0 : 𝓞 K) ∉ v.asIdeal :=
  fun v hv ↦ absurd (Set.mem_univ v) hv

/-- **Conformance with Layer 6.1 of `ArithmeticHeights`: a unit of `𝓞 K` is supported in every
`S`, including the empty one.** So `∅.integerSubmonoid` is the units, and `∅.integer K = ⊥` is
already its own localization. -/
example (u : (𝓞 K)ˣ) : (u : 𝓞 K) ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).integerSubmonoid :=
  ⟨u.ne_zero, fun v _ hmem ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)⟩

/-- **Conformance: the localization statement instantiates at `S = ∅`.** -/
example : IsLocalization (∅ : Set (HeightOneSpectrum (𝓞 K))).integerSubmonoid
    ↥((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K) :=
  isLocalization_integer _ Set.finite_empty

end NumberField
