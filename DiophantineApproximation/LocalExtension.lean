/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlacesOver

-- Used only inside proofs.
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The local extension formula

Let `F / K` be an extension of number fields and `v` a place of `K`. The places of `F` above `v`
carry the degree `[F : K]` between them, and the formula that says so is *local*: for `y` in the
base field,

```text
∏ 𝔚 above 𝔳, 𝔚 y ^ 𝔚.mult = (𝔳 y ^ 𝔳.mult) ^ [F : K]   (infinite places)
∏ 𝔚 above 𝔳, 𝔚 y          = 𝔳 y ^ [F : K]              (finite places)
```

Both are the multiplicative reading of an additive identity Mathlib already has:
`Ideal.sum_ramification_inertia_eq_finrank` at a finite place and
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` at an infinite one. Mathlib states neither
multiplicatively, and its per-place finite formula is stated for prime ideals rather than for
places, with a TODO asking for the restatement; that restatement is
`NumberField.FinitePlace.apply_algebraMap` below.

⚠ **`NumberField.InfinitePlace.inertiaDeg` is the local degree, not the residue degree.** It is
`[F_w : K_v]`, which is `1` or `2`; at a finite place `Ideal.inertiaDeg` is the residue degree `f`
alone and the local degree is `e f`. The quantity the two halves share is the **local degree**,
called `NumberField.FinitePlace.localDegree` here and read off Mathlib on the infinite side. The
two sums are then the same statement: local degrees above `v` add up to `[F : K]`.

⚠ **`NumberField.FinitePlace.LiesOver` is not `AbsoluteValue.LiesOver`.** A finite place of `F`
lies over a finite place of `K` when the *primes* do; it restricts to `v` on the nose only when
its local degree `e f` is `1`. That is `liesOver_val_iff_localDegree_eq_one`, and it is the
reason Layer 0.1 classifies the absolute values over `v` as roots of finite places. At the
infinite places there is no such gap: Mathlib's `InfinitePlace.LiesOver` *is* the restriction
condition, and the exponent there lives in `mult`, not in the place.

## Main results

* `NumberField.FinitePlace.prod_apply_algebraMap` and
  `NumberField.InfinitePlace.prod_apply_algebraMap_pow_mult`: the milestone, both halves.
* `NumberField.FinitePlace.sum_localDegree` and `NumberField.InfinitePlace.sum_mult`: the additive
  identities they rest on, `∑ e f = [F : K]` and `∑ mult 𝔚 = mult 𝔳 * [F : K]`.
* `NumberField.FinitePlace.apply_algebraMap`: the per-place local extension formula at a finite
  place, `𝔚 y = 𝔳 y ^ (e f)`, which is Mathlib's
  `FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` restated for places as its own TODO
  asks.
* `NumberField.FinitePlace.LiesOver`, `localDegree`, `placesOver`, `placesOverFinset` and
  `liesOver_val_iff_localDegree_eq_one`: the ramification vocabulary for finite places that
  Mathlib lacks, on the scale this layer needs.
* `NumberField.FinitePlace.nonempty_placesOver`, `finite_placesOver` and their infinite
  counterparts: the index set of the products is finite and nonempty.

## Implementation notes

⚠ **Mathlib has ramification theory for infinite places and none for finite ones.**
`InfinitePlace` carries `LiesOver`, `comap`, `IsUnramified`, `placesOver`, a local degree and the
count `sum_inertiaDeg_eq_finrank`; `FinitePlace` carries none of it. So the infinite half here is
three lines — `mult w = mult v * [F_w : K_v]` is `InfinitePlace.mult_mul_finrank` — and the work
on the finite side is the vocabulary: `LiesOver`, `localDegree`, `placesOver`, its finiteness and
nonemptiness, and the transfer of Mathlib's sum over `Ideal.primesOver` to a sum over places.

The `mult v` on the right of the infinite formula is what makes one statement out of two. Above a
*complex* `v` no place is ramified — ramified means complex over real — so every multiplicity
upstairs is `2` and the bare count is the degree; above a real `v` the multiplicities are mixed.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Corollary 1.3.2.

This is the second half of Layer 0.2 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField Module

namespace NumberField.FinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- A finite place of `F` **lies over** a finite place of `K` when its prime lies over the prime
of `v`. -/
protected abbrev LiesOver (w : FinitePlace F) (v : FinitePlace K) : Prop :=
  w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal

variable (K) in
/-- The local degree `e f` of a finite place of `F` over the base field `K`. -/
@[expose] noncomputable def localDegree (w : FinitePlace F) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx (𝓞 K) * w.maximalIdeal.asIdeal.inertiaDeg (𝓞 K)

theorem localDegree_pos (w : FinitePlace F) : 0 < w.localDegree K :=
  Nat.mul_pos (w.maximalIdeal.asIdeal.ramificationIdx_pos (𝓞 K))
    (w.maximalIdeal.asIdeal.inertiaDeg_pos (𝓞 K))

/-- **The local extension formula at a finite place.** -/
theorem apply_algebraMap (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] (y : K) :
    w (algebraMap K F y) = v y ^ w.localDegree K := by
  conv_lhs => rw [← w.mk_maximalIdeal]
  rw [FinitePlace.mk_algebraMap v.maximalIdeal w.maximalIdeal y, v.mk_maximalIdeal]
  rfl

variable (F) in
/-- The finite places of `F` that lie above a finite place of `K`. -/
def placesOver (v : FinitePlace K) : Set (FinitePlace F) := {w | w.LiesOver v}

theorem mem_placesOver {v : FinitePlace K} {w : FinitePlace F} :
    w ∈ placesOver F v ↔ w.LiesOver v := Iff.rfl

variable (F) in
/-- Only finitely many finite places of `F` lie above a finite place of `K`. -/
theorem finite_placesOver (v : FinitePlace K) : (placesOver F v).Finite := by
  refine Set.Finite.subset
    ((Algebra.QuasiFinite.finite_primesOver (S := 𝓞 F) v.maximalIdeal.asIdeal).preimage
      (Function.Injective.injOn
        (HeightOneSpectrum.asIdeal_injective.comp FinitePlace.maximalIdeal_injective))) ?_
  exact fun w hw => ⟨w.maximalIdeal.isPrime, hw⟩

variable (F) in
/-- The finite places of `F` above a finite place of `K`, as a `Finset`. -/
noncomputable def placesOverFinset (v : FinitePlace K) : Finset (FinitePlace F) :=
  (finite_placesOver F v).toFinset

@[simp] theorem mem_placesOverFinset {v : FinitePlace K} {w : FinitePlace F} :
    w ∈ placesOverFinset F v ↔ w.LiesOver v := by
  rw [placesOverFinset, Set.Finite.mem_toFinset, mem_placesOver]

variable (F) in
/-- **Above every finite place of `K` there is a finite place of `F`.** -/
theorem nonempty_placesOver (v : FinitePlace K) : (placesOver F v).Nonempty := by
  obtain ⟨Q, hQprime, hQover⟩ := Ideal.nonempty_primesOver (S := 𝓞 F) v.maximalIdeal.asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.maximalIdeal.ne_bot ⟨hQprime, hQover⟩
  refine ⟨FinitePlace.mk ⟨Q, hQprime, hQ⟩, ?_⟩
  change (FinitePlace.mk _).maximalIdeal.asIdeal.LiesOver _
  rw [FinitePlace.maximalIdeal_mk]
  exact hQover

/-- **`FinitePlace.LiesOver` is not `AbsoluteValue.LiesOver`.** A finite place of `F` above `v`
restricts to `v` itself exactly when its local degree is `1`; otherwise it restricts to a proper
power of `v`, which is a different absolute value. This is why Layer 0.1 classifies the absolute
values over `v` as *roots* of finite places rather than as finite places. -/
theorem liesOver_val_iff_localDegree_eq_one (w : FinitePlace F) (v : FinitePlace K)
    [w.LiesOver v] : w.1.LiesOver v.1 ↔ w.localDegree K = 1 := by
  constructor
  · intro hlo
    obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    have hzK0 : ((z : 𝓞 K) : K) ≠ 0 := fun hh => hz0 (by exact_mod_cast hh)
    have hb0 : 0 < v ((z : 𝓞 K) : K) := FinitePlace.pos_iff.mpr hzK0
    have hb1 : v ((z : 𝓞 K) : K) < 1 := by
      rw [← v.mk_maximalIdeal]
      exact (FinitePlace.mk_lt_one_iff_mem _ z).mpr hzmem
    have hres : w (algebraMap K F ((z : 𝓞 K) : K)) = v ((z : 𝓞 K) : K) :=
      AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1) w.1 _
    rw [apply_algebraMap w v] at hres
    by_contra hne
    have hlt : v ((z : 𝓞 K) : K) ^ w.localDegree K < v ((z : 𝓞 K) : K) ^ 1 :=
      pow_lt_pow_right_of_lt_one₀ hb0 hb1 (by have := w.localDegree_pos (K := K); omega)
    rw [hres, pow_one] at hlt
    exact lt_irrefl _ hlt
  · intro h
    refine ⟨AbsoluteValue.ext fun y => ?_⟩
    change w (algebraMap K F y) = v y
    rw [apply_algebraMap w v, h, pow_one]

/-- **The fundamental identity of ramification and inertia**, read through finite places: the
local degrees of the finite places of `F` above `v` sum to `[F : K]`. -/
theorem sum_localDegree (v : FinitePlace K) :
    ∑ w ∈ placesOverFinset F v, w.localDegree K = finrank K F := by
  have : Fintype (v.maximalIdeal.asIdeal.primesOver (𝓞 F)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 F) v.maximalIdeal.asIdeal).fintype
  have : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F,
    ← Ideal.sum_ramification_inertia_eq_finrank v.maximalIdeal.asIdeal (𝓞 F)]
  refine Finset.sum_bij (fun w hw => (⟨w.maximalIdeal.asIdeal,
      w.maximalIdeal.isPrime, mem_placesOverFinset.mp hw⟩ :
      v.maximalIdeal.asIdeal.primesOver (𝓞 F)))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro w₁ h₁ w₂ h₂ h
    exact FinitePlace.maximalIdeal_injective
      (HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h))
  · intro q _
    have hq : (q : Ideal (𝓞 F)) ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.maximalIdeal.ne_bot q.2
    refine ⟨FinitePlace.mk ⟨(q : Ideal (𝓞 F)), q.2.1, hq⟩, ?_, ?_⟩
    · rw [mem_placesOverFinset]
      change (FinitePlace.mk _).maximalIdeal.asIdeal.LiesOver _
      rw [FinitePlace.maximalIdeal_mk]
      exact q.2.2
    · refine Subtype.ext ?_
      change (FinitePlace.mk _).maximalIdeal.asIdeal = _
      rw [FinitePlace.maximalIdeal_mk]
  · intro w hw
    rfl

/-- **The local extension formula at a finite place, in product form.** -/
theorem prod_apply_algebraMap (v : FinitePlace K) (y : K) :
    ∏ w ∈ placesOverFinset F v, w (algebraMap K F y) = v y ^ finrank K F := by
  rw [Finset.prod_congr rfl (fun w hw => by
      have : w.LiesOver v := mem_placesOverFinset.mp hw
      exact apply_algebraMap w v y), Finset.prod_pow_eq_pow_sum, sum_localDegree]

end NumberField.FinitePlace

namespace NumberField.InfinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

variable (F) in
omit [NumberField K] in
/-- Only finitely many infinite places of `F` lie above an infinite place of `K` — there are only
finitely many infinite places at all. -/
theorem finite_placesOver (v : InfinitePlace K) : (placesOver F v).Finite := Set.toFinite _

variable (F) in
/-- The infinite places of `F` above an infinite place of `K`, as a `Finset`. -/
noncomputable def placesOverFinset (v : InfinitePlace K) : Finset (InfinitePlace F) :=
  (finite_placesOver F v).toFinset

omit [NumberField K] in
@[simp] theorem mem_placesOverFinset {v : InfinitePlace K} {w : InfinitePlace F} :
    w ∈ placesOverFinset F v ↔ w.LiesOver v := by
  rw [placesOverFinset, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- **The fundamental identity at the infinite places.** The multiplicities of the infinite
places of `F` above `v` sum to `v.mult * [F : K]`. This is Mathlib's
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` — the local degrees `[F_w : K_v]` of the
places above `v` sum to `[F : K]` — weighted by `mult v` through `mult_mul_finrank`. -/
theorem sum_mult (v : InfinitePlace K) :
    ∑ w ∈ placesOverFinset F v, w.mult = v.mult * finrank K F := by
  classical
  have hset : placesOverFinset F v = (placesOver F v).toFinset := by
    ext w
    rw [mem_placesOverFinset, Set.mem_toFinset]
    exact Iff.rfl
  rw [hset, ← sum_inertiaDeg_eq_finrank K F v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have : w.LiesOver v := by rw [Set.mem_toFinset] at hw; exact hw
  rw [inertiaDeg_eq_finrank, mult_mul_finrank]

/-- **The local extension formula at the infinite places, in product form.** -/
theorem prod_apply_algebraMap_pow_mult (v : InfinitePlace K) (y : K) :
    ∏ w ∈ placesOverFinset F v, w (algebraMap K F y) ^ w.mult
      = (v y ^ v.mult) ^ finrank K F := by
  rw [Finset.prod_congr rfl (fun w hw => by
      have : w.LiesOver v := mem_placesOverFinset.mp hw
      rw [comp_of_comap_eq (LiesOver.comap_eq w v) y]),
    Finset.prod_pow_eq_pow_sum, sum_mult, pow_mul]

end NumberField.InfinitePlace

section Examples

/-! ### Acceptance criteria -/

open NumberField.FinitePlace NumberField.InfinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **The degenerate case.** In the trivial extension the only place above `v` is `v`, of local
degree `1`, and the identity reads `1 = [K : K]`. -/
example (v : FinitePlace K) : ∑ w ∈ placesOverFinset K v, w.localDegree K = 1 := by
  rw [sum_localDegree, Module.finrank_self]

/-- **Rejection test: the exponent in the finite formula cannot be dropped.** At a place of local
degree above `1` — a ramified place, or one of inertia degree above one — `w` does not restrict
to `v` but to a proper power of it, so the formula without the exponent is false. -/
example (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] (h : w.localDegree K ≠ 1) :
    ¬ w.1.LiesOver v.1 := fun hlo => h ((liesOver_val_iff_localDegree_eq_one w v).mp hlo)

/-- **The `mult` on the right is not decoration.** Above a complex place the exponent is
`2 * [F : K]`, not `[F : K]`. -/
example (v : InfinitePlace K) (hv : v.IsComplex) (y : K) :
    ∏ w ∈ placesOverFinset F v, w (algebraMap K F y) ^ w.mult = v y ^ (2 * Module.finrank K F) := by
  rw [prod_apply_algebraMap_pow_mult, hv.mult_eq_two, pow_mul]

/-- **At most `[F : K]` places lie above `v`**, because each contributes a positive local degree.
This is the count the Subspace Theorem's local factors are bounded by. -/
example (v : FinitePlace K) : (placesOverFinset F v).card ≤ Module.finrank K F := by
  rw [← sum_localDegree (F := F) v]
  simpa using Finset.card_nsmul_le_sum (placesOverFinset F v) (fun w => w.localDegree K) 1
    (fun w _ => w.localDegree_pos)

end Examples
