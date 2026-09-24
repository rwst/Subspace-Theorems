/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlacesOverFinite
public import DiophantineApproximation.PlacesOverInfinite

-- Used only inside proofs.
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Above every place of a number field there are finitely many, and at least one

For an extension `F / K` of number fields and a place `v` of `K` — infinite or finite — the set
of absolute values of `F` lying over `v` is finite and nonempty. Both halves rest on the
classification of Layer 0.1: the absolute values over an infinite place are the infinite places
of `F` above it, and those over a finite place are the `(e f)⁻¹`-th powers of the finite places
of `F` above it.

## Main results

* `NumberField.finite_nonempty_setOf_liesOver`: the milestone, both halves at once, for a place
  given as an absolute value with `IsInfinitePlace v ∨ IsFinitePlace v`.
* `NumberField.finite_setOf_liesOver_infinitePlace`, `NumberField.finite_setOf_liesOver_finitePlace`
  and the two `exists_liesOver_*` theorems: the four statements it is assembled from.
* `NumberField.isNonarchimedean_iff_isFinitePlace`: `w` is nonarchimedean exactly when `v` is
  finite.
* `NumberField.exists_liesOver_of_liesOver`: every `w` over `v` extends to every further number
  field. These two are what the roadmap asks for beside the classification.

## Implementation notes

⚠ The hypothesis `IsInfinitePlace v ∨ IsFinitePlace v` is not decoration: an absolute value of `K`
that is neither, for instance `(|·|_v) ^ (1/2)`, still has absolute values over it — its own
square roots of the places over `v` — and the set is still finite and nonempty, but nothing in
this file proves that, because the classification is stated for places.

At a finite place the fibre is *not* a set of finite places of `F`: its members are roots of
them. Nonemptiness therefore goes through `AbsoluteValue.nonarchRpow`, which Mathlib does not
have, and it is exactly the reason that construction exists.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.3.

This is Layer 0.1 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- Over an infinite place of `K` there are finitely many absolute values of `F`: they are among
the infinite places of `F`, of which there are finitely many. -/
theorem finite_setOf_liesOver_infinitePlace (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  refine Set.Finite.subset (Set.finite_range (fun w' : InfinitePlace F => w'.1)) ?_
  intro w hw
  have : w.LiesOver v.1 := hw
  obtain ⟨w', hw'⟩ := exists_infinitePlace_eq_of_liesOver v w
  exact ⟨w', hw'⟩

/-- Over a finite place of `K` there are finitely many absolute values of `F`: each is the
`(e f)⁻¹`-th power of the place of a prime of `𝓞 F` above the prime of `v`, and there are finitely
many such primes. -/
theorem finite_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  have hexp : ∀ P : HeightOneSpectrum (𝓞 F),
      (0 : ℝ) < (((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹ := by
    intro P
    refine inv_pos.mpr ?_
    exact_mod_cast Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K))
      (P.asIdeal.inertiaDeg_pos (𝓞 K))
  set Φ : HeightOneSpectrum (𝓞 F) → AbsoluteValue F ℝ := fun P =>
    AbsoluteValue.nonarchRpow (FinitePlace.isNonarchimedean_mk P) (hexp P) with hΦ
  set S : Set (HeightOneSpectrum (𝓞 F)) :=
    {P | P.asIdeal.LiesOver v.maximalIdeal.asIdeal} with hS
  have hSfin : S.Finite := by
    refine Set.Finite.subset
      ((Algebra.QuasiFinite.finite_primesOver (S := 𝓞 F) v.maximalIdeal.asIdeal).preimage
        (Function.Injective.injOn HeightOneSpectrum.asIdeal_injective)) ?_
    exact fun P hP => ⟨P.isPrime, hP⟩
  refine Set.Finite.subset (hSfin.image Φ) ?_
  intro w hw
  have : w.LiesOver v.1 := hw
  obtain ⟨P, hover, hPt⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver (K := K) v w
  exact ⟨P, hover, (AbsoluteValue.ext fun y => (hPt y).symm)⟩

/-- **Layer 0.1, the fibre.** Above every place of `K` there are finitely many absolute values of
`F`, and at least one. -/
theorem finite_nonempty_setOf_liesOver (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite ∧
      {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with h | h
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp h
    refine ⟨finite_setOf_liesOver_infinitePlace v', ?_⟩
    obtain ⟨w, hw⟩ := exists_liesOver_infinitePlace (F := F) v'
    exact ⟨w.1, hw⟩
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp h
    exact ⟨finite_setOf_liesOver_finitePlace v', exists_liesOver_finitePlace (F := F) v'⟩

/-- **An infinite place and a finite place never have the same underlying absolute value.** The
infinite one takes the value `2` at `2`, the finite one at most `1`. -/
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.1 ≠ u.1 := by
  intro hcon
  have h1 : v.1 (((2 : ℕ) : K)) = 2 := by
    rw [← NumberField.InfinitePlace.coe_apply, NumberField.InfinitePlace.map_natCast]
    norm_num
  have h2 : u.1 (((2 : ℕ) : K)) ≤ 1 := by
    rw [← NumberField.FinitePlace.coe_apply,
      show (((2 : ℕ) : K)) = (((2 : ℤ) : K)) by push_cast; ring]
    exact NumberField.FinitePlace.apply_intCast_le_one u 2
  rw [hcon] at h1
  linarith

/-- **An absolute value over a place is nonarchimedean exactly when the place is finite.** -/
theorem isNonarchimedean_iff_isFinitePlace (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean (w : F → ℝ) ↔ IsFinitePlace v := by
  refine ⟨fun hna => ?_, fun h => ?_⟩
  · rcases hv with h | h
    · exfalso
      obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp h
      obtain ⟨φ, hφ⟩ := isInfinitePlace_of_liesOver v' w
      have h2 : w ((1 : F) + 1) = 2 := by
        rw [← hφ, place_apply]
        rw [show ((1 : F) + 1) = ((2 : ℕ) : F) by push_cast; ring, map_natCast]
        norm_num
      have h1 : w (1 : F) = 1 := w.map_one
      have := hna (1 : F) 1
      rw [h2, h1] at this
      norm_num at this
    · exact h
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp h
    exact isNonarchimedean_of_liesOver_finitePlace v' w

/-- **Every absolute value over a place extends further.** If `w` of `F` lies over a place of `K`,
then some absolute value of any number field `F'` over `F` lies over `w`. -/
theorem exists_liesOver_of_liesOver {F' : Type*} [Field F'] [NumberField F'] [Algebra F F']
    (v : AbsoluteValue K ℝ) (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ)
    [w.LiesOver v] : ∃ w' : AbsoluteValue F' ℝ, w'.LiesOver w := by
  rcases hv with h | h
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp h
    obtain ⟨w'', hw''⟩ := exists_infinitePlace_eq_of_liesOver v' w
    obtain ⟨u, hu⟩ := exists_liesOver_infinitePlace (F := F') w''
    exact ⟨u.1, hw'' ▸ hu⟩
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp h
    obtain ⟨P, t, ht, -, hPt⟩ := exists_finitePlace_rpow_eq_of_liesOver (K := K) v' w
    obtain ⟨w', hw'⟩ := exists_apply_algebraMap_eq_mk_rpow (F := F') P ht
    refine ⟨w', ⟨AbsoluteValue.ext fun u => ?_⟩⟩
    rw [show (w'.under F) u = w' (algebraMap F F' u) from rfl, hw' u, ← hPt u]

end NumberField

section Examples

/-! ### Acceptance criteria -/

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **The fibre over `v` in the trivial extension is `{v}`.** -/
example (v w : AbsoluteValue K ℝ) [w.LiesOver v] : w = v := by
  have h := AbsoluteValue.LiesOver.under_eq w v
  refine AbsoluteValue.ext fun x => ?_
  rw [← h]
  rfl

/-- **Rejection test: the exponent of Layer 0.1 cannot be dropped.** The place of a prime `𝔓` of
`𝓞 F` restricts to the place of the prime below it only when `e f = 1`; at a ramified prime, or at
one of inertia degree above one, `FinitePlace.mk 𝔓` does **not** lie over `v`, so a statement
asking for an absolute value over `v` to be a finite place of `F` would be false. -/
example (v : FinitePlace K) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver v.maximalIdeal.asIdeal]
    (h : P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) ≠ 1) :
    ¬ (FinitePlace.mk P).1.LiesOver v.1 := by
  intro hlo
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
  have hzK0 : ((z : 𝓞 K) : K) ≠ 0 := fun hh => hz0 (by exact_mod_cast hh)
  have hb0 : 0 < FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) := FinitePlace.pos_iff.mpr hzK0
  have hb1 : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) < 1 :=
    (FinitePlace.mk_lt_one_iff_mem _ z).mpr hzmem
  have hef : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
    Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
  have key : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^
      (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K))
      = FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) := by
    have hloapp : ((FinitePlace.mk P).1) (algebraMap K F ((z : 𝓞 K) : K))
        = v.1 ((z : 𝓞 K) : K) := AbsoluteValue.apply_algebraMap_of_liesOver (v := v.1) _ _
    rw [← FinitePlace.mk_algebraMap v.maximalIdeal P ((z : 𝓞 K) : K),
      FinitePlace.mk_maximalIdeal]
    exact hloapp
  have hlt : FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^
      (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K))
      < FinitePlace.mk v.maximalIdeal ((z : 𝓞 K) : K) ^ 1 :=
    pow_lt_pow_right_of_lt_one₀ hb0 hb1 (by omega)
  rw [key, pow_one] at hlt
  exact lt_irrefl _ hlt

/-- The positive counterpart: at an unramified prime of inertia degree one the place of `𝔓` does
lie over `v`, and there the absolute value of Layer 0.1 is a finite place of `F` on the nose. -/
example (v : FinitePlace K) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver v.maximalIdeal.asIdeal]
    (h : P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) = 1) :
    (FinitePlace.mk P).1.LiesOver v.1 := by
  refine ⟨AbsoluteValue.ext fun u => ?_⟩
  rw [show ((FinitePlace.mk P).1.under K) u = FinitePlace.mk P (algebraMap K F u) from rfl,
    FinitePlace.mk_algebraMap v.maximalIdeal P u, h, pow_one, FinitePlace.mk_maximalIdeal]
  rfl

/-- **An absolute value over an infinite place is archimedean**, on the nose: it sends `2` to `2`.
This is the content of `isNonarchimedean_iff_isFinitePlace` at a concrete point. -/
example (v : InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : w ((1 : F) + 1) = 2 := by
  obtain ⟨φ, hφ⟩ := isInfinitePlace_of_liesOver v w
  rw [← hφ, place_apply, show ((1 : F) + 1) = ((2 : ℕ) : F) by push_cast; ring, map_natCast]
  norm_num

end Examples
