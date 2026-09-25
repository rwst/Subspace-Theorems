/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnit

-- Used only inside proofs.
import DiophantineApproximation.PlacesOverFinite

/-!
# `S`-integers and `S`-units in an extension

For an extension `L / K` of number fields and a set `S` of primes of `𝓞 K`, take for `L` the
primes of `𝓞 L` lying over a prime of `S`, `HeightOneSpectrum.under (𝓞 K) ⁻¹' S`. An element of
`K` is an `S`-integer exactly when its image in `L` is an integer for that set, and likewise for
units; and the set is finite when `S` is. This is the passage to an extension that Layer 8.3 left
to Layer 8.4: a binary form over `K` is a product of linear forms only over a finite extension,
and its equation is solved there.

## Main results

* `NumberField.finite_preimage_under`: over a finite set of primes lie finitely many.
* `NumberField.algebraMap_mem_integer_iff`, `NumberField.map_mem_unit_iff`: `x` is an `S`-integer
  (an `S`-unit) exactly when its image is one for the primes above `S`.

## Implementation notes

⚠ **Both directions are used**, and the converse is the one that needs a prime above every prime:
Layer 8.4 descends an `L`-unit that happens to lie in `K` back to an `S`-unit of `K`. Each
direction is `FinitePlace.mk_algebraMap` — the place of `𝔓` restricted to `K` is the `e f`-th
power of the place below — and an absolute value whose positive power is at most `1` (is `1`) is
itself at most `1` (is `1`). No ramification index is computed, only its positivity.

This is part of Layer 8.4 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- **Over a finite set of primes of `𝓞 K` lie finitely many primes of `𝓞 L`.** -/
theorem finite_preimage_under {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (HeightOneSpectrum.under (𝓞 K) ⁻¹' S : Set (HeightOneSpectrum (𝓞 L))).Finite := by
  refine (hS.biUnion fun v _ ↦ (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (HeightOneSpectrum.asIdeal_injective.injOn)).subset fun P hP ↦ ?_
  exact Set.mem_biUnion hP ⟨P.isPrime, ⟨rfl⟩⟩

omit [NumberField K] [NumberField L] in
/-- Above every prime of `𝓞 K` lies a prime of `𝓞 L`. -/
theorem exists_under_eq (v : HeightOneSpectrum (𝓞 K)) :
    ∃ P : HeightOneSpectrum (𝓞 L), P.under (𝓞 K) = v := by
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 L)))
  have hQbot : Q ≠ ⊥ := fun h => v.ne_bot (by
    rw [hQover.over, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))])
  exact ⟨⟨Q, hQprime, hQbot⟩, HeightOneSpectrum.ext hQover.over.symm⟩

variable {L}

/-- Restricted to `K`, the place of a prime of `𝓞 L` is a positive power of the place below
it. -/
theorem exists_mk_algebraMap_eq_pow (P : HeightOneSpectrum (𝓞 L)) :
    ∃ n ≠ 0, ∀ x : K,
      FinitePlace.mk P (algebraMap K L x) = FinitePlace.mk (P.under (𝓞 K)) x ^ n := by
  have : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal := ⟨rfl⟩
  exact ⟨_, (Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K))
    (P.asIdeal.inertiaDeg_pos (𝓞 K))).ne', FinitePlace.mk_algebraMap _ P⟩

/-- **An element of `K` is an `S`-integer exactly when its image in `L` is an integer for the
primes above `S`.** -/
theorem algebraMap_mem_integer_iff {S : Set (HeightOneSpectrum (𝓞 K))} {x : K} :
    algebraMap K L x ∈ ((HeightOneSpectrum.under (𝓞 K) :
      HeightOneSpectrum (𝓞 L) → _) ⁻¹' S).integer L ↔ x ∈ S.integer K := by
  simp only [Set.mem_integer_iff_finitePlace]
  constructor
  · intro h v hv
    obtain ⟨P, rfl⟩ := exists_under_eq L v
    obtain ⟨n, hn, hP⟩ := exists_mk_algebraMap_eq_pow (K := K) P
    have := h P hv
    rwa [hP, pow_le_one_iff_of_nonneg (apply_nonneg _ _) hn] at this
  · intro h P hP
    obtain ⟨n, -, hP'⟩ := exists_mk_algebraMap_eq_pow (K := K) P
    rw [hP']
    exact pow_le_one₀ (apply_nonneg _ _) (h _ hP)

/-- **An element of `Kˣ` is an `S`-unit exactly when its image in `Lˣ` is a unit for the primes
above `S`.** -/
theorem map_mem_unit_iff {S : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ} :
    Units.map (algebraMap K L : K →* L) u ∈ ((HeightOneSpectrum.under (𝓞 K) :
      HeightOneSpectrum (𝓞 L) → _) ⁻¹' S).unit L ↔ u ∈ S.unit K := by
  simp only [Set.mem_unit_iff_finitePlace, Units.coe_map, MonoidHom.coe_ofClass]
  constructor
  · intro h v hv
    obtain ⟨P, rfl⟩ := exists_under_eq L v
    obtain ⟨n, hn, hP⟩ := exists_mk_algebraMap_eq_pow (K := K) P
    have := h P hv
    rwa [hP, pow_eq_one_iff_of_nonneg (apply_nonneg _ _) hn] at this
  · intro h P hP
    obtain ⟨n, -, hP'⟩ := exists_mk_algebraMap_eq_pow (K := K) P
    rw [hP', h _ hP, one_pow]

end NumberField
