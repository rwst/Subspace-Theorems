/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- Used only inside proofs.
import ArithmeticHeights.FinitePlaceIdeal
import DiophantineApproximation.FinitePlaceValues
import DiophantineApproximation.PlacesOverFinite
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Simultaneous approximation by `S`-integers

For a number field `K` and a finite set `Sfin` of finite places, every family of targets
`γ v ∈ K`, one at each infinite place and at each place of `Sfin`, is approximated by one
`Sfin`-integer `ξ`: `v (ξ + γ v) ≤ 1` at every place of `Sfin` and `w (ξ + γ w) ≤ A` at every
infinite place, with `A` depending only on `K`. This is the arithmetic input of Evertse's lemma
(`EvertseLemma.lean`), where the targets are the coefficients of the book's (7.40).

The finite conditions are met one place at a time and summed: at `v₀` the element
`-γ s a ∑_{i < N} p ^ i` has the pole of `-γ` and nothing else, where `s` is an algebraic integer
that is a unit at `v₀` and cancels the poles of `γ` elsewhere, and `a s + p = 1` with `p` in the
prime of `v₀`, so that `1 - s a ∑_{i < N} p ^ i = p ^ N`. An algebraic integer then translates the
result into a fundamental domain of `𝓞 K` in the mixed space, which moves nothing at the finite
places.

## Main results

* `NumberField.FinitePlace.exists_apply_add_le_one`: the principal part at one finite place — for
  `γ ∈ K` and a finite place `v₀`, an element `ξ` integral away from `v₀` with `v₀ (ξ + γ) ≤ 1`.
* `NumberField.FinitePlace.exists_forall_apply_add_le_one`: the same at every place of `Sfin` at
  once, `ξ` integral away from `Sfin`.
* `NumberField.exists_integer_forall_infinitePlace_add_le`: an algebraic integer moves any targets
  at the infinite places into a ball of radius `A`, depending only on `K`.
* `NumberField.exists_forall_apply_add_le`: **simultaneous approximation by `Sfin`-integers**,
  both at once.

## Implementation notes

⚠ **No completion appears.** Bombieri–Gubler take the targets in the completions `K_v` and use
that the `S`-integers are a lattice in `∏_{v ∈ S} K_v`. The targets of Evertse's lemma lie in `K`
once the forms have coefficients in `K`, and for targets in `K` the finite places need no
topology: the principal part at `v₀` is written down, from prime avoidance at finitely many
places (`NumberField.FinitePlace.exists_apply_eq_one_forall_apply_le`) and one geometric sum.

⚠ **The constant is exact at the finite places and depends only on `K` at the infinite ones.**
The book first obtains `|ξ + γ_v|_v ≤ A_v` at every place of `S` and then rescales by an
`S`-integer small at the finite places to make `A_v = 1` there. Here the finite conditions are met
with `1` directly, and the translation by `𝓞 K` that handles the infinite places does not disturb
them. So `A` is the sum of the norms of the embedded integral basis, and depends on neither
`Sfin` nor the targets.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
the proof of Lemma 7.5.29.

This is Layer 4.4 (infrastructure) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open NumberField.mixedEmbedding

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace FinitePlace

/-- **The principal part at one finite place**: for `γ ∈ K` there is an element `ξ`, integral at
every finite place other than `v₀`, with `v₀ (ξ + γ) ≤ 1`. -/
theorem exists_apply_add_le_one (v₀ : FinitePlace K) (γ : K) :
    ∃ ξ : K, v₀ (ξ + γ) ≤ 1 ∧ ∀ w : FinitePlace K, w ≠ v₀ → w ξ ≤ 1 := by
  classical
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact ⟨0, by simp, fun w _ ↦ by simp⟩
  set T : Finset (FinitePlace K) := (FinitePlace.hasFiniteMulSupport hγ).toFinset.erase v₀
    with hT
  obtain ⟨s, hs₀, hsT⟩ := exists_apply_eq_one_forall_apply_le v₀ T (Finset.notMem_erase v₀ _)
    (ε := fun w ↦ (w γ)⁻¹) fun w _ ↦ inv_pos.2 ((pos_iff).2 hγ)
  have hsnot : s ∉ v₀.maximalIdeal.asIdeal := by
    rw [← FinitePlace.mk_eq_one_iff_notMem, ← apply_eq_mk_maximalIdeal]
    exact hs₀
  obtain ⟨a, p, hp, hap⟩ := v₀.maximalIdeal.isMaximal.exists_inv hsnot
  have hpv : v₀ (p : K) < 1 := by
    rw [apply_eq_mk_maximalIdeal]
    exact (FinitePlace.mk_lt_one_iff_mem _ _).2 hp
  have hγpos : 0 < v₀ γ := (pos_iff).2 hγ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hγpos) hpv
  set e : 𝓞 K := s * (a * ∑ i ∈ Finset.range N, p ^ i) with he
  have he1 : 1 - e = p ^ N := by
    rw [he, ← mul_assoc, mul_comm s a, show a * s = 1 - p by linear_combination hap,
      mul_neg_geom_sum]
    ring
  refine ⟨-(γ * e), ?_, fun w hw ↦ ?_⟩
  · have : -(γ * (e : K)) + γ = γ * ((p : K) ^ N) := by
      have := congrArg (fun z : 𝓞 K ↦ (z : K)) he1
      push_cast at this
      rw [← this]; ring
    rw [this, map_mul, map_pow]
    calc v₀ γ * v₀ (p : K) ^ N ≤ v₀ γ * (v₀ γ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hγpos.ne'
  · rw [FinitePlace.coe_apply, AbsoluteValue.map_neg, ← FinitePlace.coe_apply, map_mul, he]
    push_cast
    rw [map_mul]
    have hint : w ((a : K) * ∑ i ∈ Finset.range N, (p : K) ^ i) ≤ 1 := by
      have := apply_le_one w (a * ∑ i ∈ Finset.range N, p ^ i)
      push_cast at this
      exact this
    by_cases hwT : w ∈ T
    · have := hsT w hwT
      calc w γ * (w (s : K) * w ((a : K) * ∑ i ∈ Finset.range N, (p : K) ^ i))
          ≤ w γ * ((w γ)⁻¹ * 1) := by gcongr
        _ = 1 := by rw [mul_one, mul_inv_cancel₀ ((pos_iff).2 hγ).ne']
    · have hw1 : w γ = 1 := by
        by_contra h
        exact hwT (Finset.mem_erase.2 ⟨hw, (Set.Finite.mem_toFinset _).2 h⟩)
      rw [hw1, one_mul]
      calc w (s : K) * w ((a : K) * ∑ i ∈ Finset.range N, (p : K) ^ i) ≤ 1 * 1 := by
            gcongr
            exact apply_le_one w s
        _ = 1 := one_mul 1

/-- **Approximation at the places of `Sfin` by `Sfin`-integers**: for targets `γ v ∈ K` there is
an element `ξ`, integral at every finite place outside `Sfin`, with `v (ξ + γ v) ≤ 1` at every
place of `Sfin`. -/
theorem exists_forall_apply_add_le_one (Sfin : Finset (FinitePlace K)) (γ : FinitePlace K → K) :
    ∃ ξ : K, (∀ v : FinitePlace K, v ∉ Sfin → v ξ ≤ 1) ∧ ∀ v ∈ Sfin, v (ξ + γ v) ≤ 1 := by
  classical
  choose ξ hξ using fun v : FinitePlace K ↦ exists_apply_add_le_one v (γ v)
  refine ⟨∑ u ∈ Sfin, ξ u, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · exact apply_sum_le_of_forall_le v zero_le_one fun u hu ↦
      (hξ u).2 v fun h ↦ hv (h ▸ hu)
  · rw [← Finset.add_sum_erase Sfin ξ hv, add_right_comm]
    refine (v.add_le _ _).trans (max_le (hξ v).1 ?_)
    exact apply_sum_le_of_forall_le v zero_le_one fun u hu ↦
      (hξ u).2 v (Finset.ne_of_mem_erase hu).symm

end FinitePlace

namespace mixedEmbedding

open scoped Classical in
/-- The norm at one infinite place is at most the norm, which is their maximum. -/
theorem normAtPlace_le_norm (w : InfinitePlace K) (z : mixedSpace K) :
    normAtPlace w z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w ↦ normAtPlace w z) (Finset.mem_univ w)

end mixedEmbedding

/-- **An algebraic integer moves any targets at the infinite places into a ball of radius `A`**,
with `A` depending only on `K`: the sum of the norms of the embedded integral basis, which bounds a
fundamental domain of `𝓞 K` in the mixed space. -/
theorem exists_integer_forall_infinitePlace_add_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : InfinitePlace K → K, ∃ a : 𝓞 K, ∀ w : InfinitePlace K,
      w ((a : K) + t w) ≤ A := by
  classical
  refine ⟨∑ i, ‖latticeBasis K i‖, Finset.sum_nonneg fun i _ ↦ norm_nonneg _, fun t ↦ ?_⟩
  let z : mixedSpace K := (fun w ↦ (mixedEmbedding K (t w.1)).1 w,
    fun w ↦ (mixedEmbedding K (t w.1)).2 w)
  have hfl := (mem_span_latticeBasis K).1 (ZSpan.floor (latticeBasis K) z).2
  obtain ⟨a, ha⟩ := hfl
  refine ⟨-a, fun w ↦ ?_⟩
  have hz : normAtPlace w (z - mixedEmbedding K (a : K)) = w ((-a : 𝓞 K) + t w) := by
    have h' : ((-a : 𝓞 K) : K) + t w = t w - a := by push_cast; ring
    rw [h', ← normAtPlace_apply, map_sub (mixedEmbedding K)]
    rcases w.isReal_or_isComplex with hw | hw
    · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw]
      rfl
    · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw]
      rfl
  have hfr : z - mixedEmbedding K (a : K) = ZSpan.fract (latticeBasis K) z := by
    rw [ZSpan.fract_apply, ← ha]
    rfl
  rw [← hz, hfr]
  exact (normAtPlace_le_norm w _).trans (ZSpan.norm_fract_le _ _)

/-- **Simultaneous approximation by `Sfin`-integers**, stated without completions: for targets
`γ v ∈ K` there is an `Sfin`-integer `ξ` with `v (ξ + γ v) ≤ 1` at every place of `Sfin` and
`w (ξ + γ w) ≤ A` at every infinite place, with `A` depending only on `K`. -/
theorem exists_forall_apply_add_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Sfin : Finset (FinitePlace K)) (γ : AbsoluteValue K ℝ → K),
      ∃ ξ : K, (∀ v : FinitePlace K, v ∉ Sfin → v ξ ≤ 1) ∧ (∀ v ∈ Sfin, v (ξ + γ v.1) ≤ 1) ∧
        ∀ w : InfinitePlace K, w (ξ + γ w.1) ≤ A := by
  obtain ⟨A, hA, hInf⟩ := exists_integer_forall_infinitePlace_add_le (K := K)
  refine ⟨A, hA, fun Sfin γ ↦ ?_⟩
  obtain ⟨ξ₀, hξ₀, hξ₀S⟩ := FinitePlace.exists_forall_apply_add_le_one Sfin fun v ↦ γ v.1
  obtain ⟨a, ha⟩ := hInf fun w ↦ ξ₀ + γ w.1
  refine ⟨ξ₀ + a, fun v hv ↦ ?_, fun v hv ↦ ?_, fun w ↦ ?_⟩
  · exact (v.add_le _ _).trans (max_le (hξ₀ v hv) (FinitePlace.apply_le_one v a))
  · rw [add_right_comm]
    exact (v.add_le _ _).trans (max_le (hξ₀S v hv) (FinitePlace.apply_le_one v a))
  · convert ha w using 2
    ring

end NumberField
