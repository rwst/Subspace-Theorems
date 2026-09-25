/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- Used only inside proofs.
import ArithmeticHeights.FinitePlaceIdeal
import DiophantineApproximation.PlacesOverFinite

/-!
# The values of a finite place

Three facts about a finite place `v` of a number field `K` that Layer 4.1 needs and Mathlib does
not state in this form. The values of `v` on `Kˣ` are exactly the integer powers of `N 𝔭`, the
norm of its prime; so for every real `r` there is a largest value of `v` that is at most `r`,
`NumberField.FinitePlace.floorValue v r`, and it misses `r` by a factor less than `N 𝔭`. An
algebraic integer can be chosen to be a unit at one place and as small as prescribed at finitely
many others. And a determinant whose rows are bounded at `v` is at most the product of the bounds.

## Main definitions

* `NumberField.FinitePlace.floorValue`: the largest value of `v` on `K` that is at most `r`.

## Main results

* `NumberField.FinitePlace.exists_apply_eq_zpow` and `NumberField.FinitePlace.zpow_mem_range`: the
  values of `v` on `Kˣ` are the integer powers of `N 𝔭`, all of them.
* `NumberField.FinitePlace.floorValue_le`, `NumberField.FinitePlace.lt_mul_floorValue`,
  `NumberField.FinitePlace.exists_apply_eq_floorValue` and
  `NumberField.FinitePlace.apply_le_floorValue`: the largest value at most `r` is at most `r`,
  exceeds `r / N 𝔭`, is a value, and bounds every value at most `r`.
* `NumberField.FinitePlace.exists_apply_eq_one_forall_apply_le`: **approximation at finitely many
  places** — an algebraic integer that is a unit at `v₀` and as small as prescribed on a finite
  set `T ∌ v₀`.
* `NumberField.FinitePlace.exists_ne_zero_forall_apply_le`: a nonzero algebraic integer as small
  as prescribed on a finite set.
* `NumberField.FinitePlace.exists_eq_of_forall_apply_le_one`: an element integral at every finite
  place is an algebraic integer.
* `NumberField.FinitePlace.apply_det_le_prod`: the ultrametric Leibniz bound.

## Implementation notes

⚠ **Approximation is prime avoidance and a power, not the Chinese remainder theorem.** An element
of `∏_{v ∈ T} 𝔭_v` outside `𝔭_{v₀}` exists because a prime containing a product of primes contains
one of them, and maximal ideals are not contained in each other; its `m`-th power is a unit at
`v₀` and tends to `0` at every place of `T`. No exponent has to be computed, and no congruence
solved.

⚠ **The largest value at most `r` is a definition in closed form**, `N 𝔭 ^ ⌊log_{N 𝔭} r⌋`, rather
than a supremum over `K`: the four properties above are what every use needs, and each is one
line from the closed form once the value group is known.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.3 and 7.5.6, where the value of the finite-place volume of an approximation domain is taken in
`Q ^ c` rather than in the value group.

This is Layer 4.1 (infrastructure) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Filter IsDedekindDomain

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place is the place of its own prime. -/
theorem apply_eq_mk_maximalIdeal (v : FinitePlace K) (x : K) :
    v x = FinitePlace.mk v.maximalIdeal x := by
  rw [FinitePlace.mk_maximalIdeal]

/-- An element of `K` that is integral at every finite place is an algebraic integer. -/
theorem exists_eq_of_forall_apply_le_one {x : K} (hx : ∀ v : FinitePlace K, v x ≤ 1) :
    ∃ z : 𝓞 K, (z : K) = x := by
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x
    fun P ↦ (FinitePlace.mk_le_one_iff P x).1 (hx _)
  exact ⟨z, hz⟩

private theorem exists_pow_le {t : K} {T : Finset (FinitePlace K)} (ht : ∀ v ∈ T, v t < 1)
    {ε : FinitePlace K → ℝ} (hε : ∀ v ∈ T, 0 < ε v) : ∃ m : ℕ, ∀ v ∈ T, v (t ^ m) ≤ ε v := by
  have h : ∀ v ∈ T, ∀ᶠ m : ℕ in atTop, v (t ^ m) ≤ ε v := by
    intro v hv
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (apply_nonneg v t) (ht v hv)
    filter_upwards [this.eventually (ge_mem_nhds (hε v hv))] with m hm
    rwa [map_pow]
  exact ((eventually_all_finset T).2 h).exists

/-- **Prime avoidance at finitely many places**: an algebraic integer lying in the prime of
every place of `T` and outside the prime of `v₀`. -/
theorem exists_apply_eq_one_forall_apply_lt_one (v₀ : FinitePlace K) (T : Finset (FinitePlace K))
    (hv₀ : v₀ ∉ T) : ∃ t : 𝓞 K, v₀ (t : K) = 1 ∧ ∀ v ∈ T, v (t : K) < 1 := by
  have hp : ∀ v : FinitePlace K, ∃ p : 𝓞 K, v ≠ v₀ →
      p ∈ v.maximalIdeal.asIdeal ∧ p ∉ v₀.maximalIdeal.asIdeal := by
    intro v
    by_cases hv : v = v₀
    · exact ⟨0, fun h ↦ (h hv).elim⟩
    have hle : ¬ v.maximalIdeal.asIdeal ≤ v₀.maximalIdeal.asIdeal := by
      intro hle
      have := v.maximalIdeal.isMaximal.eq_of_le v₀.maximalIdeal.isPrime.ne_top hle
      exact hv (FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext this))
    obtain ⟨p, hp, hp'⟩ := IsConcreteLE.not_le_iff_exists.1 hle
    exact ⟨p, fun _ ↦ ⟨hp, hp'⟩⟩
  choose p hp using hp
  have hne : ∀ v ∈ T, v ≠ v₀ := fun v hv h ↦ hv₀ (h ▸ hv)
  refine ⟨∏ v ∈ T, p v, ?_, fun v hv ↦ ?_⟩
  · rw [apply_eq_mk_maximalIdeal, FinitePlace.mk_eq_one_iff_notMem]
    have := v₀.maximalIdeal.isPrime
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v, hv, hmem⟩
    exact (hp v (hne v hv)).2 hmem
  · rw [apply_eq_mk_maximalIdeal, FinitePlace.mk_lt_one_iff_mem]
    have := v.maximalIdeal.isPrime
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨v, hv, (hp v (hne v hv)).1⟩

/-- **Approximation at finitely many places**: an algebraic integer which is a unit at `v₀` and
as small as prescribed at every place of `T`. -/
theorem exists_apply_eq_one_forall_apply_le (v₀ : FinitePlace K) (T : Finset (FinitePlace K))
    (hv₀ : v₀ ∉ T) {ε : FinitePlace K → ℝ} (hε : ∀ v ∈ T, 0 < ε v) :
    ∃ s : 𝓞 K, v₀ (s : K) = 1 ∧ ∀ v ∈ T, v (s : K) ≤ ε v := by
  obtain ⟨t, ht₀, ht⟩ := exists_apply_eq_one_forall_apply_lt_one v₀ T hv₀
  obtain ⟨m, hm⟩ := exists_pow_le ht hε
  exact ⟨t ^ m, by push_cast; rw [map_pow, ht₀, one_pow],
    fun v hv ↦ by push_cast; exact hm v hv⟩

/-- A nonzero algebraic integer as small as prescribed at every place of `T`. -/
theorem exists_ne_zero_forall_apply_le (T : Finset (FinitePlace K)) {ε : FinitePlace K → ℝ}
    (hε : ∀ v ∈ T, 0 < ε v) : ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ v ∈ T, v (d : K) ≤ ε v := by
  have hp : ∀ v : FinitePlace K, ∃ p : 𝓞 K, p ∈ v.maximalIdeal.asIdeal ∧ p ≠ 0 :=
    fun v ↦ Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
  choose p hp hp0 using hp
  have ht : ∀ v ∈ T, v ((∏ w ∈ T, p w : 𝓞 K) : K) < 1 := by
    intro v hv
    rw [apply_eq_mk_maximalIdeal, FinitePlace.mk_lt_one_iff_mem]
    have := v.maximalIdeal.isPrime
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨v, hv, hp v⟩
  obtain ⟨m, hm⟩ := exists_pow_le ht hε
  refine ⟨(∏ w ∈ T, p w) ^ m, pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun w _ ↦ hp0 w),
    fun v hv ↦ ?_⟩
  have := hm v hv
  push_cast at this ⊢
  exact this


/-- The ultrametric inequality for a finite sum, against a common bound. -/
theorem apply_sum_le_of_forall_le (v : FinitePlace K) {α : Type*} {s : Finset α} {f : α → K} {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ a ∈ s, v (f a) ≤ R) : v (∑ a ∈ s, f a) ≤ R :=
  Finset.sum_induction f (fun y ↦ v y ≤ R) (fun a b ha hb ↦ (v.add_le a b).trans (max_le ha hb))
    (by simpa using hR) h

/-- An element of the ideal generated by `g` is at most the largest value on `g`. -/
theorem apply_le_iSup_of_mem_span (v : FinitePlace K) {m : ℕ} (g : Fin m → 𝓞 K) {t : 𝓞 K}
    (ht : t ∈ Ideal.span (Set.range g)) : v (t : K) ≤ ⨆ k, v (g k : K) := by
  obtain ⟨r, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 ht
  have hbdd : BddAbove (Set.range fun k ↦ v (g k : K)) := Set.finite_range _ |>.bddAbove
  have h0 : 0 ≤ ⨆ k, v (g k : K) := Real.iSup_nonneg fun k ↦ apply_nonneg _ _
  push_cast
  refine apply_sum_le_of_forall_le v h0 fun k _ ↦ ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (apply_nonneg _ _) (apply_le_one v (r k))).trans
    (le_ciSup hbdd k)

/-- The norm of the prime of a finite place exceeds `1`. -/
theorem one_lt_absNorm (v : FinitePlace K) :
    (1 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal

/-- The values of a finite place on `Kˣ` are the integer powers of the norm of its prime. -/
theorem exists_apply_eq_zpow (v : FinitePlace K) {x : K} (hx : x ≠ 0) :
    ∃ k : ℤ, v x = (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ k := by
  rw [apply_eq_mk_maximalIdeal, FinitePlace.mk_apply, FinitePlace.norm_embedding,
    HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).2 hx)]
  exact ⟨_, by push_cast; rfl⟩

/-- Every integer power of the norm of the prime is a value. -/
theorem zpow_mem_range (v : FinitePlace K) (k : ℤ) :
    (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ k ∈ Set.range v := by
  obtain ⟨π, hπ⟩ := v.maximalIdeal.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hv : v π = (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ (-1 : ℤ) := by
    rw [apply_eq_mk_maximalIdeal, FinitePlace.mk_apply, FinitePlace.norm_embedding,
      HeightOneSpectrum.adicAbv_def,
      WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).2 hπ0)]
    rw [hπ, WithZero.log_exp]
    push_cast
    rfl
  refine ⟨π ^ (-k), ?_⟩
  rw [map_zpow₀, hv, ← zpow_mul]
  simp

/-- **The largest value of `v` on `K` that is at most `r`.** -/
noncomputable def floorValue (v : FinitePlace K) (r : ℝ) : ℝ :=
  (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^
    ⌊Real.logb (Ideal.absNorm v.maximalIdeal.asIdeal) r⌋

/-- The largest value at most `r` is positive, whatever `r`. -/
theorem floorValue_pos (v : FinitePlace K) (r : ℝ) : 0 < v.floorValue r :=
  zpow_pos (zero_lt_one.trans v.one_lt_absNorm) _

/-- The largest value at most `r` is at most `r`. -/
theorem floorValue_le (v : FinitePlace K) {r : ℝ} (hr : 0 < r) : v.floorValue r ≤ r := by
  have hN := v.one_lt_absNorm
  unfold floorValue
  rw [← Real.rpow_intCast]
  calc _ ≤ (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^
        Real.logb (Ideal.absNorm v.maximalIdeal.asIdeal) r :=
        Real.rpow_le_rpow_of_exponent_le hN.le (Int.floor_le _)
    _ = r := Real.rpow_logb (by linarith) hN.ne' hr

/-- **The largest value at most `r` misses `r` by less than the norm of the prime.** -/
theorem lt_mul_floorValue (v : FinitePlace K) {r : ℝ} (hr : 0 < r) :
    r < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) * v.floorValue r := by
  have hN := v.one_lt_absNorm
  unfold floorValue
  rw [← zpow_one_add₀ (by linarith), ← Real.rpow_intCast]
  calc r = (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^
        Real.logb (Ideal.absNorm v.maximalIdeal.asIdeal) r :=
        (Real.rpow_logb (by linarith) hN.ne' hr).symm
    _ < _ := by
        refine Real.rpow_lt_rpow_of_exponent_lt hN ?_
        push_cast
        linarith [Int.lt_floor_add_one (Real.logb (Ideal.absNorm v.maximalIdeal.asIdeal) r)]

/-- The largest value at most `r` is a value. -/
theorem exists_apply_eq_floorValue (v : FinitePlace K) (r : ℝ) :
    ∃ x : K, v x = v.floorValue r :=
  v.zpow_mem_range _

/-- A value at most `r` is at most the largest value at most `r`. -/
theorem apply_le_floorValue (v : FinitePlace K) {r : ℝ} {x : K} (hx : v x ≤ r) :
    v x ≤ v.floorValue r := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero]; exact (v.floorValue_pos r).le
  have hN := v.one_lt_absNorm
  obtain ⟨k, hk⟩ := v.exists_apply_eq_zpow hx0
  rw [hk] at hx ⊢
  unfold floorValue
  refine zpow_le_zpow_right₀ hN.le (Int.le_floor.2 ?_)
  rw [Real.le_logb_iff_rpow_le hN (lt_of_lt_of_le (zpow_pos (by linarith) k) hx),
    Real.rpow_intCast]
  exact hx

/-- **The ultrametric Leibniz bound**: a determinant whose rows are bounded is at most the
product of the bounds. -/
theorem apply_det_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (v : FinitePlace K)
    (N : Matrix ι ι K) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (h : ∀ i k, v (N i k) ≤ r i) :
    v N.det ≤ ∏ i, r i := by
  rw [Matrix.det_apply]
  refine apply_sum_le_of_forall_le v (Finset.prod_nonneg fun i _ ↦ hr i) fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul, map_mul]
  have hs : v ((σ.sign : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
  rw [hs, one_mul, map_prod, ← Equiv.prod_comp σ r]
  exact Finset.prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ h (σ i) i

end NumberField.FinitePlace
