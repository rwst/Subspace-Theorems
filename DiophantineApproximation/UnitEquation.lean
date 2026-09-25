/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceGeneralPosition

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import DiophantineApproximation.AffineProd
import DiophantineApproximation.SAdicHeight
import Mathlib.Tactic.LinearCombination
import DiophantineApproximation.RationalPlaces

/-!
# The unit equation in two variables

**Layer 8.1** (Siegel; Mahler; Lang). For a number field `K`, a finite set `S` of finite places
and `a, b ∈ Kˣ`, the equation `a x + b y = 1` has finitely many solutions in `S`-units `x, y`.

Route: enlarge `S` until `a` and `b` are `S`-units and absorb them, so that the equation is
`x + y = 1`. At every place of `S∞ ∪ S` take the three forms `X₀`, `X₁`, `X₀ + X₁`, which are in
general position in two variables. At a solution the local factor at `v` is
`|x|_v |y|_v |1|_v / ‖(x, y)‖_v ^ 3`, and over `S∞ ∪ S` the numerators have product `1` by the
`S`-product formula while the denominators have product `H(x, y) ^ 3`, the point being
`S`-primitive: the central quantity of Vojta's refinement (Layer 6.5) is **exactly**
`H(x, y) ^ (-3) = H(x, y) ^ (-2 - 1)`. So the solutions lie in finitely many proper subspaces of
`K²`, which are lines through the origin, and a line meets `X₀ + X₁ = 1` at most once.

## Main results

* `NumberField.finite_setOf_unit_add_unit_eq_one`: **the milestone**.
* `NumberField.finite_setOf_add_eq_one`: the normalized equation `x + y = 1`.
* `NumberField.generalProd_unitEquationForms_eq`: the central quantity at a solution.
* `NumberField.exists_finset_mem_unit`: every element of `Kˣ` is an `S`-unit for some finite `S`.

## Implementation notes

⚠ **No split by the largest coordinate.** The roadmap's route chooses at every place the form
`X₀ + X₁` together with the coordinate form of the *smaller* coordinate, and applies Layer 6.4 to
each of the finitely many choices. Vojta's refinement (6.5) makes that choice itself: with all
three forms at every place, the central quantity at a solution is `H ^ (-3)` on the nose, with no
comparison of coordinates and no case split, and `ε = 1`.

⚠ **Primitivity is free.** The height of the point `(x, y)` is its product of local sup norms over
`S∞ ∪ S` because the point is `S`-primitive, and it is so because `1 · x + 1 · y = 1`: the
equation itself is the Bézout relation.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 5.2.1 and §7.4; J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number
Theory*, Cambridge University Press (2015), Chapter 4.

This is Layer 8.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height IsDedekindDomain Module Module.Dual

namespace NumberField

variable {K : Type*} [Field K]

/-- **The three forms of the unit equation**: `X₀`, `X₁` and `X₀ + X₁` on `K²`. -/
noncomputable def unitEquationForms : Fin 3 → Dual K (Fin 2 → K) :=
  let X : Fin 2 → Dual K (Fin 2 → K) := fun i ↦ LinearMap.proj i
  ![X 0, X 1, X 0 + X 1]

/-- The first form is `X₀`. -/
@[simp] theorem unitEquationForms_zero (x : Fin 2 → K) : unitEquationForms 0 x = x 0 := rfl

/-- The second form is `X₁`. -/
@[simp] theorem unitEquationForms_one (x : Fin 2 → K) : unitEquationForms 1 x = x 1 := rfl

/-- The third form is `X₀ + X₁`. -/
@[simp] theorem unitEquationForms_two (x : Fin 2 → K) : unitEquationForms 2 x = x 0 + x 1 := rfl

/-- **The three forms are in general position**: any two of them are linearly independent. -/
theorem isGeneralPosition_unitEquationForms :
    IsGeneralPosition K (univ : Finset (Fin 3)) (unitEquationForms (K := K)) := by
  intro s _ hs
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hs
  obtain ⟨k, hk⟩ : ∃ k, k ∉ s := by
    by_contra! h
    have := Finset.card_le_card (fun k _ ↦ h k : (univ : Finset (Fin 3)) ⊆ s)
    simp at this
    omega
  have hev : ∀ (i j : Fin 3) (c d : K),
      c • unitEquationForms i + d • unitEquationForms j = (0 : Dual K (Fin 2 → K)) →
      c * unitEquationForms i ![1, 0] + d * unitEquationForms j ![1, 0] = 0 ∧
        c * unitEquationForms i ![0, 1] + d * unitEquationForms j ![0, 1] = 0 :=
    fun i j c d h ↦ ⟨by simpa using LinearMap.congr_fun h ![1, 0],
      by simpa using LinearMap.congr_fun h ![0, 1]⟩
  have h01 : LinearIndepOn K (unitEquationForms (K := K)) {0, 1} :=
    (LinearIndepOn.pair_iff _ (by decide)).mpr fun c d hcd ↦ by
      obtain ⟨h0, h1⟩ := hev 0 1 c d hcd
      simp only [unitEquationForms_zero, unitEquationForms_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add] at h0 h1
      exact ⟨h0, h1⟩
  have h02 : LinearIndepOn K (unitEquationForms (K := K)) {0, 2} :=
    (LinearIndepOn.pair_iff _ (by decide)).mpr fun c d hcd ↦ by
      obtain ⟨h0, h1⟩ := hev 0 2 c d hcd
      simp only [unitEquationForms_zero, unitEquationForms_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add] at h0 h1
      exact ⟨by linear_combination h0 - h1, h1⟩
  have h12 : LinearIndepOn K (unitEquationForms (K := K)) {1, 2} :=
    (LinearIndepOn.pair_iff _ (by decide)).mpr fun c d hcd ↦ by
      obtain ⟨h0, h1⟩ := hev 1 2 c d hcd
      simp only [unitEquationForms_one, unitEquationForms_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add] at h0 h1
      exact ⟨by linear_combination h1 - h0, h0⟩
  change LinearIndepOn K (unitEquationForms (K := K)) (s : Set (Fin 3))
  fin_cases k
  · exact h12.mono fun i hi ↦ by
      fin_cases i <;> simp_all
  · exact h02.mono fun i hi ↦ by
      fin_cases i <;> simp_all
  · exact h01.mono fun i hi ↦ by
      fin_cases i <;> simp_all

variable [NumberField K]

/-- **Every element of `Kˣ` is an `S`-unit for some finite `S`**: the finite places at which it is
not a unit are finitely many. -/
theorem exists_finset_mem_unit (x : Kˣ) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), x ∈ (T : Set (HeightOneSpectrum (𝓞 K))).unit K := by
  have hfin : (FinitePlace.mk ⁻¹' Function.mulSupport fun w : FinitePlace K ↦ w (x : K)).Finite :=
    (FinitePlace.hasFiniteMulSupport (Units.ne_zero x)).preimage
      FinitePlace.mk_injective.injOn
  refine ⟨hfin.toFinset, (Set.mem_unit_iff_finitePlace _ x).mpr fun v hv ↦ ?_⟩
  by_contra h
  exact hv (by simpa using h)

/-- `S`-units stay `S`-units when `S` grows. -/
theorem mem_unit_of_subset {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') {x : Kˣ}
    (hx : x ∈ S.unit K) : x ∈ S'.unit K :=
  (Set.mem_unit_iff_finitePlace _ x).mpr fun v hv ↦
    (Set.mem_unit_iff_finitePlace _ x).mp hx v fun hvS ↦ hv (h hvS)

open scoped Classical in
/-- **The central quantity at a solution of the unit equation.** With the three forms at every
infinite place and every place of `S`, the local numerators multiply to `1` by the `S`-product
formula and the denominators to `H(x, y) ^ 3`, so Vojta's quantity is `H(x, y) ^ (-3)`. -/
theorem generalProd_unitEquationForms_eq (S : Finset (HeightOneSpectrum (𝓞 K))) {x y : Kˣ}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hy : y ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hxy : (x : K) + y = 1) :
    generalProd univ (S.image FinitePlace.mk) (fun v ↦ v) (fun _ ↦ univ)
        (fun _ ↦ unitEquationForms) ![(x : K), y] =
      (mulHeight ![(x : K), y] ^ 3)⁻¹ := by
  set z : Fin 2 → K := ![(x : K), y] with hz
  have hloc : ∀ (v : AbsoluteValue K ℝ) (d : ℝ),
      (∏ k ∈ (univ : Finset (Fin 3)), v (unitEquationForms k fun j ↦ algebraMap K K (z j)) / d)
        = v (x : K) * v (y : K) * (d ^ 3)⁻¹ := by
    intro v d
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Fin.prod_univ_three,
      unitEquationForms_zero, unitEquationForms_one, unitEquationForms_two, hz,
      Matrix.cons_val_zero, Matrix.cons_val_one, hxy, map_one]
    ring
  have himg : ∀ f : FinitePlace K → ℝ,
      ∏ v ∈ S.image FinitePlace.mk, f v = ∏ v ∈ S, f (FinitePlace.mk v) :=
    fun f ↦ Finset.prod_image fun a _ b _ h ↦ FinitePlace.mk_injective h
  have hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive z := by
    refine (Set.isPrimitive_iff _ z).mpr ⟨fun i ↦ ?_, fun _ ↦ 1, fun _ ↦ one_mem _, ?_⟩
    · fin_cases i
      · exact Set.mem_integer_of_mem_unit hx
      · exact Set.mem_integer_of_mem_unit hy
    · simp [hz, Fin.sum_univ_two, hxy]
  have hH := mulHeight_eq_prod_of_isPrimitive S hprim
  have hux := prod_apply_eq_one_of_mem_unit S hx
  have huy := prod_apply_eq_one_of_mem_unit S hy
  rw [generalProd, himg]
  simp only [hloc]
  have hux' : (∏ v : InfinitePlace K, (v.1 (x : K)) ^ v.mult) *
      ∏ v ∈ S, (FinitePlace.mk v).1 (x : K) = 1 := hux
  have huy' : (∏ v : InfinitePlace K, (v.1 (y : K)) ^ v.mult) *
      ∏ v ∈ S, (FinitePlace.mk v).1 (y : K) = 1 := huy
  have e1 : ∏ v : InfinitePlace K, ((⨆ j, v (z j)) ^ 3)⁻¹ ^ v.mult =
      ((∏ v : InfinitePlace K, (⨆ j, v (z j)) ^ v.mult) ^ 3)⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun _ _ ↦ by rw [inv_pow, pow_right_comm]
  have e2 : ∏ v ∈ S, ((⨆ j, FinitePlace.mk v (z j)) ^ 3)⁻¹ =
      ((∏ v ∈ S, ⨆ j, FinitePlace.mk v (z j)) ^ 3)⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [e1, e2, hH]
  set P := ∏ v : InfinitePlace K, (⨆ j, v (z j)) ^ v.mult
  set Q := ∏ v ∈ S, ⨆ j, FinitePlace.mk v (z j)
  linear_combination ((∏ v : InfinitePlace K, (v.1 (y : K)) ^ v.mult) *
    (∏ v ∈ S, (FinitePlace.mk v).1 (y : K)) * ((P * Q) ^ 3)⁻¹) * hux' + ((P * Q) ^ 3)⁻¹ * huy'

omit [NumberField K] in
/-- **A line through the origin meets `X₀ + X₁ = 1` at most once**: two distinct points of a
subspace of `K²` on that line span `K²`. -/
theorem eq_of_mem_of_add_eq_one {W : Submodule K (Fin 2 → K)} (hW : W ≠ ⊤) {p q : Fin 2 → K}
    (hp : p ∈ W) (hq : q ∈ W) (hp1 : p 0 + p 1 = 1) (hq1 : q 0 + q 1 = 1) : p = q := by
  by_contra hne
  have hli : LinearIndependent K ![p, q] := by
    refine LinearIndependent.pair_iff.mpr fun c d hcd ↦ ?_
    have h0 := congrFun hcd 0
    have h1 := congrFun hcd 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
    have hcd' : c + d = 0 := by linear_combination h0 + h1 - c * hp1 - d * hq1
    have hc : c = 0 := by
      by_contra hc
      apply hne
      funext i
      have hi := congrFun hcd i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      have : c * (p i - q i) = 0 := by linear_combination hi - q i * hcd'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
    exact ⟨hc, by linear_combination hcd' - hc⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  refine hW (eq_top_iff.mpr (htop ▸ Submodule.span_le.mpr ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hp
  · exact hq

/-- **The normalized unit equation**: finitely many pairs of `S`-units satisfy `x + y = 1`. -/
theorem finite_setOf_add_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (p.1 : K) + p.2 = 1}.Finite := by
  classical
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_generalProd_le (F := K) (ι := Fin 2)
    univ (S.image FinitePlace.mk) (fun v ↦ v)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ ↦ univ) (fun _ ↦ unitEquationForms)
    (fun _ _ ↦ isGeneralPosition_unitEquationForms)
    (fun _ _ ↦ isGeneralPosition_unitEquationForms) one_pos
  set f : Kˣ × Kˣ → Fin 2 → K := fun p ↦ ![(p.1 : K), p.2] with hf
  have hfinj : Function.Injective f := fun p q h ↦ by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext (Units.ext h0) (Units.ext h1)
  have hsub : f '' {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧ (p.1 : K) + p.2 = 1} ⊆
      ⋃ W ∈ T, {z | z ∈ W ∧ z 0 + z 1 = 1} := by
    rintro _ ⟨p, ⟨hp1, hp2, hp⟩, rfl⟩
    have hz0 : f p ≠ 0 := fun h ↦ Units.ne_zero p.1 (by simpa [hf] using congrFun h 0)
    have hH0 : (0 : ℝ) < mulHeight (f p) := lt_of_lt_of_le zero_lt_one (one_le_mulHeight _)
    obtain ⟨W, hWT, hW⟩ := hmem (f p) hz0 (by
      rw [generalProd_unitEquationForms_eq S hp1 hp2 hp, Fintype.card_fin,
        show -((2 : ℕ) : ℝ) - 1 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hH0.le,
        Real.rpow_natCast])
    exact Set.mem_biUnion hWT ⟨hW, by simpa [hf] using hp⟩
  refine Set.Finite.of_finite_image ?_ hfinj.injOn
  refine (T.finite_toSet.biUnion fun W hW ↦ ?_).subset hsub
  exact Set.Subsingleton.finite fun p hp q hq ↦
    eq_of_mem_of_add_eq_one (hT W hW) hp.1 hq.1 hp.2 hq.2

/-- **The unit equation in two variables** (Siegel; Mahler; Lang). For a finite set `S` of finite
places and `a, b ∈ Kˣ`, finitely many pairs of `S`-units satisfy `a x + b y = 1`. -/
theorem finite_setOf_unit_add_unit_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      (a : K) * p.1 + (b : K) * p.2 = 1}.Finite := by
  classical
  obtain ⟨Ta, ha⟩ := exists_finset_mem_unit a
  obtain ⟨Tb, hb⟩ := exists_finset_mem_unit b
  set S' := S ∪ Ta ∪ Tb with hS'
  have hsub : ∀ {T : Finset (HeightOneSpectrum (𝓞 K))}, T ⊆ S' →
      (T : Set (HeightOneSpectrum (𝓞 K))) ⊆ (S' : Set (HeightOneSpectrum (𝓞 K))) :=
    fun h ↦ Finset.coe_subset.mpr h
  have ha' := mem_unit_of_subset (hsub (by rw [hS']; intro v hv; simp [hv])) ha
  have hb' := mem_unit_of_subset (hsub (by rw [hS']; intro v hv; simp [hv])) hb
  refine ((finite_setOf_add_eq_one S').preimage
    (f := fun p : Kˣ × Kˣ ↦ (a * p.1, b * p.2)) fun p _ q _ h ↦ ?_).subset ?_
  · simp only [Prod.mk.injEq, mul_right_inj] at h
    exact Prod.ext h.1 h.2
  · rintro p ⟨hp1, hp2, hp⟩
    have hS : (S : Set (HeightOneSpectrum (𝓞 K))) ⊆ S' :=
      hsub (by rw [hS']; intro v hv; simp [hv])
    exact ⟨Subgroup.mul_mem _ ha' (mem_unit_of_subset hS hp1),
      Subgroup.mul_mem _ hb' (mem_unit_of_subset hS hp2), by simpa using hp⟩

end NumberField

/-! ### Acceptance criteria -/

open NumberField

/-- Rejection: **the units are load-bearing.** In `ℚˣ` the equation `x + y = 1` has infinitely many
solutions, `(n + 2, -(n + 1))`. -/
example : {p : ℚˣ × ℚˣ | (p.1 : ℚ) + p.2 = 1}.Infinite := by
  have h1 : ∀ n : ℕ, ((n : ℚ) + 2) ≠ 0 := fun n ↦ by positivity
  have h2 : ∀ n : ℕ, (-((n : ℚ) + 1)) ≠ 0 := fun n ↦ neg_ne_zero.mpr (by positivity)
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ (Units.mk0 _ (h1 n), Units.mk0 _ (h2 n))) (fun m n h ↦ ?_) fun n ↦ ?_
  · have := congrArg (fun p : ℚˣ × ℚˣ ↦ (p.1 : ℚ)) h
    simp only [Units.val_mk0, add_left_inj, Nat.cast_inj] at this
    exact this
  · change ((n : ℚ) + 2) + -((n : ℚ) + 1) = 1
    ring

open scoped Classical in
/-- The `{2, 3}`-units of `ℚ`, as height-one primes of `𝓞 ℚ`. -/
private noncomputable def S23 : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  {(Rat.finitePlace ⟨2, Nat.prime_two⟩).maximalIdeal,
    (Rat.finitePlace ⟨3, Nat.prime_three⟩).maximalIdeal}

/-- A divisor of `72 = 2³ 3²`, with either sign, is a `{2, 3}`-unit. -/
private theorem mk0_mem_S23_unit {n : ℕ} (hn : n ∣ 72) (σ : ℚ)
    (hσ : σ = 1 ∨ σ = -1) (hσn : σ * n ≠ 0) :
    Units.mk0 (σ * n) hσn ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
  refine (Set.mk0_mem_unit_iff_finitePlace _ hσn).mpr fun v hv ↦ ?_
  obtain ⟨p, hp, hvp⟩ := Rat.exists_prime_padic_eq (FinitePlace.mk v)
  have hmem : ∀ q : Nat.Primes, (q : ℕ) = p →
      v = (Rat.finitePlace q).maximalIdeal := fun q hq ↦ by
    subst hq
    rw [← FinitePlace.maximalIdeal_mk v]
    congr 1
    exact Subtype.ext (by rw [hvp, Rat.finitePlace_val])
  have hp2 : p ≠ 2 := fun h ↦ hv (by rw [hmem ⟨2, Nat.prime_two⟩ h.symm]; simp [S23])
  have hp3 : p ≠ 3 := fun h ↦ hv (by rw [hmem ⟨3, Nat.prime_three⟩ h.symm]; simp [S23])
  have hndvd : ¬ p ∣ n := fun hpn ↦ by
    have h72 : p ∣ 2 ^ 3 * 3 ^ 2 := hpn.trans hn
    rcases (Nat.Prime.dvd_mul hp.out).mp h72 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
        (hp.out.dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp
        (hp.out.dvd_of_dvd_pow h))
  have hnorm : padicNorm p (σ * n) = 1 := by
    rcases hσ with rfl | rfl
    · rw [one_mul]; exact (padicNorm.nat_eq_one_iff n).mpr hndvd
    · rw [neg_one_mul, padicNorm.neg]; exact (padicNorm.nat_eq_one_iff n).mpr hndvd
  change (FinitePlace.mk v).1 (σ * n) = 1
  rw [hvp]
  change ((padicNorm p (σ * n) : ℚ) : ℝ) = 1
  exact_mod_cast hnorm

/-- **Conformance: `(2, -1), (3, -2), (4, -3), (9, -8)` solve `x + y = 1` in `{2, 3}`-units of
`ℚ`** — so the finite set of the milestone is not empty. -/
example : ∀ n ∈ ({1, 2, 3, 8} : Finset ℕ),
    ∃ p ∈ {p : ℚˣ × ℚˣ | p.1 ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ ∧
      p.2 ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ ∧ (p.1 : ℚ) + p.2 = 1},
      (p.1 : ℚ) = n + 1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hn72 : n ∣ 72 ∧ n + 1 ∣ 72 := by rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  have h1 : (1 : ℚ) * ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (-1 : ℚ) * (n : ℚ) ≠ 0 := by rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨(Units.mk0 _ h1, Units.mk0 _ h2), ⟨mk0_mem_S23_unit hn72.2 1
    (Or.inl rfl) h1, mk0_mem_S23_unit hn72.1 (-1) (Or.inr rfl) h2, ?_⟩, ?_⟩
  · simp only [Units.val_mk0]; push_cast; ring
  · simp only [Units.val_mk0]; push_cast; ring

/-- The `{2, 3}`-unit equation has finitely many solutions. -/
example : {p : ℚˣ × ℚˣ | p.1 ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ ∧
    p.2 ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ ∧ (p.1 : ℚ) + p.2 = 1}.Finite :=
  NumberField.finite_setOf_add_eq_one S23

/-- The normalized equation is the case `a = b = 1` of the milestone. -/
example {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    {p : Kˣ × Kˣ | p.1 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      p.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      ((1 : Kˣ) : K) * p.1 + ((1 : Kˣ) : K) * p.2 = 1}.Finite :=
  NumberField.finite_setOf_unit_add_unit_eq_one S 1 1

