/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproxProd
public import DiophantineApproximation.FormBaseChange
public import DiophantineApproximation.PlaceConjugation

-- Used only inside proofs.
import DiophantineApproximation.PlacesOver

/-!
# The central quantity of the Subspace Theorem over a Galois extension

For `E / K` Galois and a point `x` of `Kⁱ`, the quantity `approxProd` measured over `K` with one
chosen absolute value of `E` above each place, and measured over `E` at **every** place above
those places with the conjugated systems of forms, differ by exactly the degree:

```text
approxProd_E (places above S) (conjugates of L) (x over E)  =  approxProd_K S w' L x ^ [E : K].
```

This is Bombieri–Gubler's Remark 7.2.3, and it is the whole of what carries the Subspace Theorem
from coefficients in `K` to coefficients in a finite extension. The reason it is an equality and
not an inequality is that a point of `Kⁱ` sees the same local factor at every place above `v`:
the conjugation that moves the chosen absolute value to another place above `v` moves the system
of forms with it, and the point is fixed by it.

## Main results

* `NumberField.conjSystem`: the system of forms on `Eⁱ`, defined at every absolute value of `E` at
  once, which carries a conjugate of the system at `v` to each place above `v`.
* `NumberField.exists_conjSystem_inf` and `NumberField.exists_conjSystem_fin`: it *is* a conjugate
  there, with the automorphism named.
* `NumberField.conjSystem_apply_inf` and `NumberField.conjSystem_apply_fin`: the local factors at
  a point of `Kⁱ`, which is where the conjugation disappears.
* `NumberField.linearIndependent_conjSystem_inf` and
  `NumberField.linearIndependent_conjSystem_fin`: the conjugated systems are independent, which is
  what the Subspace Theorem over `E` requires of them.
* `NumberField.approxProd_conjSystem`: the identity above.

## Implementation notes

⚠ **The system has to be a function of the absolute value, so the two kinds of place must be told
apart.** `approxProd` reads its forms at `V.1` for typed places `V`, infinite and finite alike, so
`conjSystem` is defined by cases on an absolute value of `E` and the cases must not overlap;
`NumberField.InfinitePlace.val_ne_finitePlace_val` is what makes them exclusive. The alternative —
two systems — is not available, because `approxProd` takes one.

⚠ **The place of `K` under a place of `E` is recovered from the *relation*, not from a
restriction map.** The definition chooses a triple `(v, V, σ)` for each absolute value; that the
`v` it chooses is the one wanted is proved, not built in, and the proof is that both restrict the
same absolute value of `E` to `K`. This avoids needing a contraction map on finite places, which
Mathlib does not have, and avoids needing that distinct places of `K` are inequivalent.

⚠ **At a finite place the exponent is the local degree, at an infinite place it is `1`.** Mathlib
normalizes finite places so that the product formula holds with exponent one, which makes a finite
place of `E` restrict to `v ^ (e f)` rather than to `v`; the `(e f)` cancels against
`NumberField.FinitePlace.sum_localDegree` exactly as `mult` cancels against
`NumberField.InfinitePlace.sum_mult` at the infinite places. That the two cancellations produce
the same exponent `[E : K]` is why the identity is uniform.

This is part of Layer 6.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module NumberField

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- The system of forms on `Eⁱ` that puts, at every place of `E` above a place `v` of the two
finsets, a conjugate of the system at `v`. -/
noncomputable def conjSystem (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (U : AbsoluteValue E ℝ) : ι → Dual E (ι → E) :=
  if h : ∃ p : InfinitePlace K × InfinitePlace E × (E ≃ₐ[K] E),
      p.1 ∈ Sinf ∧ p.2.1.1 = U ∧ ∀ z : E, p.2.1 (p.2.2 z) = w' p.1.1 z then
    fun i ↦ (L h.choose.1.1 i).compRingHom (h.choose.2.2 : E →+* E)
  else if h' : ∃ p : FinitePlace K × FinitePlace E × (E ≃ₐ[K] E),
      p.1 ∈ Sfin ∧ p.2.1.1 = U ∧
        ∀ z : E, p.2.1 (p.2.2 z) = w' p.1.1 z ^ p.2.1.localDegree K then
    fun i ↦ (L h'.choose.1.1 i).compRingHom (h'.choose.2.2 : E →+* E)
  else fun i ↦ LinearMap.proj i

variable {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
  {w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ} {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)}

/-- At an infinite place above `v ∈ Sinf` the system is a conjugate of the one at `v`. -/
theorem exists_conjSystem_inf [IsGalois K E] (hw : ∀ v ∈ Sinf, (w' v.1).LiesOver v.1)
    {v : InfinitePlace K} (hv : v ∈ Sinf) {V : InfinitePlace E} (hV : V.LiesOver v) :
    ∃ σ : E ≃ₐ[K] E, (∀ z : E, V (σ z) = w' v.1 z) ∧
      conjSystem Sinf Sfin w' L V.1 = fun i ↦ (L v.1 i).compRingHom (σ : E →+* E) := by
  classical
  have hlo := hw v hv
  obtain ⟨σ₀, hσ₀⟩ := InfinitePlace.exists_algEquiv_apply_eq v (w' v.1) V hV
  have hex : ∃ p : InfinitePlace K × InfinitePlace E × (E ≃ₐ[K] E),
      p.1 ∈ Sinf ∧ p.2.1.1 = V.1 ∧ ∀ z : E, p.2.1 (p.2.2 z) = w' p.1.1 z :=
    ⟨(v, V, σ₀), hv, rfl, hσ₀⟩
  obtain ⟨hv', hVV, hrel⟩ := hex.choose_spec
  set p := hex.choose with hp
  have hlo' := hw p.1 hv'
  have hVeq : p.2.1 = V := Subtype.ext hVV
  have hveq : p.1 = v := by
    refine Subtype.ext (AbsoluteValue.ext fun y ↦ ?_)
    have h1 : p.2.1 (algebraMap K E y) = w' p.1.1 (algebraMap K E y) := by
      have := hrel (algebraMap K E y)
      rwa [AlgEquiv.commutes] at this
    rw [hVeq] at h1
    have h2 : w' p.1.1 (algebraMap K E y) = p.1 y :=
      congrFun (congrArg (fun (a : AbsoluteValue K ℝ) ↦ (a : K → ℝ))
        (AbsoluteValue.LiesOver.under_eq (w' p.1.1) p.1.1 (K := K))) y
    have h3 : V (algebraMap K E y) = v y :=
      congrFun (congrArg (fun (a : AbsoluteValue K ℝ) ↦ (a : K → ℝ))
        (AbsoluteValue.LiesOver.under_eq V.1 v.1 (K := K))) y
    rw [h2] at h1
    rw [← InfinitePlace.coe_apply, ← InfinitePlace.coe_apply, ← h1, h3]
  refine ⟨p.2.2, fun z ↦ ?_, ?_⟩
  · rw [← hVeq, ← hveq]; exact hrel z
  · rw [show conjSystem Sinf Sfin w' L V.1
        = fun i ↦ (L hex.choose.1.1 i).compRingHom (hex.choose.2.2 : E →+* E) by
      rw [conjSystem]
      split
      · rfl
      · exact absurd hex ‹_›, ← hp, hveq]


/-- At a finite place above `v ∈ Sfin` the system is a conjugate of the one at `v`. -/
theorem exists_conjSystem_fin [IsGalois K E] (hw : ∀ v ∈ Sfin, (w' v.1).LiesOver v.1)
    {v : FinitePlace K} (hv : v ∈ Sfin) {V : FinitePlace E} (hV : V.LiesOver v) :
    ∃ σ : E ≃ₐ[K] E, (∀ z : E, V (σ z) = w' v.1 z ^ V.localDegree K) ∧
      conjSystem Sinf Sfin w' L V.1 = fun i ↦ (L v.1 i).compRingHom (σ : E →+* E) := by
  classical
  have hVv := hV
  have hlo := hw v hv
  obtain ⟨σ₀, hσ₀⟩ := FinitePlace.exists_algEquiv_apply_eq v (w' v.1) V hV
  have hnoinf : ¬ ∃ p : InfinitePlace K × InfinitePlace E × (E ≃ₐ[K] E),
      p.1 ∈ Sinf ∧ p.2.1.1 = V.1 ∧ ∀ z : E, p.2.1 (p.2.2 z) = w' p.1.1 z := by
    rintro ⟨p, -, hpv, -⟩
    exact InfinitePlace.val_ne_finitePlace_val p.2.1 V hpv
  have hex : ∃ p : FinitePlace K × FinitePlace E × (E ≃ₐ[K] E),
      p.1 ∈ Sfin ∧ p.2.1.1 = V.1 ∧
        ∀ z : E, p.2.1 (p.2.2 z) = w' p.1.1 z ^ p.2.1.localDegree K :=
    ⟨(v, V, σ₀), hv, rfl, hσ₀⟩
  obtain ⟨hv', hVV, hrel⟩ := hex.choose_spec
  set p := hex.choose with hp
  have hlo' := hw p.1 hv'
  have hVeq : p.2.1 = V := Subtype.ext hVV
  have he : 0 < V.localDegree K := V.localDegree_pos
  have hveq : p.1 = v := by
    refine Subtype.ext (AbsoluteValue.ext fun y ↦ ?_)
    have h1 : V (algebraMap K E y) = w' p.1.1 (algebraMap K E y) ^ V.localDegree K := by
      have := hrel (algebraMap K E y)
      rwa [AlgEquiv.commutes, hVeq] at this
    have h2 : w' p.1.1 (algebraMap K E y) = p.1 y :=
      congrFun (congrArg (fun (a : AbsoluteValue K ℝ) ↦ (a : K → ℝ))
        (AbsoluteValue.LiesOver.under_eq (w' p.1.1) p.1.1 (K := K))) y
    have h3 : V (algebraMap K E y) = v y ^ V.localDegree K := V.apply_algebraMap v y
    rw [h2, h3] at h1
    exact (pow_left_inj₀ (apply_nonneg _ _) (apply_nonneg _ _) he.ne').1 h1.symm
  refine ⟨p.2.2, fun z ↦ ?_, ?_⟩
  · rw [← hVeq, ← hveq]; exact hrel z
  · rw [show conjSystem Sinf Sfin w' L V.1
        = fun i ↦ (L hex.choose.1.1 i).compRingHom (hex.choose.2.2 : E →+* E) by
      rw [conjSystem]
      split
      · exact absurd ‹_› hnoinf
      · rfl, ← hp, hveq]


/-- **The local factor at an infinite place above `v`, at a point of `Kⁱ`.** The conjugation
disappears: the point is fixed by it, so the value is the one the chosen absolute value over `v`
gives. -/
theorem conjSystem_apply_inf [IsGalois K E] (hw : ∀ v ∈ Sinf, (w' v.1).LiesOver v.1)
    {v : InfinitePlace K} (hv : v ∈ Sinf) {V : InfinitePlace E} (hV : V.LiesOver v)
    (i : ι) (x : ι → K) :
    V (conjSystem Sinf Sfin w' L V.1 i (fun j ↦ algebraMap K E (x j)))
      = w' v.1 (L v.1 i (fun j ↦ algebraMap K E (x j))) := by
  obtain ⟨σ, hσ, heq⟩ := exists_conjSystem_inf (Sfin := Sfin) (L := L) hw hv hV
  have hfix : (fun j ↦ algebraMap K E (x j)) = fun j ↦ (σ : E →+* E) (algebraMap K E (x j)) := by
    funext j
    exact (AlgEquiv.commutes σ (x j)).symm
  have hval : ((L v.1 i).compRingHom (σ : E →+* E)) (fun j ↦ algebraMap K E (x j))
      = σ (L v.1 i (fun j ↦ algebraMap K E (x j))) := by
    conv_lhs => rw [hfix]
    exact Module.Dual.compRingHom_comp (L v.1 i) (σ : E →+* E) _
  rw [heq, hval]
  exact hσ _

/-- **The local factor at a finite place above `v`, at a point of `Kⁱ`.** As at an infinite
place, except for the local degree that Mathlib's normalization of finite places carries. -/
theorem conjSystem_apply_fin [IsGalois K E] (hw : ∀ v ∈ Sfin, (w' v.1).LiesOver v.1)
    {v : FinitePlace K} (hv : v ∈ Sfin) {V : FinitePlace E} (hV : V.LiesOver v)
    (i : ι) (x : ι → K) :
    V (conjSystem Sinf Sfin w' L V.1 i (fun j ↦ algebraMap K E (x j)))
      = w' v.1 (L v.1 i (fun j ↦ algebraMap K E (x j))) ^ V.localDegree K := by
  obtain ⟨σ, hσ, heq⟩ := exists_conjSystem_fin (Sinf := Sinf) (L := L) hw hv hV
  have hfix : (fun j ↦ algebraMap K E (x j)) = fun j ↦ (σ : E →+* E) (algebraMap K E (x j)) := by
    funext j
    exact (AlgEquiv.commutes σ (x j)).symm
  have hval : ((L v.1 i).compRingHom (σ : E →+* E)) (fun j ↦ algebraMap K E (x j))
      = σ (L v.1 i (fun j ↦ algebraMap K E (x j))) := by
    conv_lhs => rw [hfix]
    exact Module.Dual.compRingHom_comp (L v.1 i) (σ : E →+* E) _
  rw [heq, hval]
  exact hσ _

/-- The conjugated system at an infinite place above `v ∈ Sinf` is linearly independent. -/
theorem linearIndependent_conjSystem_inf [IsGalois K E] (hw : ∀ v ∈ Sinf, (w' v.1).LiesOver v.1)
    (hL : ∀ v ∈ Sinf, LinearIndependent E (L v.1))
    {v : InfinitePlace K} (hv : v ∈ Sinf) {V : InfinitePlace E} (hV : V.LiesOver v) :
    LinearIndependent E (conjSystem Sinf Sfin w' L V.1) := by
  obtain ⟨σ, -, heq⟩ := exists_conjSystem_inf (Sfin := Sfin) (L := L) hw hv hV
  rw [heq]
  exact Module.Dual.linearIndependent_compRingHom (hL v hv) _

/-- The conjugated system at a finite place above `v ∈ Sfin` is linearly independent. -/
theorem linearIndependent_conjSystem_fin [IsGalois K E] (hw : ∀ v ∈ Sfin, (w' v.1).LiesOver v.1)
    (hL : ∀ v ∈ Sfin, LinearIndependent E (L v.1))
    {v : FinitePlace K} (hv : v ∈ Sfin) {V : FinitePlace E} (hV : V.LiesOver v) :
    LinearIndependent E (conjSystem Sinf Sfin w' L V.1) := by
  obtain ⟨σ, -, heq⟩ := exists_conjSystem_fin (Sinf := Sinf) (L := L) hw hv hV
  rw [heq]
  exact Module.Dual.linearIndependent_compRingHom (hL v hv) _


open scoped Classical in
/-- The fibres of the infinite places of `E` over distinct infinite places of `K` are disjoint:
an absolute value of `E` restricts to one absolute value of `K`. -/
theorem pairwiseDisjoint_placesOverFinset_inf (S : Finset (InfinitePlace K)) :
    (S : Set (InfinitePlace K)).PairwiseDisjoint (InfinitePlace.placesOverFinset E) := by
  intro v _ v' _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro V hV hV'
  rw [InfinitePlace.mem_placesOverFinset] at hV hV'
  have h1 : V.1.under K = v.1 := by have := hV; exact AbsoluteValue.LiesOver.under_eq V.1 v.1
  have h2 : V.1.under K = v'.1 := by have := hV'; exact AbsoluteValue.LiesOver.under_eq V.1 v'.1
  exact hne (Subtype.ext (h1.symm.trans h2))

open scoped Classical in
/-- The fibres of the finite places of `E` over distinct finite places of `K` are disjoint: a
prime of `𝓞 E` contracts to one prime of `𝓞 K`. -/
theorem pairwiseDisjoint_placesOverFinset_fin (S : Finset (FinitePlace K)) :
    (S : Set (FinitePlace K)).PairwiseDisjoint (FinitePlace.placesOverFinset E) := by
  intro v _ v' _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro V hV hV'
  rw [FinitePlace.mem_placesOverFinset] at hV hV'
  have h1 : v.maximalIdeal.asIdeal = V.maximalIdeal.asIdeal.under (𝓞 K) := hV.over
  have h2 : v'.maximalIdeal.asIdeal = V.maximalIdeal.asIdeal.under (𝓞 K) := hV'.over
  exact hne (FinitePlace.maximalIdeal_injective
    (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (h1.trans h2.symm)))

open scoped Classical in
/-- **The central quantity over a Galois extension** (Bombieri–Gubler, Remark 7.2.3). At a point
of `Kⁱ`, the quantity measured over `E` at every place above the given ones, with the conjugated
systems, is the quantity measured over `K` raised to the degree. -/
theorem approxProd_conjSystem [IsGalois K E] [Nonempty ι]
    (hwI : ∀ v ∈ Sinf, (w' v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w' v.1).LiesOver v.1)
    (x : ι → K) :
    approxProd (Sinf.biUnion (InfinitePlace.placesOverFinset E))
        (Sfin.biUnion (FinitePlace.placesOverFinset E)) (fun V ↦ V)
        (conjSystem Sinf Sfin w' L) (fun j ↦ algebraMap K E (x j))
      = approxProd Sinf Sfin w' L x ^ Module.finrank K E := by
  set y : ι → E := fun j ↦ algebraMap K E (x j) with hy
  have hyy : (fun j ↦ algebraMap E E (y j)) = y := by funext j; simp
  simp only [approxProd, hyy]
  rw [mul_pow]
  congr 1
  · rw [Finset.prod_biUnion (pairwiseDisjoint_placesOverFinset_inf (E := E) Sinf),
      ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have hfac : ∀ V ∈ InfinitePlace.placesOverFinset E v,
        (∏ i, V.1 (conjSystem Sinf Sfin w' L V.1 i y) / ⨆ j, V (y j)) ^ V.mult
          = (∏ i, w' v.1 (L v.1 i y) / ⨆ j, v (x j)) ^ V.mult := by
      intro V hVmem
      rw [InfinitePlace.mem_placesOverFinset] at hVmem
      have hsup : (⨆ j, V (y j)) = ⨆ j, v (x j) := by
        have hfun : (fun j ↦ V (y j)) = fun j ↦ v (x j) := by
          funext j
          have := hVmem
          exact congrFun (congrArg (fun (a : AbsoluteValue K ℝ) ↦ (a : K → ℝ))
            (AbsoluteValue.LiesOver.under_eq V.1 v.1 (K := K))) (x j)
        rw [hfun]
      congr 1
      rw [hsup]
      exact Finset.prod_congr rfl fun i _ ↦ by
        rw [show V.1 (conjSystem Sinf Sfin w' L V.1 i y) = V (conjSystem Sinf Sfin w' L V.1 i y)
          from rfl, conjSystem_apply_inf hwI hv hVmem i x]
    rw [Finset.prod_congr rfl hfac, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult, pow_mul]
  · rw [Finset.prod_biUnion (pairwiseDisjoint_placesOverFinset_fin (E := E) Sfin),
      ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have hfac : ∀ W ∈ FinitePlace.placesOverFinset E v,
        (∏ i, W.1 (conjSystem Sinf Sfin w' L W.1 i y) / ⨆ j, W (y j))
          = (∏ i, w' v.1 (L v.1 i y) / ⨆ j, v (x j)) ^ W.localDegree K := by
      intro W hWmem
      rw [FinitePlace.mem_placesOverFinset] at hWmem
      have := hWmem
      have hsup : (⨆ j, W (y j)) = (⨆ j, v (x j)) ^ W.localDegree K := by
        have hfun : (fun j ↦ W (y j)) = fun j ↦ v (x j) ^ W.localDegree K := by
          funext j
          exact W.apply_algebraMap v (x j)
        rw [hfun, Real.iSup_pow_eq (fun j ↦ apply_nonneg _ _)]
      rw [hsup, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ ↦ by
        rw [show W.1 (conjSystem Sinf Sfin w' L W.1 i y) = W (conjSystem Sinf Sfin w' L W.1 i y)
          from rfl, conjSystem_apply_fin hwF hv hWmem i x, div_pow]
    rw [Finset.prod_congr rfl hfac, Finset.prod_pow_eq_pow_sum, FinitePlace.sum_localDegree]

end NumberField
