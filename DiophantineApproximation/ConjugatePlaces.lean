/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlacesOver

-- Used only inside proofs.
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Conjugate absolute values

Let `F / K` be a Galois extension of number fields. The Galois group acts on the absolute values
of `F` by `σ • w = w ∘ σ⁻¹`, and the action preserves the fibre over a place `v` of `K`, because
`σ` fixes `K` pointwise. The theorem of this file is that the action on that fibre is
**transitive**: any two absolute values of `F` restricting to `v` are conjugate.

## Main results

* `NumberField.exists_smul_eq_of_liesOver`: the milestone — for `F / K` Galois and `v` a place of
  `K`, any two absolute values of `F` over `v` differ by an element of `Gal(F/K)`.
* `NumberField.exists_smul_eq_of_liesOver_infinitePlace` and
  `NumberField.exists_smul_eq_of_liesOver_finitePlace`: the two halves.
* `NumberField.setOf_liesOver_eq_range_smul`: the same as a set identity — the fibre over `v` is
  one orbit — which is the form Layer 6.3 uses.
* `AbsoluteValue.instMulActionAlgEquiv`: the action itself, `σ • w = w ∘ σ⁻¹`, on all absolute
  values of `F`, matching Mathlib's action on `NumberField.InfinitePlace`.
* `AbsoluteValue.liesOver_smul`: the action preserves each fibre.

## Implementation notes

The infinite half is Mathlib's `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq` read through
Layer 0.1: `w` and `w'` *are* infinite places of `F`, and their restrictions agree.

⚠ The finite half needs **no equivariance statement about finite places**, and in particular
neither `Ideal.absNorm (σ 𝔓) = Ideal.absNorm 𝔓` nor invariance of the adic valuation, none of
which Mathlib has. Layer 0.1 classifies `w ∘ σ` on its own, as an absolute value over `v`, and
Layer 0.1's uniqueness clause identifies the prime it produces: `{y ∈ 𝓞 F | w (σ y) < 1}` is the
contraction of `{y | w y < 1}` along `σ`. Mathlib's `Ideal.exists_comap_galRestrict_eq` supplies
a `σ` carrying one prime above `𝔭` to another, and that is the whole proof. The exponents need
not be compared either: each side carries the exponent its own prime dictates.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Corollary 1.3.5.

This is the first half of Layer 0.2 of the `DiophantineApproximation` roadmap.
-/

public section

open IsDedekindDomain NumberField

namespace AbsoluteValue

section Action

variable {K F S : Type*} [CommSemiring K] [Semiring F] [Algebra K F] [Semiring S] [PartialOrder S]

/-- The Galois group of `F / K` acts on the absolute values of `F` by `σ • w = w ∘ σ⁻¹`. This is
the action Mathlib defines on `NumberField.InfinitePlace`, on all absolute values at once. -/
instance instMulActionAlgEquiv : MulAction (F ≃ₐ[K] F) (AbsoluteValue F S) where
  smul σ w := w.comp (f := (σ.symm : F →+* F)) (EquivLike.injective σ.symm)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem smul_apply (σ : F ≃ₐ[K] F) (w : AbsoluteValue F S) (x : F) :
    (σ • w) x = w (σ.symm x) := rfl

end Action

/-- **Conjugation preserves the fibre.** An element of `Gal(F/K)` fixes `K` pointwise, so it
carries absolute values over `v` to absolute values over `v`. -/
theorem liesOver_smul {K F : Type*} [Field K] [Field F] [Algebra K F] {v : AbsoluteValue K ℝ}
    (w : AbsoluteValue F ℝ) [w.LiesOver v] (σ : F ≃ₐ[K] F) : (σ • w).LiesOver v :=
  ⟨AbsoluteValue.ext fun u => by
    change w (σ.symm (algebraMap K F u)) = v u
    rw [AlgEquiv.commutes, apply_algebraMap_of_liesOver (v := v) w u]⟩

end AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Conjugate absolute values above an infinite place.** -/
theorem exists_smul_eq_of_liesOver_infinitePlace [IsGalois K F] (v : InfinitePlace K)
    (w w' : AbsoluteValue F ℝ) [w.LiesOver v.1] [w'.LiesOver v.1] :
    ∃ σ : F ≃ₐ[K] F, σ • w = w' := by
  obtain ⟨w₁, hw₁⟩ := exists_infinitePlace_eq_of_liesOver v w
  obtain ⟨w₁', hw₁'⟩ := exists_infinitePlace_eq_of_liesOver v w'
  have h₁ : w₁.LiesOver v := ⟨by rw [hw₁]; exact AbsoluteValue.LiesOver.under_eq w v.1⟩
  have h₁' : w₁'.LiesOver v := ⟨by rw [hw₁']; exact AbsoluteValue.LiesOver.under_eq w' v.1⟩
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
    ((InfinitePlace.LiesOver.comap_eq w₁ v).trans (InfinitePlace.LiesOver.comap_eq w₁' v).symm)
  refine ⟨σ, AbsoluteValue.ext fun x => ?_⟩
  have hx : w₁ (σ.symm x) = w₁' x := by rw [← hσ]; rfl
  rw [AbsoluteValue.smul_apply, ← hw₁, ← hw₁']
  exact hx

/-- **Conjugate absolute values above a finite place.** -/
theorem exists_smul_eq_of_liesOver_finitePlace [IsGalois K F] (v : FinitePlace K)
    (w w' : AbsoluteValue F ℝ) [w.LiesOver v.1] [w'.LiesOver v.1] :
    ∃ σ : F ≃ₐ[K] F, σ • w = w' := by
  obtain ⟨P, hP, hPw⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver v w
  obtain ⟨Q, hQ, hQw⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver v w'
  obtain ⟨τ, hτ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K F (𝓞 F)
    (p := v.maximalIdeal.asIdeal) (P₁ := P.asIdeal) (P₂ := Q.asIdeal)
    ⟨P.isPrime, hP⟩ ⟨Q.isPrime, hQ⟩
  have hpos : ∀ R : HeightOneSpectrum (𝓞 F),
      (0 : ℝ) < (((R.asIdeal.ramificationIdx (𝓞 K) * R.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹ :=
    fun R => inv_pos.mpr (by
      exact_mod_cast Nat.mul_pos (R.asIdeal.ramificationIdx_pos (𝓞 K))
        (R.asIdeal.inertiaDeg_pos (𝓞 K)))
  have hlo : (τ.symm • w).LiesOver v.1 := AbsoluteValue.liesOver_smul w τ.symm
  obtain ⟨R, -, hRw⟩ := exists_finitePlace_rpow_inv_eq_of_liesOver v (τ.symm • w)
  have hgal : ∀ y : 𝓞 F,
      τ.symm.symm ((y : F)) = ((galRestrict (𝓞 K) K F (𝓞 F) τ y : 𝓞 F) : F) := by
    intro y
    rw [AlgEquiv.symm_symm, RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
    exact (algebraMap_galRestrict_apply (𝓞 K) τ y).symm
  have hRQ : R = Q := by
    refine HeightOneSpectrum.ext (SetLike.ext fun y => ?_)
    rw [AbsoluteValue.mem_iff_apply_lt_one_of_rpow_eq (hpos R) hRw y, ← hτ, Ideal.mem_comap,
      AbsoluteValue.mem_iff_apply_lt_one_of_rpow_eq (hpos P) hPw]
    rw [AbsoluteValue.smul_apply, hgal y]
  refine ⟨τ.symm, AbsoluteValue.ext fun x => ?_⟩
  rw [hQw x, ← hRQ, ← hRw x]

/-- **Layer 0.2, conjugate absolute values.** For `F / K` Galois, the Galois group acts
transitively on the absolute values of `F` lying over a place of `K`. -/
theorem exists_smul_eq_of_liesOver [IsGalois K F] (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w w' : AbsoluteValue F ℝ)
    [w.LiesOver v] [w'.LiesOver v] : ∃ σ : F ≃ₐ[K] F, σ • w = w' := by
  rcases hv with h | h
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp h
    exact exists_smul_eq_of_liesOver_infinitePlace v' w w'
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp h
    exact exists_smul_eq_of_liesOver_finitePlace v' w w'

/-- **The fibre over `v` is a single orbit**, the form of Layer 0.2 that Layer 6.3 uses: every
absolute value of `F` over `v` is `σ • w` for one fixed `w` over `v`, and conversely. -/
theorem setOf_liesOver_eq_range_smul [IsGalois K F] (v : AbsoluteValue K ℝ)
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v} = Set.range fun σ : F ≃ₐ[K] F => σ • w := by
  ext w'
  constructor
  · intro hw'
    have : w'.LiesOver v := hw'
    exact exists_smul_eq_of_liesOver v hv w w'
  · rintro ⟨σ, rfl⟩
    exact AbsoluteValue.liesOver_smul w σ

end NumberField

section Examples

/-! ### Acceptance criteria -/

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **In the trivial extension the action is trivial**, because `Gal(K/K)` is. Together with the
fibre computation of Layer 0.1 this is the degenerate case of transitivity. -/
example (w : AbsoluteValue K ℝ) (σ : K ≃ₐ[K] K) : σ • w = w :=
  AbsoluteValue.ext fun x => by simpa using congrArg w (σ.symm.commutes x)

/-- **Conjugation preserves the archimedean/nonarchimedean split**, on the nose: it is a
relabelling of the field. -/
example (w : AbsoluteValue F ℝ) (σ : F ≃ₐ[K] F) (hna : IsNonarchimedean (w : F → ℝ)) :
    IsNonarchimedean (((σ • w : AbsoluteValue F ℝ)) : F → ℝ) := fun x y => by
  rw [AbsoluteValue.smul_apply, AbsoluteValue.smul_apply, AbsoluteValue.smul_apply, map_add]
  exact hna (σ.symm x) (σ.symm y)

/-- **Rejection test: the inverse in `σ • w = w ∘ σ⁻¹` is not decoration.** Composing with `σ`
instead reverses the order of a product, so `σ ↦ w ∘ σ` is an anti-action and cannot be a
`MulAction`; the two agree only on a commutative Galois group. -/
example (w : AbsoluteValue F ℝ) (σ τ : F ≃ₐ[K] F) (x : F) :
    ((σ * τ) • w) x = w (τ.symm (σ.symm x)) := rfl

/-- **Transitivity does need `F / K` Galois**, and this is where it enters: without it Mathlib's
`Ideal.exists_comap_galRestrict_eq` has no conclusion to offer, and the fibre over a finite place
genuinely splits into several orbits. The hypothesis is recorded here as the instance the
milestone takes. -/
example [IsGalois K F] (v : FinitePlace K) (w w' : AbsoluteValue F ℝ)
    [w.LiesOver v.1] [w'.LiesOver v.1] : ∃ σ : F ≃ₐ[K] F, σ • w = w' :=
  NumberField.exists_smul_eq_of_liesOver_finitePlace v w w'

end Examples
