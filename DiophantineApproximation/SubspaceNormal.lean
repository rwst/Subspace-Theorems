/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Duality
public import DiophantineApproximation.WedgeForm

/-!
# The normal vector of a hyperplane and the transformed Plücker coordinates

Two pieces of linear algebra that Step III of the Subspace Theorem needs, both about a subspace
`V` of `Kⁿ⁺¹` of dimension `n`.

*The normal vector.* Such a `V` is the kernel of a single vector, `V = {x | ζ ⬝ᵥ x = 0}` with
`ζ ≠ 0`, and the Plücker coordinate of a basis of `V` at the `n`-subset omitting `k` vanishes
exactly when `ζ k` does (`Submodule.exists_normal`). This is Layer 3.5's Plücker duality
(`Submodule.exists_plucker_eq_plucker_compl`) read at the ranks `n` and `1`, where the annihilator
is a line and its one Plücker coordinate is a coordinate.

*The transformed coordinates.* For a system of forms `l : ι → Dual K (ι → K)`, the Plücker
coordinates of the transformed family `y j ↦ (l i (y j))ᵢ` are the values of the wedges of the
forms at the Plücker point of `y` (`exteriorPower.plucker_pi_apply`), so they are at once
determinants of the small numbers `l i (y j)` — which is how they are bounded at a place — and
linear forms in the Plücker coordinates of `y` with coefficients the minors of the coefficient
matrix of `l` — which is how they are bounded from below.

## Main definitions

* `Set.powersetCard.omitOne`: the `n`-element subset of an `(n+1)`-element `ι` omitting one index.
* `exteriorPower.wedgeFormCoeff`: the coefficient tuple of the wedge of the forms indexed by an
  `n`-subset, as a linear form on the Plücker coordinates.

## Main results

* `Submodule.exists_linearIndependent_fin`: a span of rank `n` is spanned by `n` independent
  members of the set.
* `Submodule.exists_normal`: the normal vector of a hyperplane, with the vanishing dictionary
  between its coordinates and the Plücker coordinates of a basis.
* `exteriorPower.plucker_pi_apply`: Laplace's identity for a transformed family.
* `exteriorPower.apply_plucker_le`, `exteriorPower.apply_plucker_pi_le` and
  `exteriorPower.apply_plucker_pi_le_of_isNonarchimedean`: the local bound on a transformed
  Plücker coordinate from local bounds on the values of the forms.

## Implementation notes

⚠ **The normal vector is not produced by a dimension count alone.** Only the inclusion
`V ⊆ ker ζ` is free — it is membership in the annihilator — and the reverse inclusion is a
comparison of ranks, for which the useful form is `Submodule.finrank_lt`: a proper submodule of
`Kⁿ⁺¹` has rank at most `n`, so `V` and `ker ζ` agree as soon as `ζ ≠ 0`. No rank-nullity
computation and no surjectivity of the functional appears.

⚠ **The vanishing dictionary is where the choice of basis disappears.** Layer 3.5 delivers *its
own* basis of `V`; the basis at hand is another one, and the two Plücker tuples differ by a
nonzero scalar because they define the same Plücker point (`Submodule.pluckerPoint_span_range`
and the injectivity of `Projectivization.mk` up to scalars). Only the *supports* are compared,
so the scalar and the sign at each index — Schmidt's involution `τ` — are both harmless.

⚠ **The transformed coordinates are a transpose away from Laplace's identity.** `plucker_apply`
reads the rows of a family along the columns of a subset, `wedgeForms_plucker` reads the forms
along the rows; the two matrices are transposes of each other, so `Matrix.det_transpose` is the
whole proof.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(7.16), (7.17) and Lemma 7.5.21; W. M. Schmidt, *On heights of algebraic subspaces and
diophantine problems*, Ann. of Math. 85 (1967), §1.

This is Layer 5.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset Module exteriorPower Matrix

namespace Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A span of rank `n` is spanned by `n` independent members of the set.** -/
theorem exists_linearIndependent_fin {s : Set V} {n : ℕ} (hs : finrank K (span K s) = n) :
    ∃ y : Fin n → V, (∀ j, y j ∈ s) ∧ LinearIndependent K y ∧
      span K (Set.range y) = span K s := by
  classical
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K s
  have hrange : Set.range ((↑) : b → V) = b := Subtype.range_coe
  have hfin : Fintype b := by
    have : FiniteDimensional K (span K (Set.range ((↑) : b → V))) := inferInstance
    exact (hbli.setFinite).fintype
  have hcard : Fintype.card b = n := by
    have hbas : Basis b K (span K (Set.range ((↑) : b → V))) := Basis.span hbli
    have hfr := finrank_eq_card_basis hbas
    rw [hrange] at hfr
    rw [← hs, ← hbspan, hfr]
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hcard
  have hr : Set.range (fun j ↦ ((e.symm j : b) : V)) = b := by
    rw [show (fun j ↦ ((e.symm j : b) : V)) = Subtype.val ∘ e.symm from rfl,
      Set.range_comp, e.symm.range_eq_univ, Set.image_univ, hrange]
  exact ⟨fun j ↦ ((e.symm j : b) : V), fun j ↦ hbsub (e.symm j).2,
    hbli.comp _ e.symm.injective, by rw [hr]; exact hbspan⟩

end Submodule

namespace Set.powersetCard

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The `n`-element subset that omits one index**, when `ι` has `n + 1` members. -/
def omitOne (hlk : 1 + n = Fintype.card ι) (k : ι) : Set.powersetCard ι n :=
  (Set.powersetCard.compl hlk).symm (Set.powersetCard.ofSingleton k)

theorem compl_omitOne (hlk : 1 + n = Fintype.card ι) (k : ι) :
    Set.powersetCard.compl hlk (omitOne hlk k) = Set.powersetCard.ofSingleton k :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem coe_omitOne (hlk : 1 + n = Fintype.card ι) (k : ι) :
    ((omitOne hlk k : Set.powersetCard ι n) : Finset ι) = ({k}ᶜ : Finset ι) := rfl

end Set.powersetCard

namespace exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}

/-- **The Plücker coordinates of a transformed family are the wedges of the forms at the
Plücker point.** This is Laplace's identity read in the other direction: transforming the
family by a system of forms and taking minors is applying the wedges of the forms. -/
theorem plucker_pi_apply (l : ι → Dual K (ι → K)) (y : Fin n → ι → K)
    (s : Set.powersetCard ι n) :
    plucker n (fun j i ↦ l i (y j)) s = wedgeForms l n s (plucker n y) := by
  rw [plucker_apply, wedgeForms_plucker, ← Matrix.det_transpose]
  rfl

/-- The coefficient tuple of the wedge of the forms indexed by `s`: its value at `t` is the
minor of the coefficient matrix of the forms cut out by the rows `s` and the columns `t`. -/
def wedgeFormCoeff (l : ι → Dual K (ι → K)) (n : ℕ) (s : Set.powersetCard ι n) :
    Set.powersetCard ι n → K :=
  plucker n fun a j ↦ l (Set.powersetCard.ofFinEmbEquiv.symm s a) (Pi.basisFun K ι j)

/-- The wedge of the forms indexed by `s`, read as a linear form in the Plücker coordinates. -/
theorem wedgeForms_eq_sum (l : ι → Dual K (ι → K)) (n : ℕ) (s : Set.powersetCard ι n)
    (z : Set.powersetCard ι n → K) :
    wedgeForms l n s z = ∑ t, wedgeFormCoeff l n s t * z t :=
  wedgeForm_apply n _ z

/-- **The coefficient tuple of a wedge of independent forms is nonzero.** -/
theorem wedgeCoeff_ne_zero {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l)
    (s : Set.powersetCard ι n) : wedgeFormCoeff l n s ≠ 0 := by
  intro h
  refine (linearIndependent_wedgeForms hl n).ne_zero s (LinearMap.ext fun z ↦ ?_)
  rw [wedgeForms_eq_sum]
  simp [show ∀ t, wedgeFormCoeff l n s t = 0 from fun t ↦ congrFun h t]

/-- **The transformed Plücker coordinates are bounded by the products of the local bounds on
the values of the forms**, with a factorial at an archimedean place. -/
theorem apply_plucker_pi_le (v : AbsoluteValue K ℝ) (l : ι → Dual K (ι → K))
    (y : Fin n → ι → K) {b : ι → ℝ} (hb : ∀ i j, v (l i (y j)) ≤ b i)
    (s : Set.powersetCard ι n) :
    v (plucker n (fun j i ↦ l i (y j)) s)
      ≤ n.factorial * ∏ i ∈ (s : Finset ι), b i := by
  rw [plucker_apply]
  refine AbsoluteValue.apply_det_le v _ fun σ ↦ ?_
  rw [← Set.powersetCard.prod_comp_ofFinEmbEquiv_symm s b]
  exact Finset.prod_le_prod₀ (fun a _ ↦ v.nonneg _) fun a _ ↦ hb _ _

/-- **A Plücker coordinate is bounded by the products of the local bounds on the entries**, with
a factorial at an archimedean place. -/
theorem apply_plucker_le (v : AbsoluteValue K ℝ) (y : Fin n → ι → K) {b : ι → ℝ}
    (hb : ∀ i j, v (y j i) ≤ b i) (s : Set.powersetCard ι n) :
    v (plucker n y s) ≤ n.factorial * ∏ i ∈ (s : Finset ι), b i := by
  rw [plucker_apply]
  refine AbsoluteValue.apply_det_le v _ fun σ ↦ ?_
  rw [← Set.powersetCard.prod_comp_ofFinEmbEquiv_symm s b]
  exact Finset.prod_le_prod₀ (fun a _ ↦ v.nonneg _) fun a _ ↦ hb _ _

/-- The nonarchimedean companion of `exteriorPower.apply_plucker_pi_le`: no factorial. -/
theorem apply_plucker_pi_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (l : ι → Dual K (ι → K)) (y : Fin n → ι → K) {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ i j, v (l i (y j)) ≤ b i) (s : Set.powersetCard ι n) :
    v (plucker n (fun j i ↦ l i (y j)) s) ≤ ∏ i ∈ (s : Finset ι), b i := by
  rw [plucker_apply]
  refine AbsoluteValue.apply_det_le_of_isNonarchimedean hv _
    (Finset.prod_nonneg fun i _ ↦ hb0 i) fun σ ↦ ?_
  rw [← Set.powersetCard.prod_comp_ofFinEmbEquiv_symm s b]
  exact Finset.prod_le_prod₀ (fun a _ ↦ v.nonneg _) fun a _ ↦ hb _ _

end exteriorPower

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}

theorem exists_normal {V : Submodule K (ι → K)} {y : Fin n → ι → K}
    (hy : LinearIndependent K y) (hVy : span K (Set.range y) = V)
    (hlk : 1 + n = Fintype.card ι) :
    ∃ ζ : ι → K, ζ ≠ 0 ∧ (∀ x, x ∈ V ↔ ζ ⬝ᵥ x = 0) ∧
      ∀ k : ι, (plucker n y (Set.powersetCard.omitOne hlk k) = 0 ↔ ζ k = 0) := by
  have hV : finrank K V = n := by
    rw [← hVy]
    exact (finrank_span_eq_card hy).trans (Fintype.card_fin n)
  obtain ⟨v, w, c, hc, hv, hw, hspanv, hspanw, hpl⟩ :=
    exists_plucker_eq_plucker_compl V hV hlk
  refine ⟨w 0, hw.ne_zero 0, ?_, ?_⟩
  · -- the kernel description
    have hmem : ∀ x ∈ V, w 0 ⬝ᵥ x = 0 := by
      intro x hx
      have hz : w 0 ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap := by
        rw [← hspanw]; exact subset_span ⟨0, rfl⟩
      rw [mem_comap_piEquiv_dualAnnihilator] at hz
      rw [dotProduct_comm]
      exact hz x hx
    have hf0 : Module.piEquiv ι K K (w 0) ≠ 0 := by
      simpa using (Module.piEquiv ι K K).map_eq_zero_iff.not.mpr (hw.ne_zero 0)
    have hle : V ≤ LinearMap.ker (Module.piEquiv ι K K (w 0)) := by
      intro x hx
      simp only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul]
      have := hmem x hx
      rw [dotProduct_comm] at this
      simpa [dotProduct] using this
    have hlt : finrank K (LinearMap.ker (Module.piEquiv ι K K (w 0))) < Fintype.card ι := by
      have := Submodule.finrank_lt (K := K) (V := ι → K)
        (s := LinearMap.ker (Module.piEquiv ι K K (w 0))) (by rwa [Ne, LinearMap.ker_eq_top])
      rwa [finrank_fintype_fun_eq_card] at this
    have heq : V = LinearMap.ker (Module.piEquiv ι K K (w 0)) :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hV]; omega)
    intro x
    rw [heq]
    simp only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul]
    rw [dotProduct_comm]
    simp [dotProduct]
  · intro k
    have h1 : finrank K (span K (Set.range y)) = n := by rw [hVy]; exact hV
    have h2 : finrank K (span K (Set.range v)) = n := by rw [hspanv]; exact hV
    have hpt : Projectivization.mk K (plucker n y) (plucker_ne_zero hy)
        = Projectivization.mk K (plucker n v) (plucker_ne_zero hv) := by
      rw [← pluckerPoint_span_range hy h1, ← pluckerPoint_span_range hv h2]
      exact pluckerPoint_congr (hVy.trans hspanv.symm) h1 h2
    obtain ⟨lam, hlam⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).1 hpt
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      exact plucker_ne_zero hy (by simpa using hlam.symm)
    have hw' : w = ![w 0] := by
      funext i
      fin_cases i
      rfl
    have hpw : plucker 1 w (Set.powersetCard.ofSingleton k) = w 0 k := by
      rw [hw']
      exact plucker_one_ofSingleton (w 0) k
    have hvk := hpl (Set.powersetCard.omitOne hlk k)
    rw [Set.powersetCard.compl_omitOne, hpw] at hvk
    have hyk : plucker n y (Set.powersetCard.omitOne hlk k)
        = lam * plucker n v (Set.powersetCard.omitOne hlk k) := by
      rw [← hlam]
      rfl
    rw [hyk]
    rcases hvk with h | h <;> rw [h] <;>
      simp [hlam0, hc]

end Submodule
