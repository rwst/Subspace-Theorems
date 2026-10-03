/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Plucker
public import QuantitativeSubspace.TwistedHeight

/-!
# Exterior powers of a twist and the twisted height of a subspace

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, §1–§2: a twist `A` of `Kⁿ` acts on `⋀^k Kⁿ` through the compound matrices of its
components, and the **twisted height of a subspace** `V` of dimension `k` is the twisted height,
for `⋀^k A`, of its Plücker coordinates. For `V` the whole space it is the adelic absolute value
of the determinant, `H_A(Ωⁿ) = |det A|_𝔸`.

## Main definitions

* `Matrix.compound k M`: the `k`-th compound matrix of `M`, the matrix of `⋀^k M` in the basis of
  `⋀^k (ι → R)` that the standard basis induces, indexed by the `k`-element subsets of `ι`.
* `NumberField.Twist.exteriorPower A k`: the twist `⋀^k A` of `⋀^k Kⁿ`.
* `NumberField.Twist.absDet A`: `|det A|_𝔸`, normalized absolutely.
* `NumberField.Twist.absSubspaceHeight A V`: the absolute twisted height `H_A(V)` of a subspace
  `V` of `Ωⁿ`.

## Main results

* `Matrix.compound_mulVec_plucker`: `⋀^k M` acts on Plücker coordinates as `M` acts on vectors.
* `Matrix.compound_mul`, `Matrix.compound_one`, `Matrix.compound_map`: functoriality, and
  compatibility with a ring homomorphism (complex conjugation, for `arch_conjugate`).
* `Matrix.compound_card_apply`: in top degree the compound matrix is the determinant.
* `NumberField.Twist.absSubspaceHeight_span_range`: the height of the span of `k` linearly
  independent points is the height of their Plücker coordinates — any basis computes it.
* `NumberField.Twist.absSubspaceHeight_top`: `H_A(Ωⁿ) = |det A|_𝔸`.
* `NumberField.Twist.absDet_pos`, `NumberField.Twist.absSubspaceHeight_pos`: both are positive.

## Implementation notes

The compound matrix is *defined* as the matrix of `exteriorPower.map`, so that multiplicativity
is functoriality of `⋀^k` and needs no Cauchy–Binet expansion; the minor formula is
`Matrix.compound_apply`. As in `ArithmeticHeights/Plucker.lean`, `[LinearOrder ι]` fixes which
wedge of basis vectors a `k`-element subset names. The height of a subspace is read from a chosen
representative of its Plücker point; `NumberField.Twist.absSubspaceHeight_eq` is the value on
any basis, which is the form a proof uses.

This is milestone Q2.1d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Matrix exteriorPower

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The `k`-th compound matrix** of `M`: the matrix of `⋀^k M` in the basis of `⋀^k (ι → R)`
induced by the standard basis. Its entries are the `k × k` minors of `M`
(`Matrix.compound_apply`). -/
noncomputable def compound (k : ℕ) (M : Matrix ι ι R) :
    Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) R :=
  LinearMap.toMatrix ((Pi.basisFun R ι).exteriorPower k) ((Pi.basisFun R ι).exteriorPower k)
    (exteriorPower.map k M.toLin')

/-- **`⋀^k M` acts on Plücker coordinates as `M` acts on vectors.** -/
theorem compound_mulVec_plucker (k : ℕ) (M : Matrix ι ι R) (v : Fin k → ι → R) :
    M.compound k *ᵥ plucker k v = plucker k fun i ↦ M *ᵥ v i := by
  simp only [plucker, Basis.equivFun_apply]
  rw [compound, LinearMap.toMatrix_mulVec_repr, map_apply_ιMulti]
  rfl

theorem compound_mul (k : ℕ) (M N : Matrix ι ι R) :
    (M * N).compound k = M.compound k * N.compound k := by
  rw [compound, compound, compound, Matrix.toLin'_mul M N, exteriorPower.map_comp,
    LinearMap.toMatrix_comp _ ((Pi.basisFun R ι).exteriorPower k)]

@[simp] theorem compound_one (k : ℕ) : (1 : Matrix ι ι R).compound k = 1 := by
  rw [compound, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- The Plücker coordinates of the basis vectors named by a `k`-element subset `t`. -/
theorem plucker_basisFun (k : ℕ) (t : Set.powersetCard ι k) :
    plucker k (fun i ↦ (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm t i) 1 : ι → R)) =
      Pi.single t 1 := by
  have h : ιMulti R k (fun i ↦ (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm t i) 1 : ι → R)) =
      (Pi.basisFun R ι).exteriorPower k t := by
    rw [basis_apply, ιMulti_family]
    congr 1
    funext i
    simp
  rw [plucker, Basis.equivFun_apply, h, Basis.repr_self, Finsupp.single_eq_pi_single]

/-- **The entries of the compound matrix are minors**: the column at `t` is the tuple of Plücker
coordinates of the columns of `M` named by `t`. -/
theorem compound_apply (k : ℕ) (M : Matrix ι ι R) (s t : Set.powersetCard ι k) :
    M.compound k s t = plucker k (fun i ↦ M.col (Set.powersetCard.ofFinEmbEquiv.symm t i)) s := by
  have h := compound_mulVec_plucker k M
    (fun i ↦ (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm t i) 1 : ι → R))
  simp only [plucker_basisFun, mulVec_single_one] at h
  exact congrFun h s

/-- **The compound matrix commutes with a ring homomorphism.** -/
theorem compound_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (M : Matrix ι ι R) :
    (M.map f).compound k = (M.compound k).map f := by
  ext s t
  rw [compound_apply, map_apply, compound_apply, ← Function.comp_apply (f := f),
    ← plucker_comp_ringHom]
  rfl

/-- In top degree there is a single `k`-element subset and the compound matrix is the
determinant. -/
theorem compound_card_apply (M : Matrix ι ι R) (s t : Set.powersetCard ι (Fintype.card ι)) :
    M.compound (Fintype.card ι) s t = M.det := by
  have hst : s = t := Subtype.ext <| by
    rw [Finset.eq_univ_of_card _ (Set.powersetCard.card_eq s),
      Finset.eq_univ_of_card _ (Set.powersetCard.card_eq t)]
  subst hst
  set σ := Set.powersetCard.ofFinEmbEquiv.symm s
  have hσ : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).mpr ⟨σ.injective, by simp⟩
  rw [compound_apply, plucker_apply, ← det_submatrix_equiv_self (Equiv.ofBijective σ hσ) M,
    ← det_transpose]
  rfl

theorem det_compound_ne_zero {K : Type*} [Field K] (k : ℕ) {M : Matrix ι ι K} (h : M.det ≠ 0) :
    (M.compound k).det ≠ 0 := by
  have h1 : M.compound k * M⁻¹.compound k = 1 := by
    rw [← compound_mul, mul_nonsing_inv _ h.isUnit, compound_one]
  exact left_ne_zero_of_mul_eq_one (by rw [← det_mul, h1, det_one])

end Matrix

namespace NumberField.Twist

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
  (A : Twist K ι)

/-- **The exterior power `⋀^k A` of a twist**: the compound matrices of its components, a twist
of `⋀^k Kⁿ` in Plücker coordinates. -/
noncomputable def exteriorPower (k : ℕ) : Twist K (Set.powersetCard ι k) where
  arch φ := (A.arch φ).compound k
  arch_det_ne_zero φ := det_compound_ne_zero k (A.arch_det_ne_zero φ)
  arch_conjugate φ := by rw [A.arch_conjugate, compound_map]
  fin v := (A.fin v).compound k
  fin_det_ne_zero v := det_compound_ne_zero k (A.fin_det_ne_zero v)
  finite_setOf_fin_ne_one := A.finite_setOf_fin_ne_one.subset fun v hv h ↦
    hv (by simp only [h, compound_one])

@[simp] theorem exteriorPower_arch (k : ℕ) (φ : K →+* ℂ) :
    (A.exteriorPower k).arch φ = (A.arch φ).compound k := rfl

@[simp] theorem exteriorPower_fin (k : ℕ) (v : FinitePlace K) :
    (A.exteriorPower k).fin v = (A.fin v).compound k := rfl

/-- **`|det A|_𝔸`**, the adelic absolute value of the determinant of a twist, normalized
absolutely: `(∏_φ |det A_φ| · ∏_v |det A_v|_v) ^ {1/[K:ℚ]}`, the product over the complex
embeddings counting each complex place twice. -/
noncomputable def absDet : ℝ :=
  ((∏ φ : K →+* ℂ, ‖(A.arch φ).det‖) * ∏ᶠ v : FinitePlace K, v (A.fin v).det) ^
    ((finrank ℚ K : ℝ))⁻¹

theorem absDet_pos : 0 < A.absDet := by
  refine Real.rpow_pos_of_pos (mul_pos (prod_pos fun φ _ ↦
    norm_pos_iff.mpr (A.arch_det_ne_zero φ)) ?_) _
  have hf : (fun v : FinitePlace K ↦ v (A.fin v).det).HasFiniteMulSupport :=
    A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])
  rw [finprod_eq_prod_of_mulSupport_subset _ (Set.Finite.coe_toFinset hf).symm.subset]
  exact prod_pos fun v _ ↦ FinitePlace.pos_iff.mpr (A.fin_det_ne_zero v)

/-- The twisted height relative to `K` of the point `1` of a one-dimensional space. -/
theorem mulHeight_const_one {κ : Type*} [Fintype κ] [DecidableEq κ] [Subsingleton κ]
    (B : Twist K κ) (s : κ) :
    B.mulHeight (fun _ ↦ (1 : K)) =
      (∏ φ : K →+* ℂ, ‖B.arch φ s s‖) * ∏ᶠ v : FinitePlace K, v (B.fin v s s) := by
  have : Unique κ := uniqueOfSubsingleton s
  rw [mulHeight]
  congr 1
  · refine prod_congr rfl fun φ _ ↦ ?_
    rw [archFactor, EuclideanSpace.norm_eq, Fintype.sum_subsingleton _ s,
      Real.sqrt_sq (norm_nonneg _)]
    simp [mulVec, dotProduct, Subsingleton.elim (default : κ) s]
  · refine finprod_congr fun v ↦ ?_
    rw [finFactor, FinitePlace.under_self, ciSup_unique]
    simp [mulVec, dotProduct, Subsingleton.elim (default : κ) s]

section Absolute

open IntermediateField

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- The absolute twisted height of a nonzero point of a one-dimensional space. -/
theorem absMulHeight_of_subsingleton {κ : Type*} [Fintype κ] [DecidableEq κ] [Subsingleton κ]
    (B : Twist K κ) {x : κ → Ω} (hx : x ≠ 0) (s : κ) :
    B.absMulHeight x = ((∏ φ : K →+* ℂ, ‖B.arch φ s s‖) *
      ∏ᶠ v : FinitePlace K, v (B.fin v s s)) ^ ((finrank ℚ K : ℝ))⁻¹ := by
  have hs : x s ≠ 0 := fun h ↦ hx (funext fun t ↦ by rwa [Subsingleton.elim t s])
  have hx1 : x = x s • (algebraMap K Ω ∘ fun _ ↦ 1) :=
    funext fun t ↦ by simp [Subsingleton.elim t s]
  rw [hx1, B.absMulHeight_smul _ hs, absMulHeight_algebraMap, mulHeight_const_one]

theorem absMulHeight_rep_mk {κ : Type*} [Fintype κ] [DecidableEq κ] (B : Twist K κ)
    {x : κ → Ω} (hx : x ≠ 0) : B.absMulHeight (Projectivization.mk Ω x hx).rep =
      B.absMulHeight x := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep Ω x hx
  rw [← ha, Units.smul_def, B.absMulHeight_smul _ a.ne_zero]

/-- **The absolute twisted height of a subspace** `V` of `Ωⁿ` (RT96 §1): the absolute twisted
height, for `⋀^k A` with `k = dim V`, of the Plücker coordinates of `V`. -/
noncomputable def absSubspaceHeight (V : Submodule Ω (ι → Ω)) : ℝ :=
  (A.exteriorPower (finrank Ω V)).absMulHeight (V.pluckerPoint rfl).rep

theorem absSubspaceHeight_pos (V : Submodule Ω (ι → Ω)) : 0 < A.absSubspaceHeight V :=
  (A.exteriorPower _).absMulHeight_pos (V.pluckerPoint rfl).rep_nonzero

theorem absSubspaceHeight_eq_pluckerPoint {k : ℕ} {V : Submodule Ω (ι → Ω)}
    (hV : finrank Ω V = k) :
    A.absSubspaceHeight V = (A.exteriorPower k).absMulHeight (V.pluckerPoint hV).rep := by
  subst hV
  rfl

/-- **The height of a subspace is computed by any basis.** -/
theorem absSubspaceHeight_eq {k : ℕ} {V : Submodule Ω (ι → Ω)} (hV : finrank Ω V = k)
    (b : Basis (Fin k) Ω V) :
    A.absSubspaceHeight V = (A.exteriorPower k).absMulHeight (plucker k fun i ↦ (b i : ι → Ω)) := by
  have hb := plucker_ne_zero (Submodule.linearIndependent_coe_basis b)
  rw [A.absSubspaceHeight_eq_pluckerPoint hV, Submodule.pluckerPoint_eq_mk hV b hb,
    absMulHeight_rep_mk]

/-- **The height of a span**: for `k` linearly independent points, the height of the subspace
they span is the height of their Plücker coordinates. -/
theorem absSubspaceHeight_span_range {k : ℕ} {v : Fin k → ι → Ω} (hv : LinearIndependent Ω v) :
    A.absSubspaceHeight (Submodule.span Ω (Set.range v)) =
      (A.exteriorPower k).absMulHeight (plucker k v) := by
  have hV : finrank Ω (Submodule.span Ω (Set.range v)) = k := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  rw [A.absSubspaceHeight_eq_pluckerPoint hV, Submodule.pluckerPoint_span_range hv hV,
    absMulHeight_rep_mk]

/-- **The height of the whole space is `|det A|_𝔸`** (RT96 §1). -/
theorem absSubspaceHeight_top : A.absSubspaceHeight (⊤ : Submodule Ω (ι → Ω)) = A.absDet := by
  set e := (Fintype.equivFin ι).symm
  have hv : LinearIndependent Ω (Pi.basisFun Ω ι ∘ e) :=
    (Pi.basisFun Ω ι).linearIndependent.comp e e.injective
  have hspan : Submodule.span Ω (Set.range (Pi.basisFun Ω ι ∘ e)) = ⊤ := by
    rw [Set.range_comp, e.range_eq_univ, Set.image_univ, Basis.span_eq]
  obtain ⟨s⟩ : Nonempty (Set.powersetCard ι (Fintype.card ι)) :=
    ⟨⟨Finset.univ, Finset.card_univ⟩⟩
  have : Subsingleton (Set.powersetCard ι (Fintype.card ι)) :=
    ⟨fun s t ↦ Subtype.ext <| by
      rw [Finset.eq_univ_of_card _ (Set.powersetCard.card_eq s),
        Finset.eq_univ_of_card _ (Set.powersetCard.card_eq t)]⟩
  rw [← hspan, A.absSubspaceHeight_span_range hv,
    absMulHeight_of_subsingleton _ (plucker_ne_zero hv) s, absDet]
  simp only [exteriorPower_arch, exteriorPower_fin, compound_card_apply]

end Absolute

end NumberField.Twist
