/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Associativity
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

-- Used only inside proofs.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Hilbert polynomials of products

For multihomogeneous ideals `I₁ ⊆ K[X]` and `I₂ ⊆ K[Y]` in disjoint sets of variables, the ideal
`I₁ K[X, Y] + I₂ K[X, Y]` defines the product `V(I₁) × V(I₂)`. Its Hilbert function is the product
of the two Hilbert functions, `h(d₁, d₂) = h₁(d₁) · h₂(d₂)`
(`MvPolynomial.hilbertFunction_prodIdeal`), so its Hilbert polynomial is
`H₁(T₁) · H₂(T₂)`, its dimension is `dim V(I₁) + dim V(I₂)` and its degrees are the products
`d_{(α₁, α₂)} = d_{α₁}(I₁) · d_{α₂}(I₂)`. This is Evertse's Lemma 2 (Acta Arith. 73 (1995)) in the
language of multidegrees.

The proof is linear algebra in each multidegree `d = (d₁, d₂)`, with no Gröbner bases.
* `h(d) ≤ h₁ h₂`: a monomial of multidegree `d` is a product `X^{c₁} Y^{c₂}`, and modulo `I` each
  factor lies in a complement `W_i` of `(I_i)_{d_i}`, so `K[X, Y]_d ⊆ I_d + W₁ W₂`.
* `h(d) ≥ h₁ h₂`: the algebra map `K[X, Y] → K[X]/I₁ ⊗ K[Y]/I₂` kills `I`, and the image of
  `K[X, Y]_d` contains `U₁ ⊗ U₂` with `U_i` the image of `K[X]_{d_i}` in `K[X]/I_i`, of dimension
  `h_i(d_i)`.

## Main definitions

* `MvPolynomial.prodIdeal I₁ I₂`: the ideal `I₁ K[X, Y] + I₂ K[X, Y]` of the product.
* `MvPolynomial.prodQuotMap I₁ I₂`: the algebra map `K[X, Y] → K[X]/I₁ ⊗ K[Y]/I₂`.

## Main statements

* `MvPolynomial.hilbertFunction_prodIdeal`: the Hilbert function of a product, from
  `MvPolynomial.hilbertFunction_prodIdeal_le` and `MvPolynomial.le_hilbertFunction_prodIdeal`.
* `MvPolynomial.hilbertPoly_prodIdeal`: its Hilbert polynomial.
* `MvPolynomial.totalDegree_hilbertPoly_prodIdeal`: its dimension.
* `MvPolynomial.multidegree_prodIdeal`: its degrees.
-/

@[expose] public section

open Module Finset
open scoped TensorProduct

variable {σ₁ σ₂ ι₁ ι₂ K : Type*}

namespace MvPolynomial

section Rename

variable {σ τ M M' R : Type*} [AddCommMonoid M] [AddCommMonoid M'] [CommSemiring R]

theorem weight_mapDomain {w : σ → M} {w' : τ → M'} (φ : M →+ M') {f : σ → τ}
    (h : ∀ s, w' (f s) = φ (w s)) (u : σ →₀ ℕ) :
    Finsupp.weight w' (Finsupp.mapDomain f u) = φ (Finsupp.weight w u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [Finsupp.mapDomain_add, map_add, hu, hv, map_add, map_add]
  | single s n => rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single, h,
      map_nsmul]

theorem isWeightedHomogeneous_rename {w : σ → M} {w' : τ → M'} (φ : M →+ M') {f : σ → τ}
    (h : ∀ s, w' (f s) = φ (w s)) {p : MvPolynomial σ R} {d : M}
    (hp : IsWeightedHomogeneous w p d) : IsWeightedHomogeneous w' (rename f p) (φ d) := by
  intro c hc
  by_contra hne
  apply hc
  refine coeff_rename_eq_zero f p c fun u hu ↦ ?_
  by_contra hu0
  exact hne (hu ▸ (weight_mapDomain φ h u).trans (congrArg φ (hp hu0)))

end Rename

variable [DecidableEq ι₁] [DecidableEq ι₂] {b₁ : σ₁ → ι₁} {b₂ : σ₂ → ι₂}

/-- Extension of a multidegree on the first factor by `0` on the second. -/
def inlDeg : (ι₁ → ℕ) →+ (ι₁ ⊕ ι₂ → ℕ) where
  toFun x := Sum.elim x 0
  map_zero' := by ext (i | i) <;> rfl
  map_add' x y := by ext (i | i) <;> simp

/-- Extension of a multidegree on the second factor by `0` on the first. -/
def inrDeg : (ι₂ → ℕ) →+ (ι₁ ⊕ ι₂ → ℕ) where
  toFun x := Sum.elim 0 x
  map_zero' := by ext (i | i) <;> rfl
  map_add' x y := by ext (i | i) <;> simp

theorem multiWeight_sumMap_inl (s : σ₁) :
    multiWeight (Sum.map b₁ b₂) (Sum.inl s) = inlDeg (multiWeight b₁ s) := by
  ext (i | i) <;> simp [multiWeight, inlDeg, Pi.single_apply]

theorem multiWeight_sumMap_inr (s : σ₂) :
    multiWeight (Sum.map b₁ b₂) (Sum.inr s) = inrDeg (multiWeight b₂ s) := by
  ext (i | i) <;> simp [multiWeight, inrDeg, Pi.single_apply]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem inlDeg_add_inrDeg (d : ι₁ ⊕ ι₂ → ℕ) :
    inlDeg (d ∘ Sum.inl) + inrDeg (d ∘ Sum.inr) = d := by
  ext (i | i) <;> simp [inlDeg, inrDeg]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem eq_mapDomain_add_mapDomain (c : σ₁ ⊕ σ₂ →₀ ℕ) :
    c = Finsupp.mapDomain Sum.inl (c.comapDomain Sum.inl Sum.inl_injective.injOn) +
      Finsupp.mapDomain Sum.inr (c.comapDomain Sum.inr Sum.inr_injective.injOn) := by
  ext (s | s) <;> simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
    Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range]

variable [Field K]

theorem isWeightedHomogeneous_rename_inl {p : MvPolynomial σ₁ K} {d : ι₁ → ℕ}
    (hp : IsWeightedHomogeneous (multiWeight b₁) p d) :
    IsWeightedHomogeneous (multiWeight (Sum.map b₁ b₂)) (rename Sum.inl p) (inlDeg d) :=
  isWeightedHomogeneous_rename inlDeg multiWeight_sumMap_inl hp

theorem isWeightedHomogeneous_rename_inr {p : MvPolynomial σ₂ K} {d : ι₂ → ℕ}
    (hp : IsWeightedHomogeneous (multiWeight b₂) p d) :
    IsWeightedHomogeneous (multiWeight (Sum.map b₁ b₂)) (rename Sum.inr p) (inrDeg d) :=
  isWeightedHomogeneous_rename inrDeg multiWeight_sumMap_inr hp

/-- The ideal `I₁ K[X, Y] + I₂ K[X, Y]` of `V(I₁) × V(I₂)`. -/
noncomputable def prodIdeal (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K)) :
    Ideal (MvPolynomial (σ₁ ⊕ σ₂) K) :=
  I₁.map (rename Sum.inl) ⊔ I₂.map (rename Sum.inr)

/-- A monomial of `K[X, Y]` is a product of monomials of `K[X]` and `K[Y]`. -/
theorem monomial_eq_rename_mul_rename (c : σ₁ ⊕ σ₂ →₀ ℕ) (a : K) :
    monomial c a = rename Sum.inl (monomial (c.comapDomain Sum.inl Sum.inl_injective.injOn) a) *
      rename Sum.inr (monomial (c.comapDomain Sum.inr Sum.inr_injective.injOn) 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, mul_one,
    ← eq_mapDomain_add_mapDomain]

theorem weight_sumMap (c : σ₁ ⊕ σ₂ →₀ ℕ) :
    Finsupp.weight (multiWeight (Sum.map b₁ b₂)) c =
      inlDeg (Finsupp.weight (multiWeight b₁) (c.comapDomain Sum.inl Sum.inl_injective.injOn)) +
      inrDeg (Finsupp.weight (multiWeight b₂) (c.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  conv_lhs => rw [eq_mapDomain_add_mapDomain c]
  rw [map_add, weight_mapDomain inlDeg multiWeight_sumMap_inl,
    weight_mapDomain inrDeg multiWeight_sumMap_inr]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem inlDeg_add_inrDeg_comp_inl (x : ι₁ → ℕ) (y : ι₂ → ℕ) :
    (inlDeg x + inrDeg y) ∘ Sum.inl = x := by
  ext i
  simp [inlDeg, inrDeg]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem inlDeg_add_inrDeg_comp_inr (x : ι₁ → ℕ) (y : ι₂ → ℕ) :
    (inlDeg x + inrDeg y) ∘ Sum.inr = y := by
  ext i
  simp [inlDeg, inrDeg]

section Count

variable {σ ι : Type*} [DecidableEq ι]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- A complement of `I_d` in `K[X]_d`; its dimension is `h_I(d)`. -/
theorem exists_complement [Finite σ] [Finite ι] (b : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℕ) :
    ∃ W : Submodule K (MvPolynomial σ K), W ≤ weightedHomogeneousSubmodule K (multiWeight b) d ∧
      weightedHomogeneousSubmodule K (multiWeight b) d ≤
        I.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b) d ⊔ W ∧
      finrank K W = hilbertFunction b I d := by
  set Γ := weightedHomogeneousSubmodule K (multiWeight b) d
  set p : Submodule K Γ := (I.restrictScalars K).comap Γ.subtype
  obtain ⟨q, hq⟩ := p.exists_isCompl
  refine ⟨q.map Γ.subtype, Submodule.map_subtype_le _ _, fun x hx ↦ ?_, ?_⟩
  · have : (⟨x, hx⟩ : Γ) ∈ p ⊔ q := hq.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp this
    have hx' : x = (y : MvPolynomial σ K) + z := by rw [← Submodule.coe_add, hyz]
    rw [hx']
    exact Submodule.add_mem_sup ⟨hy, y.2⟩ ⟨z, hz, rfl⟩
  · have h1 := Submodule.finrank_add_eq_of_isCompl hq
    have h2 : finrank K (q.map Γ.subtype) = finrank K q :=
      (Submodule.equivMapOfInjective _ Γ.injective_subtype q).finrank_eq.symm
    have h3 : finrank K p = finrank K ↥(I.restrictScalars K ⊓ Γ) := by
      have : p = (I.restrictScalars K ⊓ Γ).comap Γ.subtype := by
        rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
      rw [this]
      exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
    change _ = finrank K Γ - finrank K ↥(I.restrictScalars K ⊓ Γ)
    omega

end Count

/-- Products of `K[X]_{d₁}` and `K[Y]_{d₂}` lie in `I_d + W₁ W₂`. -/
private theorem rename_mul_rename_mem {I₁ : Ideal (MvPolynomial σ₁ K)}
    {I₂ : Ideal (MvPolynomial σ₂ K)} {d : ι₁ ⊕ ι₂ → ℕ} {W₁ : Submodule K (MvPolynomial σ₁ K)}
    {W₂ : Submodule K (MvPolynomial σ₂ K)}
    (hW₁ : W₁ ≤ weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl))
    (hW₁' : weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl) ≤
      I₁.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl) ⊔ W₁)
    (hW₂ : W₂ ≤ weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr))
    (hW₂' : weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr) ≤
      I₂.restrictScalars K ⊓ weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr) ⊔ W₂)
    {p₁ : MvPolynomial σ₁ K} {p₂ : MvPolynomial σ₂ K}
    (hp₁ : p₁ ∈ weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl))
    (hp₂ : p₂ ∈ weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr)) :
    rename Sum.inl p₁ * rename Sum.inr p₂ ∈
      (prodIdeal I₁ I₂).restrictScalars K ⊓
          weightedHomogeneousSubmodule K (multiWeight (Sum.map b₁ b₂)) d ⊔
        W₁.map (rename Sum.inl).toLinearMap * W₂.map (rename Sum.inr).toLinearMap := by
  obtain ⟨r₁, ⟨hr₁I, hr₁Γ⟩, s₁, hs₁, rfl⟩ := Submodule.mem_sup.mp (hW₁' hp₁)
  obtain ⟨r₂, ⟨hr₂I, hr₂Γ⟩, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp (hW₂' hp₂)
  have hd : inlDeg (d ∘ Sum.inl) + inrDeg (d ∘ Sum.inr) = d := inlDeg_add_inrDeg d
  have hhom : ∀ {x : MvPolynomial σ₁ K} {y : MvPolynomial σ₂ K},
      x ∈ weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl) →
      y ∈ weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr) →
      rename Sum.inl x * rename Sum.inr y ∈
        weightedHomogeneousSubmodule K (multiWeight (Sum.map b₁ b₂)) d := by
    intro x y hx hy
    rw [mem_weightedHomogeneousSubmodule, ← hd]
    exact (isWeightedHomogeneous_rename_inl (b₂ := b₂) hx).mul
      (isWeightedHomogeneous_rename_inr (b₁ := b₁) hy)
  have hI₁ : ∀ x ∈ I₁, rename Sum.inl x ∈ prodIdeal I₁ I₂ := fun x hx ↦
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)
  have hI₂ : ∀ x ∈ I₂, rename Sum.inr x ∈ prodIdeal I₁ I₂ := fun x hx ↦
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx)
  have hs₁Γ := hW₁ hs₁
  have hs₂Γ := hW₂ hs₂
  have : rename Sum.inl (r₁ + s₁) * rename Sum.inr (r₂ + s₂) =
      (rename Sum.inl r₁ * rename Sum.inr (r₂ + s₂) + rename Sum.inl s₁ * rename Sum.inr r₂) +
        rename Sum.inl s₁ * rename Sum.inr s₂ := by
    simp only [map_add]
    ring
  rw [this]
  refine Submodule.add_mem_sup (Submodule.add_mem _ ⟨?_, ?_⟩ ⟨?_, ?_⟩)
    (Submodule.mul_mem_mul ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩)
  · exact Ideal.mul_mem_right _ _ (hI₁ r₁ hr₁I)
  · exact hhom hr₁Γ (Submodule.add_mem _ hr₂Γ hs₂Γ)
  · exact Ideal.mul_mem_left _ _ (hI₂ r₂ hr₂I)
  · exact hhom hs₁Γ hr₂Γ

variable [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂]

/-- **The upper bound** `h(d₁, d₂) ≤ h₁(d₁) h₂(d₂)`. -/
theorem hilbertFunction_prodIdeal_le (I₁ : Ideal (MvPolynomial σ₁ K))
    (I₂ : Ideal (MvPolynomial σ₂ K)) (d : ι₁ ⊕ ι₂ → ℕ) :
    hilbertFunction (Sum.map b₁ b₂) (prodIdeal I₁ I₂) d ≤
      hilbertFunction b₁ I₁ (d ∘ Sum.inl) * hilbertFunction b₂ I₂ (d ∘ Sum.inr) := by
  classical
  obtain ⟨W₁, hW₁, hW₁', hr₁⟩ := exists_complement b₁ I₁ (d ∘ Sum.inl)
  obtain ⟨W₂, hW₂, hW₂', hr₂⟩ := exists_complement b₂ I₂ (d ∘ Sum.inr)
  set Γ := weightedHomogeneousSubmodule K (multiWeight (Sum.map b₁ b₂)) d
  set M := W₁.map (rename (R := K) Sum.inl).toLinearMap
  set N := W₂.map (rename (R := K) Sum.inr).toLinearMap
  have hΓ : Γ ≤ (prodIdeal I₁ I₂).restrictScalars K ⊓ Γ ⊔ M * N := by
    intro x hx
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun c hc ↦ ?_
    have hwc : Finsupp.weight (multiWeight (Sum.map b₁ b₂)) c = d :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx (mem_support_iff.mp hc)
    rw [weight_sumMap] at hwc
    rw [monomial_eq_rename_mul_rename]
    refine rename_mul_rename_mem hW₁ hW₁' hW₂ hW₂' ?_ ?_
    · rw [← hwc, inlDeg_add_inrDeg_comp_inl]
      exact isWeightedHomogeneous_monomial _ _ _ rfl
    · rw [← hwc, inlDeg_add_inrDeg_comp_inr]
      exact isWeightedHomogeneous_monomial _ _ _ rfl
  have : FiniteDimensional K W₁ := Submodule.finiteDimensional_of_le hW₁
  have : FiniteDimensional K W₂ := Submodule.finiteDimensional_of_le hW₂
  have : FiniteDimensional K ↥(M * N) := by
    rw [← Submodule.mulMap_range]
    infer_instance
  have : FiniteDimensional K ↥((prodIdeal I₁ I₂).restrictScalars K ⊓ Γ) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hMN : finrank K ↥(M * N) ≤ finrank K W₁ * finrank K W₂ := by
    rw [← Submodule.mulMap_range]
    refine (LinearMap.finrank_range_le _).trans ?_
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_le_mul (Submodule.finrank_map_le _ _) (Submodule.finrank_map_le _ _)
  have hle := (Submodule.finrank_mono hΓ).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [hilbertFunction]
  change finrank K Γ - finrank K ↥((prodIdeal I₁ I₂).restrictScalars K ⊓ Γ) ≤ _
  rw [← hr₁, ← hr₂]
  omega

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
theorem finrank_comap_subtype {V : Type*} [AddCommGroup V] [Module K V] (J Γ : Submodule K V) :
    finrank K ↥(J.comap Γ.subtype) = finrank K ↥(J ⊓ Γ) := by
  have : J.comap Γ.subtype = (J ⊓ Γ).comap Γ.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [this]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

section Lower

variable {σ ι : Type*} [DecidableEq ι]

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
/-- The image of `K[X]_d` in `K[X]/I` has dimension `h_I(d)`. -/
theorem finrank_map_mk [Finite σ] [Finite ι] (b : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℕ) :
    finrank K ↥((weightedHomogeneousSubmodule K (multiWeight b) d).map
      (Ideal.Quotient.mkₐ K I).toLinearMap) = hilbertFunction b I d := by
  set Γ := weightedHomogeneousSubmodule K (multiWeight b) d
  set ψ := (Ideal.Quotient.mkₐ K I).toLinearMap ∘ₗ Γ.subtype
  have hker : LinearMap.ker ψ = (I.restrictScalars K).comap Γ.subtype := by
    ext x
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_comp, Submodule.range_subtype, hker, finrank_comap_subtype] at h
  rw [hilbertFunction]
  change _ = finrank K Γ - finrank K ↥(I.restrictScalars K ⊓ Γ)
  omega

end Lower

/-- The algebra map `K[X, Y] → K[X]/I₁ ⊗ K[Y]/I₂`. -/
noncomputable def prodQuotMap (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K)) :
    MvPolynomial (σ₁ ⊕ σ₂) K →ₐ[K] (MvPolynomial σ₁ K ⧸ I₁) ⊗[K] (MvPolynomial σ₂ K ⧸ I₂) :=
  aeval (R := K) (Sum.elim (fun s ↦ Ideal.Quotient.mk I₁ (X s) ⊗ₜ[K] 1) fun s ↦
    1 ⊗ₜ[K] Ideal.Quotient.mk I₂ (X s))

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
theorem prodQuotMap_rename_mul_rename (I₁ : Ideal (MvPolynomial σ₁ K))
    (I₂ : Ideal (MvPolynomial σ₂ K)) (p : MvPolynomial σ₁ K) (q : MvPolynomial σ₂ K) :
    prodQuotMap I₁ I₂ (rename Sum.inl p * rename Sum.inr q) =
      Ideal.Quotient.mk I₁ p ⊗ₜ Ideal.Quotient.mk I₂ q := by
  have h₁ : (prodQuotMap I₁ I₂).comp (rename Sum.inl) =
      Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ K I₁) :=
    algHom_ext fun s ↦ by simp [prodQuotMap]
  have h₂ : (prodQuotMap I₁ I₂).comp (rename Sum.inr) =
      Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ K I₂) :=
    algHom_ext fun s ↦ by simp [prodQuotMap]
  rw [map_mul, ← AlgHom.comp_apply, h₁, ← AlgHom.comp_apply (prodQuotMap I₁ I₂), h₂]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
theorem prodIdeal_le_ker (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K)) :
    prodIdeal I₁ I₂ ≤ RingHom.ker (prodQuotMap I₁ I₂) := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_)
    (Ideal.map_le_iff_le_comap.mpr fun q hq ↦ ?_)
  · rw [Ideal.mem_comap, RingHom.mem_ker, ← mul_one (rename Sum.inl p), ← map_one (rename Sum.inr),
      prodQuotMap_rename_mul_rename, Ideal.Quotient.eq_zero_iff_mem.mpr hp, TensorProduct.zero_tmul]
  · rw [Ideal.mem_comap, RingHom.mem_ker, ← one_mul (rename Sum.inr q), ← map_one (rename Sum.inl),
      prodQuotMap_rename_mul_rename, Ideal.Quotient.eq_zero_iff_mem.mpr hq, TensorProduct.tmul_zero]

/-- **The lower bound** `h(d₁, d₂) ≥ h₁(d₁) h₂(d₂)`. -/
theorem le_hilbertFunction_prodIdeal (I₁ : Ideal (MvPolynomial σ₁ K))
    (I₂ : Ideal (MvPolynomial σ₂ K)) (d : ι₁ ⊕ ι₂ → ℕ) :
    hilbertFunction b₁ I₁ (d ∘ Sum.inl) * hilbertFunction b₂ I₂ (d ∘ Sum.inr) ≤
      hilbertFunction (Sum.map b₁ b₂) (prodIdeal I₁ I₂) d := by
  set Γ := weightedHomogeneousSubmodule K (multiWeight (Sum.map b₁ b₂)) d
  set Γ₁ := weightedHomogeneousSubmodule K (multiWeight b₁) (d ∘ Sum.inl)
  set Γ₂ := weightedHomogeneousSubmodule K (multiWeight b₂) (d ∘ Sum.inr)
  set U₁ := Γ₁.map (Ideal.Quotient.mkₐ K I₁).toLinearMap
  set U₂ := Γ₂.map (Ideal.Quotient.mkₐ K I₂).toLinearMap
  set φ := prodQuotMap I₁ I₂
  set T := TensorProduct.map U₁.subtype U₂.subtype
  have hT : Function.Injective T :=
    TensorProduct.map_injective_of_flat_flat _ _ U₁.injective_subtype U₂.injective_subtype
  have hrange : LinearMap.range T ≤ Γ.map φ.toLinearMap := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul u₁ u₂ =>
      obtain ⟨p₁, hp₁, hu₁⟩ := u₁.2
      obtain ⟨p₂, hp₂, hu₂⟩ := u₂.2
      refine ⟨rename Sum.inl p₁ * rename Sum.inr p₂, ?_, ?_⟩
      · refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
        rw [← inlDeg_add_inrDeg d]
        exact (isWeightedHomogeneous_rename_inl (b₂ := b₂) hp₁).mul
          (isWeightedHomogeneous_rename_inr (b₁ := b₁) hp₂)
      · simp only [T, TensorProduct.map_tmul, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
          φ, prodQuotMap_rename_mul_rename]
        rw [← hu₁, ← hu₂]
        rfl
  set ψ := φ.toLinearMap ∘ₗ Γ.subtype
  have hker : ((prodIdeal I₁ I₂).restrictScalars K).comap Γ.subtype ≤ LinearMap.ker ψ :=
    fun x hx ↦ prodIdeal_le_ker I₁ I₂ hx
  have hψ := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_comp, Submodule.range_subtype] at hψ
  have h1 := Submodule.finrank_mono hker
  rw [finrank_comap_subtype] at h1
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hT, Module.finrank_tensorProduct, finrank_map_mk,
    finrank_map_mk] at h2
  have hh : hilbertFunction (Sum.map b₁ b₂) (prodIdeal I₁ I₂) d =
      finrank K Γ - finrank K ↥((prodIdeal I₁ I₂).restrictScalars K ⊓ Γ) := rfl
  rw [hh]
  omega

/-- **The Hilbert function of a product**: `h(d₁, d₂) = h₁(d₁) · h₂(d₂)`. -/
theorem hilbertFunction_prodIdeal (I₁ : Ideal (MvPolynomial σ₁ K))
    (I₂ : Ideal (MvPolynomial σ₂ K)) (d : ι₁ ⊕ ι₂ → ℕ) :
    hilbertFunction (Sum.map b₁ b₂) (prodIdeal I₁ I₂) d =
      hilbertFunction b₁ I₁ (d ∘ Sum.inl) * hilbertFunction b₂ I₂ (d ∘ Sum.inr) :=
  le_antisymm (hilbertFunction_prodIdeal_le I₁ I₂ d) (le_hilbertFunction_prodIdeal I₁ I₂ d)

section Polynomial

omit [Field K] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂] in
theorem mapDomain_add_mapDomain_eq_iff (u : σ₁ →₀ ℕ) (v : σ₂ →₀ ℕ) (c : σ₁ ⊕ σ₂ →₀ ℕ) :
    Finsupp.mapDomain Sum.inl u + Finsupp.mapDomain Sum.inr v = c ↔
      u = c.comapDomain Sum.inl Sum.inl_injective.injOn ∧
        v = c.comapDomain Sum.inr Sum.inr_injective.injOn := by
  constructor
  · rintro rfl
    constructor <;> ext s <;> simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
      Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range]
  · rintro ⟨rfl, rfl⟩
    exact (eq_mapDomain_add_mapDomain c).symm

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
/-- The coefficients of a product of polynomials in disjoint variables. -/
theorem coeff_rename_inl_mul_rename_inr {R : Type*} [CommSemiring R] (P : MvPolynomial ι₁ R)
    (Q : MvPolynomial ι₂ R) (α : ι₁ ⊕ ι₂ →₀ ℕ) :
    (rename Sum.inl P * rename Sum.inr Q).coeff α =
      P.coeff (α.comapDomain Sum.inl Sum.inl_injective.injOn) *
        Q.coeff (α.comapDomain Sum.inr Sum.inr_injective.injOn) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hP']
  | monomial u a =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' hQ hQ' =>
      simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hQ, hQ']
    | monomial v c =>
      rw [rename_monomial, rename_monomial, monomial_mul_monomial, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases hu : u = α.comapDomain Sum.inl Sum.inl_injective.injOn <;>
        by_cases hv : v = α.comapDomain Sum.inr Sum.inr_injective.injOn <;>
        simp [hu, hv, mapDomain_add_mapDomain_eq_iff]

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
/-- Disjoint variables add total degrees. -/
theorem totalDegree_rename_inl_mul_rename_inr {P : MvPolynomial ι₁ ℚ} {Q : MvPolynomial ι₂ ℚ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (rename Sum.inl P * rename Sum.inr Q).totalDegree = P.totalDegree + Q.totalDegree := by
  refine le_antisymm ((totalDegree_mul _ _).trans (add_le_add (totalDegree_rename_le _ _)
    (totalDegree_rename_le _ _))) ?_
  obtain ⟨α₁, hα₁, h₁⟩ := exists_coeff_ne_zero_degree_eq hP
  obtain ⟨α₂, hα₂, h₂⟩ := exists_coeff_ne_zero_degree_eq hQ
  set α := Finsupp.mapDomain Sum.inl α₁ + Finsupp.mapDomain Sum.inr α₂
  obtain ⟨e₁, e₂⟩ := (mapDomain_add_mapDomain_eq_iff α₁ α₂ α).mp rfl
  have hne : (rename Sum.inl P * rename Sum.inr Q).coeff α ≠ 0 := by
    rw [coeff_rename_inl_mul_rename_inr, ← e₁, ← e₂]
    exact mul_ne_zero hα₁ hα₂
  have hα : α.degree = α₁.degree + α₂.degree := by simp [α]
  rw [← h₁, ← h₂, ← hα, Finsupp.degree_apply]
  exact le_totalDegree (mem_support_iff.mpr hne)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
theorem isWeightedHomogeneous_map {σ τ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    {w : σ → M} {w' : τ → M'} (φ : M →+ M') {f : σ → τ} (h : ∀ s, w' (f s) = φ (w s))
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous w) :
    (I.map (rename (R := K) f)).IsWeightedHomogeneous w' := by
  classical
  set H := {p ∈ I | ∃ d, IsWeightedHomogeneous w p d}
  have hIH : I = Ideal.span H := by
    refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr fun p hp ↦ hp.1)
    rw [← sum_weightedHomogeneousComponent w p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    exact Ideal.sum_mem _ fun d _ ↦ Ideal.subset_span
      ⟨hI hp d, d, weightedHomogeneousComponent_isWeightedHomogeneous d p⟩
  rw [hIH, Ideal.map_span]
  refine isWeightedHomogeneous_span fun _ ⟨p, ⟨_, d, hd⟩, hp⟩ ↦ ?_
  exact ⟨φ d, hp ▸ isWeightedHomogeneous_rename φ h hd⟩

omit [Finite σ₁] [Finite σ₂] [Finite ι₁] [Finite ι₂] in
theorem isWeightedHomogeneous_prodIdeal {I₁ : Ideal (MvPolynomial σ₁ K)}
    {I₂ : Ideal (MvPolynomial σ₂ K)} (hI₁ : I₁.IsWeightedHomogeneous (multiWeight b₁))
    (hI₂ : I₂.IsWeightedHomogeneous (multiWeight b₂)) :
    (prodIdeal I₁ I₂).IsWeightedHomogeneous (multiWeight (Sum.map b₁ b₂)) :=
  (isWeightedHomogeneous_map inlDeg multiWeight_sumMap_inl hI₁).sup
    (isWeightedHomogeneous_map inrDeg multiWeight_sumMap_inr hI₂)

/-- **The Hilbert polynomial of a product**: `H(T₁, T₂) = H₁(T₁) · H₂(T₂)`. -/
theorem hilbertPoly_prodIdeal (hb₁ : Function.Surjective b₁) (hb₂ : Function.Surjective b₂)
    {I₁ : Ideal (MvPolynomial σ₁ K)} {I₂ : Ideal (MvPolynomial σ₂ K)}
    (hI₁ : I₁.IsWeightedHomogeneous (multiWeight b₁))
    (hI₂ : I₂.IsWeightedHomogeneous (multiWeight b₂)) :
    hilbertPoly (Sum.map b₁ b₂) (prodIdeal I₁ I₂) =
      rename Sum.inl (hilbertPoly b₁ I₁) * rename Sum.inr (hilbertPoly b₂ I₂) := by
  obtain ⟨d₁, hd₁⟩ := exists_forall_le_hilbertFunction_eq_hilbertPoly hb₁ hI₁
  obtain ⟨d₂, hd₂⟩ := exists_forall_le_hilbertFunction_eq_hilbertPoly hb₂ hI₂
  refine hilbertPoly_eq_of_forall_le (Sum.map_surjective.mpr ⟨hb₁, hb₂⟩)
    (isWeightedHomogeneous_prodIdeal hI₁ hI₂) (d₀ := Sum.elim d₁ d₂) fun d hd ↦ ?_
  rw [hilbertFunction_prodIdeal, Nat.cast_mul, map_mul, eval_rename, eval_rename,
    hd₁ (d ∘ Sum.inl) fun i ↦ hd (Sum.inl i), hd₂ (d ∘ Sum.inr) fun i ↦ hd (Sum.inr i)]
  rfl

/-- **The dimension of a product** is the sum of the dimensions. -/
theorem totalDegree_hilbertPoly_prodIdeal (hb₁ : Function.Surjective b₁)
    (hb₂ : Function.Surjective b₂) {I₁ : Ideal (MvPolynomial σ₁ K)}
    {I₂ : Ideal (MvPolynomial σ₂ K)} (hI₁ : I₁.IsWeightedHomogeneous (multiWeight b₁))
    (hI₂ : I₂.IsWeightedHomogeneous (multiWeight b₂)) (hne₁ : hilbertPoly b₁ I₁ ≠ 0)
    (hne₂ : hilbertPoly b₂ I₂ ≠ 0) :
    (hilbertPoly (Sum.map b₁ b₂) (prodIdeal I₁ I₂)).totalDegree =
      (hilbertPoly b₁ I₁).totalDegree + (hilbertPoly b₂ I₂).totalDegree := by
  rw [hilbertPoly_prodIdeal hb₁ hb₂ hI₁ hI₂, totalDegree_rename_inl_mul_rename_inr hne₁ hne₂]

/-- **The degrees of a product** (Evertse 1995, Lemma 2):
`d_{(α₁, α₂)}(I₁ × I₂) = d_{α₁}(I₁) · d_{α₂}(I₂)`. -/
theorem multidegree_prodIdeal [Fintype ι₁] [Fintype ι₂] (hb₁ : Function.Surjective b₁)
    (hb₂ : Function.Surjective b₂) {I₁ : Ideal (MvPolynomial σ₁ K)}
    {I₂ : Ideal (MvPolynomial σ₂ K)} (hI₁ : I₁.IsWeightedHomogeneous (multiWeight b₁))
    (hI₂ : I₂.IsWeightedHomogeneous (multiWeight b₂)) (α : ι₁ ⊕ ι₂ →₀ ℕ) :
    multidegree (Sum.map b₁ b₂) (prodIdeal I₁ I₂) α =
      multidegree b₁ I₁ (α.comapDomain Sum.inl Sum.inl_injective.injOn) *
        multidegree b₂ I₂ (α.comapDomain Sum.inr Sum.inr_injective.injOn) := by
  rw [multidegree, multidegree, multidegree, hilbertPoly_prodIdeal hb₁ hb₂ hI₁ hI₂,
    coeff_rename_inl_mul_rename_inr, Fintype.prod_sum_type]
  simp only [Finsupp.comapDomain_apply]
  ring

end Polynomial

end MvPolynomial
