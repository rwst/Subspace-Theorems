/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Multigraded

/-!
# Graded pieces of quotients of polynomial rings

For an ideal `I` of `R[X]`, multigraded by blocks `b : σ → ι`, `MvPolynomial.gradedPiece b I k`
is the `R`-module `(R[X]/I)_k = R[X]_k / (I ∩ R[X]_k)`. It is a finite `R`-module.

* `MvPolynomial.gradedPiece.factor`: the projection `(R[X]/I)_k → (R[X]/I')_k` for `I ≤ I'`.
* `MvPolynomial.gradedPiece.mulMap`: multiplication `(R[X]/I')_k → (R[X]/I)_{a+k}` by a form `f`
  of multidegree `a` with `f I' ⊆ I`.
* `MvPolynomial.gradedPiece.exact_mulMap_factor`: for a multihomogeneous `I`, the sequence
  `0 → (R[X]/I')_k → (R[X]/I)_{a+k} → (R[X]/(I + (f)))_{a+k} → 0` is exact as soon as
  `f g ∈ I` forces `g ∈ I'` in multidegree `k`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι R : Type*} [CommRing R] [DecidableEq ι] (b : σ → ι)

/-- The multidegree-`k` part `(R[X]/I)_k` of `R[X]/I`, as an `R`-module. -/
abbrev gradedPiece (I : Ideal (MvPolynomial σ R)) (k : ι → ℕ) : Type _ :=
  weightedHomogeneousSubmodule R (multiWeight b) k ⧸
    (I.restrictScalars R).comap (weightedHomogeneousSubmodule R (multiWeight b) k).subtype

namespace gradedPiece

variable {b}

omit [DecidableEq ι] in
theorem weightedHomogeneousSubmodule_eq_span [Fintype σ] [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) : weightedHomogeneousSubmodule R (multiWeight b) k =
      Submodule.span R ((fun c ↦ monomial c (1 : R)) '' (blockMonomials b k : Set (σ →₀ ℕ))) := by
  refine le_antisymm (fun p hp ↦ ?_) (Submodule.span_le.mpr ?_)
  · rw [p.as_sum]
    refine Submodule.sum_mem _ fun c hc ↦ ?_
    rw [← mul_one (p.coeff c), ← smul_eq_mul, ← smul_monomial]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_, rfl⟩)
    exact mem_blockMonomials.mpr (hp (mem_support_iff.mp hc))
  · rintro _ ⟨c, hc, rfl⟩
    exact isWeightedHomogeneous_monomial _ _ _ (mem_blockMonomials.mp hc)

instance [Finite σ] [Finite ι] (I : Ideal (MvPolynomial σ R)) (k : ι → ℕ) :
    Module.Finite R (gradedPiece b I k) := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  have : Module.Finite R (weightedHomogeneousSubmodule R (multiWeight b) k) := by
    rw [Module.Finite.iff_fg, weightedHomogeneousSubmodule_eq_span]
    exact Submodule.fg_span ((blockMonomials b k).finite_toSet.image _)
  infer_instance

/-- The projection `(R[X]/I)_k → (R[X]/I')_k` for `I ≤ I'`. -/
noncomputable def factor {I I' : Ideal (MvPolynomial σ R)} (h : I ≤ I') (k : ι → ℕ) :
    gradedPiece b I k →ₗ[R] gradedPiece b I' k :=
  Submodule.mapQ _ _ LinearMap.id fun _ hx ↦ h hx

theorem factor_surjective {I I' : Ideal (MvPolynomial σ R)} (h : I ≤ I') (k : ι → ℕ) :
    Function.Surjective (factor (b := b) h k) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨Submodule.mkQ _ x, rfl⟩

/-- Multiplication by a form `f` of multidegree `a`, `(R[X]/I')_k → (R[X]/I)_{k+a}`, when
`I' f ⊆ I`. -/
noncomputable def mulMap {I I' : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) (h : ∀ g ∈ I', g * f ∈ I) (k : ι → ℕ) :
    gradedPiece b I' k →ₗ[R] gradedPiece b I (k + a) :=
  Submodule.mapQ _ _ ((LinearMap.mulRight R f).restrict fun _ hg ↦ IsWeightedHomogeneous.mul
    hg hf) fun _ hg ↦ h _ hg

theorem mulMap_mk {I I' : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) (h : ∀ g ∈ I', g * f ∈ I) {k : ι → ℕ}
    (g : weightedHomogeneousSubmodule R (multiWeight b) k) :
    mulMap hf h k (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk ⟨g * f, IsWeightedHomogeneous.mul g.2 hf⟩ :=
  rfl

theorem mulMap_injective {I I' : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) (h : ∀ g ∈ I', g * f ∈ I) {k : ι → ℕ}
    (hinj : ∀ g ∈ weightedHomogeneousSubmodule R (multiWeight b) k, g * f ∈ I → g ∈ I') :
    Function.Injective (mulMap hf h k) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, mulMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj g g.2 hx)

/-- **Exactness** of `(R[X]/I')_k → (R[X]/I)_{k+a} → (R[X]/(I + (f)))_{k+a}` for a
multihomogeneous `I`. -/
theorem exact_mulMap_factor {I I' : Ideal (MvPolynomial σ R)} {f : MvPolynomial σ R}
    {a : ι → ℕ} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hf : IsWeightedHomogeneous (multiWeight b) f a) (h : ∀ g ∈ I', g * f ∈ I) (k : ι → ℕ) :
    Function.Exact (mulMap hf h k)
      (factor (b := b) (le_sup_left : I ≤ I ⊔ Ideal.span {f}) (k + a)) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  constructor
  · intro hy
    have hy' : (y : MvPolynomial σ R) ∈ I ⊔ Ideal.span {f} := by
      change Submodule.Quotient.mk (p := (Submodule.comap
        (weightedHomogeneousSubmodule R (multiWeight b) (k + a)).subtype
        (Submodule.restrictScalars R (I ⊔ Ideal.span {f})))) y = 0 at hy
      have := (Submodule.Quotient.mk_eq_zero _).mp hy
      exact this
    obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp hy'
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hyc : (y : MvPolynomial σ R) =
        weightedHomogeneousComponent (multiWeight b) (k + a) (y : MvPolynomial σ R) :=
      ((mem_weightedHomogeneousSubmodule R _ _ _).mp y.2).weightedHomogeneousComponent_same.symm
    rw [← hjz, map_add, hf.weightedHomogeneousComponent_add_mul] at hyc
    refine ⟨Submodule.Quotient.mk ⟨_, weightedHomogeneousComponent_mem _ g k⟩, ?_⟩
    rw [mulMap_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change weightedHomogeneousComponent _ k g * f - (y : MvPolynomial σ R) ∈ I
    rw [← hjz, hyc, show ∀ x z : MvPolynomial σ R, z - (x + z) = -x from fun x z ↦ by ring]
    exact I.neg_mem (hI hj (k + a))
  · rintro ⟨x, hx⟩
    rw [← hx]
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ x
    have : ((g : MvPolynomial σ R) * f) ∈ I ⊔ Ideal.span {f} :=
      Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    rw [Submodule.mkQ_apply, mulMap_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr this

end gradedPiece

end MvPolynomial
