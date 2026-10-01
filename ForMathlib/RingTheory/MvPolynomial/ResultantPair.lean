/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantProduct
public import ForMathlib.RingTheory.MvPolynomial.Specialization

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Specializing the product map of Prop. 3.5

The product specialization `ω : U₀ ↦ V W` of Rémond's Prop. 3.5 (`MvPolynomial.productMap`)
commutes with specializing the other forms `U_l`: if specializing them sends `F` to
`c ∏_j U(x_j)`, it sends `ω(F)` to `c ∏_j V(x_j) W(x_j)` (`MvPolynomial.specPair_productMap`).
This is what Rémond's Thm 2.2 (LNM 1752, Ch. 7) uses at every place.

## Main definitions

* `MvPolynomial.splitSum`, `MvPolynomial.splitPair`: the variables of `K[(e + e', d')]` and of
  `K[(e', e, d')]`, split into those of the first form(s) and those of the `U_l`.
* `MvPolynomial.specPair`: specializing the `U_l` in `K[(e', e, d')]`, keeping `V` and `W`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

section Product

variable {K L : Type*} [Field K] [Field L] (φ : K →+* L) {κ : Type*} (e e' : ι → ℕ)
  (d' : κ → ι → ℕ)

/-- The variables of `K[(e + e', d')]`: those of `U₀` and those of the `U_l`. -/
def splitSum : GenericVar b (sumIndex e e' d') ≃
    GenericVar b (fun _ : Unit ↦ e + e') ⊕ GenericVar b d' where
  toFun
    | ⟨none, m⟩ => .inl ⟨(), m⟩
    | ⟨some l, m⟩ => .inr ⟨l, m⟩
  invFun
    | .inl ⟨_, m⟩ => ⟨none, m⟩
    | .inr ⟨l, m⟩ => ⟨some l, m⟩
  left_inv := by rintro ⟨_ | l, m⟩ <;> rfl
  right_inv := by rintro (⟨_, m⟩ | ⟨l, m⟩) <;> rfl

/-- The variables of `K[(e', e, d')]`: those of `V`, of `W` and of the `U_l`. -/
def splitPair : GenericVar b (pairIndex e e' d') ≃
    (GenericVar b (fun _ : Unit ↦ e) ⊕ GenericVar b (fun _ : Unit ↦ e')) ⊕ GenericVar b d' where
  toFun
    | ⟨none, m⟩ => .inl (.inr ⟨(), m⟩)
    | ⟨some none, m⟩ => .inl (.inl ⟨(), m⟩)
    | ⟨some (some l), m⟩ => .inr ⟨l, m⟩
  invFun
    | .inl (.inl ⟨_, m⟩) => ⟨some none, m⟩
    | .inl (.inr ⟨_, m⟩) => ⟨none, m⟩
    | .inr ⟨l, m⟩ => ⟨some (some l), m⟩
  left_inv := by rintro ⟨_ | _ | l, m⟩ <;> rfl
  right_inv := by rintro ((⟨_, m⟩ | ⟨_, m⟩) | ⟨l, m⟩) <;> rfl

variable {e e' d'}

/-- `specEval` at the index `(e + e', d')`, through `splitSum`. -/
theorem specEval_sumIndex (y : GenericVar b d' → L) :
    specEval (d := sumIndex e e' d') b φ y =
      eval₂Hom (C.comp φ) fun v ↦ (splitSum e e' d' v).elim X fun l ↦ C (y l) := by
  refine ringHom_ext (fun a ↦ ?_) fun v ↦ ?_
  · exact (eval₂_C (C.comp φ) _ a).trans (eval₂_C (C.comp φ) _ a).symm
  · refine (eval₂_X (C.comp φ) _ v).trans ((eval₂_X (C.comp φ) _ v).trans ?_).symm
    rcases v with ⟨_ | l, m⟩ <;> rfl

theorem eval_specEval_eq {d : Option κ → ι → ℕ} (y : GenericVar b (fun l : κ ↦ d (some l)) → L)
    (z : GenericVar b (fun _ : Unit ↦ d none) → L) {g : GenericVar b d → L}
    (hnone : ∀ m, g ⟨none, m⟩ = z ⟨(), m⟩) (hsome : ∀ l m, g ⟨some l, m⟩ = y ⟨l, m⟩)
    (F : MvPolynomial (GenericVar b d) K) :
    eval z (specEval b φ y F) = eval₂ φ g F := by
  rw [specEval, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext v
    rcases v with ⟨_ | l, m⟩
    · simp [hnone]
    · simp [hsome]

theorem eval₂_productMap_eq (g : GenericVar b (pairIndex e e' d') → L)
    {g' : GenericVar b (sumIndex e e' d') → L}
    (hnone : ∀ m, g' ⟨none, m⟩ = eval₂ φ g ((genericForm K b (pairIndex e e' d') (some none) *
      genericForm K b (pairIndex e e' d') none).coeff (m : σ →₀ ℕ)))
    (hsome : ∀ l m, g' ⟨some l, m⟩ = g ⟨some (some l), m⟩)
    (F : MvPolynomial (GenericVar b (sumIndex e e' d')) K) :
    eval₂ φ g (productMap b K e e' d' F) = eval₂ φ g' F := by
  change eval₂ φ g (aeval _ F) = _
  rw [aeval_def, ← coe_eval₂Hom φ g, eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext v
    rcases v with ⟨_ | l, m⟩
    · simp [hnone]
    · simp [hsome]

/-- `∑_m [X^m](V W)(g) x^m = V(x)(g) W(x)(g)`. -/
theorem sum_eval₂_coeff_mul (g : GenericVar b (pairIndex e e' d') → L) (x : σ → L) :
    ∑ m ∈ blockMonomials b (e + e'),
      eval₂ φ g ((genericForm K b (pairIndex e e' d') (some none) *
        genericForm K b (pairIndex e e' d') none).coeff m) * ∏ s, x s ^ m s =
      (∑ m : blockMonomials b e, g ⟨some none, m⟩ * ∏ s, x s ^ (m : σ →₀ ℕ) s) *
        ∑ m : blockMonomials b e', g ⟨none, m⟩ * ∏ s, x s ^ (m : σ →₀ ℕ) s := by
  classical
  set P := genericForm K b (pairIndex e e' d') (some none) *
    genericForm K b (pairIndex e e' d') none
  have hP : P.IsWeightedHomogeneous (multiWeight b) (e + e') :=
    (isWeightedHomogeneous_genericForm (some none)).mul (isWeightedHomogeneous_genericForm none)
  have hsupp : P.support ⊆ blockMonomials b (e + e') := fun m hm ↦
    mem_blockMonomials.2 (hP (mem_support_iff.1 hm))
  have h1 : eval₂ (eval₂Hom φ g) x P =
      ∑ m ∈ blockMonomials b (e + e'), eval₂ φ g (P.coeff m) * ∏ s, x s ^ m s := by
    rw [eval₂_eq']
    refine Finset.sum_subset hsupp fun m _ hm ↦ ?_
    rw [notMem_support_iff.1 hm]
    simp
  rw [← h1, eval₂_mul, eval₂_genericForm, eval₂_genericForm]
  simp only [coe_eval₂Hom, eval₂_X]
  rfl

theorem eval_pointForm_eq {e : ι → ℕ} (z : GenericVar b (fun _ : Unit ↦ e) → L) (x : σ → L) :
    eval z (pointForm b e x) = ∑ m : blockMonomials b e, z ⟨(), m⟩ * ∏ s, x s ^ (m : σ →₀ ℕ) s := by
  rw [eval_pointForm, eval₂_genericForm]
  simp

variable (e e' d') in
/-- Specializing the forms `U_l` of `K[(e', e, d')]` at `y`, keeping `V` and `W`. -/
noncomputable def specPair (y : GenericVar b d' → L) :
    MvPolynomial (GenericVar b (pairIndex e e' d')) K →+*
      MvPolynomial (GenericVar b (fun _ : Unit ↦ e) ⊕ GenericVar b (fun _ : Unit ↦ e')) L :=
  eval₂Hom (C.comp φ) fun v ↦ (splitPair e e' d' v).elim X fun l ↦ C (y l)

/-- **The product map commutes with specialization**: if specializing the `U_l` at `y` sends
`F` to `c ∏_j U(x_j)`, it sends `ω(F)` to `c ∏_j V(x_j) W(x_j)`. -/
theorem specPair_productMap [Infinite L] (y : GenericVar b d' → L)
    (F : MvPolynomial (GenericVar b (sumIndex e e' d')) K) {c : L} {Z : Multiset (σ → L)}
    (h : specEval (d := sumIndex e e' d') b φ y F = C c * (Z.map (pointForm b (e + e'))).prod) :
    specPair φ e e' d' y (productMap b K e e' d' F) =
      C c * (Z.map fun x ↦ rename Sum.inl (pointForm b e x) *
        rename Sum.inr (pointForm b e' x)).prod := by
  refine MvPolynomial.funext fun vw ↦ ?_
  set gB : GenericVar b (pairIndex e e' d') → L := fun v ↦
    eval vw ((splitPair e e' d' v).elim X fun l ↦ C (y l))
  set ψ : GenericVar b (fun _ : Unit ↦ e + e') → L := fun v ↦
    eval₂ φ gB ((genericForm K b (pairIndex e e' d') (some none) *
      genericForm K b (pairIndex e e' d') none).coeff (v.2 : σ →₀ ℕ))
  set g0 : GenericVar b (sumIndex e e' d') → L := fun v ↦ (splitSum e e' d' v).elim ψ y
  have hG : eval₂ φ g0 F = eval ψ (C c * (Z.map (pointForm b (e + e'))).prod) :=
    (eval_specEval_eq (d := sumIndex e e' d') φ y ψ (g := g0) (fun m ↦ rfl)
      (fun l m ↦ rfl) F).symm.trans (congrArg (eval ψ) h)
  rw [specPair, coe_eval₂Hom, eval₂_comp_left, show (eval vw).comp (C.comp φ) = φ from
    RingHom.ext fun a ↦ by simp]
  change eval₂ φ gB _ = _
  rw [eval₂_productMap_eq φ gB (g' := g0) (fun m ↦ rfl) (fun l m ↦ (eval_C _).symm),
    hG, map_mul, map_mul, eval_C, eval_C, map_multiset_prod, map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun x _ ↦ ?_
  simp only [Function.comp_apply, map_mul, eval_rename, eval_pointForm_eq]
  have hs := sum_eval₂_coeff_mul φ gB x
  rw [← Finset.sum_coe_sort (blockMonomials b (e + e'))] at hs
  exact hs.trans (by simp [gB, splitPair])

end Product

end MvPolynomial
