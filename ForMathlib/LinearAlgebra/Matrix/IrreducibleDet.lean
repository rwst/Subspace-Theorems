/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.Basic

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The generic determinant is irreducible

Over a field `K`, the determinant of the matrix of indeterminates `(X_{ij})` is an irreducible,
hence prime, element of `K[X_{ij}]` (`Matrix.irreducible_det_mvPolynomialX`,
`Matrix.prime_det_mvPolynomialX`).

The proof: the determinant has degree exactly `1` in every variable, so in a factorization
`det = F G` every variable occurs in exactly one factor. No monomial of the determinant contains
two entries of one row or one column; identifying two such variables shows that they occur in
the same factor. Rows and columns connect all entries, so one factor is constant.
-/

@[expose] public section

open MvPolynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- After renaming the variables of the generic determinant by `ρ`, the degree in `v` is at most
`1` if the entries renamed to `v` lie in one row or one column. -/
theorem degreeOf_rename_det_mvPolynomialX_le [Nontrivial R] {V : Type*} (ρ : n × n → V) (v : V)
    (hρ : ∀ p q, ρ p = v → ρ q = v → p.1 = q.1 ∨ p.2 = q.2) :
    degreeOf v (rename ρ (det (mvPolynomialX n n R))) ≤ 1 := by
  classical
  rw [AlgHom.map_det, det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 : ∀ z : ℤ, degreeOf v (z : MvPolynomial V R) = 0 := fun z ↦ by
    rw [← map_intCast (C : R →+* MvPolynomial V R), degreeOf_C]
  rw [h1, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp only [AlgHom.mapMatrix_apply, map_apply, mvPolynomialX_apply, rename_X, degreeOf_X]
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_one.mpr fun i hi j hj ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases hρ _ _ hi.symm hj.symm with h | h
  · exact σ.injective h
  · exact h

/-- Every entry is a variable of the generic determinant. -/
theorem mem_vars_det_mvPolynomialX [Nontrivial R] (p : n × n) :
    p ∈ vars (det (mvPolynomialX n n R)) := by
  classical
  by_contra hp
  obtain ⟨a, b⟩ := p
  let s : n × n → R := fun q ↦ (Equiv.swap a b).permMatrix R q.1 q.2
  have heq : eval s (det (mvPolynomialX n n R)) =
      eval (Function.update s (a, b) 0) (det (mvPolynomialX n n R)) := by
    refine hom_congr_vars (by ext; simp) (fun q hq _ ↦ ?_) rfl
    have : q ≠ (a, b) := fun h ↦ hp (h ▸ hq)
    simp [Function.update_of_ne this]
  rw [eval_det_mvPolynomialX, eval_det_mvPolynomialX] at heq
  have h1 : det (of fun i j ↦ s (i, j)) = det ((Equiv.swap a b).permMatrix R) := rfl
  rw [h1, det_permutation, det_eq_zero_of_column_eq_zero b fun i ↦ ?_] at heq
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap a b)) with h | h <;>
      simp [h] at heq
  · by_cases hi : i = a
    · simp [hi]
    · have : (i, b) ≠ (a, b) := fun h ↦ hi (Prod.ext_iff.mp h).1
      simp only [of_apply, Function.update_of_ne this, s, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      rw [ite_eq_right_iff]
      intro h
      exact absurd ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_right a b)) hi

/-- The generic determinant has degree `1` in every entry. -/
theorem degreeOf_det_mvPolynomialX [Nontrivial R] (p : n × n) :
    degreeOf p (det (mvPolynomialX n n R)) = 1 := by
  refine le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr
    (mem_vars_iff_degreeOf_ne_zero.mp (mem_vars_det_mvPolynomialX (R := R) p)))
  simpa [rename_id_apply] using degreeOf_rename_det_mvPolynomialX_le (R := R) id p
    (by rintro q r rfl rfl; simp)

end CommRing

variable {K : Type*} [Field K]

/-- In a factorization of the generic determinant, two entries of one row or one column occur
in the same factor. -/
theorem degreeOf_eq_one_of_mul_eq_det {F G : MvPolynomial (n × n) K}
    (hFG : det (mvPolynomialX n n K) = F * G) {v w : n × n} (hvw : v ≠ w)
    (hline : v.1 = w.1 ∨ v.2 = w.2) (hv : degreeOf v F = 1) : degreeOf w F = 1 := by
  classical
  have hP0 := det_mvPolynomialX_ne_zero n K
  have hF0 : F ≠ 0 := left_ne_zero_of_mul (hFG ▸ hP0)
  have hG0 : G ≠ 0 := right_ne_zero_of_mul (hFG ▸ hP0)
  have hsum : ∀ p, degreeOf p F + degreeOf p G = 1 := fun p ↦ by
    rw [← degreeOf_mul_eq hF0 hG0, ← hFG, degreeOf_det_mvPolynomialX]
  by_contra hw
  have hwF : degreeOf w F = 0 := by have := hsum w; omega
  have hvG : degreeOf v G = 0 := by have := hsum v; omega
  have hwG : degreeOf w G = 1 := by have := hsum w; omega
  let ρ : n × n → n × n := Function.update id w v
  have hρw : ρ w = v := by simp [ρ]
  have hρ : ∀ p, p ≠ w → ρ p = p := fun p hp ↦ by simp [ρ, Function.update_of_ne hp]
  -- Identifying `w` with `v` keeps the degree of the determinant in `v` at most `1`.
  have hle := degreeOf_rename_det_mvPolynomialX_le (R := K) ρ v fun p q hp hq ↦ by
    have hvw' : ∀ p, ρ p = v → p = v ∨ p = w := fun p hp ↦ by
      by_cases h : p = w
      · exact Or.inr h
      · exact Or.inl ((hρ p h).symm.trans hp)
    rcases hvw' p hp with rfl | rfl <;> rcases hvw' q hq with rfl | rfl
    · exact Or.inl rfl
    · exact hline
    · exact hline.imp Eq.symm Eq.symm
    · exact Or.inl rfl
  -- `F` does not involve `w`, so the renaming fixes it.
  have hρF : rename ρ F = F := by
    have := hom_congr_vars (f₁ := (rename ρ).toRingHom) (f₂ := RingHom.id _) (p₁ := F)
      (by ext; simp) (fun i hi _ ↦ ?_) rfl
    · simpa using this
    have : i ≠ w := fun h ↦ by
      rw [h, mem_vars_iff_degreeOf_ne_zero] at hi
      exact hi hwF
    simp [hρ i this]
  -- `G` does not involve `v`, so the renaming is injective on its variables.
  have hρG : degreeOf v (rename ρ G) = 1 := by
    obtain ⟨G', rfl⟩ := exists_rename_eq_of_vars_subset_range G (Subtype.val : {p // p ≠ v} → _)
      Subtype.val_injective fun p hp ↦ ⟨⟨p, fun h ↦ by
        rw [h, Finset.mem_coe, mem_vars_iff_degreeOf_ne_zero] at hp
        exact hp hvG⟩, rfl⟩
    have hinj : Function.Injective (ρ ∘ Subtype.val : {p // p ≠ v} → n × n) := by
      rintro ⟨p, hp⟩ ⟨q, hq⟩ h
      simp only [Function.comp_apply] at h
      refine Subtype.ext (show p = q from ?_)
      by_cases hpw : p = w <;> by_cases hqw : q = w
      · exact hpw.trans hqw.symm
      · rw [hpw, hρw, hρ q hqw] at h
        exact absurd h.symm hq
      · rw [hqw, hρw, hρ p hpw] at h
        exact absurd h hp
      · rwa [hρ p hpw, hρ q hqw] at h
    rw [rename_rename]
    have h1 := degreeOf_rename_of_injective (p := G') hinj ⟨w, hvw.symm⟩
    have h2 := degreeOf_rename_of_injective (p := G') Subtype.val_injective ⟨w, hvw.symm⟩
    simp only [Function.comp_apply, hρw] at h1 h2
    rw [h1, ← h2, hwG]
  have hρG0 : rename ρ G ≠ 0 := fun h ↦ by simp [h] at hρG
  rw [hFG, map_mul, degreeOf_mul_eq (by rw [hρF]; exact hF0) hρG0, hρF, hv, hρG] at hle
  omega

/-- **The generic determinant is irreducible** over a field. -/
theorem irreducible_det_mvPolynomialX [Nonempty n] : Irreducible (det (mvPolynomialX n n K)) := by
  classical
  have hP0 := det_mvPolynomialX_ne_zero n K
  obtain ⟨a₀⟩ := ‹Nonempty n›
  refine irreducible_iff.mpr ⟨fun hu ↦ ?_, fun F G hFG ↦ ?_⟩
  · obtain ⟨Q, hQ⟩ := hu.exists_right_inv
    have hQ0 : Q ≠ 0 := right_ne_zero_of_mul (hQ ▸ one_ne_zero)
    have h := congrArg totalDegree hQ
    rw [totalDegree_mul_of_isDomain hP0 hQ0, totalDegree_one] at h
    have := degreeOf_le_totalDegree (det (mvPolynomialX n n K)) (a₀, a₀)
    rw [degreeOf_det_mvPolynomialX] at this
    omega
  -- If `F` involves one entry, it involves all of them, and `G` is constant.
  have main : ∀ F G : MvPolynomial (n × n) K, det (mvPolynomialX n n K) = F * G →
      degreeOf (a₀, a₀) F = 1 → IsUnit G := by
    intro F G hFG h₀
    have hF0 : F ≠ 0 := left_ne_zero_of_mul (hFG ▸ hP0)
    have hG0 : G ≠ 0 := right_ne_zero_of_mul (hFG ▸ hP0)
    have hrow : ∀ b, degreeOf (a₀, b) F = 1 := fun b ↦ by
      by_cases hb : b = a₀
      · rwa [hb]
      · exact degreeOf_eq_one_of_mul_eq_det (v := (a₀, a₀)) (w := (a₀, b)) hFG
          (by simp [Ne.symm hb]) (Or.inl rfl) h₀
    have hall : ∀ p : n × n, degreeOf p G = 0 := fun ⟨a, b⟩ ↦ by
      have hF : degreeOf (a, b) F = 1 := by
        by_cases ha : a = a₀
        · rw [ha]
          exact hrow b
        · exact degreeOf_eq_one_of_mul_eq_det (v := (a₀, b)) (w := (a, b)) hFG
            (by simp [Ne.symm ha]) (Or.inr rfl) (hrow b)
      have := degreeOf_mul_eq hF0 hG0 (n := (a, b))
      rw [← hFG, degreeOf_det_mvPolynomialX, hF] at this
      omega
    have hdeg : G.totalDegree = 0 := (totalDegree_eq_zero_iff _ G).mpr fun m hm p ↦
      Nat.le_zero.mp ((monomial_le_degreeOf p hm).trans (hall p).le)
    rw [totalDegree_eq_zero_iff_eq_C] at hdeg
    rw [hdeg] at hG0 ⊢
    exact (Ne.isUnit fun h ↦ hG0 (by rw [h, map_zero])).map C
  have hF0 : F ≠ 0 := left_ne_zero_of_mul (hFG ▸ hP0)
  have hG0 : G ≠ 0 := right_ne_zero_of_mul (hFG ▸ hP0)
  have := degreeOf_mul_eq hF0 hG0 (n := (a₀, a₀))
  rw [← hFG, degreeOf_det_mvPolynomialX] at this
  by_cases h : degreeOf (a₀, a₀) F = 1
  · exact Or.inr (main F G hFG h)
  · exact Or.inl (main G F (hFG.trans (mul_comm F G)) (by omega))

/-- **The generic determinant is prime** over a field. -/
theorem prime_det_mvPolynomialX [Nonempty n] : Prime (det (mvPolynomialX n n K)) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_det_mvPolynomialX

end Matrix
