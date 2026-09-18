/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Plucker

-- Used only by the example at the end of the file: the ultrametric inequality for a sum.
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Fintype.Order

/-!
# The Grassmann–Plücker comultiplication

Stack two families of vectors. The Plücker coordinates of the stack are a bilinear combination of
those of the two blocks:

`p(B;C)_s = ∑_{t,t'} ε(t,t',s) · p(B)_t · p(C)_{t'}`,

where the coefficient `ε(t,t',s)` is `0` unless `t` and `t'` are disjoint with union `s`, and is a
sign otherwise. This is the multiplication table of the exterior algebra read in the Plücker basis
— the comultiplication `Λ^{q+r} → Λ^q ⊗ Λ^r` paired against a decomposable — and, read as a
statement about determinants, it is the **Laplace expansion along a block of rows**. Mathlib has
neither.

It is one of the two routes to the finite-place half of Layer 3.6. Through it, the
submultiplicativity `‖p(B;C)‖ᵥ ≤ ‖p(B)‖ᵥ ‖p(C)‖ᵥ` at a nonarchimedean place is immediate: a sum is
no larger than its largest term, and the coefficients are signs. That is the example at the end of
this file; `ArithmeticHeights/Nonarchimedean.lean` reaches the same inequality by normalizing both
families to integral bases of their saturated lattices, and goes further, to the submodular
inequality the milestone actually needs.

## Main results

* `exteriorPower.plucker_append_eq_sum`: the identity itself.
* `exteriorPower.wedgeCoeff`: the structure constants, together with
  `exteriorPower.wedgeCoeff_eq_zero_or_eq_one_or_eq_neg_one` — each is `0`, `1` or `-1` — and the
  two vanishing lemmas `exteriorPower.wedgeCoeff_eq_zero_of_not_disjoint` and
  `exteriorPower.wedgeCoeff_eq_zero_of_union_ne`, which collapse the double sum to a sum over the
  ways of splitting `s`.
* `exteriorPower.det_append_eq_sum`: the **Laplace expansion of a determinant along a block of
  rows**, the classical statement, as a corollary.
* `exteriorPower.sum_wedgeCoeff_mul_eq_zero`: the **exchange relation**. The comultiplication sum
  vanishes when the stacked family is linearly dependent — in particular when the rows of `C` lie
  in the span of those of `B`.

## Implementation notes

The structure constants are *defined* as the Plücker coordinates of the wedge of standard basis
vectors, `wedgeCoeff t t' s = p(e_t; e_{t'})_s`, rather than as an explicit sign attached to a
shuffle permutation. That is what makes the identity cheap: both sides are bilinear, and the
identity is then nothing but the expansion of a product of two basis expansions, carried out in
`ExteriorAlgebra R M` where the wedge of a stack is literally the product
(`ExteriorAlgebra.ιMulti_mul_ιMulti`) and `⋀[R]^k M` is a submodule of it. That the constants are
signs is proved separately, from the shape of the resulting matrix: it is a `0/1` matrix which has
a zero row, a zero column, or is a permutation matrix.

`Set.powersetCard.permOfDisjoint` is Mathlib's shuffle permutation and would give the constants
explicitly, but it has no API — no lemma at all relates it to `Finset.orderEmbOfFin` — so pinning
the sign to it would cost more than it is worth here. Nothing downstream needs the sign itself,
only that it is one.

## What this does not give

The milestone needs the comultiplication with a **common first block**,
`p(A;B;C) ⊗ p(A) = ± ∑ p(A;B) ⊗ p(A;C)`, which is not the identity above: its left side is
quadratic in `A`, so it is not a statement about a single wedge product and no bilinear expansion
reaches it. It does follow from the identity above together with the exchange relation, by
induction on the number of rows of `C`: expanding the last row of `C` on both sides matches the
terms of the two sums except for those where the contracted index lands in `A`'s set, and those
cancel in blocks, each block being an instance of the exchange relation. The sign bookkeeping of
that induction is what is not done here — `ArithmeticHeights/Nonarchimedean.lean` obtains the
inequality the milestone needs without any of it.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§2.8.

W. V. D. Hodge and D. Pedoe, *Methods of Algebraic Geometry*, Volume I, Cambridge University Press
(1947), Chapter VII, §6, for the Plücker relations and the Laplace expansion in this form.

This is Layer 3.6 of the `ArithmeticHeights` roadmap.
-/
public section

namespace exteriorPower

open Module Set.powersetCard

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {q r : ℕ}

/-- The **structure constant of the wedge product** in the Plücker basis: the coordinate at `s` of
the wedge of the standard basis vectors named by `t` followed by those named by `t'`. -/
@[expose] noncomputable def wedgeCoeff (t : Set.powersetCard ι q) (t' : Set.powersetCard ι r)
    (s : Set.powersetCard ι (q + r)) : R :=
  plucker (q + r) (fun j ↦ Pi.basisFun R ι
    (Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) j)) s

private theorem ιMulti_eq_sum (k : ℕ) (X : Fin k → (ι → R)) :
    ιMulti R k X = ∑ t : Set.powersetCard ι k,
      plucker k X t • ((Pi.basisFun R ι).exteriorPower k) t := by
  conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).equivFun.symm_apply_apply (ιMulti R k X)]
  rw [Basis.equivFun_symm_apply]
  rfl

/-- **The Grassmann–Plücker comultiplication.** The Plücker coordinates of a family stacked from
two blocks are the bilinear combination of the Plücker coordinates of the blocks with the structure
constants of the wedge product. This is the generalized Laplace expansion along a block of rows,
which Mathlib does not have. -/
theorem plucker_append_eq_sum (B : Fin q → (ι → R)) (C : Fin r → (ι → R))
    (s : Set.powersetCard ι (q + r)) :
    plucker (q + r) (Fin.append B C) s
      = ∑ t : Set.powersetCard ι q, ∑ t' : Set.powersetCard ι r,
          wedgeCoeff t t' s * (plucker q B t * plucker r C t') := by
  have key : ιMulti R (q + r) (Fin.append B C)
      = ∑ t : Set.powersetCard ι q, ∑ t' : Set.powersetCard ι r,
          (plucker q B t * plucker r C t') •
            ιMulti R (q + r) (fun j ↦ Pi.basisFun R ι
              (Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) j)) := by
    have append_basisFun (t : Set.powersetCard ι q) (t' : Set.powersetCard ι r) :
        Fin.append (⇑(Pi.basisFun R ι) ∘ ⇑(ofFinEmbEquiv.symm t))
            (⇑(Pi.basisFun R ι) ∘ ⇑(ofFinEmbEquiv.symm t'))
          = fun j ↦ Pi.basisFun R ι
              (Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) j) := by
      funext j
      induction j using Fin.addCases with
      | left a => simp
      | right b => simp
    apply Subtype.val_injective
    rw [ιMulti_apply_coe, ← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ιMulti_apply_coe,
      ← ιMulti_apply_coe, ιMulti_eq_sum q B, ιMulti_eq_sum r C]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun t' _ ↦ ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [basis_apply, basis_apply, ιMulti_family, ιMulti_family,
      ιMulti_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti,
      append_basisFun, ιMulti_apply_coe]
  rw [plucker, key, map_sum]
  simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun t' _ ↦ ?_
  change plucker q B t * plucker r C t' * plucker (q + r) (fun j ↦ Pi.basisFun R ι
      (Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) j)) s
    = wedgeCoeff t t' s * (plucker q B t * plucker r C t')
  rw [wedgeCoeff]
  ring

/-! ### The structure constants are signs -/

private theorem det_indicator_eq_zero_or {n : Type*} [Fintype n] [DecidableEq n] {α : Type*}
    [DecidableEq α] (f g : n → α) (hg : Function.Injective g) :
    (Matrix.of fun i j ↦ if g j = f i then (1 : R) else 0).det = 0 ∨
      (Matrix.of fun i j ↦ if g j = f i then (1 : R) else 0).det = 1 ∨
        (Matrix.of fun i j ↦ if g j = f i then (1 : R) else 0).det = -1 := by
  classical
  by_cases hf : Function.Injective f
  · by_cases hsurj : ∀ j, ∃ i, f i = g j
    · choose σ₀ hσ₀ using hsurj
      have hinjσ : Function.Injective σ₀ := fun j₁ j₂ h ↦ hg (by rw [← hσ₀ j₁, ← hσ₀ j₂, h])
      let σ : Equiv.Perm n := Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hinjσ)
      have hσ (j : n) : σ j = σ₀ j := rfl
      have hM : (Matrix.of fun i j ↦ if g j = f i then (1 : R) else 0)
          = (1 : Matrix n n R).submatrix id σ := by
        ext i j
        simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
        rw [← hσ₀ j]
        have hiff : (f (σ₀ j) = f i) ↔ (i = σ j) := by
          rw [hσ]
          exact ⟨fun h ↦ (hf h).symm, fun h ↦ by rw [h]⟩
        simp only [hiff]
      rw [hM, Matrix.det_permute', Matrix.det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    · obtain ⟨j, hj⟩ := not_forall.mp hsurj
      refine .inl (Matrix.det_eq_zero_of_column_eq_zero j fun i ↦ ?_)
      simp only [Matrix.of_apply, ite_eq_right_iff]
      exact fun h ↦ absurd ⟨i, h.symm⟩ hj
  · obtain ⟨i₁, i₂, hfi, hne⟩ := Function.not_injective_iff.mp hf
    exact .inl (Matrix.det_zero_of_row_eq hne (by funext j; simp [hfi]))

private theorem wedgeCoeff_eq_det (t : Set.powersetCard ι q) (t' : Set.powersetCard ι r)
    (s : Set.powersetCard ι (q + r)) :
    wedgeCoeff t t' s = (Matrix.of fun i j ↦
      if (ofFinEmbEquiv.symm s : Fin (q + r) ↪o ι) j
          = Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) i
        then (1 : R) else 0).det := by
  classical
  rw [wedgeCoeff, plucker_apply]
  congr 1
  ext i j
  simp [Pi.single_apply]

/-- **The structure constants of the wedge product are signs.** Each is `0`, `1` or `-1`, so the
comultiplication expresses a Plücker coordinate of a stack as a signed sum of products of Plücker
coordinates of the blocks. -/
theorem wedgeCoeff_eq_zero_or_eq_one_or_eq_neg_one (t : Set.powersetCard ι q)
    (t' : Set.powersetCard ι r) (s : Set.powersetCard ι (q + r)) :
    wedgeCoeff (R := R) t t' s = 0 ∨ wedgeCoeff (R := R) t t' s = 1 ∨
      wedgeCoeff (R := R) t t' s = -1 := by
  classical
  simp only [wedgeCoeff_eq_det]
  exact det_indicator_eq_zero_or _ _ (ofFinEmbEquiv.symm s).injective

omit [Fintype ι] in
private theorem append_mem_union (t : Set.powersetCard ι q) (t' : Set.powersetCard ι r)
    (i : Fin (q + r)) :
    Fin.append (⇑(ofFinEmbEquiv.symm t)) (⇑(ofFinEmbEquiv.symm t')) i
      ∈ (t : Finset ι) ∪ (t' : Finset ι) := by
  induction i using Fin.addCases with
  | left a =>
      rw [Fin.append_left]
      exact Finset.mem_union_left _ (mem_coe_iff.2 ((mem_range_ofFinEmbEquiv_symm_iff_mem t _).1
        ⟨a, rfl⟩))
  | right b =>
      rw [Fin.append_right]
      exact Finset.mem_union_right _ (mem_coe_iff.2 ((mem_range_ofFinEmbEquiv_symm_iff_mem t' _).1
        ⟨b, rfl⟩))

/-- A structure constant vanishes unless the two index sets are disjoint: two equal columns would
be wedged together. -/
theorem wedgeCoeff_eq_zero_of_not_disjoint {t : Set.powersetCard ι q} {t' : Set.powersetCard ι r}
    (h : ¬ Disjoint (t : Finset ι) (t' : Finset ι)) (s : Set.powersetCard ι (q + r)) :
    wedgeCoeff (R := R) t t' s = 0 := by
  classical
  rw [wedgeCoeff_eq_det]
  obtain ⟨x, hxt, hxt'⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨a, ha⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t x).2 (mem_coe_iff.1 hxt)
  obtain ⟨b, hb⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t' x).2 (mem_coe_iff.1 hxt')
  refine Matrix.det_zero_of_row_eq (i := Fin.castAdd r a) (j := Fin.natAdd q b)
    (Fin.ne_of_val_ne (by simp; omega)) ?_
  funext j
  simp [ha, hb]

/-- A structure constant vanishes unless the two index sets partition `s`. -/
theorem wedgeCoeff_eq_zero_of_union_ne {t : Set.powersetCard ι q} {t' : Set.powersetCard ι r}
    {s : Set.powersetCard ι (q + r)} (h : (t : Finset ι) ∪ (t' : Finset ι) ≠ (s : Finset ι)) :
    wedgeCoeff (R := R) t t' s = 0 := by
  classical
  by_cases hd : Disjoint (t : Finset ι) (t' : Finset ι)
  swap
  · exact wedgeCoeff_eq_zero_of_not_disjoint hd s
  have hcard : ((t : Finset ι) ∪ (t' : Finset ι)).card = (s : Finset ι).card := by
    rw [Finset.card_union_of_disjoint hd, Set.powersetCard.card_eq t,
      Set.powersetCard.card_eq t', Set.powersetCard.card_eq s]
  have hsub : ¬ (s : Finset ι) ⊆ (t : Finset ι) ∪ (t' : Finset ι) := fun hc ↦
    h (Finset.eq_of_subset_of_card_le hc hcard.le).symm
  obtain ⟨x, hxs, hx⟩ := Finset.not_subset.mp hsub
  obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s x).2 (mem_coe_iff.1 hxs)
  rw [wedgeCoeff_eq_det]
  refine Matrix.det_eq_zero_of_column_eq_zero j fun i ↦ ?_
  simp only [Matrix.of_apply, ite_eq_right_iff]
  exact fun hc ↦ absurd (hj ▸ hc ▸ append_mem_union t t' i) hx

/-! ### The exchange relation -/

/-- **The exchange relation.** When the stacked family is linearly dependent the comultiplication
sum vanishes identically. Taking `B` to span a subspace containing every row of `C`, with `C`
nonempty, this is the relation that says a wedge is killed by wedging on a vector of its own span;
it is the extra ingredient the comultiplication identity with a *shared* first block needs, beyond
the two-block expansion proved above. -/
theorem sum_wedgeCoeff_mul_eq_zero {K : Type*} [Field K] {B : Fin q → (ι → K)}
    {C : Fin r → (ι → K)} (h : ¬ LinearIndependent K (Fin.append B C))
    (s : Set.powersetCard ι (q + r)) :
    ∑ t : Set.powersetCard ι q, ∑ t' : Set.powersetCard ι r,
        wedgeCoeff t t' s * (plucker q B t * plucker r C t') = 0 := by
  rw [← plucker_append_eq_sum]
  simpa using congrFun ((plucker_eq_zero_iff (q + r) (Fin.append B C)).2 h) s

/-! ### The Laplace expansion along a block of rows -/

/-- **The Laplace expansion of a determinant along a block of rows**, which Mathlib does not have.
The determinant of a square matrix whose rows are cut into two blocks is the signed sum, over the
ways of cutting the columns into two blocks of the matching sizes, of the products of the two
minors. The signs are the structure constants of the wedge product. -/
theorem det_append_eq_sum (B : Fin q → (Fin (q + r) → R)) (C : Fin r → (Fin (q + r) → R))
    (s : Set.powersetCard (Fin (q + r)) (q + r)) :
    (Matrix.of (Fin.append B C)).det
      = ∑ t : Set.powersetCard (Fin (q + r)) q, ∑ t' : Set.powersetCard (Fin (q + r)) r,
          wedgeCoeff t t' s *
            ((Matrix.of fun i j ↦ B i (ofFinEmbEquiv.symm t j)).det *
              (Matrix.of fun i j ↦ C i (ofFinEmbEquiv.symm t' j)).det) := by
  rw [← plucker_fin_eq_det (Fin.append B C) s, plucker_append_eq_sum]
  simp only [plucker_apply]

/-! ### Examples -/

section Examples

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

private theorem apply_sum_le_of_forall_le {α : Type*} (hv : IsNonarchimedean v) {s : Finset α}
    {g : α → K} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i ∈ s, v (g i) ≤ c) : v (∑ i ∈ s, g i) ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using hc
  · exact (hv.apply_sum_le_sup hne).trans (Finset.sup'_le _ _ h)

/-- **Submultiplicativity of the Plücker norm at a nonarchimedean place, by the other route.**
This is the statement of `exteriorPower.iSup_plucker_append_le`, which
`ArithmeticHeights/Nonarchimedean.lean` proves by normalizing both families to integral bases of
their saturated lattices. Here it is read straight off the comultiplication instead: the
coordinate of the stack is a signed sum of products of coordinates of the blocks, and at a
nonarchimedean place a sum is no larger than its largest term. Neither route subsumes the other —
that one also yields the submodular inequality, which the identity alone does not. -/
example (hv : IsNonarchimedean v) (B : Fin q → (ι → K)) (C : Fin r → (ι → K)) :
    (⨆ s : Set.powersetCard ι (q + r), v (plucker (q + r) (Fin.append B C) s)) ≤
      (⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
        ⨆ s : Set.powersetCard ι r, v (plucker r C s) := by
  have hnn : (0 : ℝ) ≤ (⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
      ⨆ s : Set.powersetCard ι r, v (plucker r C s) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun s ↦ ?_) hnn
  rw [plucker_append_eq_sum]
  refine apply_sum_le_of_forall_le hv hnn fun t _ ↦ ?_
  refine apply_sum_le_of_forall_le hv hnn fun t' _ ↦ ?_
  rw [map_mul, map_mul]
  have hc : v (wedgeCoeff (R := K) t t' s) ≤ 1 := by
    rcases wedgeCoeff_eq_zero_or_eq_one_or_eq_neg_one (R := K) t t' s with h | h | h <;>
      rw [h] <;> simp
  have h1 : v (plucker q B t) ≤ ⨆ s : Set.powersetCard ι q, v (plucker q B s) :=
    Finite.le_ciSup_of_le t le_rfl
  have h2 : v (plucker r C t') ≤ ⨆ s : Set.powersetCard ι r, v (plucker r C s) :=
    Finite.le_ciSup_of_le t' le_rfl
  calc v (wedgeCoeff t t' s) * (v (plucker q B t) * v (plucker r C t'))
      ≤ 1 * ((⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
          ⨆ s : Set.powersetCard ι r, v (plucker r C s)) :=
        mul_le_mul hc (mul_le_mul h1 h2 (v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
          (mul_nonneg (v.nonneg _) (v.nonneg _)) zero_le_one
    _ = _ := one_mul _

end Examples

end exteriorPower

end
