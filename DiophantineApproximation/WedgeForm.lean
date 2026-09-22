/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Plucker
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

-- Used only inside proofs.
import ArithmeticHeights.CauchyBinet
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Exterior powers of a system of forms

For `p` linear forms `l 0, …, l (p - 1)` on `Kⁱ`, the wedge `l 0 ∧ ⋯ ∧ l (p - 1)` is a linear form
on `⋀^p Kⁱ`. It is read here in the Plücker coordinates of `ArithmeticHeights` 3.1, as a form on
`Set.powersetCard ι p → K` whose coefficients are the Plücker coordinates of the rows of
coefficients of the `l a`; on the wedge of `p` vectors it is the determinant of the matrix of
values, **Laplace's identity** (Bombieri–Gubler (7.16)), which is the Cauchy–Binet identity of
`ArithmeticHeights` 3.4. For a system of forms indexed by `ι` the wedges are indexed by the
`p`-subsets of `ι`, and they are independent when the forms are (Bombieri–Gubler 7.5.30); the
wedges `x J` of the members of a basis are independent too. And for a basis `x` of `Kⁱ`, the span
of the wedges `x J` of the `p`-subsets `J` that meet the first `k` indices, `k + p = #ι`, depends
only on the span of `x 0, …, x (k - 1)` and determines it (Lemma 7.5.33): it is the kernel of the
wedge of the last `p` coordinate forms of the basis. Finally, the two bounds for a determinant
that turn Laplace's identity into estimates at a place: `p!` times a bound on its terms, and the
bound itself at a nonarchimedean place.

## Main results

* `exteriorPower.wedgeForm` and `exteriorPower.wedgeForm_plucker`: the wedge of `p` forms, and
  Laplace's identity `(l 0 ∧ ⋯ ∧ l (p-1)) (y 0 ∧ ⋯ ∧ y (p-1)) = det (l a (y b))`.
* `exteriorPower.wedgeForms`: the wedges of a family of forms, indexed by the `p`-subsets.
* `exteriorPower.linearIndependent_wedgeForms` and `exteriorPower.linearIndependent_plucker_comp`:
  the wedges of independent forms, and of the members of a basis, are independent.
* `exteriorPower.wedgeSpan`, `exteriorPower.mem_span_iff_forall_plucker_mem_wedgeSpan` and
  `exteriorPower.wedgeSpan_eq_wedgeSpan_iff`: Lemma 7.5.33 — the span of the wedges meeting the
  first `k` indices determines, and is determined by, the span of the first `k` vectors.
* `exteriorPower.wedgeSpan_eq_ker`, `exteriorPower.plucker_topBlock_notMem_wedgeSpan` and
  `exteriorPower.finrank_wedgeSpan_add_one`: it is the kernel of the wedge of the last `p`
  coordinate forms, a hyperplane missing the wedge of the top block `exteriorPower.topBlock`.
* `Set.powersetCard.prod_prod_mem` and `Set.powersetCard.sum_sum_mem`: each member of `ι` lies in
  `(#ι - 1).choose (p - 1)` of the `p`-subsets.
* `AbsoluteValue.apply_det_le` and `AbsoluteValue.apply_det_le_of_isNonarchimedean`: the two bounds
  for a determinant.

## Implementation notes

⚠ **The exterior power is read in coordinates.** The approximation domains of Layer 4.1 live on
`κ → K` for a finite type `κ`, with forms in `Dual K (κ → K)`, and Layer 6.1 applies Layers 4.2,
4.3 and 5.6 to domains in `⋀^p Kⁱ`. So the exterior power is `Set.powersetCard ι p → K`, the
coordinates of `Module.Basis.exteriorPower` that `ArithmeticHeights` 3.1 uses, and the wedge of
forms is a form there; Mathlib's pairing of `⋀^p M` with `⋀^p (Dual R M)` enters only through the
Cauchy–Binet identity. `[LinearOrder ι]`, standing in `ArithmeticHeights` 3.1, names the wedge of
basis vectors a subset stands for; a different order changes each coordinate by a sign.

⚠ **Independence comes from a biorthogonal family, and the determinant is not needed.** The book
records that the wedges of independent forms are independent. Here that follows from vectors
`y j` with `l i (y j) = δ i j`: by Laplace's identity the wedges of the forms and of the `y j` are
biorthogonal too. The determinant of the system of wedges is a power of the determinant of the
system — the Sylvester–Franke theorem — but nothing downstream uses its value: the constants of
Layers 4.1–4.3 may depend on the forms, and they see the wedges only through their independence.

⚠ **Lemma 7.5.33 needs no pairing between `⋀^p` and `⋀^k`.** The book's proof identifies the span
of the wedges meeting the first `k` indices with the annihilator of `x 0 ∧ ⋯ ∧ x (k - 1)` under the
perfect pairing `⋀^p × ⋀^k → ⋀^{#ι}`. The dual route is shorter: with `f` the coordinate forms of
the basis, the span is the kernel of the single form `f k ∧ ⋯ ∧ f (#ι - 1)`, since the wedges `x J`
form a basis biorthogonal to the wedges of the `f`; and a vector `u` lies in the span of the first
`k` vectors exactly when every wedge through `u` lies in that kernel — if `f j₀ u ≠ 0` for some
`j₀ ≥ k`, replacing `x j₀` by `u` in the top block gives a wedge on which the form is `f j₀ u`, by
Cramer's rule. So the span determines `W` directly, and `W` determines it because every generator
has a factor in `W`, on which the last coordinate forms of any other basis of the same `W` vanish.

⚠ **Two acceptance tests.** In two variables the wedge of two forms on the wedge of two vectors is
the `2 × 2` determinant with the forms along the rows: that pins the orientation of Laplace's
identity. And in `ℚ³` with `k = 1` the wedge `e₀ ∧ (e₁ + e₂)` lies in the span of the wedges
meeting the first index while the top wedge `e₁ ∧ e₂` does not: the span is of the wedges that
*meet* the first `k` indices, which would be `0` here if it were those contained in them.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.2, (7.16), 7.5.30 and Lemma 7.5.33.

This is Layer 4.5 (infrastructure) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- The sign of a permutation does not change an absolute value. -/
private theorem apply_sign_smul (v : AbsoluteValue K ℝ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (a : K) :
    v (Equiv.Perm.sign σ • a) = v a := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The determinant is at most `p!` times a bound on its terms.** -/
theorem apply_det_le (v : AbsoluteValue K ℝ) {p : ℕ} (M : Matrix (Fin p) (Fin p) K) {b : ℝ}
    (h : ∀ σ : Equiv.Perm (Fin p), ∏ i, v (M (σ i) i) ≤ b) : v M.det ≤ p.factorial * b := by
  rw [Matrix.det_apply]
  calc v (∑ σ : Equiv.Perm (Fin p), Equiv.Perm.sign σ • ∏ i, M (σ i) i)
      ≤ ∑ σ : Equiv.Perm (Fin p), v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) := v.sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin p), b := Finset.sum_le_sum fun σ _ ↦ by
        rw [apply_sign_smul, map_prod]; exact h σ
    _ = p.factorial * b := by simp [Fintype.card_perm]

/-- **A nonarchimedean determinant is at most a common bound on its terms.** -/
theorem apply_det_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {p : ℕ} (M : Matrix (Fin p) (Fin p) K) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ σ : Equiv.Perm (Fin p), ∏ i, v (M (σ i) i) ≤ b) : v M.det ≤ b := by
  rw [Matrix.det_apply]
  refine Finset.sum_induction _ (fun y ↦ v y ≤ b) (fun a c ha hc ↦ (hv a c).trans (max_le ha hc))
    (by simpa using hb) fun σ _ ↦ ?_
  rw [apply_sign_smul, map_prod]
  exact h σ

end AbsoluteValue

namespace Set.powersetCard

/-- A product over the members of a subset, as a product over its enumeration in order. -/
@[to_additive /-- A sum over the members of a subset, as a sum over its enumeration in order. -/]
theorem prod_comp_ofFinEmbEquiv_symm {ι : Type*} [LinearOrder ι] {M : Type*} [CommMonoid M]
    {p : ℕ} (T : Set.powersetCard ι p) (g : ι → M) :
    ∏ a, g (Set.powersetCard.ofFinEmbEquiv.symm T a) = ∏ t ∈ (T : Finset ι), g t := by
  refine (Fintype.prod_equiv ((T : Finset ι).orderIsoOfFin T.prop).toEquiv _
    (fun t : (T : Finset ι) ↦ g t) fun a ↦ ?_).trans (Finset.prod_coe_sort _ _)
  exact congrArg g (Finset.coe_orderIsoOfFin_apply _ _ a).symm

variable {ι : Type*} [Fintype ι]

/-- **Double counting**: each member of `ι` lies in `(#ι - 1).choose (p - 1)` of the `p`-subsets. -/
@[to_additive /-- **Double counting**: each member of `ι` lies in `(#ι - 1).choose (p - 1)` of
the `p`-subsets. -/]
theorem prod_prod_mem {M : Type*} [CommMonoid M] (g : ι → M) {p : ℕ} (hp : 0 < p) :
    ∏ T : Set.powersetCard ι p, ∏ t ∈ (T : Finset ι), g t =
      (∏ t, g t) ^ (Fintype.card ι - 1).choose (p - 1) := by
  classical
  rw [← Finset.prod_subtype (Finset.powersetCard p Finset.univ)
    (p := (· ∈ Set.powersetCard ι p)) (fun s ↦ by simp [Set.powersetCard.mem_iff])
    (f := fun s ↦ ∏ t ∈ s, g t)]
  rw [Finset.prod_comm' (t' := Finset.univ)
    (s' := fun t ↦ (Finset.powersetCard p Finset.univ).filter ({t} ⊆ ·))
    (fun s t ↦ by simp)]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [Finset.prod_const, Finset.card_filter_powersetCard_subset _ _ _ (by simp)
    (by rw [Finset.card_singleton]; exact hp)]
  simp

end Set.powersetCard

namespace exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The wedge of `p` forms**, `l 0 ∧ ⋯ ∧ l (p - 1)`, as a form on the Plücker coordinates: its
coefficient at a `p`-subset `s` is the Plücker coordinate at `s` of the rows of coefficients of the
`l a`. -/
noncomputable def wedgeForm (p : ℕ) (l : Fin p → Dual K (ι → K)) :
    Dual K (Set.powersetCard ι p → K) :=
  ∑ s, plucker p (fun a j ↦ l a (Pi.basisFun K ι j)) s • LinearMap.proj s

/-- The wedge of forms evaluated on a coordinate vector. -/
theorem wedgeForm_apply (p : ℕ) (l : Fin p → Dual K (ι → K)) (z : Set.powersetCard ι p → K) :
    wedgeForm p l z = ∑ s, plucker p (fun a j ↦ l a (Pi.basisFun K ι j)) s * z s := by
  simp [wedgeForm]

/-- **Laplace's identity** (Bombieri–Gubler (7.16)): the wedge of `p` forms on the wedge of `p`
vectors is the determinant of the matrix of values. It is the Cauchy–Binet identity of
`ArithmeticHeights` 3.4. -/
theorem wedgeForm_plucker (p : ℕ) (l : Fin p → Dual K (ι → K)) (y : Fin p → ι → K) :
    wedgeForm p l (plucker p y) = (Matrix.of fun a b ↦ l a (y b)).det := by
  rw [wedgeForm_apply, sum_plucker_mul_plucker]
  congr 1
  ext a b
  simp only [Matrix.of_apply, dotProduct]
  conv_rhs => rw [← (Pi.basisFun K ι).sum_repr (y b)]
  simp [map_sum, mul_comm]

/-- **The wedges of a family of forms**: for each `p`-subset `T` of the indices, the wedge of the
forms indexed by `T`, in increasing order. -/
noncomputable def wedgeForms {κ : Type*} [LinearOrder κ] (l : κ → Dual K (ι → K)) (p : ℕ) :
    Set.powersetCard κ p → Dual K (Set.powersetCard ι p → K) :=
  fun T ↦ wedgeForm p (l ∘ Set.powersetCard.ofFinEmbEquiv.symm T)

/-- Laplace's identity for the wedges of a family of forms. -/
theorem wedgeForms_plucker {κ : Type*} [LinearOrder κ] (l : κ → Dual K (ι → K)) (p : ℕ)
    (T : Set.powersetCard κ p) (y : Fin p → ι → K) :
    wedgeForms l p T (plucker p y) =
      (Matrix.of fun a b ↦ l (Set.powersetCard.ofFinEmbEquiv.symm T a) (y b)).det :=
  wedgeForm_plucker p _ y

/-- **Biorthogonality is inherited by the wedges**: if `l i (y j) = δ i j`, the wedge of the forms
indexed by `T` on the wedge of the vectors indexed by `T'` is `δ T T'`. -/
theorem wedgeForms_plucker_eq_ite {κ : Type*} [LinearOrder κ] {l : κ → Dual K (ι → K)}
    {y : κ → ι → K} (h : ∀ i j, l i (y j) = if i = j then 1 else 0) (p : ℕ)
    (T T' : Set.powersetCard κ p) :
    wedgeForms l p T (plucker p (y ∘ Set.powersetCard.ofFinEmbEquiv.symm T')) =
      if T = T' then 1 else 0 := by
  rw [wedgeForms_plucker]
  split_ifs with hT
  · subst hT
    convert Matrix.det_one (R := K) (n := Fin p)
    ext a b
    simp only [Matrix.of_apply, Function.comp_apply, h, Matrix.one_apply,
      (Set.powersetCard.ofFinEmbEquiv.symm T).injective.eq_iff]
  · obtain ⟨t, htT, htT'⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne T T').1 hT
    obtain ⟨a, ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T t).2 htT
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b ↦ ?_
    simp only [Matrix.of_apply, Function.comp_apply, h, ha]
    rw [ite_eq_right_iff]
    rintro rfl
    exact (htT' ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T' _).1 ⟨b, rfl⟩)).elim


/-- A family of forms with a biorthogonal family of vectors is linearly independent. -/
private theorem linearIndependent_of_apply_eq_ite {V κ : Type*} [AddCommGroup V] [Module K V]
    [Finite κ] [DecidableEq κ] {l : κ → Dual K V} {y : κ → V}
    (h : ∀ i j, l i (y j) = if i = j then 1 else 0) : LinearIndependent K l := by
  have := Fintype.ofFinite κ
  refine Fintype.linearIndependent_iff.2 fun g hg i ↦ ?_
  have := congrArg (fun φ : Dual K V ↦ φ (y i)) hg
  simpa [Finset.sum_apply, h] using this

/-- A family of vectors with a biorthogonal family of forms is linearly independent. -/
private theorem linearIndependent_of_apply_eq_ite' {V κ : Type*} [AddCommGroup V] [Module K V]
    [Finite κ] [DecidableEq κ] {l : κ → Dual K V} {y : κ → V}
    (h : ∀ i j, l i (y j) = if i = j then 1 else 0) : LinearIndependent K y := by
  have := Fintype.ofFinite κ
  refine Fintype.linearIndependent_iff.2 fun g hg j ↦ ?_
  have := congrArg (l j) hg
  simpa [map_sum, h, eq_comm] using this

/-- Independent forms have a biorthogonal family of vectors. -/
private theorem exists_apply_eq_ite_of_linearIndependent {ι : Type*} [Finite ι] [DecidableEq ι]
    {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) :
    ∃ y : ι → ι → K, ∀ i j, l i (y j) = if i = j then 1 else 0 := by
  have := Fintype.ofFinite ι
  let b : Basis ι K (Dual K (ι → K)) :=
    Basis.mk hl (hl.span_eq_top_of_card_eq_finrank' (by simp)).ge
  refine ⟨fun j ↦ (Module.evalEquiv K (ι → K)).symm (b.dualBasis j), fun i j ↦ ?_⟩
  have hb : l i = b i := by simp [b]
  rw [hb, Module.apply_evalEquiv_symm_apply, Basis.dualBasis_apply_self]

omit [LinearOrder ι] in
/-- The coordinate forms of a basis are biorthogonal to it. -/
private theorem exists_apply_eq_ite_of_linearIndependent' {x : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) :
    ∃ f : Fin (Fintype.card ι) → Dual K (ι → K), ∀ i j, f i (x j) = if i = j then 1 else 0 := by
  let b : Basis (Fin (Fintype.card ι)) K (ι → K) :=
    Basis.mk hx (hx.span_eq_top_of_card_eq_finrank' (by simp)).ge
  refine ⟨b.coord, fun i j ↦ ?_⟩
  have hb : x j = b j := by simp [b]
  rw [hb, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl


/-- **The wedges of independent forms are independent** (Bombieri–Gubler 7.5.30). -/
theorem linearIndependent_wedgeForms {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l)
    (p : ℕ) : LinearIndependent K (wedgeForms l p) := by
  classical
  obtain ⟨y, hy⟩ := exists_apply_eq_ite_of_linearIndependent hl
  exact linearIndependent_of_apply_eq_ite (wedgeForms_plucker_eq_ite hy p)

/-- **The wedges of the members of a basis are independent**: for a basis `x` of `ι → K`, the
Plücker vectors `x J` of the `p`-subsets `J` of the indices. -/
theorem linearIndependent_plucker_comp {x : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) (p : ℕ) :
    LinearIndependent K fun J : Set.powersetCard (Fin (Fintype.card ι)) p ↦
      plucker p (x ∘ Set.powersetCard.ofFinEmbEquiv.symm J) := by
  classical
  obtain ⟨f, hf⟩ := exists_apply_eq_ite_of_linearIndependent' hx
  exact linearIndependent_of_apply_eq_ite' (wedgeForms_plucker_eq_ite hf p)

/-- **The wedge of integral vectors is integral** at a nonarchimedean place: each Plücker
coordinate is a determinant of coordinates. -/
theorem apply_plucker_le_one {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) {p : ℕ}
    {y : Fin p → ι → K} (hy : ∀ b i, v (y b i) ≤ 1) (s : Set.powersetCard ι p) :
    v (plucker p y s) ≤ 1 := by
  rw [plucker_apply]
  exact AbsoluteValue.apply_det_le_of_isNonarchimedean hv _ zero_le_one fun σ ↦
    Finset.prod_le_one₀ (fun _ _ ↦ v.nonneg _) fun _ _ ↦ hy _ _

/-! ### The wedges of a basis away from the top block -/

section Subspace

variable {N : ℕ}

/-- **The span of the wedges that meet the first `k` indices** (Bombieri–Gubler, Lemma 7.5.33): for
a family `x` of `N` vectors, the span in the Plücker coordinates of the wedges `x J` of the
`p`-subsets `J` of the indices that contain an index below `k`. -/
noncomputable def wedgeSpan (k p : ℕ) (x : Fin N → ι → K) :
    Submodule K (Set.powersetCard ι p → K) :=
  Submodule.span K ((fun J ↦ plucker p (x ∘ Set.powersetCard.ofFinEmbEquiv.symm J)) ''
    {J : Set.powersetCard (Fin N) p | ∃ j ∈ J, (j : ℕ) < k})

omit [Fintype ι] [LinearOrder ι] in
/-- The last `p` of `k + p = N` indices, in order. -/
def topBlockEmb {k p : ℕ} (h : k + p = N) : Fin p ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun a ↦ ⟨k + a, by omega⟩) fun _ _ hab ↦
    Fin.mk_lt_mk.2 (Nat.add_lt_add_left (Fin.lt_def.1 hab) k)

omit [Fintype ι] [LinearOrder ι] in
/-- The `a`-th index of the top block is `k + a`. -/
theorem topBlockEmb_apply {k p : ℕ} (h : k + p = N) (a : Fin p) :
    (topBlockEmb h a : ℕ) = k + a := rfl

omit [Fintype ι] [LinearOrder ι] in
/-- **The top block** `{k, …, N - 1}` of `k + p = N` indices, as a `p`-subset. -/
def topBlock {k p : ℕ} (h : k + p = N) : Set.powersetCard (Fin N) p :=
  Set.powersetCard.ofFinEmbEquiv (topBlockEmb h)

omit [Fintype ι] [LinearOrder ι] in
private theorem ofFinEmbEquiv_symm_top {k p : ℕ} (h : k + p = N) :
    Set.powersetCard.ofFinEmbEquiv.symm (topBlock h) = topBlockEmb h :=
  Equiv.symm_apply_apply _ _

omit [Fintype ι] [LinearOrder ι] in
/-- An index lies in the top block exactly when it is at least `k`. -/
theorem mem_topBlock {k p : ℕ} (h : k + p = N) {j : Fin N} : j ∈ topBlock h ↔ k ≤ (j : ℕ) := by
  rw [topBlock, Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  refine ⟨?_, fun hj ↦ ⟨⟨j - k, by omega⟩, Fin.ext (by simp [topBlockEmb_apply]; omega)⟩⟩
  rintro ⟨a, rfl⟩
  simp [topBlockEmb_apply]

omit [Fintype ι] [LinearOrder ι] in
/-- **A `p`-subset other than the top block meets the first `k` indices.** -/
theorem exists_lt_of_ne_topBlock {k p : ℕ} (h : k + p = N) {J : Set.powersetCard (Fin N) p}
    (hJ : J ≠ topBlock h) : ∃ j ∈ J, (j : ℕ) < k := by
  by_contra! hc
  exact hJ (Set.powersetCard.eq_iff_subset.2 fun j hj ↦ (mem_topBlock h).2 (hc j hj))

omit [LinearOrder ι] in
private theorem card_powersetCard_fin (p : ℕ) :
    Fintype.card (Set.powersetCard (Fin (Fintype.card ι)) p) =
      Fintype.card (Set.powersetCard ι p) := by
  rw [Fintype.card_eq_nat_card (α := Set.powersetCard (Fin _) p),
    Fintype.card_eq_nat_card (α := Set.powersetCard ι p), Set.powersetCard.card,
    Set.powersetCard.card, Nat.card_fin, Nat.card_eq_fintype_card]

variable {x : Fin (Fintype.card ι) → ι → K} {f : Fin (Fintype.card ι) → Dual K (ι → K)}

/-- **A vector lies in the span of the first `k` members of a basis exactly when every wedge
through it is killed by the wedge of the last `p` coordinate forms.** -/
private theorem mem_span_iff_forall_wedgeForms_eq_zero (hx : LinearIndependent K x)
    (hf : ∀ i j, f i (x j) = if i = j then 1 else 0) {k p : ℕ} (h : k + p = Fintype.card ι)
    (u : ι → K) :
    u ∈ Submodule.span K (x '' {j | (j : ℕ) < k}) ↔
      ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u →
        wedgeForms f p (topBlock h) (plucker p ω) = 0 := by
  have hform : ∀ ω : Fin p → ι → K, wedgeForms f p (topBlock h) (plucker p ω) =
      (Matrix.of fun a b ↦ f (topBlockEmb h a) (ω b)).det := fun ω ↦ by
    rw [wedgeForms_plucker, ofFinEmbEquiv_symm_top]
  -- the last `p` coordinate forms vanish on the span of the first `k` vectors
  have hvan : ∀ a : Fin p, Submodule.span K (x '' {j | (j : ℕ) < k}) ≤ LinearMap.ker
      (f (topBlockEmb h a)) := fun a ↦ by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hf, ite_eq_right_iff]
    intro hja
    have := topBlockEmb_apply h a
    rw [hja] at this
    simp only [Set.mem_ofPred_eq] at hj
    omega
  refine ⟨fun hu ω b hb ↦ ?_, fun H ↦ ?_⟩
  · rw [hform]
    refine Matrix.det_eq_zero_of_column_eq_zero b fun a ↦ ?_
    rw [Matrix.of_apply, hb]
    exact hvan a hu
  · by_contra hu
    -- some coordinate of `u` beyond the first `k` is nonzero
    have hsum : u = ∑ j, f j u • x j := by
      have hsp := hx.span_eq_top_of_card_eq_finrank' (by simp)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
        (hsp ▸ Submodule.mem_top : u ∈ Submodule.span K (Set.range x))
      have hcf : ∀ i, f i u = c i := fun i ↦ by
        rw [← hc, map_sum]
        simp [hf]
      simp_rw [hcf]
      exact hc.symm
    obtain ⟨j₀, hj₀k, hj₀⟩ : ∃ j₀ : Fin (Fintype.card ι), k ≤ (j₀ : ℕ) ∧ f j₀ u ≠ 0 := by
      by_contra! hc
      refine hu ?_
      rw [hsum]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      by_cases hj : (j : ℕ) < k
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · rw [hc j (by omega), zero_smul]
        exact Submodule.zero_mem _
    set a₀ : Fin p := ⟨j₀ - k, by omega⟩ with ha₀
    have htop : topBlockEmb h a₀ = j₀ := Fin.ext (by simp [topBlockEmb_apply, ha₀]; omega)
    have H₀ := H (Function.update (x ∘ topBlockEmb h) a₀ u) a₀ (Function.update_self _ _ _)
    rw [hform] at H₀
    have hmat : (Matrix.of fun a b ↦
          f (topBlockEmb h a) (Function.update (x ∘ topBlockEmb h) a₀ u b)) =
        (1 : Matrix (Fin p) (Fin p) K).updateCol a₀ fun a ↦ f (topBlockEmb h a) u := by
      ext a b
      by_cases hb : b = a₀
      · subst hb
        simp
      · simp [Function.update_of_ne hb, Matrix.updateCol_ne hb, hf, Matrix.one_apply,
          (topBlockEmb h).injective.eq_iff]
    rw [hmat, ← Matrix.cramer_apply, Matrix.cramer_one] at H₀
    exact hj₀ (htop ▸ H₀)

/-- **The span of the wedges meeting the first `k` indices is a hyperplane**: the kernel of the
wedge of the last `p` coordinate forms of the basis (the book's annihilator of
`x 0 ∧ ⋯ ∧ x (k - 1)`, read on the dual side). -/
theorem wedgeSpan_eq_ker (hx : LinearIndependent K x)
    (hf : ∀ i j, f i (x j) = if i = j then 1 else 0) {k p : ℕ} (h : k + p = Fintype.card ι) :
    wedgeSpan k p x = LinearMap.ker (wedgeForms f p (topBlock h)) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun z hz ↦ ?_
  · rintro _ ⟨J, ⟨j, hjJ, hjk⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, wedgeForms_plucker_eq_ite hf, ite_eq_right_iff]
    rintro rfl
    exact absurd ((mem_topBlock h).1 hjJ) (by omega)
  · have hind := linearIndependent_plucker_comp hx p
    have hsp := hind.span_eq_top_of_card_eq_finrank'
      (by rw [card_powersetCard_fin, Module.finrank_fintype_fun_eq_card])
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
      (hsp ▸ Submodule.mem_top : z ∈ Submodule.span K (Set.range _))
    have hc₀ : c (topBlock h) = 0 := by
      rw [LinearMap.mem_ker, ← hc, map_sum] at hz
      simpa [wedgeForms_plucker_eq_ite hf] using hz
    rw [← hc]
    refine Submodule.sum_mem _ fun J _ ↦ ?_
    by_cases hJ : J = topBlock h
    · rw [hJ, hc₀, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, exists_lt_of_ne_topBlock h hJ, rfl⟩)

/-- **The wedges meeting the first `k` indices determine the span of the first `k` vectors**
(Bombieri–Gubler, Lemma 7.5.33, second half): for a basis `x` and `k + p = #ι`, a vector lies in
the span of `x 0, …, x (k - 1)` exactly when every wedge of `p` vectors through it lies in
`wedgeSpan k p x`. -/
theorem mem_span_iff_forall_plucker_mem_wedgeSpan (hx : LinearIndependent K x) {k p : ℕ}
    (h : k + p = Fintype.card ι) (u : ι → K) :
    u ∈ Submodule.span K (x '' {j | (j : ℕ) < k}) ↔
      ∀ (ω : Fin p → ι → K) (b : Fin p), ω b = u → plucker p ω ∈ wedgeSpan k p x := by
  obtain ⟨f, hf⟩ := exists_apply_eq_ite_of_linearIndependent' hx
  rw [wedgeSpan_eq_ker hx hf h]
  exact mem_span_iff_forall_wedgeForms_eq_zero hx hf h u

/-- **The span of the wedges meeting the first `k` indices depends only on the span of the first
`k` vectors, and determines it** (Bombieri–Gubler, Lemma 7.5.33). -/
theorem wedgeSpan_eq_wedgeSpan_iff {x' : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) (hx' : LinearIndependent K x') {k p : ℕ}
    (h : k + p = Fintype.card ι) :
    wedgeSpan k p x = wedgeSpan k p x' ↔
      Submodule.span K (x '' {j | (j : ℕ) < k}) = Submodule.span K (x' '' {j | (j : ℕ) < k}) := by
  refine ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩
  · ext u
    rw [mem_span_iff_forall_plucker_mem_wedgeSpan hx h, hW,
      mem_span_iff_forall_plucker_mem_wedgeSpan hx' h]
  · -- each generator of one span has a vector in the common span, so lies in the other
    have key : ∀ {y y' : Fin (Fintype.card ι) → ι → K}, LinearIndependent K y' →
        Submodule.span K (y '' {j | (j : ℕ) < k}) = Submodule.span K (y' '' {j | (j : ℕ) < k}) →
        wedgeSpan k p y ≤ wedgeSpan k p y' := fun {y y'} hy' hyy' ↦ by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨J, ⟨j, hjJ, hjk⟩, rfl⟩
      obtain ⟨b, hb⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J j).2 hjJ
      refine (mem_span_iff_forall_plucker_mem_wedgeSpan hy' h (y j)).1 ?_ _ b
        (by rw [Function.comp_apply, hb])
      rw [← hyy']
      exact Submodule.subset_span ⟨j, hjk, rfl⟩
    exact le_antisymm (key hx' hW) (key hx hW.symm)

/-- **The wedge of the top block is not in the span of the others**: the span of the wedges
meeting the first `k` indices is proper. -/
theorem plucker_topBlock_notMem_wedgeSpan (hx : LinearIndependent K x) {k p : ℕ}
    (h : k + p = Fintype.card ι) :
    plucker p (x ∘ Set.powersetCard.ofFinEmbEquiv.symm (topBlock h)) ∉ wedgeSpan k p x := by
  classical
  obtain ⟨f, hf⟩ := exists_apply_eq_ite_of_linearIndependent' hx
  rw [wedgeSpan_eq_ker hx hf h, LinearMap.mem_ker, wedgeForms_plucker_eq_ite hf]
  simp

/-- **The span of the wedges meeting the first `k` indices has codimension one.** -/
theorem finrank_wedgeSpan_add_one (hx : LinearIndependent K x) {k p : ℕ}
    (h : k + p = Fintype.card ι) :
    Module.finrank K (wedgeSpan k p x) + 1 = Fintype.card (Set.powersetCard ι p) := by
  classical
  obtain ⟨f, hf⟩ := exists_apply_eq_ite_of_linearIndependent' hx
  rw [wedgeSpan_eq_ker hx hf h]
  have hrange : LinearMap.range (wedgeForms f p (topBlock h)) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun a ↦ ⟨a • plucker p (x ∘ Set.powersetCard.ofFinEmbEquiv.symm
      (topBlock h)), ?_⟩
    simp [wedgeForms_plucker_eq_ite hf]
  have := LinearMap.finrank_range_add_finrank_ker (wedgeForms f p (topBlock h))
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at this
  omega

end Subspace

end exteriorPower

open exteriorPower

section Tests

/-- **Laplace's identity pins the orientation**: in two variables the wedge of two forms on the
wedge of two vectors is the `2 × 2` determinant with the forms along the rows. -/
example {K ι : Type*} [Field K] [Fintype ι] [LinearOrder ι] (l : Fin 2 → Dual K (ι → K))
    (y : Fin 2 → ι → K) :
    wedgeForm 2 l (plucker 2 y) = l 0 (y 0) * l 1 (y 1) - l 0 (y 1) * l 1 (y 0) := by
  rw [wedgeForm_plucker, Matrix.det_fin_two]
  rfl

/-- The standard basis of `ℚ³`, indexed as the vectors of Lemma 7.5.33 are. -/
private noncomputable def basis3 (j : Fin (Fintype.card (Fin 3))) : Fin 3 → ℚ :=
  Pi.basisFun ℚ (Fin 3) (Fin.cast (Fintype.card_fin 3) j)

private theorem linearIndependent_basis3 : LinearIndependent ℚ basis3 :=
  (Pi.basisFun ℚ (Fin 3)).linearIndependent.comp _ (Fin.cast_injective _)

/-- **Lemma 7.5.33 in `ℚ³` with `k = 1`**: the wedge `e₀ ∧ (e₁ + e₂)` has a factor in the span of
`e₀`, so it lies in the span of the wedges meeting the first index, and the top wedge `e₁ ∧ e₂`
does not. A span of the wedges *contained in* the first `k` indices would be `0` here. -/
example : plucker 2 ![basis3 0, basis3 1 + basis3 2] ∈ wedgeSpan 1 2 basis3 ∧
    plucker 2 ![basis3 1, basis3 2] ∉ wedgeSpan 1 2 basis3 := by
  have h : 1 + 2 = Fintype.card (Fin 3) := by simp
  refine ⟨(mem_span_iff_forall_plucker_mem_wedgeSpan linearIndependent_basis3 h (basis3 0)).1
    (Submodule.subset_span ⟨0, by simp, rfl⟩) _ 0 rfl, ?_⟩
  have htop :
      basis3 ∘ Set.powersetCard.ofFinEmbEquiv.symm (topBlock h) = ![basis3 1, basis3 2] := by
    rw [topBlock, Equiv.symm_apply_apply]
    funext a
    fin_cases a <;> rfl
  rw [← htop]
  exact plucker_topBlock_notMem_wedgeSpan linearIndependent_basis3 h

end Tests
