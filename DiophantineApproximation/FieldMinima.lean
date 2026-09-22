/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SuccessiveMinima
public import DiophantineApproximation.ModuleCovolume
public import Mathlib.NumberTheory.NumberField.House

-- Used only inside proofs.
import ArithmeticHeights.Extraction
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.AlgebraTower

/-!
# Successive minima over a number field

For a number field `K` of degree `d`, an `𝓞 K`-submodule `Λ` of `Kⁱ` whose mixed embedding is a
lattice in `(K ⊗ ℝ)ⁱ = ι → mixedSpace K`, and a symmetric convex body `B` there, the `i`-th
**successive minimum over `K`** is the least dilation `t` for which `Λ ∩ t B` contains `i + 1`
vectors linearly independent **over `K`**. The real successive minima `λ` of `ArithmeticHeights`
count vectors independent over `ℝ`, and the lattice has rank `d #ι`; this file compares the two:

```text
λ i  ≤  μ i  ≤  λ (d i),        λ (d (i + 1) - 1)  ≤  c_K μ i,
```

with `c_K` the largest house of a member of the integral basis of `𝓞 K`. The first inequality is
that `K`-independent vectors stay independent over `ℝ`; the second is the extraction lemma of
`ArithmeticHeights` applied to vectors realizing the real minima; the third multiplies vectors
realizing `μ i` by the integral basis, which the body absorbs because it is balanced over every
completion. Minkowski's second theorem over `K` follows in `FieldMinkowski.lean`.

## Main definitions

* `NumberField.successiveMinimum`: the `i`-th successive minimum over `K`, indexed from `0`.
* `NumberField.integralBasisHouse`: the constant `c_K`, the largest house of a member of Mathlib's
  integral basis `NumberField.integralBasis K`.

## Main results

* `NumberField.successiveMinimum_mixedImage_le`: `λ i ≤ μ i`.
* `NumberField.successiveMinimum_le_successiveMinimum_mixedImage`: `μ i ≤ λ (d i)`.
* `NumberField.successiveMinimum_mixedImage_le_mul`: `λ (d (i + 1) - 1) ≤ c_K μ i`.
* `NumberField.exists_linearIndependent_mem_smul_successiveMinimum`: the minima are attained, by one
  family of `#ι` vectors of `Λ` independent over `K`.
* `NumberField.successiveMinimum_pos`, `NumberField.successiveMinimum_le_of_le` and
  `NumberField.successiveMinimum_eq_zero_of_le`: positive and monotone below `#ι`, zero above it.
* `NumberField.finite_setOf_mem_of_isBounded`: a bounded set holds finitely many points of `Λ`.
* `NumberField.mixedEmbedding.linearIndependent_pi`: tuples independent over `ℚ` stay independent
  over `ℝ` under the mixed embedding.

## Implementation notes

⚠ **The minima are indexed from `0`**, as `ZLattice.successiveMinimum` is: the roadmap's `μ l`,
`l = 1, …, n + 1`, is `successiveMinimum Λ B (l - 1)`, and its `λ l ≤ μ l ≤ λ (d (l − 1) + 1)` and
`λ (d l) ≤ c_K μ l` are the three inequalities displayed above.

⚠ **The lattice alone makes the minima finite.** Below `#ι` the set of admissible dilations is
nonempty because the extraction lemma turns the `d #ι` independent vectors realizing the real
minima into `#ι` vectors of `Λ` independent over `K`. So `Λ` enters only through
`[DiscreteTopology Λ.mixedImage]` and `[IsZLattice ℝ Λ.mixedImage]`, with no separate hypothesis
that it spans `Kⁱ`, and `μ i ≤ λ (d i)` is the same argument read quantitatively.

⚠ **Attainment needs no greedy minimality.** Cassels' Lemma 1 over `ℝ` builds the realizing
family greedily and carries a minimality clause through the induction. Over `K` each minimum is
attained by finiteness alone — a dilate of a bounded body holds finitely many points of `Λ`, and
the body is closed — and one family realizing all of them is assembled afterwards by the selection
step of the extraction lemma: `i + 1` independent vectors realizing `μ i` contain one outside the
span of the `i` already chosen.

⚠ **Independence over `ℚ` meets `ℝ` by base change, not through the lattice.** In the coordinates
of `NumberField.mixedEmbedding.latticeBasis`, the mixed embedding of `x` has the coordinates of `x`
in `NumberField.integralBasis K` (`latticeBasis_repr_apply`), and Mathlib's
`linearIndependent_algebraMap_comp_iff` says rational vectors independent over `ℚ` are independent
over `ℝ`. Nothing about discreteness is used.

⚠ **Only the comparison with `c_K` uses that the body is balanced over every completion.** The
hypothesis is stated as `mul_mem_approxBody` states it for approximation domains: multiplying by an
element of the mixed space of local norms at most `1` keeps the body.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition C.2.9 and Theorem C.2.11. J. W. S. Cassels, *An Introduction to the Geometry of
Numbers*, Springer (1959), Chapter VIII.

This is Layer 4.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

open scoped Pointwise Topology

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- **Tuples independent over `ℚ` stay independent over `ℝ` under the mixed embedding.** In the
coordinates of `latticeBasis K` a tuple has the coordinates of its preimage in `integralBasis K`,
and rational vectors independent over `ℚ` are independent over `ℝ`. -/
theorem linearIndependent_pi [Finite ι] {κ : Type*} {x : κ → ι → K}
    (hx : LinearIndependent ℚ x) : LinearIndependent ℝ (fun k j ↦ mixedEmbedding K (x k j)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set P := Pi.basis fun _ : ι ↦ latticeBasis K
  set Q := Pi.basis fun _ : ι ↦ integralBasis K
  have hc : LinearIndependent ℚ (fun k ↦ Q.equivFun (x k)) :=
    hx.map' Q.equivFun.toLinearMap Q.equivFun.ker
  have hR := (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 hc
  refine LinearIndependent.of_comp P.equivFun.toLinearMap ?_
  convert hR using 1
  ext k ⟨j, r⟩
  simp [P, Q, latticeBasis_repr_apply]

/-- The dimension of the space of tuples: `(K ⊗ ℝ)ⁱ` has real dimension `d #ι`. -/
theorem finrank_pi [Fintype ι] : finrank ℝ (ι → mixedSpace K) = finrank ℚ K * Fintype.card ι := by
  rw [Module.finrank_pi_fintype, mixedEmbedding.finrank, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

end NumberField.mixedEmbedding

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*}

/-- The `i`-th **successive minimum over `K`** of an `𝓞 K`-submodule `Λ` of `Kⁱ` with respect to
a set `B` of `(K ⊗ ℝ)ⁱ`: the least dilation `t` for which `Λ ∩ t B` contains `i + 1` vectors
linearly independent over `K`. It is indexed from `0`, as `ZLattice.successiveMinimum` is, and for
`i ≥ #ι` there is no such family and the value is `sInf ∅ = 0`. -/
noncomputable def successiveMinimum (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ x : Fin (i + 1) → ι → K,
    (∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) ∧ LinearIndependent K x}

variable {Λ : Submodule (𝓞 K) (ι → K)} {B : Set (ι → mixedSpace K)} {i : ℕ}

/-- An admissible dilation bounds the minimum from above. -/
theorem successiveMinimum_le {t : ℝ} (ht : 0 < t) {x : Fin (i + 1) → ι → K}
    (hx : ∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B)
    (hind : LinearIndependent K x) : successiveMinimum Λ B i ≤ t :=
  csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ⟨ht, x, hx, hind⟩

/-- The minima are nonnegative. -/
theorem successiveMinimum_nonneg (Λ : Submodule (𝓞 K) (ι → K)) (B : Set (ι → mixedSpace K))
    (i : ℕ) : 0 ≤ successiveMinimum Λ B i :=
  Real.sInf_nonneg fun _ ht ↦ ht.1.le

/-- Above the rank the minima vanish: `Kⁱ` holds no `i + 1` independent vectors, so the set of
admissible dilations is empty. -/
theorem successiveMinimum_eq_zero_of_le [Fintype ι] (Λ : Submodule (𝓞 K) (ι → K))
    (B : Set (ι → mixedSpace K)) (hi : Fintype.card ι ≤ i) : successiveMinimum Λ B i = 0 := by
  have hempty : {t : ℝ | 0 < t ∧ ∃ x : Fin (i + 1) → ι → K,
      (∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) ∧
        LinearIndependent K x} = ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨x, -, hind⟩
    have := hind.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
    omega
  rw [successiveMinimum, hempty, Real.sInf_empty]

variable [NumberField K]

variable (K) in
/-- The constant `c_K` of the comparison between the two kinds of minima: the largest house of a
member of the integral basis `NumberField.integralBasis K`, so that every conjugate of every
member has absolute value at most `c_K`. -/
noncomputable def integralBasisHouse : ℝ :=
  ⨆ r, house (integralBasis K r)

/-- Every member of the integral basis has house at most `c_K`. -/
theorem house_integralBasis_le (r : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    house (integralBasis K r) ≤ integralBasisHouse K :=
  le_ciSup (f := fun r ↦ house (integralBasis K r)) (Set.finite_range _).bddAbove r

/-- Every member of the integral basis has absolute value at most `c_K` at every infinite
place. -/
theorem apply_integralBasis_le (w : InfinitePlace K) (r : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    w (integralBasis K r) ≤ integralBasisHouse K := by
  rw [← w.norm_embedding_eq]
  exact (norm_embedding_le_house _ _).trans (house_integralBasis_le r)

variable (K) in
/-- `c_K ≥ 1`: a nonzero algebraic integer has a conjugate of absolute value at least `1`. -/
theorem one_le_integralBasisHouse : 1 ≤ integralBasisHouse K := by
  obtain ⟨r⟩ := (integralBasis K).index_nonempty
  refine le_trans ?_ (house_integralBasis_le r)
  refine one_le_house_of_isIntegral ?_ ((integralBasis K).ne_zero r)
  rw [integralBasis_apply]
  exact (RingOfIntegers.basis K r).isIntegral_coe

/-- The mixed embedding of tuples, as a `ℚ`-linear map: the `f` of the extraction lemma. -/
private noncomputable def embedQ : (ι → K) →ₗ[ℚ] (ι → mixedSpace K) :=
  LinearMap.pi fun j ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap ∘ₗ LinearMap.proj j

private theorem embedQ_apply (x : ι → K) :
    (embedQ x : ι → mixedSpace K) = fun j ↦ mixedEmbedding K (x j) := rfl

/-- The extraction lemma of `ArithmeticHeights`, for the mixed embedding: from `d m` vectors of
`Kⁱ` with independent mixed embeddings, `m` of them independent over `K`, the `j`-th among the
first `d j + 1`. -/
private theorem exists_linearIndependent_comp {m : ℕ} {u : Fin (finrank ℚ K * m) → ι → K}
    (h : LinearIndependent ℝ (fun k j ↦ mixedEmbedding K (u k j))) :
    ∃ s : Fin m → Fin (finrank ℚ K * m), LinearIndependent K (u ∘ s) ∧
      ∀ j, (s j).val ≤ finrank ℚ K * j.val := by
  have h' : LinearIndependent ℝ (embedQ ∘ u) := by
    have : (embedQ ∘ u : Fin _ → ι → mixedSpace K) = fun k j ↦ mixedEmbedding K (u k j) :=
      funext fun k ↦ embedQ_apply (u k)
    rw [this]
    exact h
  exact LinearIndependent.exists_linearIndependent_comp_finrank_mul (F := ℚ) (E := ℝ) (K := K)
    (V := ι → K) (W := ι → mixedSpace K) embedQ h'

section Lattice

variable [Fintype ι]

open scoped Classical in
/-- **Extraction from the real minima**: `#ι` vectors of `Λ`, independent over `K`, the `k`-th of
gauge at most the `d k`-th real minimum. -/
private theorem exists_extraction (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    ∃ y : Fin (Fintype.card ι) → ι → K, LinearIndependent K y ∧ ∀ k, y k ∈ Λ ∧
      gauge B (fun j ↦ mixedEmbedding K (y k j)) ≤
        ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * k) := by
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum Λ.mixedImage hB₀ hB₁ hB₂ hB₃
  have hdim : finrank ℝ (ι → mixedSpace K) = finrank ℚ K * Fintype.card ι :=
    mixedEmbedding.finrank_pi
  choose u huΛ hu using fun j ↦ Submodule.mem_mixedImage.1 (hvL j)
  set u' : Fin (finrank ℚ K * Fintype.card ι) → ι → K := fun j ↦ u (Fin.cast hdim.symm j)
  have hu' : LinearIndependent ℝ (fun k j ↦ mixedEmbedding K (u' k j)) := by
    have : (fun k j ↦ mixedEmbedding K (u' k j)) = v ∘ Fin.cast hdim.symm := by
      ext j : 1
      simp only [Function.comp_apply, u', hu]
    rw [this]
    exact hvind.comp _ (Fin.cast_injective _)
  obtain ⟨s, hsind, hsle⟩ := exists_linearIndependent_comp hu'
  refine ⟨u' ∘ s, hsind, fun k ↦ ⟨huΛ _, ?_⟩⟩
  have hk : finrank ℚ K * k < finrank ℝ (ι → mixedSpace K) := by
    rw [hdim]
    exact Nat.mul_lt_mul_of_pos_left k.isLt Module.finrank_pos
  calc gauge B (fun j ↦ mixedEmbedding K ((u' ∘ s) k j))
      = ZLattice.successiveMinimum Λ.mixedImage B (Fin.cast hdim.symm (s k)) := by
        rw [← hvg, ← hu]; rfl
    _ ≤ ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * k) :=
        ZLattice.successiveMinimum_le_of_le (by simpa using hsle k) hk hB₀ hB₁ hB₂

open scoped Classical in
/-- Below the rank there is an admissible dilation: the extraction supplies the independent
vectors, and the body absorbs them. -/
private theorem exists_mem_admissible (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hi : i < Fintype.card ι) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : Fin (i + 1) → ι → K,
      (∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) ∧ LinearIndependent K x := by
  have h₀ : B ∈ 𝓝 (0 : ι → mixedSpace K) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨y, hyind, hy⟩ := exists_extraction Λ hB₀ hB₁ hB₂ hB₃
  set x : Fin (i + 1) → ι → K := fun k ↦ y (Fin.castLE hi k)
  set t : ℝ := 1 + ∑ k, gauge B (fun j ↦ mixedEmbedding K (x k j))
  have hlt : ∀ k, gauge B (fun j ↦ mixedEmbedding K (x k j)) < t := fun k ↦ by
    have : gauge B (fun j ↦ mixedEmbedding K (x k j)) ≤
        ∑ k, gauge B (fun j ↦ mixedEmbedding K (x k j)) :=
      Finset.single_le_sum (f := fun k ↦ gauge B (fun j ↦ mixedEmbedding K (x k j)))
        (fun k _ ↦ gauge_nonneg _) (Finset.mem_univ k)
    linarith
  refine ⟨t, ?_, x, fun k ↦ ⟨(hy _).1, mem_smul_of_gauge_lt hB₀ h₀ (hlt k)⟩, ?_⟩
  · have : (0 : ℝ) ≤ ∑ k, gauge B (fun j ↦ mixedEmbedding K (x k j)) :=
      Finset.sum_nonneg fun k _ ↦ gauge_nonneg _
    linarith
  · exact hyind.comp _ (Fin.castLE_injective hi)

open scoped Classical in
/-- Below the rank, a lower bound for every admissible dilation is a lower bound for the
minimum. -/
theorem le_successiveMinimum (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hi : i < Fintype.card ι)
    {c : ℝ} (H : ∀ t : ℝ, 0 < t → ∀ x : Fin (i + 1) → ι → K,
      (∀ k, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ t • B) → LinearIndependent K x →
        c ≤ t) :
    c ≤ successiveMinimum Λ B i :=
  le_csInf (exists_mem_admissible Λ hB₀ hB₁ hB₂ hB₃ hi) fun _ ht ↦
    H _ ht.1 _ ht.2.choose_spec.1 ht.2.choose_spec.2

open scoped Classical in
/-- The minima are monotone below the rank. The hypothesis `j < #ι` is not removable, since the
minima vanish above it. -/
theorem successiveMinimum_le_of_le (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    {j : ℕ} (hij : i ≤ j) (hj : j < Fintype.card ι) :
    successiveMinimum Λ B i ≤ successiveMinimum Λ B j := by
  refine le_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃ hj fun t ht x hx hind ↦ ?_
  have hle : i + 1 ≤ j + 1 := by omega
  exact successiveMinimum_le ht (x := fun k ↦ x (k.castLE hle)) (fun k ↦ hx _)
    (hind.comp _ (Fin.castLE_injective hle))

open scoped Classical in
/-- **`λ i ≤ μ i`**: vectors of `Λ` independent over `K` have mixed embeddings independent over
`ℝ`, so every dilation admissible for the minimum over `K` is admissible for the real one. -/
theorem successiveMinimum_mixedImage_le (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hi : i < Fintype.card ι) :
    ZLattice.successiveMinimum Λ.mixedImage B i ≤ successiveMinimum Λ B i := by
  refine le_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃ hi fun t ht x hx hind ↦ ?_
  exact ZLattice.successiveMinimum_le ht (v := fun k j ↦ mixedEmbedding K (x k j))
    (fun k ↦ ⟨(hx k).2, Submodule.mem_mixedImage.2 ⟨x k, (hx k).1, rfl⟩⟩)
    (mixedEmbedding.linearIndependent_pi (hind.restrict_scalars' ℚ))

open scoped Classical in
/-- The minima are positive below the rank, because the real ones are. -/
theorem successiveMinimum_pos (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hi : i < Fintype.card ι) : 0 < successiveMinimum Λ B i := by
  have hi' : i < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    nlinarith [Module.finrank_pos (R := ℚ) (M := K)]
  exact (ZLattice.successiveMinimum_pos Λ.mixedImage hB₀ hB₁ hB₂ hB₃ hi').trans_le
    (successiveMinimum_mixedImage_le Λ hB₀ hB₁ hB₂ hB₃ hi)

open scoped Classical in
/-- **`μ i ≤ λ (d i)`, the extraction lemma**: among the `d #ι` independent vectors realizing the
real minima there are `#ι` independent over `K`, the `k`-th among the first `d k + 1`, hence of
gauge at most `λ (d k)`. -/
theorem successiveMinimum_le_successiveMinimum_mixedImage (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hi : i < Fintype.card ι) :
    successiveMinimum Λ B i ≤ ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * i) := by
  have h₀ : B ∈ 𝓝 (0 : ι → mixedSpace K) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨y, hyind, hy⟩ := exists_extraction Λ hB₀ hB₁ hB₂ hB₃
  have hdi : finrank ℚ K * i < finrank ℝ (ι → mixedSpace K) := by
    rw [mixedEmbedding.finrank_pi]
    exact Nat.mul_lt_mul_of_pos_left hi Module.finrank_pos
  refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
  have htpos : 0 < t := (ZLattice.successiveMinimum_pos Λ.mixedImage hB₀ hB₁ hB₂ hB₃ hdi).trans ht
  refine successiveMinimum_le htpos (x := fun k ↦ y (Fin.castLE hi k)) (fun k ↦ ⟨(hy _).1, ?_⟩)
    (hyind.comp _ (Fin.castLE_injective hi))
  refine mem_smul_of_gauge_lt hB₀ h₀ (lt_of_le_of_lt ((hy _).2.trans ?_) ht)
  refine ZLattice.successiveMinimum_le_of_le ?_ hdi hB₀ hB₁ hB₂
  have : (Fin.castLE hi k : ℕ) ≤ i := by simpa using Nat.lt_succ_iff.1 k.isLt
  exact Nat.mul_le_mul_left _ this

open scoped Classical in
/-- **`λ (d (i + 1) - 1) ≤ c_K μ i`**: for `i + 1` vectors `x k` of `Λ` independent over `K` in
`t B`, the `d (i + 1)` vectors `ω r • x k`, `ω` the integral basis, lie in `Λ` because it is an
`𝓞 K`-module, are independent over `ℚ` and hence over `ℝ`, and lie in `c_K t B` because the body is
balanced over every completion. -/
theorem successiveMinimum_mixedImage_le_mul (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) →
      (fun j ↦ a * z j) ∈ B) (hi : i < Fintype.card ι) :
    ZLattice.successiveMinimum Λ.mixedImage B (finrank ℚ K * (i + 1) - 1) ≤
      integralBasisHouse K * successiveMinimum Λ B i := by
  set c := integralBasisHouse K with hc
  have hc0 : 0 < c := zero_lt_one.trans_le (one_le_integralBasisHouse K)
  rw [← div_le_iff₀' hc0]
  refine le_successiveMinimum Λ hB₀ hB₁ hB₂ hB₃ hi fun t ht x hx hind ↦ ?_
  rw [div_le_iff₀' hc0]
  set ω := integralBasis K
  set y : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin (i + 1) → ι → K := fun p ↦ ω p.1 • x p.2
  have hyind : LinearIndependent ℚ y := linearIndependent_smul ω.linearIndependent hind
  have hcard : Fintype.card (Fin (finrank ℚ K * (i + 1) - 1 + 1)) =
      Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K) × Fin (i + 1)) := by
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, ← finrank_eq_card_basis ω]
    have : 1 ≤ finrank ℚ K * (i + 1) := Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero Module.finrank_pos.ne' (Nat.succ_ne_zero i))
    omega
  set e := Fintype.equivOfCardEq hcard
  refine ZLattice.successiveMinimum_le (mul_pos hc0 ht)
    (v := fun m j ↦ mixedEmbedding K (y (e m) j)) (fun m ↦ ⟨?_, ?_⟩)
    ((mixedEmbedding.linearIndependent_pi hyind).comp _ e.injective)
  · obtain ⟨z, hz, hzx⟩ := (hx (e m).2).2
    set a : mixedSpace K := c⁻¹ • mixedEmbedding K (ω (e m).1)
    have ha : ∀ w, normAtPlace w a ≤ 1 := fun w ↦ by
      rw [normAtPlace_smul, normAtPlace_apply, abs_of_pos (inv_pos.2 hc0), inv_mul_le_one₀ hc0]
      exact apply_integralBasis_le w _
    have heq : (fun j ↦ mixedEmbedding K (y (e m) j)) = (c * t) • fun j ↦ a * z j := by
      ext1 j
      have hzj := congrFun hzx j
      simp only [Pi.smul_apply] at hzj
      simp only [y, a, Pi.smul_apply, smul_eq_mul, map_mul, ← hzj, smul_mul_assoc, mul_smul_comm,
        smul_smul]
      rw [mul_comm c t, mul_assoc, mul_inv_cancel₀ hc0.ne', mul_one]
    rw [heq]
    exact Set.smul_mem_smul_set (hBbal z hz a ha)
  · refine Submodule.mem_mixedImage.2 ⟨y (e m), ?_, rfl⟩
    have : y (e m) = (RingOfIntegers.basis K (e m).1) • x (e m).2 := by
      simp only [y, ω, integralBasis_apply, algebraMap_smul]
    rw [this]
    exact Λ.smul_mem _ (hx _).1

omit [Fintype ι] in
open scoped Classical in
/-- **A bounded set holds finitely many points of `Λ`**: their mixed embeddings lie in a bounded
part of a discrete closed subgroup, and the mixed embedding is injective. -/
theorem finite_setOf_mem_of_isBounded [Finite ι] (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] (hB₃ : Bornology.IsBounded B) :
    {x : ι → K | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ B}.Finite := by
  have : Fintype ι := Fintype.ofFinite ι
  have hfin : (B ∩ (Λ.mixedImage : Set (ι → mixedSpace K))).Finite := by
    refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hB₃ ?_
    have : DiscreteTopology Λ.mixedImage.toAddSubgroup :=
      inferInstanceAs (DiscreteTopology Λ.mixedImage)
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discreteTopology
  refine (hfin.preimage ?_).subset fun x hx ↦ ⟨hx.2, Submodule.mem_mixedImage.2 ⟨x, hx.1, rfl⟩⟩
  intro x _ y _ hxy
  funext j
  exact mixedEmbedding_injective K (congrFun hxy j)

open scoped Classical in
/-- **Each minimum is attained**, by finiteness alone: among the finitely many independent families
in `(μ i + 1) B` take one of least largest gauge; every admissible dilation below `μ i + 1` bounds
that gauge, so it is at most `μ i`, and the body is closed. -/
private theorem exists_mem_smul_successiveMinimum (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) (hi : i < Fintype.card ι) :
    ∃ x : Fin (i + 1) → ι → K, LinearIndependent K x ∧ ∀ k, x k ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (x k j)) ∈ successiveMinimum Λ B i • B := by
  set m := successiveMinimum Λ B i with hmdef
  have hm : 0 < m := successiveMinimum_pos Λ hB₀ hB₁ hB₂ hB₃ hi
  have h₀ : B ∈ 𝓝 (0 : ι → mixedSpace K) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 fun x hx ↦ hB₁ x hx
  have hne := exists_mem_admissible Λ hB₀ hB₁ hB₂ hB₃ hi
  set T := m + 1
  have hmono : ∀ {t : ℝ}, 0 < t → t ≤ T → t • B ⊆ T • B := fun ht htT ↦
    hbal.smul_mono (by rw [Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (by linarith)]; exact htT)
  set F := {x : ι → K | x ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ T • B}
  set S : Set (Fin (i + 1) → ι → K) := {x | (∀ k, x k ∈ F) ∧ LinearIndependent K x}
  have hSfin : S.Finite :=
    (Set.Finite.pi fun _ ↦ finite_setOf_mem_of_isBounded Λ (hB₃.smul₀ T)).subset fun x hx ↦
      Set.mem_univ_pi.2 hx.1
  set g : (Fin (i + 1) → ι → K) → ℝ := fun x ↦
    Finset.univ.sup' Finset.univ_nonempty fun k ↦ gauge B (fun j ↦ mixedEmbedding K (x k j))
  have hSne : S.Nonempty := by
    obtain ⟨t₀, ⟨ht₀, y, hy, hyind⟩, ht₀T⟩ := exists_lt_of_csInf_lt hne (lt_add_one m)
    exact ⟨y, fun k ↦ ⟨(hy k).1, hmono ht₀ ht₀T.le (hy k).2⟩, hyind⟩
  obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S g hSfin hSne
  have hgx : g x ≤ m := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ⟨ht, y, hy, hyind⟩, htlt⟩ :=
      exists_lt_of_csInf_lt hne (lt_min hcon (lt_add_one m))
    have hyS : y ∈ S :=
      ⟨fun k ↦ ⟨(hy k).1, hmono ht (htlt.le.trans (min_le_right _ _)) (hy k).2⟩, hyind⟩
    have hgy : g y ≤ t := Finset.sup'_le _ _ fun k _ ↦ gauge_le_of_mem ht.le (hy k).2
    linarith [hxmin y hyS, min_le_left (g x) T]
  refine ⟨x, hxS.2, fun k ↦ ⟨(hxS.1 k).1, ?_⟩⟩
  rw [← gauge_le_iff_mem_smul hB₀ hB₄ h₀ hm]
  exact (Finset.le_sup' (fun k ↦ gauge B (fun j ↦ mixedEmbedding K (x k j)))
    (Finset.mem_univ k)).trans hgx

open scoped Classical in
/-- **The minima over `K` are attained by one family**: there are `#ι` vectors of `Λ`, independent
over `K`, the `k`-th in `μ k B`. Each minimum is attained separately, and the family is assembled
one vector at a time: `k + 1` independent vectors realizing `μ k` contain one outside the span of
the `k` already chosen. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hB₄ : IsClosed B) :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧ ∀ k, x k ∈ Λ ∧
      (fun j ↦ mixedEmbedding K (x k j)) ∈ successiveMinimum Λ B k • B := by
  suffices H : ∀ m ≤ Fintype.card ι, ∃ x : Fin m → ι → K, LinearIndependent K x ∧
      ∀ k : Fin m, x k ∈ Λ ∧ (fun j ↦ mixedEmbedding K (x k j)) ∈ successiveMinimum Λ B k • B from
    H _ le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ ⟨Fin.elim0, linearIndependent_empty_type, fun k ↦ k.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨x, hxind, hx⟩ := ih (by omega)
    obtain ⟨y, hyind, hy⟩ :=
      exists_mem_smul_successiveMinimum (i := m) Λ hB₀ hB₁ hB₂ hB₃ hB₄ (by omega)
    have hex : ∃ j, y j ∉ Submodule.span K (Set.range x) := by
      by_contra hcon
      push Not at hcon
      have hle : Submodule.span K (Set.range y) ≤ Submodule.span K (Set.range x) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 hcon)
      have h1 := Submodule.finrank_mono hle
      rw [finrank_span_eq_card hyind, Fintype.card_fin] at h1
      have h2 : finrank K (Submodule.span K (Set.range x)) ≤ Fintype.card (Fin m) :=
        finrank_range_le_card (R := K) x
      rw [Fintype.card_fin] at h2
      omega
    obtain ⟨j, hj⟩ := hex
    refine ⟨Fin.snoc x (y j), linearIndependent_finSnoc.2 ⟨hxind, hj⟩, Fin.lastCases ?_ fun k ↦ ?_⟩
    · simpa using hy j
    · simpa using hx k

end Lattice

end NumberField
