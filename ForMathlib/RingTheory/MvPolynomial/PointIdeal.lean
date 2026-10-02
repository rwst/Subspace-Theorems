/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.GenericSection
public import ForMathlib.RingTheory.MvPolynomial.ProductStructure

-- Used only inside proofs.
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# The ideal of a point of a multiprojective space

Let the variables of `K[X]` be in blocks `b : σ → ι`, and let `P : σ → K` be the coordinates of a
point of `∏_i ℙ^{n_i}(K)`, nonzero in every block. `MvPolynomial.pointIdeal b P` is the kernel of
`X_s ↦ P_s Y_{b s}`, `K[X] → K[Y]`. It is a multihomogeneous prime
(`MvPolynomial.isWeightedHomogeneous_pointIdeal`) with nonzero Hilbert polynomial
(`MvPolynomial.hilbertPoly_pointIdeal_ne_zero`), and a multihomogeneous polynomial lies in it iff
it vanishes at `P` (`MvPolynomial.mem_pointIdeal_iff`). A multihomogeneous prime `𝔭` defines a
subvariety through `P` iff `𝔭 ≤ pointIdeal b P`.

`MvPolynomial.sub_mem_of_not_algebraicIndepOn`: if `𝔭 ≤ pointIdeal b P` and the variables
`x_{s₀}`, `x_u` of one block, `P_{s₀} ≠ 0`, are algebraically dependent modulo `𝔭`, then
`P_{s₀} X_u - P_u X_{s₀} ∈ 𝔭`. So if the projection of `V(𝔭)` to a factor `ℙ¹` is a point, it is
the projection of `P`. The proof: `y = P_{s₀} x_u - P_u x_{s₀}` is algebraic over `K[x_{s₀}]`, so
if `y ≠ 0` it divides a nonzero `r ∈ K[x_{s₀}]`; but `y` vanishes at `P` while `x_{s₀}` maps to
the transcendental `P_{s₀} Y_i`.

This is used for Evertse's Roth lemma (Evertse 1995, §5) in Layer Q1.4 of the
`QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι K : Type*} [Field K] (b : σ → ι) (P : σ → K)

/-- The map `X_s ↦ P_s Y_{b s}`. -/
noncomputable def pointMap : MvPolynomial σ K →ₐ[K] MvPolynomial ι K :=
  aeval fun s ↦ C (P s) * X (b s)

/-- **The ideal of the point `P`**: the kernel of `X_s ↦ P_s Y_{b s}`. -/
noncomputable def pointIdeal : Ideal (MvPolynomial σ K) :=
  RingHom.ker (pointMap b P)

instance : (pointIdeal b P).IsPrime :=
  RingHom.ker_isPrime _

variable {b P}

theorem mem_pointIdeal {g : MvPolynomial σ K} : g ∈ pointIdeal b P ↔ pointMap b P g = 0 :=
  RingHom.mem_ker

theorem pointMap_X (s : σ) : pointMap b P (X s) = C (P s) * X (b s) := by
  simp [pointMap]

theorem pointMap_monomial (μ : σ →₀ ℕ) (c : K) :
    pointMap b P (monomial μ c) =
      monomial (μ.mapDomain b) (c * μ.prod fun s e ↦ P s ^ e) := by
  have hX : (μ.prod fun s e ↦ (X (b s) : MvPolynomial ι K) ^ e) = monomial (μ.mapDomain b) 1 := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp
  have hprod : (μ.prod fun s e ↦ (C (P s) * X (b s) : MvPolynomial ι K) ^ e) =
      C (μ.prod fun s e ↦ P s ^ e) * monomial (μ.mapDomain b) 1 := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul, hX, map_finsuppProd]
    simp
  rw [pointMap, aeval_monomial, algebraMap_eq, hprod, ← mul_assoc, ← C_mul, C_mul_monomial,
    mul_one]

omit [Field K] in
/-- `|μ|_b = b_* μ`: the multidegree of a monomial is its image under the blocks. -/
theorem weight_multiWeight_eq_mapDomain [Finite σ] [DecidableEq ι] (μ : σ →₀ ℕ) :
    Finsupp.weight (multiWeight b) μ = ⇑(μ.mapDomain b) := by
  classical
  have := Fintype.ofFinite σ
  funext i
  rw [weight_multiWeight_apply, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine (Finset.sum_subset (fun s hs ↦ ?_) (fun s hs' hs ↦ ?_)).symm
  · simp only [Finset.mem_filter] at hs ⊢
    exact ⟨mem_univ s, hs.2⟩
  · simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_and', not_not] at hs
    exact hs (by simpa using hs')

theorem coeff_pointMap [Finite σ] [DecidableEq ι] (g : MvPolynomial σ K) (ν : ι →₀ ℕ) :
    (pointMap b P g).coeff ν = eval P (weightedHomogeneousComponent (multiWeight b) ν g) := by
  classical
  conv_lhs => rw [g.as_sum]
  rw [map_sum, coeff_sum, weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [pointMap_monomial, coeff_monomial, eval_monomial]
  exact if_congr (by rw [weight_multiWeight_eq_mapDomain, DFunLike.coe_fn_eq]) rfl rfl

/-- A multihomogeneous `g` of multidegree `ν` maps to `g(P) Y^ν`. -/
theorem pointMap_eq_monomial [Finite σ] [DecidableEq ι] {g : MvPolynomial σ K} {ν : ι →₀ ℕ}
    (hg : IsWeightedHomogeneous (multiWeight b) g ⇑ν) :
    pointMap b P g = monomial ν (eval P g) := by
  classical
  ext ν'
  rw [coeff_pointMap, coeff_monomial, weightedHomogeneousComponent_of_mem hg]
  by_cases h : ν = ν'
  · subst h
    simp
  · have h' : ¬(⇑ν' = ⇑ν) := fun h' ↦ h (DFunLike.coe_fn_eq.mp h').symm
    simp only [h, h', ↓reduceIte, map_zero]

/-- A multihomogeneous polynomial lies in `pointIdeal b P` iff it vanishes at `P`. -/
theorem mem_pointIdeal_iff [Finite σ] [DecidableEq ι] {g : MvPolynomial σ K} {ν : ι →₀ ℕ}
    (hg : IsWeightedHomogeneous (multiWeight b) g ⇑ν) : g ∈ pointIdeal b P ↔ eval P g = 0 := by
  rw [mem_pointIdeal, pointMap_eq_monomial hg, monomial_eq_zero]

theorem isWeightedHomogeneous_pointIdeal [Finite σ] [Finite ι] [DecidableEq ι] :
    (pointIdeal b P).IsWeightedHomogeneous (multiWeight b) := by
  intro g hg d
  have := Fintype.ofFinite ι
  set ν : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  have hν : ⇑ν = d := Finsupp.coe_equivFunOnFinite_symm d
  have hd := weightedHomogeneousComponent_isWeightedHomogeneous (w := multiWeight b) d g
  rw [← hν] at hd ⊢
  rw [mem_pointIdeal_iff hd, ← coeff_pointMap, mem_pointIdeal.mp hg]
  rfl

theorem X_notMem_pointIdeal {s : σ} (hs : P s ≠ 0) : X s ∉ pointIdeal b P := by
  rw [mem_pointIdeal, pointMap_X]
  exact mul_ne_zero (C_ne_zero.mpr hs) (X_ne_zero _)

/-- The point ideal of a point with a nonzero coordinate in every block has nonzero Hilbert
polynomial. -/
theorem hilbertPoly_pointIdeal_ne_zero [Finite σ] [Finite ι] [DecidableEq ι]
    (hb : Function.Surjective b) (hP : ∀ i, ∃ s, b s = i ∧ P s ≠ 0) :
    hilbertPoly b (pointIdeal b P) ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  choose t ht hPt using hP
  refine hilbertPoly_ne_zero_of_not_le hb isWeightedHomogeneous_pointIdeal fun hle ↦ ?_
  have hmem : (monomial (∑ i, Finsupp.single (t i) 1) 1 : MvPolynomial σ K) ∈
      irrelevantIdeal K b := by
    refine Ideal.subset_span ⟨_, ?_, rfl⟩
    rw [Finset.mem_coe, mem_blockMonomials]
    funext i
    rw [weight_multiWeight_apply]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · simp [ht]
    · intro j _ hji
      refine Finset.sum_eq_zero fun s hs ↦ ?_
      simp only [Finset.mem_filter] at hs
      rw [ite_eq_right_iff]
      rintro rfl
      exact (hji (by rw [← hs.2, ht])).elim
    · simp
  have h := hle hmem
  rw [monomial_sum_single_eq_prod, mem_pointIdeal, map_prod] at h
  refine Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ?_) h
  rw [pow_one, pointMap_X]
  exact mul_ne_zero (C_ne_zero.mpr (hPt i)) (X_ne_zero _)

/-- **A projection which is a point is the projection of `P`.** Let `𝔭 ≤ pointIdeal b P` be a
prime, i.e. `P ∈ V(𝔭)`, and let `x_{s₀}`, `x_u` be variables of the same block, `P_{s₀} ≠ 0`,
algebraically dependent modulo `𝔭`. Then `P_{s₀} X_u - P_u X_{s₀} ∈ 𝔭`. -/
theorem sub_mem_of_not_algebraicIndepOn {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭 ≤ pointIdeal b P) {s₀ u : σ} (hu : b u = b s₀) (hP₀ : P s₀ ≠ 0)
    (hdep : ¬AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk 𝔭 (X s)) {s₀, u}) :
    C (P s₀) * X u - C (P u) * X s₀ ∈ 𝔭 := by
  classical
  by_cases hus : u = s₀
  · subst hus
    rw [sub_self]
    exact 𝔭.zero_mem
  set A := MvPolynomial σ K ⧸ 𝔭
  set x : σ → A := fun s ↦ Ideal.Quotient.mk 𝔭 (X s)
  set φ : A →ₐ[K] MvPolynomial ι K := Ideal.Quotient.liftₐ 𝔭 (pointMap b P)
    fun a ha ↦ mem_pointIdeal.mp (h𝔭 ha)
  have hφ : ∀ g, φ (Ideal.Quotient.mk 𝔭 g) = pointMap b P g := fun g ↦ rfl
  -- `φ(x_{s₀}) = P_{s₀} Y_i` is transcendental, hence so is `x_{s₀}`.
  have htr : Transcendental K (φ (x s₀)) := by
    have h := (transcendental_X K (b s₀)).aeval (Polynomial.C (P s₀) * Polynomial.X)
      (by rw [Polynomial.natDegree_C_mul_X _ hP₀]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hP₀)
    rwa [show φ (x s₀) = Polynomial.aeval (X (b s₀) : MvPolynomial ι K)
      (Polynomial.C (P s₀) * Polynomial.X) by simp [x, hφ, pointMap_X, algebraMap_eq]]
  have htr₀ : Transcendental K (x s₀) := fun h ↦ htr (h.algHom φ)
  -- `x_u` is algebraic over `K[x_{s₀}]`.
  set R := Algebra.adjoin K {x s₀}
  have halg : IsAlgebraic R (x u) := by
    have hpair : ({s₀, u} : Set σ) = insert u {s₀} := Set.pair_comm s₀ u
    rw [hpair, AlgebraicIndepOn.insert_iff (by simpa using hus)] at hdep
    have hind : AlgebraicIndepOn K x {s₀} := by
      rw [AlgebraicIndepOn, algebraicIndependent_singleton_iff ⟨s₀, rfl⟩]
      exact htr₀
    have h := not_and.mp hdep hind
    rw [Set.image_singleton] at h
    exact not_not.mp h
  -- `y = P_{s₀} x_u - P_u x_{s₀}` is algebraic over `K[x_{s₀}]` and vanishes at `P`.
  by_contra hy
  set y : A := Ideal.Quotient.mk 𝔭 (C (P s₀) * X u - C (P u) * X s₀)
  have hy0 : y ≠ 0 := fun h ↦ hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx₀R : IsAlgebraic R (x s₀) :=
    isAlgebraic_algebraMap (⟨x s₀, Algebra.subset_adjoin rfl⟩ : R)
  have hcR : ∀ c : K, IsAlgebraic R (algebraMap K A c) := fun c ↦
    isAlgebraic_algebraMap (algebraMap K R c)
  have hyalg : IsAlgebraic R y := by
    have : y = algebraMap K A (P s₀) * x u + algebraMap K A (-P u) * x s₀ := by
      simp only [y, x, map_sub, map_mul, map_neg, ← algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      ring
    rw [this]
    exact ((hcR _).mul halg).add ((hcR _).mul hx₀R)
  have hφy : φ y = 0 := by
    simp only [y, hφ, map_sub, map_mul, pointMap_X, hu, algHom_C, algebraMap_eq]
    ring
  obtain ⟨r, hr0, c, hc⟩ := hyalg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)
  have hφr : φ (r : A) = 0 := by
    change φ (algebraMap R A r) = 0
    rw [hc, map_mul, hφy, zero_mul]
  obtain ⟨q, hq⟩ : ∃ q : Polynomial K, Polynomial.aeval (x s₀) q = r := by
    have h := r.2
    simp only [R, Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  have hq0 : q = 0 := by
    refine transcendental_iff.mp htr q ?_
    rw [Polynomial.aeval_algHom_apply, hq, hφr]
  exact hr0 (Subtype.ext (by rw [← hq, hq0, map_zero]; rfl))

/-- **A projection of rank one is the projection of `P`.** If `𝔭 ≤ pointIdeal b P` is a prime and
the variables of block `k` have rank at most `1` modulo `𝔭`, then `P_s X_t - P_t X_s ∈ 𝔭` for all
`s`, `t` in block `k`: the projection of `V(𝔭)` to the factor `k` is the point `P_k`. -/
theorem sub_mem_of_eRk_le_one {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭 ≤ pointIdeal b P) {k : ι} {s₀ : σ} (hs₀ : b s₀ = k) (hP₀ : P s₀ ≠ 0)
    (hrk : (varMatroid 𝔭).eRk {s | b s = k} ≤ 1) {s t : σ} (hs : b s = k) (ht : b t = k) :
    C (P s) * X t - C (P t) * X s ∈ 𝔭 := by
  classical
  have hℓ : ∀ u, b u = k → C (P s₀) * X u - C (P u) * X s₀ ∈ 𝔭 := by
    intro u hu
    by_cases hus : s₀ = u
    · subst hus
      rw [sub_self]
      exact 𝔭.zero_mem
    refine sub_mem_of_not_algebraicIndepOn h𝔭 (hu.trans hs₀.symm) hP₀ fun hind ↦ ?_
    have hle := (varMatroid_indep_iff.mpr hind).encard_le_eRk_of_subset (X := {s | b s = k})
      (Set.pair_subset hs₀ hu)
    rw [Set.encard_pair hus] at hle
    exact absurd (hle.trans hrk) (by decide)
  have hmul : C (P s₀) * (C (P s) * X t - C (P t) * X s) ∈ 𝔭 := by
    have h := 𝔭.sub_mem (𝔭.mul_mem_left (C (P s)) (hℓ t ht)) (𝔭.mul_mem_left (C (P t)) (hℓ s hs))
    convert h using 1
    ring
  refine (Ideal.IsPrime.mem_or_mem ‹_› hmul).resolve_left fun hC ↦ ?_
  exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hC (hP₀.isUnit.map C))

end MvPolynomial
