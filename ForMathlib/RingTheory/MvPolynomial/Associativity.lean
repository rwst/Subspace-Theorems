/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.Ideal.LocalLength
public import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The associativity formula for multiprojective degrees

For a multihomogeneous ideal `I` of `K[X]`, the top form of the Hilbert polynomial is a sum over
the multihomogeneous primes `𝔭 ⊇ I` of maximal dimension, weighted by the lengths
`ℓ(K[X]_𝔭 / I_𝔭)`:
`[T^α] H_I = ∑_𝔭 ℓ(K[X]_𝔭 / I_𝔭) · [T^α] H_𝔭` for `|α| ≥ deg H_I`. In terms of degrees,
`d_α(I) = ∑_𝔭 ℓ_𝔭 · d_α(𝔭)`. See G. Rémond, *Élimination multihomogène*, Chapter 5 of
Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001),
§2.3, and J.-H. Evertse, Acta Arith. **73** (1995), §2.

The proof goes through a *prime filtration*
`I = J_0 ⊂ J_1 ⊂ ⋯ ⊂ J_r = K[X]` with `J_k = J_{k-1} + (f_k)` for multihomogeneous `f_k`, and
`(J_{k-1} : f_k) = 𝔮_k` a multihomogeneous prime (`MvPolynomial.exists_primeFiltration`). A
maximal colon ideal `(J : f)` is prime by the graded primality criterion, which needs a total
order on the grading: we use `Lex (ι → ℕ)`. Each step gives
`H_{J_{k-1}} = H_{J_k} + H_{𝔮_k}(T - deg f_k)` and
`ℓ((K[X]/J_{k-1})_𝔭) = ℓ((K[X]/𝔮_k)_𝔭) + ℓ((K[X]/J_k)_𝔭)`.

Summing up, `H_I = ∑_k H_{𝔮_k}(T - a_k)`. Every summand has nonnegative top coefficients, so there
is no cancellation (`MvPolynomial.totalDegree_le_totalDegree_sum`): `deg H_I` is the largest
`deg H_{𝔮_k}`, and the top form of `H_I` is the sum of the top forms of the `H_{𝔮_k}` of that
degree. The same argument shows that a strictly larger multihomogeneous prime has strictly smaller
dimension (`MvPolynomial.totalDegree_hilbertPoly_lt_of_lt`), so a prime `𝔭` of maximal dimension
meets the filtration only in the factors `𝔮_k = 𝔭`, and `ℓ((K[X]/I)_𝔭)` counts them.

As in `ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree`, dimension means `deg H_I`.

## Main statements

* `Ideal.IsWeightedHomogeneous.isPrime_of_mem_or_mem`: the graded primality criterion for the
  multigrading.
* `Ideal.IsWeightedHomogeneous.of_mem_minimalPrimes`: minimal primes of multihomogeneous ideals
  are multihomogeneous.
* `MvPolynomial.exists_primeFiltration`: prime filtrations between multihomogeneous ideals, with
  their effect on Hilbert polynomials and on localized lengths.
* `MvPolynomial.hilbertPoly_ne_zero_of_le`, `MvPolynomial.totalDegree_hilbertPoly_le_of_le`:
  a smaller ideal has a larger dimension.
* `MvPolynomial.coeff_hilbertPoly_le_of_le`, `MvPolynomial.multidegree_le_of_le`: a larger ideal
  has smaller top coefficients and degrees.
* `MvPolynomial.totalDegree_hilbertPoly_lt_of_lt`: a strictly larger prime has a strictly smaller
  dimension.
* `MvPolynomial.coeff_hilbertPoly_eq_sum_localLength` and
  `MvPolynomial.multidegree_eq_sum_localLength`: **the associativity formula**.
-/

@[expose] public section

open Finset

variable {σ ι K : Type*}

namespace MvPolynomial

section NonnegTop

variable {τ : Type*}

theorem exists_coeff_ne_zero_degree_eq {R : Type*} [CommSemiring R] {P : MvPolynomial ι R}
    (hP : P ≠ 0) : ∃ α : ι →₀ ℕ, P.coeff α ≠ 0 ∧ α.degree = P.totalDegree := by
  have hne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hP
  obtain ⟨α, hα, hαdeg⟩ := Finset.exists_mem_eq_sup _ hne fun s ↦ s.sum fun _ e ↦ e
  refine ⟨α, mem_support_iff.mp hα, ?_⟩
  rw [Finsupp.degree_apply, totalDegree, hαdeg]
  rfl

/-- **Nonnegative top forms do not cancel.** If every `P t` has nonnegative coefficients in all
degrees `≥ deg P t`, a nonzero summand survives in the sum, with its degree. -/
theorem totalDegree_le_totalDegree_sum {s : Finset τ} {P : τ → MvPolynomial ι ℚ}
    (h : ∀ t ∈ s, ∀ α : ι →₀ ℕ, (P t).totalDegree ≤ α.degree → 0 ≤ (P t).coeff α)
    {t₀ : τ} (ht₀ : t₀ ∈ s) (hne : P t₀ ≠ 0) :
    (P t₀).totalDegree ≤ (∑ t ∈ s, P t).totalDegree ∧ ∑ t ∈ s, P t ≠ 0 := by
  classical
  set u := s.filter (P · ≠ 0)
  obtain ⟨t₁, ht₁, hmax⟩ := u.exists_max_image (fun t ↦ (P t).totalDegree)
    ⟨t₀, Finset.mem_filter.mpr ⟨ht₀, hne⟩⟩
  obtain ⟨ht₁s, ht₁0⟩ := Finset.mem_filter.mp ht₁
  obtain ⟨α, hα, hαdeg⟩ := exists_coeff_ne_zero_degree_eq ht₁0
  have hnn : ∀ t ∈ s, 0 ≤ (P t).coeff α := by
    intro t ht
    by_cases ht0 : P t = 0
    · simp [ht0]
    · exact h t ht α (hαdeg ▸ hmax t (Finset.mem_filter.mpr ⟨ht, ht0⟩))
  have hpos : 0 < (∑ t ∈ s, P t).coeff α := by
    rw [coeff_sum]
    exact lt_of_lt_of_le (lt_of_le_of_ne (hnn t₁ ht₁s) hα.symm)
      (Finset.single_le_sum hnn ht₁s)
  have hle : α.degree ≤ (∑ t ∈ s, P t).totalDegree := by
    rw [Finsupp.degree_apply]
    exact le_totalDegree (mem_support_iff.mpr hpos.ne')
  refine ⟨?_, fun h0 ↦ by simp [h0] at hpos⟩
  exact (hmax t₀ (Finset.mem_filter.mpr ⟨ht₀, hne⟩)).trans (hαdeg ▸ hle)

theorem totalDegree_shiftPoly (a : ι → ℕ) (P : MvPolynomial ι ℚ) :
    (shiftPoly a P).totalDegree = P.totalDegree := by
  refine le_antisymm (totalDegree_shiftPoly_le a P) ?_
  by_cases hP : P = 0
  · simp [hP]
  obtain ⟨α, hα, hαdeg⟩ := exists_coeff_ne_zero_degree_eq hP
  rw [← hαdeg, Finsupp.degree_apply]
  refine le_totalDegree (mem_support_iff.mpr ?_)
  rwa [agreeAbove_shiftPoly a P α hαdeg.ge]

theorem coeff_shiftPoly_nonneg {a : ι → ℕ} {P : MvPolynomial ι ℚ}
    (h : ∀ α : ι →₀ ℕ, P.totalDegree ≤ α.degree → 0 ≤ P.coeff α) (α : ι →₀ ℕ)
    (hα : (shiftPoly a P).totalDegree ≤ α.degree) : 0 ≤ (shiftPoly a P).coeff α := by
  rw [totalDegree_shiftPoly] at hα
  rw [agreeAbove_shiftPoly a P α hα]
  exact h α hα

theorem shiftPoly_ne_zero (a : ι → ℕ) {P : MvPolynomial ι ℚ} (hP : P ≠ 0) :
    shiftPoly a P ≠ 0 := by
  obtain ⟨α, hα, hαdeg⟩ := exists_coeff_ne_zero_degree_eq hP
  intro h
  apply hα
  rw [← agreeAbove_shiftPoly a P α hαdeg.ge, h]
  simp

theorem shiftPoly_C (a : ι → ℕ) (c : ℚ) : shiftPoly a (C c) = C c := by
  simp [shiftPoly]

end NonnegTop

section Graded

variable [Field K]

theorem exists_isWeightedHomogeneous_mem_notMem {M : Type*} [AddCommMonoid M] {w : σ → M}
    {J L : Ideal (MvPolynomial σ K)} (hL : L.IsWeightedHomogeneous w) (h : ¬ L ≤ J) :
    ∃ f e, IsWeightedHomogeneous w f e ∧ f ∈ L ∧ f ∉ J := by
  classical
  obtain ⟨y, hyL, hyJ⟩ := Set.not_subset.mp h
  by_contra! H
  apply hyJ
  rw [← sum_weightedHomogeneousComponent w y,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp y)]
  exact J.sum_mem fun d _ ↦
    H _ d (weightedHomogeneousComponent_isWeightedHomogeneous d y) (hL hyL d)

attribute [local instance] weightedGradedAlgebra in
theorem _root_.Ideal.IsWeightedHomogeneous.isPrime_of_mem_or_mem_lex [LinearOrder ι] [Finite ι]
    {w : σ → Lex (ι → ℕ)} {P : Ideal (MvPolynomial σ K)} (hP : P.IsWeightedHomogeneous w)
    (hne : P ≠ ⊤)
    (h : ∀ {x y d e}, IsWeightedHomogeneous w x d → IsWeightedHomogeneous w y e → x * y ∈ P →
      x ∈ P ∨ y ∈ P) : P.IsPrime := by
  rw [isWeightedHomogeneous_iff_isHomogeneous] at hP
  refine hP.isPrime_of_homogeneous_mem_or_mem hne ?_
  intro x y hx hy hxy
  obtain ⟨d, hx⟩ := hx
  obtain ⟨e, hy⟩ := hy
  exact h hx hy hxy

variable [DecidableEq ι] {b : σ → ι}

/-- **The graded primality criterion.** A multihomogeneous ideal is prime as soon as it satisfies
the primality condition for multihomogeneous elements. -/
theorem _root_.Ideal.IsWeightedHomogeneous.isPrime_of_mem_or_mem [Finite ι]
    {P : Ideal (MvPolynomial σ K)} (hP : P.IsWeightedHomogeneous (multiWeight b)) (hne : P ≠ ⊤)
    (h : ∀ {x y d e}, IsWeightedHomogeneous (multiWeight b) x d →
      IsWeightedHomogeneous (multiWeight b) y e → x * y ∈ P → x ∈ P ∨ y ∈ P) : P.IsPrime := by
  have := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hc : ∀ (d : Lex (ι → ℕ)) (p : MvPolynomial σ K),
      weightedHomogeneousComponent (fun s ↦ toLex (multiWeight b s)) d p =
        weightedHomogeneousComponent (multiWeight b) (ofLex d) p := by
    intro d p
    classical
    ext c
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    rfl
  refine Ideal.IsWeightedHomogeneous.isPrime_of_mem_or_mem_lex
    (w := fun s ↦ toLex (multiWeight b s)) (fun p hp d ↦ ?_) hne
    fun {x y d e} hx hy hxy ↦ h (d := ofLex d) (e := ofLex e) hx hy hxy
  rw [hc]
  exact hP hp _

/-- **Minimal primes of multihomogeneous ideals are multihomogeneous.** The ideal generated by
the multihomogeneous elements of a prime `𝔭 ⊇ I` is prime by the graded primality criterion and
contains `I`, so it is `𝔭` when `𝔭` is minimal. -/
theorem _root_.Ideal.IsWeightedHomogeneous.of_mem_minimalPrimes [Finite ι]
    {I 𝔭 : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (h𝔭 : 𝔭 ∈ I.minimalPrimes) : 𝔭.IsWeightedHomogeneous (multiWeight b) := by
  classical
  set J := Ideal.span {f | f ∈ 𝔭 ∧ ∃ e, IsWeightedHomogeneous (multiWeight b) f e}
  have hJ : J.IsWeightedHomogeneous (multiWeight b) :=
    isWeightedHomogeneous_span fun g hg ↦ hg.2
  have hJ𝔭 : J ≤ 𝔭 := Ideal.span_le.mpr fun f hf ↦ hf.1
  have hJp : J.IsPrime := by
    refine hJ.isPrime_of_mem_or_mem (ne_top_of_le_ne_top h𝔭.1.1.ne_top hJ𝔭) ?_
    intro x y d e hx hy hxy
    refine (h𝔭.1.1.mem_or_mem (hJ𝔭 hxy)).imp (fun h ↦ ?_) fun h ↦ ?_
    · exact Ideal.subset_span ⟨h, d, hx⟩
    · exact Ideal.subset_span ⟨h, e, hy⟩
  have hIJ : I ≤ J := by
    intro p hp
    rw [← sum_weightedHomogeneousComponent (multiWeight b) p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    exact J.sum_mem fun d _ ↦ Ideal.subset_span
      ⟨h𝔭.1.2 (hI hp d), d, weightedHomogeneousComponent_isWeightedHomogeneous d p⟩
  rwa [le_antisymm hJ𝔭 (h𝔭.2 ⟨hJp, hIJ⟩ hJ𝔭)] at hJ

/-- **Maximal colon ideals are prime.** Between multihomogeneous ideals `J` and `L ⊄ J` there is a
multihomogeneous `f ∈ L \ J` with `(J : f)` prime. -/
theorem exists_isPrime_colon [Finite σ] [Finite ι] {J L : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) (hL : L.IsWeightedHomogeneous (multiWeight b))
    (h : ¬ L ≤ J) :
    ∃ f e, IsWeightedHomogeneous (multiWeight b) f e ∧ f ∈ L ∧ f ∉ J ∧
      (J.colon {f}).IsPrime := by
  set S : Set (Ideal (MvPolynomial σ K)) :=
    {Q | ∃ f e, IsWeightedHomogeneous (multiWeight b) f e ∧ f ∈ L ∧ f ∉ J ∧ Q = J.colon {f}}
  obtain ⟨f₀, e₀, hf₀, hf₀L, hf₀J⟩ := exists_isWeightedHomogeneous_mem_notMem hL h
  obtain ⟨Q, ⟨f, e, hf, hfL, hfJ, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr inferInstance S ⟨_, f₀, e₀, hf₀, hf₀L, hf₀J, rfl⟩
  refine ⟨f, e, hf, hfL, hfJ, (hJ.colon hf).isPrime_of_mem_or_mem ?_ fun {x y d d'} hx _ hxy ↦ ?_⟩
  · intro htop
    apply hfJ
    have : (1 : MvPolynomial σ K) ∈ J.colon {f} := htop ▸ Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at this
  · by_cases hxQ : x ∈ J.colon {f}
    · exact Or.inl hxQ
    right
    have hxf : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxQ
    have hle : J.colon {f} ≤ J.colon {x * f} := fun z hz ↦ by
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hz ⊢
      rw [mul_left_comm]
      exact J.mul_mem_left x hz
    have heq := (lt_or_eq_of_le hle).resolve_left
      (hmax _ ⟨x * f, d + e, hx.mul hf, L.mul_mem_left x hfL, hxf, rfl⟩)
    rw [heq]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy ⊢
    rwa [← mul_assoc, mul_comm y x]

theorem le_colon_singleton (J : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    J ≤ J.colon {f} := fun x hx ↦ by
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact J.mul_mem_right f hx

/-- **Prime filtrations.** Between multihomogeneous ideals `J ≤ L` there is a chain
`J = J_0 ⊂ ⋯ ⊂ J_n = L` whose steps are `J_k = J_{k-1} + (f_k)` with `(J_{k-1} : f_k) = 𝔮_k` a
multihomogeneous prime. So `H_J = H_L + ∑ k, H_{𝔮_k}(T - a_k)` with `a_k = deg f_k`, and
`ℓ((K[X]/J)_𝔭) = ℓ((K[X]/L)_𝔭) + ∑ k, ℓ((K[X]/𝔮_k)_𝔭)` for every prime `𝔭`. -/
theorem exists_primeFiltration [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {L : Ideal (MvPolynomial σ K)} (hL : L.IsWeightedHomogeneous (multiWeight b))
    {J : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hJL : J ≤ L) :
    ∃ (n : ℕ) (a : Fin n → ι → ℕ) (𝔮 : Fin n → Ideal (MvPolynomial σ K)),
      (∀ k, (𝔮 k).IsPrime ∧ (𝔮 k).IsWeightedHomogeneous (multiWeight b) ∧ J ≤ 𝔮 k) ∧
      hilbertPoly b J = hilbertPoly b L + ∑ k, shiftPoly (a k) (hilbertPoly b (𝔮 k)) ∧
      ∀ (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
        Ideal.localLength 𝔭 J = Ideal.localLength 𝔭 L + ∑ k, Ideal.localLength 𝔭 (𝔮 k) := by
  induction J using IsNoetherian.induction with
  | hgt J IH =>
  by_cases hLJ : L ≤ J
  · obtain rfl := le_antisymm hJL hLJ
    exact ⟨0, Fin.elim0, Fin.elim0, fun k ↦ k.elim0, by simp, fun 𝔭 _ ↦ by simp⟩
  obtain ⟨f, e, hf, hfL, hfJ, hprime⟩ := exists_isPrime_colon hJ hL hLJ
  have hJ' : Ideal.IsWeightedHomogeneous (multiWeight b) (J ⊔ Ideal.span {f}) :=
    hJ.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e, (Set.mem_singleton_iff.mp hx) ▸ hf⟩)
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h ↦
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨n, a, 𝔮, h𝔮, hH, hℓ⟩ := IH _ hlt hJ'
    (sup_le hJL (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfL)))
  refine ⟨n + 1, Fin.cons e a, Fin.cons (J.colon {f}) 𝔮, fun k ↦ ?_, ?_, fun 𝔭 _ ↦ ?_⟩
  · refine Fin.cases ⟨hprime, hJ.colon hf, le_colon_singleton J f⟩ (fun k ↦ ?_) k
    exact ⟨(h𝔮 k).1, (h𝔮 k).2.1, le_sup_left.trans (h𝔮 k).2.2⟩
  · have hf0 : f ≠ 0 := fun h ↦ hfJ (h ▸ J.zero_mem)
    have := hilbertPoly_sup_span_singleton hb hJ hf hf0
    rw [hH] at this
    rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [add_left_comm, this, add_sub_cancel]
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Ideal.localLength_eq_add_colon 𝔭 J f, hℓ 𝔭]
    simp only [Fin.cons_succ]
    ring

theorem hilbertPoly_top [Finite σ] [Finite ι] (hb : Function.Surjective b) :
    hilbertPoly b (⊤ : Ideal (MvPolynomial σ K)) = 0 := by
  refine hilbertPoly_eq_of_forall_le hb (isWeightedHomogeneous_top _) (d₀ := 0) fun d _ ↦ ?_
  rw [hilbertFunction, Submodule.restrictScalars_top, top_inf_eq, Nat.sub_self]
  simp

/-- The Hilbert polynomial along a prime filtration, as a sum with nonnegative top forms. -/
private theorem nonneg_filtration [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {L : Ideal (MvPolynomial σ K)} (hL : L.IsWeightedHomogeneous (multiWeight b)) {n : ℕ}
    {a : Fin n → ι → ℕ} {𝔮 : Fin n → Ideal (MvPolynomial σ K)}
    (h𝔮 : ∀ k, (𝔮 k).IsWeightedHomogeneous (multiWeight b)) :
    ∀ t ∈ (univ : Finset (Option (Fin n))), ∀ α : ι →₀ ℕ,
      (t.elim (hilbertPoly b L) fun k ↦ shiftPoly (a k) (hilbertPoly b (𝔮 k))).totalDegree ≤
        α.degree →
      0 ≤ (t.elim (hilbertPoly b L) fun k ↦ shiftPoly (a k) (hilbertPoly b (𝔮 k))).coeff α := by
  rintro (_ | k) _ α hα
  · exact coeff_hilbertPoly_nonneg hb hL hα
  · exact coeff_shiftPoly_nonneg (fun α hα ↦ coeff_hilbertPoly_nonneg hb (h𝔮 k) hα) α hα

/-- A multihomogeneous ideal inside one with nonzero Hilbert polynomial has nonzero Hilbert
polynomial. -/
theorem hilbertPoly_ne_zero_of_le [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {J L : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hL : L.IsWeightedHomogeneous (multiWeight b)) (hJL : J ≤ L) (hne : hilbertPoly b L ≠ 0) :
    hilbertPoly b J ≠ 0 := by
  obtain ⟨n, a, 𝔮, h𝔮, hH, -⟩ := exists_primeFiltration hb hL hJ hJL
  have := (totalDegree_le_totalDegree_sum (nonneg_filtration hb hL (a := a)
    fun k ↦ (h𝔮 k).2.1) (mem_univ none) hne).2
  rw [Fintype.sum_option] at this
  simp only [Option.elim_none, Option.elim_some] at this
  rwa [← hH] at this

/-- **A smaller ideal has a larger dimension.** -/
theorem totalDegree_hilbertPoly_le_of_le [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {J L : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hL : L.IsWeightedHomogeneous (multiWeight b)) (hJL : J ≤ L) :
    (hilbertPoly b L).totalDegree ≤ (hilbertPoly b J).totalDegree := by
  by_cases hne : hilbertPoly b L = 0
  · simp [hne]
  obtain ⟨n, a, 𝔮, h𝔮, hH, -⟩ := exists_primeFiltration hb hL hJ hJL
  have := (totalDegree_le_totalDegree_sum (nonneg_filtration hb hL (a := a)
    fun k ↦ (h𝔮 k).2.1) (mem_univ none) hne).1
  rw [Fintype.sum_option] at this
  simp only [Option.elim_none, Option.elim_some] at this
  rwa [← hH] at this

/-- **A larger ideal has smaller top coefficients.** For multihomogeneous `J ≤ L`,
`[T^α] H_L ≤ [T^α] H_J` in every degree `|α| ≥ deg H_J`. -/
theorem coeff_hilbertPoly_le_of_le [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {J L : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hL : L.IsWeightedHomogeneous (multiWeight b)) (hJL : J ≤ L) {α : ι →₀ ℕ}
    (hα : (hilbertPoly b J).totalDegree ≤ α.degree) :
    (hilbertPoly b L).coeff α ≤ (hilbertPoly b J).coeff α := by
  obtain ⟨n, a, 𝔮, h𝔮, hH, -⟩ := exists_primeFiltration hb hL hJ hJL
  have hnn := nonneg_filtration hb hL (a := a) fun k ↦ (h𝔮 k).2.1
  rw [hH, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum, le_add_iff_nonneg_right]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  by_cases h0 : shiftPoly (a k) (hilbertPoly b (𝔮 k)) = 0
  · simp [h0]
  have := (totalDegree_le_totalDegree_sum hnn (mem_univ (some k)) h0).1
  rw [Fintype.sum_option] at this
  simp only [Option.elim_none, Option.elim_some] at this
  rw [← hH] at this
  exact hnn (some k) (mem_univ _) α (this.trans hα)

/-- **A larger ideal has smaller degrees**: `d_α(L) ≤ d_α(J)` for multihomogeneous `J ≤ L` and
`|α| ≥ deg H_J`. -/
theorem multidegree_le_of_le [Finite σ] [Fintype ι] (hb : Function.Surjective b)
    {J L : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hL : L.IsWeightedHomogeneous (multiWeight b)) (hJL : J ≤ L) {α : ι →₀ ℕ}
    (hα : (hilbertPoly b J).totalDegree ≤ α.degree) :
    multidegree b L α ≤ multidegree b J α :=
  mul_le_mul_of_nonneg_left (coeff_hilbertPoly_le_of_le hb hJ hL hJL hα)
    (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)

/-- **A strictly larger prime has a strictly smaller dimension.** For multihomogeneous primes
`𝔮 < 𝔭` with `H_𝔭 ≠ 0`, `deg H_𝔭 < deg H_𝔮`. -/
theorem totalDegree_hilbertPoly_lt_of_lt [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {𝔮 𝔭 : Ideal (MvPolynomial σ K)} [𝔮.IsPrime] (h𝔮 : 𝔮.IsWeightedHomogeneous (multiWeight b))
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hlt : 𝔮 < 𝔭) (hne : hilbertPoly b 𝔭 ≠ 0) :
    (hilbertPoly b 𝔭).totalDegree < (hilbertPoly b 𝔮).totalDegree := by
  obtain ⟨g, e, hg, hg𝔭, hg𝔮⟩ := exists_isWeightedHomogeneous_mem_notMem h𝔭 (not_le_of_gt hlt)
  have hJ : (𝔮 ⊔ Ideal.span {g}).IsWeightedHomogeneous (multiWeight b) :=
    h𝔮.sup (isWeightedHomogeneous_span fun x hx ↦ ⟨e, (Set.mem_singleton_iff.mp hx) ▸ hg⟩)
  have hJ𝔭 : 𝔮 ⊔ Ideal.span {g} ≤ 𝔭 :=
    sup_le hlt.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg𝔭))
  have hne' := hilbertPoly_ne_zero_of_le hb hJ h𝔭 hJ𝔭 hne
  have h1 := totalDegree_hilbertPoly_le_of_le hb hJ h𝔭 hJ𝔭
  have h2 := totalDegree_hilbertPoly_sup_span_singleton_le hb h𝔮 hg hg𝔮
  have hpos : 1 ≤ (hilbertPoly b 𝔮).totalDegree := by
    by_contra h0
    push Not at h0
    have hc := totalDegree_eq_zero_iff_eq_C.mp (Nat.lt_one_iff.mp h0)
    apply hne'
    rw [hilbertPoly_sup_span_singleton_of_isPrime hb h𝔮 hg hg𝔮, hc, shiftPoly_C, sub_self]
  omega

/-- **The associativity formula.** Let `I` be multihomogeneous, and let `P` be the set of
multihomogeneous primes `𝔭 ⊇ I` of maximal dimension: `H_𝔭 ≠ 0` and `deg H_𝔭 = deg H_I`. Then `P`
is finite, the lengths `ℓ_𝔭 = ℓ(K[X]_𝔭 / I_𝔭)` are finite, and in every degree `|α| ≥ deg H_I`,
`[T^α] H_I = ∑_{𝔭 ∈ P} ℓ_𝔭 · [T^α] H_𝔭`. -/
theorem coeff_hilbertPoly_eq_sum_localLength [Finite σ] [Finite ι] (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (P : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧ I ≤ 𝔭 ∧
        hilbertPoly b 𝔭 ≠ 0 ∧ (hilbertPoly b 𝔭).totalDegree = (hilbertPoly b I).totalDegree) ∧
      (∀ 𝔭 ∈ P, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 I = ℓ 𝔭) ∧
      ∀ α : ι →₀ ℕ, (hilbertPoly b I).totalDegree ≤ α.degree →
        (hilbertPoly b I).coeff α = ∑ 𝔭 ∈ P, (ℓ 𝔭 : ℚ) * (hilbertPoly b 𝔭).coeff α := by
  classical
  obtain ⟨m, a, 𝔮, h𝔮, hH, hℓ⟩ :=
    exists_primeFiltration hb (isWeightedHomogeneous_top _) hI le_top
  rw [hilbertPoly_top hb, zero_add] at hH
  set n := (hilbertPoly b I).totalDegree
  have hdeg : ∀ k, (hilbertPoly b (𝔮 k)).totalDegree ≤ n := by
    intro k
    by_cases h0 : hilbertPoly b (𝔮 k) = 0
    · simp [h0]
    have := (totalDegree_le_totalDegree_sum (s := univ) (fun k _ α hα ↦ coeff_shiftPoly_nonneg
      (fun α hα ↦ coeff_hilbertPoly_nonneg hb (h𝔮 k).2.1 hα) α hα) (mem_univ k)
      (shiftPoly_ne_zero (a k) h0)).1
    rwa [totalDegree_shiftPoly, ← hH] at this
  have hcoeff : ∀ α : ι →₀ ℕ, n ≤ α.degree →
      (hilbertPoly b I).coeff α = ∑ k, (hilbertPoly b (𝔮 k)).coeff α := by
    intro α hα
    rw [hH, coeff_sum]
    exact sum_congr rfl fun k _ ↦ agreeAbove_shiftPoly _ _ α ((hdeg k).trans hα)
  have hkey : ∀ 𝔭 : Ideal (MvPolynomial σ K), 𝔭.IsWeightedHomogeneous (multiWeight b) →
      hilbertPoly b 𝔭 ≠ 0 → (hilbertPoly b 𝔭).totalDegree = n → ∀ k, 𝔮 k ≤ 𝔭 → 𝔮 k = 𝔭 := by
    intro 𝔭 h𝔭 hne hn k hk
    by_contra hk'
    have := (h𝔮 k).1
    have := totalDegree_hilbertPoly_lt_of_lt hb (h𝔮 k).2.1 h𝔭 (lt_of_le_of_ne hk hk') hne
    have := hdeg k
    omega
  have hlen : ∀ (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime],
      𝔭.IsWeightedHomogeneous (multiWeight b) → hilbertPoly b 𝔭 ≠ 0 →
      (hilbertPoly b 𝔭).totalDegree = n → Ideal.localLength 𝔭 I = (#{k | 𝔮 k = 𝔭} : ℕ) := by
    intro 𝔭 _ h𝔭 hne hn
    rw [hℓ 𝔭, Ideal.localLength_top, zero_add, Finset.card_filter, Nat.cast_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    by_cases hk : 𝔮 k = 𝔭
    · subst hk
      simp [Ideal.localLength_self]
    · rw [Ideal.localLength_of_not_le fun h ↦ hk (hkey 𝔭 h𝔭 hne hn k h)]
      simp [hk]
  refine ⟨(univ.image 𝔮).filter fun 𝔭 ↦ hilbertPoly b 𝔭 ≠ 0 ∧
    (hilbertPoly b 𝔭).totalDegree = n, fun 𝔭 ↦ #{k | 𝔮 k = 𝔭}, fun 𝔭 ↦ ?_, fun 𝔭 h𝔭 _ ↦ ?_,
    fun α hα ↦ ?_⟩
  · simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, rfl⟩, hne, hn⟩
      exact ⟨(h𝔮 k).1, (h𝔮 k).2.1, (h𝔮 k).2.2, hne, hn⟩
    · rintro ⟨hprime, h𝔭, hI𝔭, hne, hn⟩
      refine ⟨?_, hne, hn⟩
      have hpos := Ideal.localLength_ne_zero hI𝔭
      rw [hℓ 𝔭, Ideal.localLength_top, zero_add] at hpos
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
      by_cases hk' : 𝔮 k ≤ 𝔭
      · exact ⟨k, hkey 𝔭 h𝔭 hne hn k hk'⟩
      · exact absurd (Ideal.localLength_of_not_le hk') hk
  · simp only [mem_filter, mem_image, mem_univ, true_and] at h𝔭
    obtain ⟨⟨k, rfl⟩, hne, hn⟩ := h𝔭
    exact hlen _ (h𝔮 k).2.1 hne hn
  · rw [hcoeff α hα, Finset.sum_comp (f := fun 𝔭 ↦ (hilbertPoly b 𝔭).coeff α) (g := 𝔮),
      Finset.sum_filter_of_ne]
    · exact sum_congr rfl fun 𝔭 _ ↦ nsmul_eq_mul _ _
    · intro 𝔭 h𝔭 h0
      obtain ⟨k, -, rfl⟩ := mem_image.mp h𝔭
      refine ⟨fun h ↦ h0 (by simp [h]), ?_⟩
      by_contra hn
      exact h0 (by rw [coeff_eq_zero_of_totalDegree_lt_degree
        ((lt_of_le_of_ne (hdeg k) hn).trans_le hα), mul_zero])

/-- **The associativity formula for degrees.** In every degree `|α| ≥ deg H_I`,
`d_α(I) = ∑_{𝔭 ∈ P} ℓ(K[X]_𝔭 / I_𝔭) · d_α(𝔭)`, the sum over the multihomogeneous primes
`𝔭 ⊇ I` of maximal dimension. -/
theorem multidegree_eq_sum_localLength [Finite σ] [Fintype ι] (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (P : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧ I ≤ 𝔭 ∧
        hilbertPoly b 𝔭 ≠ 0 ∧ (hilbertPoly b 𝔭).totalDegree = (hilbertPoly b I).totalDegree) ∧
      (∀ 𝔭 ∈ P, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 I = ℓ 𝔭) ∧
      ∀ α : ι →₀ ℕ, (hilbertPoly b I).totalDegree ≤ α.degree →
        multidegree b I α = ∑ 𝔭 ∈ P, (ℓ 𝔭 : ℚ) * multidegree b 𝔭 α := by
  obtain ⟨P, ℓ, hP, hℓ, h⟩ := coeff_hilbertPoly_eq_sum_localLength hb hI
  refine ⟨P, ℓ, hP, hℓ, fun α hα ↦ ?_⟩
  rw [multidegree, h α hα, Finset.mul_sum]
  refine sum_congr rfl fun 𝔭 _ ↦ ?_
  rw [multidegree]
  ring

end Graded

end MvPolynomial
