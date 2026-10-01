/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
public import ForMathlib.RingTheory.MvPolynomial.TransversalHeight
public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# The degree of a prime in the type of a transcendence basis

Let `𝔭` be a multihomogeneous prime of `B = K[X_s : s ∈ σ]`, the variables in blocks `b : σ → ι`,
and `(x_t)_{t ∈ T}` a transcendence basis of `B/𝔭` made of variables and meeting every block.
Then `deg H_𝔭 = |T| - |ι|` and the degree `d_β(𝔭)` of type `β_i = |T ∩ block i| - 1` is a positive
integer (`MvPolynomial.totalDegree_hilbertPoly_eq_and_one_le_multidegree`). This is the
nonvanishing of the degree in the type given by the projections (G. Rémond, *Élimination
multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.), *Introduction to algebraic independence
theory*, LNM 1752 (2001), Theorem 2.10(3)), which Rémond 2001 uses to divide by `d_β(𝔭)`.

The proof is a cone decomposition of the standard monomials of `𝔭`
(`MvPolynomial.exists_hilbertPoly_eq_sum_conePoly_lex`). For every lexicographic order, the free
variables `V` of a cone `a + ℕ^V` of standard monomials are algebraically independent modulo `𝔭`
(`X^a f` for `f ∈ 𝔭 ∩ K[X_V]` would have a standard leading monomial), so `|V| ≤ |T|` and every cone
has type of degree `≤ |T| - |ι|`. For the lexicographic order in which the variables outside `T`
come first, the monomials in `X_T` are standard (a polynomial whose leading monomial is in `X_T`
lies in `K[X_T]`), so `T` itself is the set of free variables of a cone. By
`MvPolynomial.totalDegree_eq_sup_of_eq_sum_conePoly`, `d_β(𝔭)` counts the cones of type `β`.

The adapted transcendence basis of `MvPolynomial.exists_transversal_fin` meets every block when
`H_𝔭 ≠ 0`. A variable `X_s ∉ 𝔭` of block `i` is transcendental over the variables of the other
blocks, by homogeneity in block `i` alone (`MvPolynomial.not_isAlgebraic_of_isWeightedHomogeneous`).

## Main statements

* `MvPolynomial.algebraicIndepOn_iff`: algebraic independence of variables modulo an ideal.
* `MvPolynomial.totalDegree_hilbertPoly_eq_and_one_le_multidegree`: `deg H_𝔭 = |T| - |ι|` and
  `d_β(𝔭) ≥ 1` for the type `β` of a transcendence basis meeting every block.
* `MvPolynomial.not_isAlgebraic_of_isWeightedHomogeneous`: `X_s ∉ 𝔭` stays transcendental over the
  variables of the other blocks.
* `MvPolynomial.exists_isTranscendenceBasis_adapted`: an adapted transcendence basis, for any
  ordering of the variables, meeting every block.
* `MvPolynomial.exists_transversal_fin_of_hilbertPoly_ne_zero`: the transversal equations of
  `MvPolynomial.exists_transversal_fin`, with a transcendence basis meeting every block.
* `MvPolynomial.totalDegree_hilbertPoly_add_height`: `deg H_𝔭 + ht 𝔭 + |ι| = |σ|`, and some degree
  of `𝔭` is at least `1`.
-/

@[expose] public section

open Finset
open scoped MonomialOrder

namespace MvPolynomial

variable {σ ι K : Type*} [Field K]

theorem _root_.Ideal.IsWeightedHomogeneous.comp {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    {w : σ → M} {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous w) (φ : M →+ N) :
    I.IsWeightedHomogeneous (φ ∘ w) := by
  classical
  intro p hp n
  have hw : ∀ c : σ →₀ ℕ, Finsupp.weight (φ ∘ w) c = φ (Finsupp.weight w c) := by
    intro c
    simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]
  have : weightedHomogeneousComponent (φ ∘ w) n p =
      ∑ d ∈ (p.support.image (Finsupp.weight w)).filter (φ · = n),
        weightedHomogeneousComponent w d p := by
    ext c
    rw [coeff_weightedHomogeneousComponent, coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq, hw]
    by_cases hc : p.coeff c = 0
    · simp [hc]
    · have : Finsupp.weight w c ∈ p.support.image (Finsupp.weight w) :=
        Finset.mem_image_of_mem _ (mem_support_iff.mpr hc)
      simp [this]
  rw [this]
  exact sum_mem fun d _ ↦ hI hp d

section Independent

theorem aeval_mk_X (I : Ideal (MvPolynomial σ K)) (V : Set σ) (f : MvPolynomial V K) :
    aeval (fun t : V ↦ Ideal.Quotient.mk I (X (t : σ))) f =
      Ideal.Quotient.mk I (rename Subtype.val f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp => simp [hp]

/-- **Algebraic independence of variables modulo an ideal**: no nonzero polynomial in them lies in
the ideal. -/
theorem algebraicIndepOn_iff (I : Ideal (MvPolynomial σ K)) (V : Set σ) :
    AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk I (X s)) V ↔
      ∀ f ∈ supported K V, f ∈ I → f = 0 := by
  rw [AlgebraicIndepOn, algebraicIndependent_iff]
  constructor
  · intro h f hf hfI
    rw [supported_eq_range_rename] at hf
    obtain ⟨g, rfl⟩ := hf
    have := h g (by rw [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]; exact hfI)
    rw [this, map_zero]
  · intro h g hg
    rw [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem] at hg
    have := h _ (by rw [supported_eq_range_rename]; exact ⟨g, rfl⟩) hg
    exact rename_injective _ Subtype.val_injective (by rw [this, map_zero])

variable [LinearOrder σ] [WellFoundedGT σ]

/-- The free variables of a cone of standard monomials are independent modulo the ideal. -/
theorem eq_zero_of_forall_add_notMem_leadingMonomials {I : Ideal (MvPolynomial σ K)}
    {a : σ →₀ ℕ} {V : Finset σ}
    (h : ∀ c : σ →₀ ℕ, c.support ⊆ V → a + c ∉ leadingMonomials MonomialOrder.lex I)
    {f : MvPolynomial σ K} (hf : f ∈ supported K (V : Set σ)) (hfI : f ∈ I) : f = 0 := by
  classical
  by_contra h0
  refine h (MonomialOrder.lex.degree f) (fun s hs ↦ ?_)
    (add_mem_leadingMonomials ⟨f, hfI, h0, rfl⟩ a)
  rw [mem_supported] at hf
  exact Finset.mem_coe.mp (hf ((mem_vars_iff_mem_support s).mpr
    ⟨_, MonomialOrder.degree_mem_support h0, hs⟩))

/-- For the lexicographic order in which the variables outside `T` come first, a polynomial
whose leading monomial is in the variables `T` is a polynomial in them. So if no nonzero
polynomial in `X_T` lies in `I`, the monomials in `X_T` are standard. -/
theorem notMem_leadingMonomials_lex {I : Ideal (MvPolynomial σ K)} {T : Finset σ}
    (hT : ∀ s ∈ T, ∀ t ∉ T, t < s) (hI : ∀ f ∈ supported K (T : Set σ), f ∈ I → f = 0)
    {c : σ →₀ ℕ} (hc : c.support ⊆ T) : c ∉ leadingMonomials MonomialOrder.lex I := by
  classical
  rintro ⟨f, hfI, hf0, rfl⟩
  refine hf0 (hI f ?_ hfI)
  rw [mem_supported]
  intro s hs
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hs
  obtain ⟨d, hd, hsd⟩ := hs
  by_contra hsT
  set S := d.support.filter (· ∉ T)
  have hS : S.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨hsd, hsT⟩⟩
  set u := S.min' hS
  obtain ⟨hud, huT⟩ := Finset.mem_filter.mp (S.min'_mem hS)
  have hzero : ∀ j, j ∉ T → (MonomialOrder.lex.degree f) j = 0 := fun j hj ↦
    Finsupp.notMem_support_iff.mp fun h ↦ hj (hc h)
  have hlt : MonomialOrder.lex.degree f ≺[MonomialOrder.lex] d := by
    rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
    refine ⟨u, fun j hj ↦ ?_, ?_⟩
    · have hjT : j ∉ T := fun h ↦ (hT j h u huT).not_gt hj
      change (MonomialOrder.lex.degree f) j = d j
      rw [hzero j hjT]
      by_contra hdj
      exact (S.min'_le j (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (Ne.symm hdj),
        hjT⟩)).not_gt hj
    · change (MonomialOrder.lex.degree f) u < d u
      rw [hzero u huT]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hud)
  exact (MonomialOrder.le_degree hd).not_gt hlt

end Independent

section Degree

variable [Fintype ι] [DecidableEq ι]

/-- For `V` meeting every block, the type of `V` has degree `|V| - |ι|`. -/
theorem degree_coneType_add_card (b : σ → ι) {V : Finset σ}
    (hV : ∀ i, ∃ s ∈ V, b s = i) : (coneType b V).degree + Fintype.card ι = #V := by
  classical
  have hdeg : (coneType b V).degree = ∑ i, (#{s ∈ V | b s = i} - 1) := by
    rw [Finsupp.degree_eq_sum]
    simp [coneType]
  rw [hdeg, Finset.card_eq_sum_card_fiberwise (f := b) (t := univ) fun _ _ ↦ mem_univ _,
    ← Finset.card_univ, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  obtain ⟨s, hs, hsi⟩ := hV i
  have : 0 < #{s ∈ V | b s = i} := Finset.card_pos.mpr ⟨s, by simp [hs, hsi]⟩
  omega

variable [Finite σ]

/-- **The degree in the type of a transcendence basis is positive** (Rémond, LNM 1752, Ch. 5,
Thm 2.10(3)). Let `(x_t)_{t ∈ T}` be a transcendence basis of `B/𝔭` made of variables and meeting
every block. Then `deg H_𝔭 = |T| - |ι|`, and `d_β(𝔭) ≥ 1` for `β_i = |T ∩ block i| - 1`. -/
theorem totalDegree_hilbertPoly_eq_and_one_le_multidegree {b : σ → ι}
    (hb : Function.Surjective b) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) {T : Finset σ}
    (hT : IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))))
    (hTb : ∀ i, ∃ s ∈ T, b s = i) :
    (hilbertPoly b 𝔭).totalDegree = (coneType b T).degree ∧
      1 ≤ multidegree b 𝔭 (coneType b T) := by
  classical
  have := Fintype.ofFinite σ
  -- The variables outside `T` come first.
  set e : σ → ℕ := fun s ↦ (if s ∈ T then Fintype.card σ else 0) + Fintype.equivFin σ s
  have he : Function.Injective e := by
    intro s t h
    have hs := (Fintype.equivFin σ s).2
    have ht := (Fintype.equivFin σ t).2
    simp only [e] at h
    refine (Fintype.equivFin σ).injective (Fin.ext ?_)
    split_ifs at h <;> omega
  let : LinearOrder σ := LinearOrder.lift' e he
  have hTord : ∀ s ∈ T, ∀ t ∉ T, t < s := by
    intro s hs t ht
    change e t < e s
    have := (Fintype.equivFin σ t).2
    simp only [e, hs, ht, ite_true, ite_false]
    omega
  obtain ⟨A, V, hVb, hVstd, hTcone, hH⟩ := exists_hilbertPoly_eq_sum_conePoly_lex hb h𝔭
  obtain ⟨htot, hcoeff⟩ := totalDegree_eq_sup_of_eq_sum_conePoly hH
  have hindep : ∀ W : Finset σ, AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk 𝔭 (X s))
      (W : Set σ) → #W ≤ #T := by
    intro W hW
    have h2 := AlgebraicIndependent.lift_cardinalMk_le_trdeg hW
    rw [← hT.lift_cardinalMk_eq_trdeg, Cardinal.lift_le, Finset.coe_sort_coe,
      Finset.coe_sort_coe, Cardinal.mk_coe_finset, Cardinal.mk_coe_finset] at h2
    exact_mod_cast h2
  obtain ⟨aT, haT, hVT⟩ := hTcone T hTb fun c hc ↦ notMem_leadingMonomials_lex hTord
    ((algebraicIndepOn_iff 𝔭 _).mp hT.1) hc
  have hsup : A.sup (fun a ↦ (coneType b (V a)).degree) = (coneType b T).degree := by
    refine le_antisymm (Finset.sup_le fun a ha ↦ ?_) (hVT ▸ Finset.le_sup (f := fun a ↦
      (coneType b (V a)).degree) haT)
    have h1 := degree_coneType_add_card b (hVb a ha)
    have h2 := degree_coneType_add_card b hTb
    have h3 := hindep (V a) ((algebraicIndepOn_iff 𝔭 _).mpr fun f hf hfI ↦
      eq_zero_of_forall_add_notMem_leadingMonomials (hVstd a ha) hf hfI)
    omega
  refine ⟨htot.trans hsup, ?_⟩
  rw [multidegree, mul_comm, hcoeff _ (by rw [htot, hsup])]
  exact_mod_cast Finset.card_pos.mpr ⟨aT, Finset.mem_filter.mpr ⟨haT, by rw [hVT]⟩⟩

omit [Fintype ι] in
/-- If `H_I ≠ 0`, every block has a variable outside `I`. -/
theorem exists_X_notMem_of_hilbertPoly_ne_zero [Finite ι] {b : σ → ι} (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b I ≠ 0) (i : ι) : ∃ s, b s = i ∧ X s ∉ I := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  obtain ⟨A, V, hVb, hVstd, -, hH⟩ := exists_hilbertPoly_eq_sum_conePoly_lex hb hI
  obtain ⟨a, ha⟩ : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hne (by rw [hH, h, Finset.sum_empty])
  obtain ⟨s, hs, hsi⟩ := hVb a ha i
  refine ⟨s, hsi, fun hX ↦ X_ne_zero (R := K) s ?_⟩
  exact eq_zero_of_forall_add_notMem_leadingMonomials (hVstd a ha)
    (X_mem_supported.mpr (Finset.mem_coe.mpr hs)) hX

end Degree

section Blocks

variable [DecidableEq ι]

/-- **A variable stays transcendental over the other blocks.** If `𝔭` is a multihomogeneous prime
and `X_s ∉ 𝔭`, then `X_s mod 𝔭` is transcendental over the variables `X_t mod 𝔭` of the blocks
other than that of `s`. A relation `∑_k c_k x_s^k = 0` lifts to `∑_k C_k X_s^k ∈ 𝔭` with the
`C_k` of degree `0` in the block of `s`; by homogeneity in that block every `C_k X_s^k` is in `𝔭`,
so every `C_k` is. -/
theorem not_isAlgebraic_of_isWeightedHomogeneous {b : σ → ι} {𝔭 : Ideal (MvPolynomial σ K)}
    [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) {s : σ} (hs : X s ∉ 𝔭)
    {W : Set σ} (hW : ∀ t ∈ W, b t ≠ b s) :
    ¬IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' W))
      (Ideal.Quotient.mk 𝔭 (X s)) := by
  classical
  rintro ⟨p, hp0, hp⟩
  set w : σ → ℕ := Pi.evalAddMonoidHom (fun _ : ι ↦ ℕ) (b s) ∘ multiWeight b
  have hw : 𝔭.IsWeightedHomogeneous w := h𝔭.comp _
  have hws : w s = 1 := by simp [w, multiWeight]
  have hwW : ∀ t ∈ W, w t = 0 := fun t ht ↦ by
    simp [w, multiWeight, hW t ht]
  choose g hg using adjoinLift_surjective 𝔭 W
  set C : ℕ → MvPolynomial σ K := fun k ↦ rename Subtype.val (g (p.coeff k))
  have hC : ∀ k, Ideal.Quotient.mk 𝔭 (C k) = (p.coeff k : MvPolynomial σ K ⧸ 𝔭) := by
    intro k
    rw [← coe_adjoinLift, hg]
  have hCw : ∀ k, IsWeightedHomogeneous w (C k) 0 := by
    intro k c hc
    have hsupp : ∀ t ∈ c.support, t ∈ W := by
      intro t ht
      have : t ∈ (C k).vars := (mem_vars_iff_mem_support t).mpr ⟨c, mem_support_iff.mpr hc, ht⟩
      have := vars_rename (σ := W) Subtype.val (g (p.coeff k)) this
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp this
      exact u.2
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun t ht ↦ by rw [hwW t (hsupp t ht), smul_zero]
  have hterm : ∀ k, IsWeightedHomogeneous w (C k * X s ^ k) k := by
    intro k
    have := (hCw k).mul ((isWeightedHomogeneous_X K w s).pow k)
    rwa [hws, smul_eq_mul, mul_one, zero_add] at this
  set F := ∑ k ∈ p.support, C k * X s ^ k
  have hF : F ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    simp only [map_mul, map_pow, hC]
    rw [← hp, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _)]
    rw [Finset.sum_subset (Polynomial.supp_subset_range_natDegree_succ) fun k _ hk ↦ by
      rw [Polynomial.notMem_support_iff.mp hk]; simp]
    simp [Algebra.smul_def]
  obtain ⟨k, hk⟩ := Polynomial.nonempty_support_iff.mpr hp0
  have hcomp : weightedHomogeneousComponent w k F = C k * X s ^ k := by
    rw [map_sum, Finset.sum_eq_single k (fun j _ hjk ↦
      (hterm j).weightedHomogeneousComponent_ne _ (Ne.symm hjk)) (fun h ↦ absurd hk h)]
    exact (hterm k).weightedHomogeneousComponent_same
  have hmem := hw hF k
  rw [hcomp] at hmem
  have hCk : C k ∈ 𝔭 := (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_right
    fun h ↦ hs (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  have : (p.coeff k : MvPolynomial σ K ⧸ 𝔭) = 0 := by
    rw [← hC, Ideal.Quotient.eq_zero_iff_mem]
    exact hCk
  exact Polynomial.mem_support_iff.mp hk (Subtype.ext this)

variable [Finite ι] [Finite σ]

/-- **An adapted transcendence basis meets every block.** If `H_𝔭 ≠ 0` and every `x_s`, `s ∉ T`,
is algebraic over some of the `x_t`, `t ∈ T`, then `T` meets every block: a block missed by `T`
has a variable `X_s ∉ 𝔭`, transcendental over the other blocks. -/
theorem forall_exists_mem_of_isAlgebraic {b : σ → ι} (hb : Function.Surjective b)
    {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) {T : Finset σ} {W : σ → Set σ} (hW : ∀ s, W s ⊆ T)
    (halg : ∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
      ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' W s)) (Ideal.Quotient.mk 𝔭 (X s))) (i : ι) :
    ∃ s ∈ T, b s = i := by
  by_contra h
  push Not at h
  obtain ⟨s, hsi, hs⟩ := exists_X_notMem_of_hilbertPoly_ne_zero hb h𝔭 hne i
  have hsT : s ∉ T := fun h' ↦ h s h' hsi
  exact not_isAlgebraic_of_isWeightedHomogeneous h𝔭 hs
    (fun u hu ↦ hsi ▸ h u (hW s hu)) (halg s hsT)

/-- **An adapted transcendence basis meeting every block**, for any ordering `g` of the
variables: each `x_s`, `s ∉ T`, is algebraic over the `x_t`, `t ∈ T`, with `g t ≥ g s`. -/
theorem exists_isTranscendenceBasis_adapted {κ : Type*} [LinearOrder κ] (g : σ → κ)
    {b : σ → ι} (hb : Function.Surjective b) (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0) :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ g s ≤ g t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      ∀ i, ∃ s ∈ T, b s = i := by
  obtain ⟨T, hB, halg⟩ := exists_isTranscendenceBasis_isAlgebraic g 𝔭
  exact ⟨T, hB, halg, forall_exists_mem_of_isAlgebraic hb h𝔭 hne (fun _ _ h ↦ h.1) halg⟩

variable [CharZero K]

/-- **Transversal equations with a transcendence basis meeting every block.** The data of
`MvPolynomial.exists_transversal_fin`, where moreover `T` meets every block if `H_𝔭 ≠ 0`, and
`t + |T| = |σ|`. -/
theorem exists_transversal_fin_of_hilbertPoly_ne_zero [LinearOrder ι] {b : σ → ι}
    (hb : Function.Surjective b) (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime]
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ}
    (ht : 𝔭.height = t) :
    ∃ T : Finset σ,
      IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
        ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
          (Ideal.Quotient.mk 𝔭 (X s))) ∧
      (∀ i, ∃ s ∈ T, b s = i) ∧ t + #T = Nat.card σ ∧
      ∃ v : Fin t → σ, Function.Injective v ∧ Set.range v = (T : Set σ)ᶜ ∧
      ∃ Q : Fin t → MvPolynomial σ K, (∀ α, Q α ∈ 𝔭) ∧
        (∀ α β, α ≠ β → pderiv (v α) (Q β) ∈ 𝔭) ∧ ∀ α, pderiv (v α) (Q α) ∉ 𝔭 := by
  obtain ⟨T, hB, hadapt, v, hv, hrange, hQ⟩ := exists_transversal_fin b 𝔭 ht
  refine ⟨T, hB, hadapt, forall_exists_mem_of_isAlgebraic hb h𝔭 hne (fun _ _ h ↦ h.1) hadapt,
    ?_, v, hv, hrange, hQ⟩
  · have h1 := Set.ncard_range_of_injective hv
    rw [hrange, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rw [← h1, ← Set.ncard_coe_finset, add_comm, Set.ncard_add_ncard_compl]

/-- **The dimension of a multihomogeneous prime** in characteristic `0`: if `H_𝔭 ≠ 0` and `𝔭` has
height `t`, then `deg H_𝔭 + t + |ι| = |σ|`, and some degree `d_β(𝔭)` with `|β| = deg H_𝔭` is at
least `1`. -/
theorem totalDegree_hilbertPoly_add_height [Fintype ι] {b : σ → ι} (hb : Function.Surjective b)
    (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t) :
    (hilbertPoly b 𝔭).totalDegree + t + Fintype.card ι = Nat.card σ ∧
      ∃ β : ι →₀ ℕ, β.degree = (hilbertPoly b 𝔭).totalDegree ∧ 1 ≤ multidegree b 𝔭 β := by
  classical
  have := Fintype.ofFinite σ
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨T, hT, -, hTb, hcard, -⟩ := exists_transversal_fin_of_hilbertPoly_ne_zero hb 𝔭 h𝔭 hne ht
  obtain ⟨hdeg, hone⟩ := totalDegree_hilbertPoly_eq_and_one_le_multidegree hb h𝔭 hT hTb
  have h1 := degree_coneType_add_card b hTb
  exact ⟨by omega, coneType b T, hdeg.symm, hone⟩

end Blocks

end MvPolynomial
