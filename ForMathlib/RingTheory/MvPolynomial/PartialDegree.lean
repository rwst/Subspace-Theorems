/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Projection
public import ForMathlib.RingTheory.MvPolynomial.ProductStructure

/-!
# Partial degrees of the Hilbert polynomial of a prime

Let `𝔭` be a multihomogeneous prime of `B = K[X_s : s ∈ σ]`, the variables in blocks `b : σ → ι`,
with `H_𝔭 ≠ 0`. For a set `J` of blocks, let `r_J` be the rank of the variables of the blocks `J`
modulo `𝔭`, that is the transcendence degree of `K[x_s : b s ∈ J]`, `x_s = X_s mod 𝔭`
(`MvPolynomial.blockRank`, a rank in the algebraic matroid `MvPolynomial.varMatroid`). Then
`e_J(B/𝔭) = r_J - |J|` is the partial degree of the Hilbert polynomial `H_𝔭` in `(T_i)_{i ∈ J}`,
and for `J ⊆ J₁` one monomial of `H_𝔭` of top degree attains both `e_J` and `e_{J₁}` (G. Rémond,
*Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.), *Introduction to algebraic
independence theory*, LNM 1752 (2001), Thm 2.10(1), (3) for primes; Lemma 2.7).

The proofs use the cone decomposition of the standard monomials
(`MvPolynomial.exists_hilbertPoly_eq_sum_conePoly_lex`). The monomials of a cone polynomial lie
below its type, and the free variables of a cone are independent modulo `𝔭`, which gives the upper
bound. For the lower bound, take nested bases `I ⊆ I₁ ⊆ T` of the variables of `J`, of `J₁`, and
of all variables; `T` is a transcendence basis meeting every block, and its type is a monomial of
`H_𝔭` with nonzero coefficient (`MvPolynomial.totalDegree_hilbertPoly_eq_and_one_le_multidegree`).

## Main statements

* `MvPolynomial.le_coneType_of_coeff_conePoly_ne_zero`: the monomials of a cone polynomial lie
  below its type.
* `MvPolynomial.blockRank_mono`, `MvPolynomial.blockRank_inter_add_blockRank_union_le`:
  `J ↦ r_J` is monotone and submodular (Lemma 2.7).
* `MvPolynomial.sum_add_card_le_blockRank`: `∑_{i ∈ J} α_i ≤ r_J - |J|` for every monomial `T^α`
  of `H_𝔭`.
* `MvPolynomial.exists_coeff_hilbertPoly_ne_zero_blockRank`: a monomial of `H_𝔭` of top degree
  with `∑_{i ∈ J} α_i = r_J - |J|` and `∑_{i ∈ J₁} α_i = r_{J₁} - |J₁|`.
* `MvPolynomial.card_le_blockRank`: `|J| ≤ r_J`.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι K : Type*} [DecidableEq ι]

section DegreeOf

variable {R : Type*} [CommSemiring R]

/-- A substitution `X_j ↦ f_j` with `deg_{X_i} f_j ≤ [i = j]` does not raise the degree in
`X_i`. -/
theorem degreeOf_aeval_le {f : ι → MvPolynomial ι R} {i : ι}
    (hf : ∀ j, degreeOf i (f j) ≤ if i = j then 1 else 0) (P : MvPolynomial ι R) :
    degreeOf i (aeval f P) ≤ degreeOf i P := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β hβ ↦ ?_)
  rw [aeval_monomial, Finsupp.prod]
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [algebraMap_eq, degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  refine le_trans ?_ (monomial_le_degreeOf i hβ)
  calc ∑ j ∈ β.support, degreeOf i (f j ^ β j)
      ≤ ∑ j ∈ β.support, β j * (if i = j then 1 else 0) :=
        Finset.sum_le_sum fun j _ ↦ (degreeOf_pow_le _ _ _).trans
          (Nat.mul_le_mul_left _ (hf j))
    _ ≤ β i := by
        rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [Ne.symm hji])
          (fun h ↦ by simp [Finsupp.notMem_support_iff.mp h])]
        simp

end DegreeOf

omit [DecidableEq ι] in
theorem degreeOf_shiftPoly_le (a : ι → ℕ) (P : MvPolynomial ι ℚ) (i : ι) :
    degreeOf i (shiftPoly a P) ≤ degreeOf i P := by
  classical
  refine degreeOf_aeval_le (fun j ↦ ?_) P
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ (by rw [degreeOf_C]; exact Nat.zero_le _))
  by_cases hij : i = j
  · subst hij
    simp
  · simp [degreeOf_X_of_ne hij]

theorem degreeOf_binomPoly_le (n : ℕ) (j i : ι) :
    degreeOf i (binomPoly n j) ≤ if i = j then n else 0 := by
  rw [binomPoly]
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add, Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k hk ↦ ?_)
  rw [Finset.mem_range, ascPochhammer_natDegree] at hk
  rw [smul_eq_C_mul]
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_pow_le _ _ _).trans ?_
  have h1 : degreeOf i (X j + 1 : MvPolynomial ι ℚ) ≤ if i = j then 1 else 0 := by
    refine (degreeOf_add_le _ _ _).trans (max_le ?_ (by simp))
    by_cases hij : i = j
    · subst hij
      simp
    · simp [degreeOf_X_of_ne hij, hij]
  split_ifs at h1 ⊢ with hij
  · exact (Nat.mul_le_mul_left _ h1).trans (by omega)
  · simp [Nat.le_zero.mp h1]

section Cones

variable [Fintype ι]

/-- The monomials of a cone polynomial lie below its type. -/
theorem le_coneType_of_coeff_conePoly_ne_zero {b : σ → ι} {V : Finset σ} {w : ι → ℕ}
    {α : ι →₀ ℕ} (hα : (conePoly b V w).coeff α ≠ 0) (i : ι) : α i ≤ coneType b V i := by
  have h1 := monomial_le_degreeOf i (mem_support_iff.mpr hα)
  refine h1.trans ((degreeOf_shiftPoly_le _ _ i).trans ((degreeOf_prod_le _ _ _).trans ?_))
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by
    have := degreeOf_binomPoly_le (#{s ∈ V | b s = j} - 1) j i
    simpa [Ne.symm hji] using this) (by simp)]
  have := degreeOf_binomPoly_le (#{s ∈ V | b s = i} - 1) i i
  simpa [coneType] using this

/-- For `V` meeting every block, `∑_{i ∈ J} (|V ∩ block i| - 1) + |J| = |V ∩ blocks J|`. -/
theorem sum_coneType_add_card (b : σ → ι) {V : Finset σ}
    (hV : ∀ i, ∃ s ∈ V, b s = i) (J : Finset ι) :
    ∑ i ∈ J, coneType b V i + #J = #{s ∈ V | b s ∈ J} := by
  rw [Finset.card_eq_sum_card_fiberwise (s := {s ∈ V | b s ∈ J}) (f := b) (t := J)
      fun s hs ↦ (mem_filter.mp hs).2,
    Finset.card_eq_sum_ones J, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hfib : {s ∈ {s ∈ V | b s ∈ J} | b s = i} = {s ∈ V | b s = i} := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun s _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hi, h⟩⟩
  obtain ⟨s, hs, hsi⟩ := hV i
  have : 0 < #{s ∈ V | b s = i} := Finset.card_pos.mpr ⟨s, by simp [hs, hsi]⟩
  rw [hfib]
  simp only [coneType, Finsupp.equivFunOnFinite_symm_apply_apply]
  omega


end Cones

section Rank

variable [Field K]

/-- The rank of the variables of the blocks `J` modulo `𝔭`, that is the transcendence degree of
`K[x_s : b s ∈ J]`, `x_s = X_s mod 𝔭`. It is `ht 𝔭_J + n_J + |J| - ht 𝔭_J` in Rémond's
notation, so Rémond's `e_J(B/𝔭) = n_J - ht 𝔭_J` is `blockRank 𝔭 b J - |J|`. -/
noncomputable def blockRank (𝔭 : Ideal (MvPolynomial σ K)) [𝔭.IsPrime] (b : σ → ι)
    (J : Set ι) : ℕ :=
  ((varMatroid 𝔭).eRk (b ⁻¹' J)).toNat

omit [DecidableEq ι]

variable [Finite σ] {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]

theorem cast_blockRank (b : σ → ι) (J : Set ι) :
    (blockRank 𝔭 b J : ℕ∞) = (varMatroid 𝔭).eRk (b ⁻¹' J) :=
  ENat.natCast_toNat (((varMatroid 𝔭).eRk_le_encard _).trans_lt
    (Set.toFinite _).encard_lt_top).ne

theorem card_le_blockRank_of_algebraicIndepOn {b : σ → ι} {J : Set ι} {W : Finset σ}
    (hW : AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk 𝔭 (X s)) (W : Set σ))
    (hWJ : ∀ s ∈ W, b s ∈ J) : #W ≤ blockRank 𝔭 b J := by
  have h := (varMatroid_indep_iff.mpr hW).encard_le_eRk_of_subset (X := b ⁻¹' J)
    fun s hs ↦ hWJ s hs
  rw [← cast_blockRank, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

omit [Finite σ] in
/-- Variables independent modulo `𝔭` over which every variable is algebraic form a transcendence
basis of `B/𝔭`. -/
theorem isTranscendenceBasis_of_forall_isAlgebraic {T : Set σ}
    (hT : AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk 𝔭 (X s)) T)
    (halg : ∀ s, IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' T))
      (Ideal.Quotient.mk 𝔭 (X s))) :
    IsTranscendenceBasis K (fun t : T ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) := by
  set x : σ → MvPolynomial σ K ⧸ 𝔭 := fun t ↦ Ideal.Quotient.mk 𝔭 (X t)
  have : Nontrivial (MvPolynomial σ K ⧸ 𝔭) := hT.algebraMap_injective.nontrivial
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨hT, ?_⟩
  change Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun t : T ↦ x t)) _
  rw [← Set.image_eq_range]
  constructor
  intro a
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (s := Set.range x)
    (fun _ ⟨⟨s, hs⟩, _⟩ ↦ hs ▸ halg s) ?_
  have hP : Ideal.Quotient.mk 𝔭 P = aeval x P :=
    congrArg (· P) (MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ K 𝔭))
  have hmem : Ideal.Quotient.mk 𝔭 P ∈ Algebra.adjoin K (Set.range x) := by
    rw [hP, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨P, rfl⟩
  exact isAlgebraic_algebraMap (⟨_, hmem⟩ : Algebra.adjoin K (Set.range x))

/-- `J ↦ blockRank 𝔭 b J` is monotone (Rémond, LNM 1752, Ch. 5, Lemma 2.7, first
inequality). -/
theorem blockRank_mono (b : σ → ι) {J J' : Set ι} (h : J ⊆ J') :
    blockRank 𝔭 b J ≤ blockRank 𝔭 b J' := by
  have := (varMatroid 𝔭).eRk_mono (Set.preimage_mono (f := b) h)
  rw [← cast_blockRank, ← cast_blockRank] at this
  exact_mod_cast this

/-- `J ↦ blockRank 𝔭 b J` is submodular (Rémond, LNM 1752, Ch. 5, Lemma 2.7, second
inequality). -/
theorem blockRank_inter_add_blockRank_union_le (b : σ → ι) (J J' : Set ι) :
    blockRank 𝔭 b (J ∩ J') + blockRank 𝔭 b (J ∪ J') ≤ blockRank 𝔭 b J + blockRank 𝔭 b J' := by
  have := (varMatroid 𝔭).eRk_inter_add_eRk_union_le (b ⁻¹' J) (b ⁻¹' J')
  rw [← Set.preimage_inter, ← Set.preimage_union, ← cast_blockRank, ← cast_blockRank,
    ← cast_blockRank, ← cast_blockRank] at this
  exact_mod_cast this

variable [Finite ι] [DecidableEq ι]

/-- **The partial degrees of `H_𝔭` are at most the `e_J`** (Rémond, LNM 1752, Ch. 5,
Thm 2.10(1), upper bound for primes). For every monomial `T^α` of `H_𝔭` and every set of blocks
`J`, `∑_{i ∈ J} α_i ≤ e_J(B/𝔭) = blockRank 𝔭 b J - |J|`. The monomials of a cone polynomial lie
below its type, and the free variables of a cone of standard monomials are independent
modulo `𝔭`. -/
theorem sum_add_card_le_blockRank {b : σ → ι} (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) {α : ι →₀ ℕ}
    (hα : (hilbertPoly b 𝔭).coeff α ≠ 0) (J : Finset ι) :
    ∑ i ∈ J, α i + #J ≤ blockRank 𝔭 b J := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  obtain ⟨A, V, hVb, hVstd, -, hH⟩ := exists_hilbertPoly_eq_sum_conePoly_lex hb h𝔭
  rw [hH, coeff_sum] at hα
  obtain ⟨a, ha, hαa⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have hind : AlgebraicIndepOn K (fun s ↦ Ideal.Quotient.mk 𝔭 (X s)) (V a : Set σ) :=
    (algebraicIndepOn_iff 𝔭 _).mpr fun f hf hfI ↦
      eq_zero_of_forall_add_notMem_leadingMonomials (hVstd a ha) hf hfI
  have hle := card_le_blockRank_of_algebraicIndepOn
    (hind.mono (Finset.coe_subset.mpr (Finset.filter_subset (fun s ↦ b s ∈ J) (V a))))
    (J := (J : Set ι)) fun s hs ↦ (mem_filter.mp hs).2
  rw [← sum_coneType_add_card b (hVb a ha)] at hle
  refine le_trans ?_ hle
  gcongr with i
  exact le_coneType_of_coeff_conePoly_ne_zero hαa i

/-- **A monomial of `H_𝔭` with the partial degrees `e_J`, `e_{J₁}`** (Rémond, LNM 1752, Ch. 5,
Thm 2.10(3) for primes). For `J ⊆ J₁` there is a monomial `T^α` of `H_𝔭` of total degree
`deg H_𝔭` with `∑_{i ∈ J} α_i = e_J(B/𝔭)` and `∑_{i ∈ J₁} α_i = e_{J₁}(B/𝔭)`. Take nested bases
`I ⊆ I₁ ⊆ T` of the variables of `J`, of `J₁`, and of all variables in the algebraic matroid; `T`
meets every block and `α` is its type. With the upper bound, `e_J(B/𝔭)` is the partial degree of
`H_𝔭` in `(T_i)_{i ∈ J}`. -/
theorem exists_coeff_hilbertPoly_ne_zero_blockRank {b : σ → ι} (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0)
    {J J₁ : Finset ι} (hJ : J ⊆ J₁) :
    ∃ α : ι →₀ ℕ, (hilbertPoly b 𝔭).coeff α ≠ 0 ∧
      α.degree = (hilbertPoly b 𝔭).totalDegree ∧
      ∑ i ∈ J, α i + #J = blockRank 𝔭 b J ∧ ∑ i ∈ J₁, α i + #J₁ = blockRank 𝔭 b J₁ := by
  classical
  have := Fintype.ofFinite ι
  set M := varMatroid 𝔭
  set x : σ → MvPolynomial σ K ⧸ 𝔭 := fun t ↦ Ideal.Quotient.mk 𝔭 (X t)
  have hE : ∀ S : Set σ, S ⊆ M.E := fun S ↦ by simp [M, varMatroid]
  obtain ⟨I, hI⟩ := M.exists_isBasis (b ⁻¹' J) (hE _)
  obtain ⟨I₁, hI₁, hII₁⟩ := hI.indep.subset_isBasis_of_subset
    (hI.subset.trans (Set.preimage_mono (Finset.coe_subset.mpr hJ))) (hE _)
  obtain ⟨B, hB, hI₁B⟩ := hI₁.indep.exists_isBase_superset
  obtain ⟨T, rfl⟩ : ∃ T : Finset σ, (T : Set σ) = B := ⟨(Set.toFinite B).toFinset, by simp⟩
  have hindT : AlgebraicIndepOn K x (T : Set σ) := varMatroid_indep_iff.mp hB.indep
  have halg : ∀ s, IsAlgebraic (Algebra.adjoin K (x '' T)) (x s) := by
    intro s
    by_contra h
    by_cases hs : s ∈ T
    · exact h (isAlgebraic_algebraMap
        (⟨x s, Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : Algebra.adjoin K (x '' T)))
    · have := hB.eq_of_subset_indep (varMatroid_indep_iff.mpr (hindT.insert h))
        (Set.subset_insert _ _)
      exact hs (Finset.mem_coe.mp (this ▸ Set.mem_insert s _))
  have hTB := isTranscendenceBasis_of_forall_isAlgebraic hindT halg
  have hTb := forall_exists_mem_of_isAlgebraic hb h𝔭 hne (W := fun _ ↦ (T : Set σ))
    (fun _ ↦ subset_rfl) fun s _ ↦ halg s
  obtain ⟨htot, hmult⟩ := totalDegree_hilbertPoly_eq_and_one_le_multidegree hb h𝔭 hTB hTb
  -- The blocks `J` meet `T` in the basis `I`.
  have hrank : ∀ {J : Finset ι} {I : Set σ}, M.IsBasis I (b ⁻¹' J) → I ⊆ T →
      ∑ i ∈ J, coneType b T i + #J = blockRank 𝔭 b J := by
    intro J I hI hIT
    have hIT' := hI.inter_eq_of_subset_indep hIT hB.indep
    have h := cast_blockRank (𝔭 := 𝔭) b J
    have hfil : (T : Set σ) ∩ b ⁻¹' J = ↑({s ∈ T | b s ∈ J}) := by
      ext s
      simp
    rw [hI.eRk_eq_encard, ← hIT', hfil, Set.encard_coe_eq_coe_finsetCard] at h
    rw [sum_coneType_add_card b hTb]
    exact_mod_cast h.symm
  refine ⟨coneType b T, fun h ↦ ?_, htot.symm, hrank hI (hII₁.trans hI₁B), hrank hI₁ hI₁B⟩
  rw [multidegree, h, mul_zero] at hmult
  exact absurd hmult (by norm_num)

/-- If `H_𝔭 ≠ 0`, the variables of the blocks `J` have rank at least `|J|`, that is
`e_J(B/𝔭) ≥ 0` (Rémond, LNM 1752, Ch. 5, Lemma 2.7, last assertion). -/
theorem card_le_blockRank {b : σ → ι} (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0) (J : Finset ι) :
    #J ≤ blockRank 𝔭 b J := by
  obtain ⟨α, -, -, h, -⟩ := exists_coeff_hilbertPoly_ne_zero_blockRank hb h𝔭 hne
    (subset_refl J)
  omega

end Rank

section Transfer

/-- If every closure in `M` lies in the closure in `N`, then for `S ⊆ S₁`
`r_N(S₁) - r_N(S) ≤ r_M(S₁) - r_M(S)`. -/
theorem _root_.Matroid.eRk_add_eRk_le_of_closure_subset {M N : Matroid σ}
    (hMN : ∀ U, M.closure U ⊆ N.closure U) (hE : M.E = Set.univ) {S S₁ : Set σ}
    (h : S ⊆ S₁) : N.eRk S₁ + M.eRk S ≤ N.eRk S + M.eRk S₁ := by
  obtain ⟨B, hB⟩ := M.exists_isBasis S (hE ▸ Set.subset_univ S)
  obtain ⟨B₁, hB₁, hBB₁⟩ := hB.indep.subset_isBasis_of_subset (hB.subset.trans h)
    (hE ▸ Set.subset_univ S₁)
  have h1 : N.eRk S₁ ≤ N.eRk S + (B₁ \ B).encard := by
    have hS₁ : S₁ ⊆ N.closure B₁ := fun s hs ↦ hMN B₁ (hB₁.subset_closure hs)
    calc N.eRk S₁ ≤ N.eRk (N.closure B₁) := N.eRk_mono hS₁
      _ = N.eRk B₁ := N.eRk_closure_eq B₁
      _ ≤ N.eRk (S ∪ (B₁ \ B)) := N.eRk_mono fun t ht ↦ by
          by_cases htB : t ∈ B
          · exact Or.inl (hB.subset htB)
          · exact Or.inr ⟨ht, htB⟩
      _ ≤ N.eRk S + (B₁ \ B).encard := N.eRk_union_le_eRk_add_encard S _
  have h2 : M.eRk S₁ = (B₁ \ B).encard + M.eRk S := by
    rw [← hB₁.encard_eq_eRk, ← hB.encard_eq_eRk, Set.encard_sdiff_add_encard_of_subset hBB₁]
  rw [h2]
  calc N.eRk S₁ + M.eRk S ≤ N.eRk S + (B₁ \ B).encard + M.eRk S := add_le_add_left h1 _
    _ = N.eRk S + ((B₁ \ B).encard + M.eRk S) := add_assoc _ _ _

variable {K L : Type*} [Field K] [Field L]

theorem mem_closure_varMatroid_iff {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] {U : Set σ}
    {s : σ} : s ∈ (varMatroid 𝔭).closure U ↔
      IsAlgebraic (Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' U))
        (Ideal.Quotient.mk 𝔭 (X s)) := by
  rw [varMatroid, Matroid.comap_closure_eq, Set.mem_preimage,
    AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure]

/-- **Algebraic relations transfer along an extension of primes**: if `𝔮 ∩ K[X] = 𝔭` for a
prime `𝔮` of `L[X]`, then every `x_s` algebraic over `K[x_T]` modulo `𝔭` is algebraic over
`L[y_T]` modulo `𝔮`. -/
theorem closure_varMatroid_subset (ρ : K →+* L) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    {q : Ideal (MvPolynomial σ L)} [q.IsPrime] (hq : q.comap (map ρ) = 𝔭) (U : Set σ) :
    (varMatroid 𝔭).closure U ⊆ (varMatroid q).closure U := by
  intro s hs
  rw [mem_closure_varMatroid_iff] at hs ⊢
  set φ : MvPolynomial σ K ⧸ 𝔭 →+* MvPolynomial σ L ⧸ q :=
    Ideal.Quotient.lift 𝔭 ((Ideal.Quotient.mk q).comp (map ρ)) fun a ha ↦ by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hq]
      exact ha
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.mem_comap, hq] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hφX : ∀ t, φ (Ideal.Quotient.mk 𝔭 (X t)) = Ideal.Quotient.mk q (X t) := fun t ↦ by
    simp [φ]
  set A := Algebra.adjoin K ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' U)
  set B := Algebra.adjoin L ((fun t ↦ Ideal.Quotient.mk q (X t)) '' U)
  obtain ⟨p, hp0, hp⟩ := hs
  have hmem : ∀ a ∈ A, φ a ∈ B := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨t, ht, (hφX t).symm⟩
    | algebraMap r =>
      have : φ (algebraMap K _ r) = algebraMap L _ (ρ r) := by
        change φ (Ideal.Quotient.mk 𝔭 (C r)) = Ideal.Quotient.mk q (C (ρ r))
        simp [φ]
      rw [this]
      exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  set ψ : A →+* B := (φ.comp A.val.toRingHom).codRestrict B.toSubsemiring fun a ↦ hmem a a.2
  have hψ : Function.Injective ψ := fun a b h ↦
    Subtype.ext (hφ (congrArg Subtype.val h))
  refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hφX s]
  have hcomp : (algebraMap B (MvPolynomial σ L ⧸ q)).comp ψ = φ.comp (algebraMap A _) := rfl
  rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]

variable [Finite σ]

omit [DecidableEq ι] in
/-- **Block ranks along an extension of primes**: if `𝔮 ∩ K[X] = 𝔭`, then for `J ⊆ J₁`,
`r_{J₁}(𝔮) - r_J(𝔮) ≤ r_{J₁}(𝔭) - r_J(𝔭)` (the last assertion of Rémond's Lemma 2.12). -/
theorem blockRank_add_blockRank_le (ρ : K →+* L) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    {q : Ideal (MvPolynomial σ L)} [q.IsPrime] (hq : q.comap (map ρ) = 𝔭) (b : σ → ι)
    {J J₁ : Set ι} (h : J ⊆ J₁) :
    blockRank q b J₁ + blockRank 𝔭 b J ≤ blockRank q b J + blockRank 𝔭 b J₁ := by
  have := Matroid.eRk_add_eRk_le_of_closure_subset (closure_varMatroid_subset ρ hq)
    (by simp [varMatroid]) (Set.preimage_mono (f := b) h)
  rw [← cast_blockRank, ← cast_blockRank, ← cast_blockRank, ← cast_blockRank] at this
  exact_mod_cast this

end Transfer

end MvPolynomial

end
