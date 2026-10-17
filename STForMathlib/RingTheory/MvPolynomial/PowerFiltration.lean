/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import STForMathlib.RingTheory.MvPolynomial.CompleteIntersection
public import STForMathlib.RingTheory.MvPolynomial.DehomogenizeIdeal
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.MvPolynomial.Basic

-- Used only inside proofs.
import STForMathlib.LinearAlgebra.AdaptedBasis
import STForMathlib.RingTheory.MvPolynomial.HomogeneousRegular
import STForMathlib.RingTheory.MvPolynomial.LexCancellation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The filtration by powers of `γ`

Let `I = (G₁, …, G_b) ⊆ k[X_s | s ∈ σ]`, `V_N^* = V_N / (I ∩ V_N)` the polynomials of degree `≤ N`
modulo `I` (`MvPolynomial.quotDegLE`), and `γ₁, …, γ_t` of degree `≤ δ`. For `e ∈ ℕ^t` with
`δ σ(e) ≤ N`, `σ(e) = ∑ e_j`, put `S_e = γ^e V^*_{N - δ σ(e)}` (`MvPolynomial.powPiece`), and,
lexicographically, `W_{> i} = ∑_{e > i} S_e` (`MvPolynomial.powFiltrationGT`). This is the
filtration of Corvaja–Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), §3:
`W_{(i)} = S_i + W_{> i}`, and `W_{> i}` is the next space `W_{(i')}`.

If the homogenizations `G^h` and `γ^h = homogenize δ γ` satisfy: `X₀` regular modulo `(G^h)`
and `γ^h` regular modulo `(G^h)`, then (Lemma 3.1, in dimensions)
`dim W_{(i)} - dim W_{> i} = dim (k[X₀, X] / (G^h, γ^h))_{N - δ σ(i)}`
(`MvPolynomial.finrank_powPiece_sup_eq`): `q ↦ γ^i q(1, X)` maps the forms of degree
`N - δ σ(i)` onto `S_i`, and `γ^i q(1, X) ∈ W_{> i}` exactly when `q ∈ (G^h, γ^h)`. One direction
is Lemma 2.4 (the degrees fit), homogenization and Lemma 2.2; the other is the expansion of
`q ∈ (G^h, γ^h)` in degree `N - δ σ(i)`.

When `(G^h, γ^h)` has height `|σ|` (a complete intersection of dimension `0` in `ℙ^{|σ|}`) and
`(G^h, X₀)` has height `b + 1`, Lemma 2.3 bounds this by `E δ^t`, `E = ∏ deg G_l`, with equality
when `N - δ σ(i) ≥ N₀ = t (δ - 1) + ∑ (deg G_l - 1)` (Lemma 3.2). The basis of `V_N^*` adapted
to the filtration (`MvPolynomial.exists_adapted_basis`) then consists of classes
`γ^{ℓ(x)} q_x`, `deg q_x ≤ N - δ σ(ℓ(x))`, with at most `E δ^t` of each exponent, and exactly
`E δ^t` for `δ σ(i) + N₀ ≤ N`.

## Main statements

* `MvPolynomial.finrank_powPiece_sup_eq`: Corvaja–Zannier 2004, Lemma 3.1, in dimensions.
* `MvPolynomial.finrank_powPiece_sup_le`, `MvPolynomial.finrank_powPiece_sup_eq_of_le`:
  Lemma 3.2.
* `MvPolynomial.exists_adapted_basis`: the adapted basis of `V_N^*`, and
  `MvPolynomial.exists_adapted_basis_fin` the same indexed by `Fin (dim V_N^*)`.
* `MvPolynomial.exists_monomial_basis`: a basis of `V_N^*` of classes of monomials, one of them
  `1`.
-/

@[expose] public section

open Finset Module

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/-- `V_N^*`: the polynomials of degree `≤ N` modulo `I`. -/
noncomputable def quotDegLE (I : Ideal (MvPolynomial σ k)) (N : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k N).map (Ideal.Quotient.mkₐ k I).toLinearMap

variable {t : ℕ}

/-- `S_e = γ^e V^*_{N - δ σ(e)}`, the classes of `γ^e q` with `deg q ≤ N - δ ∑ e_j`. -/
noncomputable def powPiece (I : Ideal (MvPolynomial σ k)) (γ : Fin t → MvPolynomial σ k)
    (δ N : ℕ) (e : Fin t → ℕ) : Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k (N - δ * ∑ j, e j)).map
    ((Ideal.Quotient.mkₐ k I).toLinearMap ∘ₗ LinearMap.mulLeft k (∏ j, γ j ^ e j))

/-- The exponents `e` with `δ σ(e) ≤ N`, lexicographically ordered. -/
noncomputable def powIndex (t δ N : ℕ) : Finset (Lex (Fin t → ℕ)) :=
  ((Fintype.piFinset fun _ : Fin t ↦ range (N + 1)).filter fun e ↦ δ * ∑ j, e j ≤ N).map
    toLex.toEmbedding

/-- `W_{> i} = ∑_{e >_lex i} S_e`. -/
noncomputable def powFiltrationGT (I : Ideal (MvPolynomial σ k)) (γ : Fin t → MvPolynomial σ k)
    (δ N : ℕ) (i : Fin t → ℕ) : Submodule k (MvPolynomial σ k ⧸ I) :=
  (@Finset.filter _ (toLex i < ·) (LinearOrder.toDecidableLT (toLex i)) (powIndex t δ N)).sup
    fun e ↦ powPiece I γ δ N (ofLex e)

variable {I : Ideal (MvPolynomial σ k)} {γ : Fin t → MvPolynomial σ k} {δ N : ℕ}

theorem mem_powPiece {e : Fin t → ℕ} {x : MvPolynomial σ k ⧸ I} :
    x ∈ powPiece I γ δ N e ↔ ∃ q : MvPolynomial σ k, q.totalDegree ≤ N - δ * ∑ j, e j ∧
      Ideal.Quotient.mk I ((∏ j, γ j ^ e j) * q) = x := by
  simp [powPiece, mem_restrictTotalDegree]

theorem mem_powIndex (hδ : 0 < δ) {e : Lex (Fin t → ℕ)} :
    e ∈ powIndex t δ N ↔ δ * ∑ j, ofLex e j ≤ N := by
  simp only [powIndex, Finset.mem_map_equiv, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  refine ⟨And.right, fun h ↦ ⟨fun j ↦ ?_, h⟩⟩
  have := Finset.single_le_sum (f := ofLex e) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have : ∑ j, ofLex e j ≤ δ * ∑ j, ofLex e j := Nat.le_mul_of_pos_left _ hδ
  change ofLex e j < N + 1
  omega

instance [Finite σ] : FiniteDimensional k (quotDegLE I N) := by
  unfold quotDegLE
  infer_instance

instance [Finite σ] (e : Fin t → ℕ) : FiniteDimensional k (powPiece I γ δ N e) := by
  unfold powPiece
  infer_instance

instance [Finite σ] (i : Fin t → ℕ) : FiniteDimensional k (powFiltrationGT I γ δ N i) := by
  unfold powFiltrationGT
  infer_instance

theorem totalDegree_prod_pow_le (hγ : ∀ j, (γ j).totalDegree ≤ δ) (e : Fin t → ℕ) :
    (∏ j, γ j ^ e j).totalDegree ≤ δ * ∑ j, e j := by
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [mul_sum]
  exact sum_le_sum fun j _ ↦ (totalDegree_pow _ _).trans (by rw [mul_comm]; gcongr; exact hγ j)

theorem powPiece_le_quotDegLE (hγ : ∀ j, (γ j).totalDegree ≤ δ) {e : Fin t → ℕ}
    (he : δ * ∑ j, e j ≤ N) : powPiece I γ δ N e ≤ quotDegLE I N := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_powPiece.mp hx
  refine ⟨(∏ j, γ j ^ e j) * q, (mem_restrictTotalDegree _ _ _).mpr ?_, rfl⟩
  have := totalDegree_prod_pow_le hγ e
  exact (totalDegree_mul _ _).trans (by omega)

theorem powPiece_zero : powPiece I γ δ N 0 = quotDegLE I N := by
  simp [powPiece, quotDegLE]

/-- The pieces fill `V_N^*`. -/
theorem sup_powPiece (hδ : 0 < δ) (hγ : ∀ j, (γ j).totalDegree ≤ δ) :
    (powIndex t δ N).sup (fun e ↦ powPiece I γ δ N (ofLex e)) = quotDegLE I N := by
  refine le_antisymm (Finset.sup_le fun e he ↦ powPiece_le_quotDegLE hγ
    ((mem_powIndex hδ).mp he)) ?_
  rw [← powPiece_zero]
  exact Finset.le_sup (f := fun e ↦ powPiece I γ δ N (ofLex e)) (b := toLex 0)
    ((mem_powIndex hδ).mpr (show δ * ∑ j, (0 : Fin t → ℕ) j ≤ N by simp))

theorem prod_pow_add_single (γ : Fin t → MvPolynomial σ k) (i : Fin t → ℕ) (j : Fin t) :
    ∏ l, γ l ^ (i + Pi.single j 1 : Fin t → ℕ) l = (∏ l, γ l ^ i l) * γ j := by
  classical
  simp only [Pi.add_apply, pow_add, prod_mul_distrib, Pi.single_apply, pow_ite, pow_one,
    pow_zero, prod_ite_eq', mem_univ, ↓reduceIte]

variable {b : ℕ} {G : Fin b → MvPolynomial σ k}

section Filtration

variable [Finite σ]

/-- **The quotients of the filtration** (Corvaja–Zannier 2004, Lemma 3.1, in dimensions). If
`X₀` and `γ^h = homogenize δ γ` are regular modulo `(G^h)`, then
`dim (S_i + W_{> i}) = dim W_{> i} + dim (k[X₀, X] / (G^h, γ^h))_{N - δ σ(i)}`. -/
theorem finrank_powPiece_sup_eq (hδ : 0 < δ) (hγ : ∀ j, (γ j).totalDegree ≤ δ)
    (hX : (Ideal.span (Set.range fun l ↦ homogenization (G l))).colon {X none} =
      Ideal.span (Set.range fun l ↦ homogenization (G l)))
    (hreg : IsRegularSeq t (Ideal.span (Set.range fun l ↦ homogenization (G l)))
      fun j ↦ homogenize δ (γ j))
    {i : Fin t → ℕ} (hi : δ * ∑ j, i j ≤ N) :
    finrank k ↥(powPiece (Ideal.span (Set.range G)) γ δ N i ⊔
        powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) =
      finrank k (powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) +
        hilbertFunction (oneBlock (Option σ))
          (Ideal.span (Set.range fun l ↦ homogenization (G l)) ⊔
            Ideal.span (Set.range fun j ↦ homogenize δ (γ j))) (fun _ ↦ N - δ * ∑ j, i j) := by
  let : DecidablePred (toLex i < · : Lex (Fin t → ℕ) → Prop) := LinearOrder.toDecidableLT (toLex i)
  set I := Ideal.span (Set.range G)
  set Gh := fun l ↦ homogenization (G l)
  set γh := fun j ↦ homogenize δ (γ j)
  set J := Ideal.span (Set.range Gh) ⊔ Ideal.span (Set.range γh)
  set M := N - δ * ∑ j, i j
  set W := powFiltrationGT I γ δ N i
  set S : Lex (Fin t → ℕ) → Submodule k (MvPolynomial σ k ⧸ I) :=
    fun e ↦ powPiece I γ δ N (ofLex e)
  set s := @Finset.filter _ (toLex i < ·) (LinearOrder.toDecidableLT (toLex i)) (powIndex t δ N)
  set P := weightedHomogeneousSubmodule k (multiWeight (oneBlock (Option σ))) (fun _ ↦ M)
  set f : MvPolynomial (Option σ) k →ₗ[k] MvPolynomial σ k ⧸ I :=
    (Ideal.Quotient.mkₐ k I).toLinearMap ∘ₗ LinearMap.mulLeft k (∏ j, γ j ^ i j) ∘ₗ
      (dehomogenize (R := k) (σ := σ)).toLinearMap
  have hf : ∀ q, f q = Ideal.Quotient.mk I ((∏ j, γ j ^ i j) * dehomogenize q) := fun _ ↦ rfl
  have hP : ∀ q, q ∈ P ↔ q.IsHomogeneous M := fun q ↦
    (mem_weightedHomogeneousSubmodule _ _ _ _).trans isWeightedHomogeneous_oneBlock_iff
  have hGhom : ∀ l, (Gh l).IsHomogeneous (G l).totalDegree := fun l ↦
    isHomogeneous_homogenization (G l)
  have hdehom : ∀ v ∈ Ideal.span (Set.range Gh), dehomogenize v ∈ I := by
    intro v hv
    have h := Ideal.mem_map_of_mem (dehomogenize (R := k) (σ := σ)) hv
    rw [Ideal.map_span, ← Set.range_comp] at h
    have hG : (⇑(dehomogenize (R := k) (σ := σ)) ∘ Gh) = G :=
      funext fun l ↦ dehomogenize_homogenization (G l)
    rwa [hG] at h
  have hmap : P.map f = powPiece I γ δ N i := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact mem_powPiece.mpr ⟨dehomogenize q, totalDegree_dehomogenize_le ((hP q).mp hq), rfl⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_powPiece.mp hx
      exact ⟨homogenize M p, (hP _).mpr (isHomogeneous_homogenize hp), by
        rw [hf, dehomogenize_homogenize]⟩
  have hcomap : P ⊓ W.comap f = P ⊓ J.restrictScalars k := by
    ext q
    simp only [Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]
    refine and_congr_right fun hq ↦ ?_
    have hq' := (hP q).mp hq
    constructor
    · intro hW
      change f q ∈ s.sup S at hW
      rw [Finset.sup_eq_iSup, Submodule.mem_iSup_finset_iff_exists_sum] at hW
      obtain ⟨μ, hμ⟩ := hW
      have hμ' : ∀ e : Lex (Fin t → ℕ), ∃ r : MvPolynomial σ k,
          r.totalDegree ≤ N - δ * ∑ j, ofLex e j ∧
          Ideal.Quotient.mk I ((∏ j, γ j ^ ofLex e j) * r) = μ e := fun e ↦
        mem_powPiece.mp (μ e).2
      choose r hr hrμ using hμ'
      have hsN : ∀ e ∈ s, δ * ∑ j, ofLex e j ≤ N := fun e he ↦
        (mem_powIndex hδ).mp (Finset.mem_filter.mp he).1
      set D := (∏ j, γ j ^ i j) * dehomogenize q - ∑ e ∈ s, (∏ j, γ j ^ ofLex e j) * r e
      have hD : D ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, sub_eq_zero]
        simp only [hrμ]
        rw [hμ, hf]
      have hdeg : D.totalDegree ≤ N := by
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · have h1 := totalDegree_prod_pow_le hγ i
          have h2 := totalDegree_dehomogenize_le hq'
          exact (totalDegree_mul _ _).trans (by omega)
        · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he ↦ ?_)
          have h1 := totalDegree_prod_pow_le hγ (ofLex e)
          have h2 := hr e
          have h3 := hsN e he
          exact (totalDegree_mul _ _).trans (by omega)
      obtain ⟨A, hA, hAsum⟩ := exists_sum_mul_eq_of_mem_span hX hD hdeg
      have hhom : (∏ j, γh j ^ i j) * q -
          ∑ e ∈ s, (∏ j, γh j ^ ofLex e j) * homogenize (N - δ * ∑ j, ofLex e j) (r e) ∈
            Ideal.span (Set.range Gh) := by
        have h1 : homogenize N D = (∏ j, γh j ^ i j) * q -
            ∑ e ∈ s, (∏ j, γh j ^ ofLex e j) * homogenize (N - δ * ∑ j, ofLex e j) (r e) := by
          rw [map_sub, map_sum]
          congr 1
          · conv_lhs => rw [show N = δ * ∑ j, i j + M by omega]
            rw [homogenize_mul (totalDegree_prod_pow_le hγ i) (totalDegree_dehomogenize_le hq'),
              homogenize_prod_pow univ hγ i, homogenize_dehomogenize hq']
          · refine sum_congr rfl fun e he ↦ ?_
            have := hsN e he
            conv_lhs => rw [show N = δ * ∑ j, ofLex e j + (N - δ * ∑ j, ofLex e j) by omega]
            rw [homogenize_mul (totalDegree_prod_pow_le hγ _) (hr e), homogenize_prod_pow univ hγ]
        rw [← h1, ← hAsum, map_sum]
        refine Ideal.sum_mem _ fun l _ ↦ ?_
        by_cases hAl : A l = 0
        · simp [hAl]
        · have := hA l hAl
          rw [show N = (N - (G l).totalDegree) + (G l).totalDegree by omega,
            homogenize_mul (by omega) le_rfl]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
      exact mem_sup_span_range_of_prod_pow_mul_sub_sum_mem hreg s (fun e ↦ ofLex e)
        (fun e ↦ homogenize (N - δ * ∑ j, ofLex e j) (r e))
        (fun e he ↦ (Finset.mem_filter.mp he).2) hhom
    · intro hJ
      obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.mp hJ
      have hq_eq : q = homogeneousComponent M v + homogeneousComponent M u := by
        rw [← map_add, huv]
        exact hq'.weightedHomogeneousComponent_same.symm
      rw [hq_eq, map_add]
      refine add_mem ?_ ?_
      · have hv' : homogeneousComponent M v ∈ Ideal.span (Set.range Gh) :=
          isWeightedHomogeneous_span (w := (1 : Option σ → ℕ)) (fun g hg ↦ by
            obtain ⟨l, rfl⟩ := hg
            exact ⟨_, hGhom l⟩) hv M
        have : f (homogeneousComponent M v) = 0 := by
          rw [hf, Ideal.Quotient.eq_zero_iff_mem]
          exact I.mul_mem_left _ (hdehom _ hv')
        rw [this]
        exact zero_mem _
      · obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hu
        rw [map_sum, map_sum]
        refine sum_mem fun j _ ↦ ?_
        rw [smul_eq_mul]
        by_cases hδM : δ ≤ M
        · have h := (isHomogeneous_homogenize (hγ j)).weightedHomogeneousComponent_add_mul
            (a j) (M - δ)
          rw [Nat.sub_add_cancel hδM] at h
          rw [show homogeneousComponent M (a j * γh j) = _ from h, hf, map_mul dehomogenize,
            dehomogenize_homogenize]
          have hsum : ∑ l, (i + Pi.single j 1 : Fin t → ℕ) l = ∑ l, i l + 1 := by
            simp [Finset.sum_add_distrib]
          refine Finset.le_sup (f := S) (b := toLex (i + Pi.single j 1))
            (Finset.mem_filter.mpr ⟨(mem_powIndex hδ).mpr ?_, ?_⟩) ?_
          · change δ * ∑ l, (i + Pi.single j 1 : Fin t → ℕ) l ≤ N
            rw [hsum, mul_add, mul_one]
            omega
          · exact Pi.toLex_strictMono (Pi.lt_def.mpr ⟨fun l ↦ by simp, j, by simp⟩)
          · refine mem_powPiece.mpr ⟨dehomogenize (homogeneousComponent (M - δ) (a j)), ?_, ?_⟩
            · have := totalDegree_dehomogenize_le
                (homogeneousComponent_isHomogeneous (M - δ) (a j))
              change _ ≤ N - δ * ∑ l, (i + Pi.single j 1 : Fin t → ℕ) l
              rw [hsum, mul_add, mul_one]
              omega
            · change Ideal.Quotient.mk I ((∏ l, γ l ^ (i + Pi.single j 1 : Fin t → ℕ) l) * _) = _
              rw [prod_pow_add_single, mul_assoc, mul_comm (γ j)]
              rfl
        · have h := (isHomogeneous_homogenize (hγ j)).weightedHomogeneousComponent_mul_eq_zero
            (a j) (d' := M) hδM
          rw [show homogeneousComponent M (a j * γh j) = 0 from h, map_zero]
          exact zero_mem _
  have key := Submodule.finrank_map_sup_add_finrank_inf_comap f P W
  rw [hmap, hcomap] at key
  have hle := Submodule.finrank_mono (inf_le_left : P ⊓ J.restrictScalars k ≤ P)
  rw [inf_comm] at key hle
  rw [show hilbertFunction (oneBlock (Option σ)) J (fun _ ↦ M) =
    finrank k P - finrank k ↥(J.restrictScalars k ⊓ P) from rfl]
  omega

end Filtration

section Count

variable [Fintype σ]

/-- Lemma 2.3 for `(G^h, γ^h)`: the Hilbert function of `k[X₀, X] / (G^h, γ^h)` is `≤ E δ^t`, and
`= E δ^t` from degree `N₀ = t (δ - 1) + ∑ (deg G_l - 1)` on. -/
private theorem hilbertFunction_powPiece (hγ : ∀ j, (γ j).totalDegree ≤ δ)
    (hcard : Fintype.card σ = b + t)
    (hht : (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ j)))).height = (b + t : ℕ)) (M : ℕ) :
    hilbertFunction (oneBlock (Option σ))
        (Ideal.span (Set.range fun l ↦ homogenization (G l)) ⊔
          Ideal.span (Set.range fun j ↦ homogenize δ (γ j))) (fun _ ↦ M) ≤
        (∏ l, (G l).totalDegree) * δ ^ t ∧
      (t * (δ - 1) + ∑ l, ((G l).totalDegree - 1) ≤ M →
        hilbertFunction (oneBlock (Option σ))
          (Ideal.span (Set.range fun l ↦ homogenization (G l)) ⊔
            Ideal.span (Set.range fun j ↦ homogenize δ (γ j))) (fun _ ↦ M) =
          (∏ l, (G l).totalDegree) * δ ^ t) := by
  set φ := Fin.append (fun l ↦ homogenization (G l)) fun j ↦ homogenize δ (γ j)
  set e : Fin (b + t) → ℕ := Fin.append (fun l ↦ (G l).totalDegree) fun _ ↦ δ
  have hφ : ∀ j, ∃ n, (φ j).IsHomogeneous n := fun j ↦ by
    induction j using Fin.addCases with
    | left l => exact ⟨_, by simpa [φ] using isHomogeneous_homogenization (G l)⟩
    | right l => exact ⟨_, by simpa [φ] using isHomogeneous_homogenize (hγ l)⟩
  have hg : ∀ j, IsWeightedHomogeneous (multiWeight (oneBlock (Option σ))) (φ j)
      (fun _ ↦ e j) := fun j ↦ by
    refine isWeightedHomogeneous_oneBlock ?_
    induction j using Fin.addCases with
    | left l => simpa [φ, e] using isHomogeneous_homogenization (G l)
    | right l => simpa [φ, e] using isHomogeneous_homogenize (hγ l)
  have hreg := isRegularSeq_of_height_eq hφ hht
  have hσ : Fintype.card (Option σ) = b + t + 1 := by rw [Fintype.card_option, hcard]
  have hspan : Ideal.span (Set.range φ) = Ideal.span (Set.range fun l ↦ homogenization (G l)) ⊔
      Ideal.span (Set.range fun j ↦ homogenize δ (γ j)) := by
    rw [range_append, Ideal.span_union]
  have hprod : ∏ j, e j = (∏ l, (G l).totalDegree) * δ ^ t := by
    simp [e, Fin.prod_univ_add]
  have hsum : ∑ j, (e j - 1) = t * (δ - 1) + ∑ l, ((G l).totalDegree - 1) := by
    simp [e, Fin.sum_univ_add, add_comm]
  rw [← hspan, ← hprod]
  exact ⟨hilbertFunction_span_range_le hσ hg hreg M, fun hM ↦
    hilbertFunction_span_range_eq hσ hg hreg (hsum ▸ hM)⟩

/-- **The dimensions of the quotients** (Corvaja–Zannier 2004, Lemma 3.2). If `(G^h, γ^h)` has
height `|σ| = b + t` and `(G^h, X₀)` height `b + 1`, then
`dim W_{(i)} - dim W_{> i} ≤ E δ^t`, `E = ∏ deg G_l`, with equality when
`δ σ(i) + N₀ ≤ N`, `N₀ = t (δ - 1) + ∑ (deg G_l - 1)`. -/
theorem finrank_powPiece_sup_le_and (hδ : 0 < δ) (hγ : ∀ j, (γ j).totalDegree ≤ δ)
    (hcard : Fintype.card σ = b + t)
    (hht : (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ j)))).height = (b + t : ℕ))
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1)
    {i : Fin t → ℕ} (hi : δ * ∑ j, i j ≤ N) :
    finrank k ↥(powPiece (Ideal.span (Set.range G)) γ δ N i ⊔
        powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) ≤
      finrank k (powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) +
        (∏ l, (G l).totalDegree) * δ ^ t ∧
    (δ * ∑ j, i j + (t * (δ - 1) + ∑ l, ((G l).totalDegree - 1)) ≤ N →
      finrank k ↥(powPiece (Ideal.span (Set.range G)) γ δ N i ⊔
          powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) =
        finrank k (powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) +
          (∏ l, (G l).totalDegree) * δ ^ t) := by
  have hGh : ∀ l, ∃ n, (homogenization (G l)).IsHomogeneous n := fun l ↦
    ⟨_, isHomogeneous_homogenization (G l)⟩
  have hγh : ∀ j, ∃ n, (homogenize δ (γ j)).IsHomogeneous n := fun j ↦
    ⟨_, isHomogeneous_homogenize (hγ j)⟩
  have hX := colon_eq_of_height_insert_eq hGh ⟨1, isHomogeneous_X k none⟩ hXh
  have hreg := isRegularSeq_append_of_height_eq hGh hγh hht
  rw [finrank_powPiece_sup_eq hδ hγ hX hreg hi]
  obtain ⟨h1, h2⟩ := hilbertFunction_powPiece hγ hcard hht (N - δ * ∑ j, i j)
  exact ⟨by omega, fun h ↦ by rw [h2 (by omega)]⟩

/-- **The adapted basis** (Corvaja–Zannier 2004, §3, after Lemma 3.2). Let `δ > 0`,
`deg γ_j ≤ δ`, `|σ| = b + t`, `(G^h, γ^h)` of height `b + t` and `(G^h, X₀)` of height `b + 1`. Then
`V_N^*` has a basis of classes of `γ^{ℓ(x)} q_x` with `δ σ(ℓ(x)) ≤ N` and
`deg q_x ≤ N - δ σ(ℓ(x))`, with at most `E δ^t` elements of each exponent `i`,
`E = ∏ deg G_l`, and exactly `E δ^t` when `δ σ(i) + N₀ ≤ N`,
`N₀ = t (δ - 1) + ∑ (deg G_l - 1)`. -/
theorem exists_adapted_basis (hδ : 0 < δ) (hγ : ∀ j, (γ j).totalDegree ≤ δ)
    (hcard : Fintype.card σ = b + t)
    (hht : (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ j)))).height = (b + t : ℕ))
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1) :
    ∃ (ι : Type) (_ : Fintype ι) (ℓ : ι → Fin t → ℕ) (q : ι → MvPolynomial σ k),
      (∀ x, δ * ∑ j, ℓ x j ≤ N) ∧ (∀ x, (q x).totalDegree ≤ N - δ * ∑ j, ℓ x j) ∧
      LinearIndependent k
        (fun x ↦ Ideal.Quotient.mk (Ideal.span (Set.range G)) ((∏ j, γ j ^ ℓ x j) * q x)) ∧
      Submodule.span k (Set.range fun x ↦
        Ideal.Quotient.mk (Ideal.span (Set.range G)) ((∏ j, γ j ^ ℓ x j) * q x)) =
          quotDegLE (Ideal.span (Set.range G)) N ∧
      (∀ i, (univ.filter (ℓ · = i)).card ≤ (∏ l, (G l).totalDegree) * δ ^ t) ∧
      ∀ i, δ * ∑ j, i j + (t * (δ - 1) + ∑ l, ((G l).totalDegree - 1)) ≤ N →
        (univ.filter (ℓ · = i)).card = (∏ l, (G l).totalDegree) * δ ^ t := by
  classical
  obtain ⟨ι, _, v, ℓ, hℓ, hv, hli, hspan, hcount⟩ :=
    Submodule.exists_adapted_family (fun e ↦ powPiece (Ideal.span (Set.range G)) γ δ N (ofLex e))
      (powIndex t δ N)
  choose q hq hqv using fun x ↦ mem_powPiece.mp (hv x)
  have hfun : (fun x ↦ Ideal.Quotient.mk (Ideal.span (Set.range G))
      ((∏ j, γ j ^ ofLex (ℓ x) j) * q x)) = v := funext hqv
  -- The count of an exponent `i` with `δ σ(i) ≤ N` is `dim W_{(i)} - dim W_{> i}`.
  have hcnt : ∀ i : Fin t → ℕ, δ * ∑ j, i j ≤ N →
      (univ.filter (fun x ↦ ofLex (ℓ x) = i)).card +
          finrank k (powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) =
        finrank k ↥(powPiece (Ideal.span (Set.range G)) γ δ N i ⊔
          powFiltrationGT (Ideal.span (Set.range G)) γ δ N i) := by
    intro i hi
    have h := hcount (toLex i) ((mem_powIndex hδ).mpr hi)
    unfold powFiltrationGT
    convert h using 3
    all_goals try rfl
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ h ▸ rfl⟩
  have hzero : ∀ i : Fin t → ℕ, ¬ δ * ∑ j, i j ≤ N →
      (univ.filter (fun x ↦ ofLex (ℓ x) = i)).card = 0 := by
    intro i hi
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - rfl
    exact hi ((mem_powIndex hδ).mp (hℓ x))
  refine ⟨ι, inferInstance, fun x ↦ ofLex (ℓ x), q, fun x ↦ (mem_powIndex hδ).mp (hℓ x), hq,
    hfun ▸ hli, by rw [hfun, hspan, sup_powPiece hδ hγ], fun i ↦ ?_, fun i hi ↦ ?_⟩
  · beta_reduce
    by_cases hi : δ * ∑ j, i j ≤ N
    · have := (finrank_powPiece_sup_le_and hδ hγ hcard hht hXh hi).1
      have := hcnt i hi
      omega
    · rw [hzero i hi]
      exact Nat.zero_le _
  · beta_reduce
    have hi' : δ * ∑ j, i j ≤ N := by omega
    have := (finrank_powPiece_sup_le_and hδ hγ hcard hht hXh hi').2 hi
    have := hcnt i hi'
    omega

/-- **The adapted basis, indexed by `Fin (dim V_N^*)`**, so that the bases for different `γ`
share an index type. -/
theorem exists_adapted_basis_fin (hδ : 0 < δ) (hγ : ∀ j, (γ j).totalDegree ≤ δ)
    (hcard : Fintype.card σ = b + t)
    (hht : (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ j)))).height = (b + t : ℕ))
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1) :
    ∃ (ℓ : Fin (finrank k (quotDegLE (Ideal.span (Set.range G)) N)) → Fin t → ℕ)
      (q : Fin (finrank k (quotDegLE (Ideal.span (Set.range G)) N)) → MvPolynomial σ k),
      (∀ x, δ * ∑ j, ℓ x j ≤ N) ∧ (∀ x, (q x).totalDegree ≤ N - δ * ∑ j, ℓ x j) ∧
      LinearIndependent k
        (fun x ↦ Ideal.Quotient.mk (Ideal.span (Set.range G)) ((∏ j, γ j ^ ℓ x j) * q x)) ∧
      Submodule.span k (Set.range fun x ↦
        Ideal.Quotient.mk (Ideal.span (Set.range G)) ((∏ j, γ j ^ ℓ x j) * q x)) =
          quotDegLE (Ideal.span (Set.range G)) N ∧
      (∀ i, (univ.filter (ℓ · = i)).card ≤ (∏ l, (G l).totalDegree) * δ ^ t) ∧
      ∀ i, δ * ∑ j, i j + (t * (δ - 1) + ∑ l, ((G l).totalDegree - 1)) ≤ N →
        (univ.filter (ℓ · = i)).card = (∏ l, (G l).totalDegree) * δ ^ t := by
  obtain ⟨ι, _, ℓ, q, h1, h2, hli, hspan, h5, h6⟩ :=
    exists_adapted_basis (N := N) hδ hγ hcard hht hXh
  have hcardι : Fintype.card ι = finrank k (quotDegLE (Ideal.span (Set.range G)) N) := by
    rw [← hspan, finrank_span_eq_card hli]
  set e : Fin (finrank k (quotDegLE (Ideal.span (Set.range G)) N)) ≃ ι :=
    (Fintype.equivFinOfCardEq hcardι).symm
  have hcnt : ∀ i, (univ.filter fun x ↦ ℓ (e x) = i).card = (univ.filter (ℓ · = i)).card :=
    fun i ↦ card_equiv e fun x ↦ by simp
  refine ⟨ℓ ∘ e, q ∘ e, fun x ↦ h1 _, fun x ↦ h2 _, hli.comp e e.injective, ?_,
    fun i ↦ (hcnt i).trans_le (h5 i), fun i hi ↦ (hcnt i).trans (h6 i hi)⟩
  exact (congrArg (Submodule.span k) (e.surjective.range_comp fun x ↦
    Ideal.Quotient.mk (Ideal.span (Set.range G)) ((∏ j, γ j ^ ℓ x j) * q x))).trans hspan

end Count

/-- **A monomial basis of `V_N^*` containing `1`**: if `1 ∉ I`, the classes of some monomials of
degree `≤ N`, indexed by `Fin (dim V_N^*)`, form a basis of `V_N^*`, and one of them is `1`. -/
theorem exists_monomial_basis [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : (1 : MvPolynomial σ k) ∉ I) (N : ℕ) :
    ∃ m : Fin (finrank k (quotDegLE I N)) → σ →₀ ℕ,
      (∀ i, (monomial (m i) (1 : k)).totalDegree ≤ N) ∧
      LinearIndependent k (fun i ↦ Ideal.Quotient.mk I (monomial (m i) 1)) ∧
      Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk I (monomial (m i) 1)) =
        quotDegLE I N ∧ ∃ i₀, m i₀ = 0 := by
  classical
  set v : (σ →₀ ℕ) → MvPolynomial σ k ⧸ I := fun m ↦ Ideal.Quotient.mk I (monomial m 1)
  set T : Set (σ →₀ ℕ) := {m | (monomial m (1 : k)).totalDegree ≤ N}
  have hTV : Submodule.span k (v '' T) = quotDegLE I N := by
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨monomial m 1, (mem_restrictTotalDegree _ _ _).mpr hm, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, mem_restrictTotalDegree] at hp
      rw [p.as_sum, map_sum]
      refine Submodule.sum_mem _ fun m hm ↦ ?_
      rw [show monomial m (p.coeff m) = p.coeff m • monomial m (1 : k) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
      change (monomial m (1 : k)).totalDegree ≤ N
      rw [totalDegree_monomial _ one_ne_zero]
      exact (le_totalDegree hm).trans hp
  have h0 : LinearIndepOn k v {0} := by
    refine (linearIndepOn_singleton_iff k).mpr fun h ↦ hI ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [v] using h
  have h0T : ({0} : Set (σ →₀ ℕ)) ⊆ T := by simp [T]
  obtain ⟨B, hBT, h0B, hTB, hli⟩ := exists_linearIndepOn_extension h0 h0T
  have hBV : ∀ x : B, v x ∈ quotDegLE I N := fun x ↦
    hTV ▸ Submodule.subset_span ⟨x, hBT x.2, rfl⟩
  have hliV : LinearIndependent k (fun x : B ↦ (⟨v x, hBV x⟩ : quotDegLE I N)) :=
    LinearIndependent.of_comp (quotDegLE I N).subtype hli
  have : Finite B := hliV.finite_of_isNoetherian
  have := Fintype.ofFinite B
  have hrange : Set.range (fun x : B ↦ v x) = v '' B := (Set.image_eq_range v B).symm
  have hspanB : Submodule.span k (Set.range fun x : B ↦ v x) = quotDegLE I N := by
    rw [hrange]
    refine le_antisymm (Submodule.span_le.mpr ?_) (hTV ▸ Submodule.span_le.mpr hTB)
    rintro _ ⟨x, hx, rfl⟩
    exact hBV ⟨x, hx⟩
  have hcard : Fintype.card B = finrank k (quotDegLE I N) := by
    rw [← hspanB, finrank_span_eq_card hli]
  set e : Fin (finrank k (quotDegLE I N)) ≃ B := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i ↦ (e i).1, fun i ↦ hBT (e i).2, hli.comp e e.injective, ?_,
    e.symm ⟨0, h0B rfl⟩, by simp⟩
  exact (congrArg (Submodule.span k) (e.surjective.range_comp fun x : B ↦ v x)).trans hspanB

end MvPolynomial
