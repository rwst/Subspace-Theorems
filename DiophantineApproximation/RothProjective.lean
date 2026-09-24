/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproxProd

/-!
# Roth's theorem on the projective line

**Layer 3.4** (Bombieri–Gubler, Theorem 7.2.2 for `n = 1`, and Example 7.2.7). The Subspace
Theorem for `Fintype.card ι = 2` is Roth's theorem, and this file proves it in that case from
Layer 3.3, together with the converse.

## Main results

* `NumberField.finite_setOf_prod_onePointApprox_le_const`: Layer 3.3 with a constant in front of
  the height, which is the form both directions consume.
* `NumberField.exists_finset_submodule_of_approxProd_le_card_two`: **Layer 3.4**, the Subspace
  Theorem in two variables.
* `NumberField.finite_setOf_prod_min_one_le_of_subspace`: the converse, Roth's theorem of Layer
  3.2 recovered from the two-variable Subspace Theorem.

## Implementation notes

⚠ **The exceptional subspaces of the projective line are its points.** For two variables a proper
subspace of `K²` is a line, so the conclusion "the solutions lie in finitely many proper
subspaces" says exactly that there are finitely many solutions in `ℙ¹(K)`. The finite set built
here is the set of lines `K ⬝ (1, β)` for the finitely many `β` Layer 3.3 produces, together with
the single line `K ⬝ (0, 1)` at infinity, which the hypothesis does not constrain at all: a point
with `x i₀ = 0` is exceptional for free.

⚠ **The split by which form is small is over `2 ^ |S|` choices, and it cannot be avoided.** At a
place the two forms have two different zeros, and which of them the point is near depends on the
point. Roth's theorem takes one target per place, so the solution set is covered by one Roth set
for each of the finitely many choice functions `S → ι`. This is the same split Ridout's theorem
needs in Layer 3.3, at a different place in the argument.

⚠ **The choice function has to be extended off `S`, and the extension needs that no finite place
is an infinite place.** Roth's theorem indexes its targets by an arbitrary `AbsoluteValue K ℝ`,
so a choice made on `↥Sinf ⊕ ↥Sfin` must be spread to all of them. `Function.extend` does it,
and the two extensions compose only because the underlying absolute value of an infinite place is
never that of a finite place — `NumberField.InfinitePlace.val_ne_finitePlace_val`, proved here
from `v 2 = 2` against `v 2 ≤ 1`.

⚠ **The constant is absorbed once, in `finite_setOf_prod_onePointApprox_le_const`.** Both
directions produce an inequality with a constant in front of the height, and both are finished by
applying Layer 3.3 at a smaller exponent and collecting the bounded-height remainder with
Northcott. Doing it once, in a lemma, is what keeps the two directions short.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.2, Remark 7.2.3 and Example 7.2.7.

This is part of Layer 3.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Module AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Layer 3.3, with a constant.** Roth's theorem with targets in `OnePoint F` tolerates a
constant in front of the height: applying it at an exponent strictly between `2` and `κ` and
collecting the remaining bounded-height solutions by Northcott absorbs any `C`. -/
theorem finite_setOf_prod_onePointApprox_le_const (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → OnePoint F) (C : ℝ) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ C * mulHeight₁ β ^ (-κ)}.Finite := by
  classical
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  set κ₁ : ℝ := (κ + 2) / 2 with hκ₁def
  have hκ₁2 : 2 < κ₁ := by rw [hκ₁def]; linarith
  have hκ₁κ : κ₁ < κ := by rw [hκ₁def]; linarith
  set B : ℝ := C' ^ (κ - κ₁)⁻¹ with hBdef
  have hroth := finite_setOf_prod_onePointApprox_le Sinf Sfin w hwInf hwFin α hκ₁2
  have hnorth := finite_setOfPred_mulHeight₁_le (K := K) B
  refine Set.Finite.subset (hroth.union hnorth) ?_
  intro β hβ
  rw [Set.mem_ofPred_eq] at hβ
  by_cases hbig : mulHeight₁ β ≤ B
  · exact Or.inr hbig
  refine Or.inl ?_
  rw [Set.mem_ofPred_eq]
  push Not at hbig
  have hβpos : (0 : ℝ) < mulHeight₁ β := mulHeight₁_pos β
  have hC'le : C' ≤ mulHeight₁ β ^ (κ - κ₁) := by
    have hBκ : B ^ (κ - κ₁) = C' := by
      rw [hBdef, Real.rpow_inv_rpow (by linarith) (by linarith)]
    rw [← hBκ]
    exact Real.rpow_le_rpow (by positivity) hbig.le (by linarith)
  calc (∏ v ∈ Sinf, (w v.1).onePointApprox (α v.1) (algebraMap K F β) ^ v.mult) *
        ∏ v ∈ Sfin, (w v.1).onePointApprox (α v.1) (algebraMap K F β)
      ≤ C * mulHeight₁ β ^ (-κ) := hβ
    _ ≤ C' * mulHeight₁ β ^ (-κ) :=
        mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hβpos.le _)
    _ ≤ mulHeight₁ β ^ (κ - κ₁) * mulHeight₁ β ^ (-κ) :=
        mul_le_mul_of_nonneg_right hC'le (Real.rpow_nonneg hβpos.le _)
    _ = mulHeight₁ β ^ (-κ₁) := by
        rw [← Real.rpow_add hβpos]
        ring_nf

/-- **Layer 3.4: Roth's theorem on the projective line.** The Subspace Theorem of Layer 6.3 for
`Fintype.card ι = 2`, proved here from Layer 3.3: the solutions of the approximation inequality
lie in finitely many proper subspaces of `K²`, that is, in finitely many points of `ℙ¹(K)`. -/
theorem exists_finset_submodule_of_approxProd_le_card_two {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 2)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ V ∈ T, x ∈ V := by
  classical
  -- the two indices
  obtain ⟨i₀, i₁, hne, huniv⟩ : ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ ∀ i, i = i₀ ∨ i = i₁ := by
    have hnc : Nat.card ι = 2 := by rw [Nat.card_eq_fintype_card, hcard]
    obtain ⟨p, q, hpq, hset⟩ := Nat.card_eq_two_iff.mp hnc
    refine ⟨p, q, hpq, fun i ↦ ?_⟩
    have hmem : i ∈ ({p, q} : Set ι) := by rw [hset]; exact Set.mem_univ i
    simpa using hmem
  -- the coefficients of the forms
  obtain ⟨a, ha⟩ : ∃ a : AbsoluteValue K ℝ → ι → F,
      ∀ u i, a u i = L u i fun j ↦ if i₀ = j then (1 : F) else 0 := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : AbsoluteValue K ℝ → ι → F,
      ∀ u i, b u i = L u i fun j ↦ if i₁ = j then (1 : F) else 0 := ⟨_, fun _ _ ↦ rfl⟩
  have hab : ∀ (u : AbsoluteValue K ℝ) (i : ι) (y : ι → F),
      L u i y = a u i * y i₀ + b u i * y i₁ := by
    intro u i y
    rw [ha, hb, LinearMap.pi_apply_eq_sum_univ (L u i) y,
      Finset.univ_eq_pair_of_forall_eq_or huniv, Finset.sum_pair hne]
    simp only [smul_eq_mul]
    ring
  have hdet : ∀ u : AbsoluteValue K ℝ, LinearIndependent F (L u) →
      a u i₀ * b u i₁ - a u i₁ * b u i₀ ≠ 0 :=
    fun u hu ↦ det_ne_zero_of_linearIndependent hne huniv hu (hab u)
  -- the constant at each place, and its product over `S`
  set Γ : AbsoluteValue K ℝ → ℝ := fun u ↦
    ((w u).formConst (a u i₀) (b u i₀) + (w u).formConst (a u i₁) (b u i₁)) *
      ((w u (a u i₀) + w u (a u i₁) + w u (b u i₀) + w u (b u i₁)) /
        w u (a u i₀ * b u i₁ - a u i₁ * b u i₀)) with hΓdef
  have hΓnn : ∀ u : AbsoluteValue K ℝ, 0 ≤ Γ u := by
    intro u
    have h1 : (0 : ℝ) ≤ w u (a u i₀) := (w u).nonneg _
    have h2 : (0 : ℝ) ≤ w u (a u i₁) := (w u).nonneg _
    have h3 : (0 : ℝ) ≤ w u (b u i₀) := (w u).nonneg _
    have h4 : (0 : ℝ) ≤ w u (b u i₁) := (w u).nonneg _
    have hsum : (0 : ℝ) ≤ w u (a u i₀) + w u (a u i₁) + w u (b u i₀) + w u (b u i₁) := by linarith
    simp only [hΓdef]
    exact mul_nonneg (add_nonneg ((w u).formConst_nonneg _ _) ((w u).formConst_nonneg _ _))
      (div_nonneg hsum ((w u).nonneg _))
  set Cst : ℝ := (∏ v ∈ Sinf, Γ v.1 ^ v.mult) * ∏ v ∈ Sfin, Γ v.1 with hCstdef
  -- the choice of one of the two forms at each place of `S`, spread to every absolute value
  have hinjInf : Function.Injective fun v : ↥Sinf ↦ (v : InfinitePlace K).1 :=
    fun p q h ↦ Subtype.ext (Subtype.ext h)
  have hinjFin : Function.Injective fun v : ↥Sfin ↦ (v : FinitePlace K).1 :=
    fun p q h ↦ Subtype.ext (Subtype.ext h)
  have hdisj : ∀ v : ↥Sfin,
      ¬∃ p : ↥Sinf, (p : InfinitePlace K).1
        = (v : FinitePlace K).1 := by
    rintro v ⟨p, hp⟩
    exact InfinitePlace.val_ne_finitePlace_val (p : InfinitePlace K) (v : FinitePlace K) hp
  set pick : ((↥Sinf ⊕ ↥Sfin) → ι) → AbsoluteValue K ℝ → ι := fun σ ↦
    Function.extend (fun v : ↥Sinf ↦ (v : InfinitePlace K).1)
      (fun v ↦ σ (Sum.inl v))
      (Function.extend (fun v : ↥Sfin ↦ (v : FinitePlace K).1)
        (fun v ↦ σ (Sum.inr v)) fun _ ↦ i₀) with hpickdef
  have hpickInf : ∀ (σ : (↥Sinf ⊕ ↥Sfin) → ι) (v : InfinitePlace K) (hv : v ∈ Sinf),
      pick σ v.1 = σ (Sum.inl ⟨v, hv⟩) := by
    intro σ v hv
    rw [hpickdef]
    exact hinjInf.extend_apply _ _ ⟨v, hv⟩
  have hpickFin : ∀ (σ : (↥Sinf ⊕ ↥Sfin) → ι) (v : FinitePlace K) (hv : v ∈ Sfin),
      pick σ v.1 = σ (Sum.inr ⟨v, hv⟩) := by
    intro σ v hv
    simp only [hpickdef]
    rw [Function.extend_apply' _ _ _ (hdisj ⟨v, hv⟩)]
    exact hinjFin.extend_apply _ _ ⟨v, hv⟩
  set tgt : ((↥Sinf ⊕ ↥Sfin) → ι) → AbsoluteValue K ℝ → OnePoint F := fun σ u ↦
    OnePoint.formRoot (a u (pick σ u)) (b u (pick σ u)) with htgtdef
  have hfin : ∀ σ : (↥Sinf ⊕ ↥Sfin) → ι,
      {β : K | (∏ v ∈ Sinf, (w v.1).onePointApprox (tgt σ v.1) (algebraMap K F β) ^ v.mult) *
          ∏ v ∈ Sfin, (w v.1).onePointApprox (tgt σ v.1) (algebraMap K F β)
        ≤ Cst * mulHeight₁ β ^ (-(2 + ε))}.Finite := fun σ ↦
    finite_setOf_prod_onePointApprox_le_const Sinf Sfin w hwInf hwFin (tgt σ) Cst (by linarith)
  -- the exceptional lines
  set pt : K → (ι → K) := fun β i ↦ if i = i₀ then (1 : K) else β with hptdef
  have hpt0 : ∀ β : K, pt β i₀ = 1 := fun β ↦ by rw [hptdef]; exact ite_eq_left rfl
  have hpt1 : ∀ β : K, pt β i₁ = β := fun β ↦ by rw [hptdef]; exact ite_eq_right (Ne.symm hne)
  refine ⟨insert (Submodule.span K {(Pi.single i₁ 1 : ι → K)})
    (Finset.univ.biUnion fun σ : (↥Sinf ⊕ ↥Sfin) → ι ↦
      (hfin σ).toFinset.image fun β ↦ Submodule.span K {pt β}), ?_, ?_⟩
  · -- every member of the list is a proper subspace
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV'
    · intro htop
      have hmem : (Pi.single i₀ 1 : ι → K) ∈ Submodule.span K {(Pi.single i₁ 1 : ι → K)} := by
        rw [htop]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have h0 := congrFun hc i₀
      rw [Pi.smul_apply, Pi.single_eq_of_ne hne, Pi.single_eq_same, smul_eq_mul, mul_zero] at h0
      exact one_ne_zero h0.symm
    · obtain ⟨σ, -, hσm⟩ := Finset.mem_biUnion.mp hV'
      obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hσm
      intro htop
      have hmem : (Pi.single i₁ 1 : ι → K) ∈ Submodule.span K {pt β} := by
        rw [htop]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have h0 := congrFun hc i₀
      have h1 := congrFun hc i₁
      rw [Pi.smul_apply, hpt0, smul_eq_mul, mul_one, Pi.single_eq_of_ne hne] at h0
      rw [Pi.smul_apply, hpt1, smul_eq_mul, Pi.single_eq_same, h0, zero_mul] at h1
      exact one_ne_zero h1.symm
  · -- every solution lies in one of them
    intro x hx0 hxle
    by_cases hxi : x i₀ = 0
    · refine ⟨Submodule.span K {(Pi.single i₁ 1 : ι → K)}, Finset.mem_insert_self _ _,
        Submodule.mem_span_singleton.mpr ⟨x i₁, ?_⟩⟩
      funext i
      rcases huniv i with rfl | rfl
      · rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul, mul_zero, hxi]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · set β : K := x i₁ / x i₀ with hβdef
      set bF : F := algebraMap K F β with hbFdef
      set Λ : AbsoluteValue K ℝ → ι → ℝ := fun u i ↦
        (w u).onePointApprox (OnePoint.formRoot (a u i) (b u i)) bF with hΛdef
      set P : AbsoluteValue K ℝ → ℝ := fun u ↦
        ∏ i, w u (L u i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) with hPdef
      have hΛnn : ∀ (u : AbsoluteValue K ℝ) (i : ι), 0 ≤ Λ u i := by
        intro u i
        rw [hΛdef]
        exact (w u).onePointApprox_nonneg _ _
      have hPnn : ∀ u : AbsoluteValue K ℝ, 0 ≤ P u := by
        intro u
        rw [hPdef]
        exact Finset.prod_nonneg fun i _ ↦
          div_nonneg ((w u).nonneg _) (Real.iSup_nonneg fun j ↦ u.nonneg _)
      have hlocal : ∀ u : AbsoluteValue K ℝ, (w u).LiesOver u → LinearIndependent F (L u) →
          min (Λ u i₀) (Λ u i₁) ≤ Γ u * P u := by
        intro u hwu hLu
        have hinst : (w u).LiesOver u := hwu
        exact onePointApprox_min_le_localFactor (w u) hne huniv (hab u) (hdet u hLu) hxi
      -- the place-by-place choice of the smaller factor
      set σ : (↥Sinf ⊕ ↥Sfin) → ι := fun s ↦ Sum.elim
        (fun v : ↥Sinf ↦ if Λ (v : InfinitePlace K).1 i₀
          ≤ Λ (v : InfinitePlace K).1 i₁ then i₀ else i₁)
        (fun v : ↥Sfin ↦ if Λ (v : FinitePlace K).1 i₀
          ≤ Λ (v : FinitePlace K).1 i₁ then i₀ else i₁) s with hσdef
      have hchoice : ∀ (u : AbsoluteValue K ℝ) (i : ι),
          (i = if Λ u i₀ ≤ Λ u i₁ then i₀ else i₁) → Λ u i = min (Λ u i₀) (Λ u i₁) := by
        intro u i hi
        by_cases h : Λ u i₀ ≤ Λ u i₁
        · rw [hi, ite_eq_left h, min_eq_left h]
        · rw [hi, ite_eq_right h, min_eq_right (not_le.mp h).le]
      have hmatchInf : ∀ (v : InfinitePlace K) (hv : v ∈ Sinf),
          (w v.1).onePointApprox (tgt σ v.1) bF = min (Λ v.1 i₀) (Λ v.1 i₁) := by
        intro v hv
        have hstep : (w v.1).onePointApprox (tgt σ v.1) bF = Λ v.1 (σ (Sum.inl ⟨v, hv⟩)) := by
          rw [htgtdef, hΛdef]
          simp only []
          rw [hpickInf σ v hv]
        rw [hstep]
        exact hchoice v.1 _ rfl
      have hmatchFin : ∀ (v : FinitePlace K) (hv : v ∈ Sfin),
          (w v.1).onePointApprox (tgt σ v.1) bF = min (Λ v.1 i₀) (Λ v.1 i₁) := by
        intro v hv
        have hstep : (w v.1).onePointApprox (tgt σ v.1) bF = Λ v.1 (σ (Sum.inr ⟨v, hv⟩)) := by
          rw [htgtdef, hΛdef]
          simp only []
          rw [hpickFin σ v hv]
        rw [hstep]
        exact hchoice v.1 _ rfl
      -- the product over `S`
      have hA : (∏ v ∈ Sinf, (w v.1).onePointApprox (tgt σ v.1) bF ^ v.mult)
          ≤ (∏ v ∈ Sinf, Γ v.1 ^ v.mult) * ∏ v ∈ Sinf, P v.1 ^ v.mult := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀
          (fun v _ ↦ pow_nonneg ((w v.1).onePointApprox_nonneg _ _) _) fun v hv ↦ ?_
        rw [← mul_pow, hmatchInf v hv]
        exact pow_le_pow_left₀ (le_min (hΛnn _ _) (hΛnn _ _))
          (hlocal v.1 (hwInf v hv) (hLInf v hv)) _
      have hB : (∏ v ∈ Sfin, (w v.1).onePointApprox (tgt σ v.1) bF)
          ≤ (∏ v ∈ Sfin, Γ v.1) * ∏ v ∈ Sfin, P v.1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀
          (fun v _ ↦ (w v.1).onePointApprox_nonneg _ _) fun v hv ↦ ?_
        rw [hmatchFin v hv]
        exact hlocal v.1 (hwFin v hv) (hLFin v hv)
      have happrox : approxProd Sinf Sfin w L x
          = (∏ v ∈ Sinf, P v.1 ^ v.mult) * ∏ v ∈ Sfin, P v.1 := rfl
      have hexp : mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) = mulHeight₁ β ^ (-(2 + ε)) := by
        rw [Height.mulHeight_eq_mulHeight₁_div huniv x, ← hβdef, hcard]
        congr 1
        push_cast
        ring
      have hsol : (∏ v ∈ Sinf, (w v.1).onePointApprox (tgt σ v.1) (algebraMap K F β) ^ v.mult) *
          ∏ v ∈ Sfin, (w v.1).onePointApprox (tgt σ v.1) (algebraMap K F β)
          ≤ Cst * mulHeight₁ β ^ (-(2 + ε)) := by
        have h0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, (w v.1).onePointApprox (tgt σ v.1) bF :=
          Finset.prod_nonneg fun v _ ↦ (w v.1).onePointApprox_nonneg _ _
        have h1 : (0 : ℝ) ≤ (∏ v ∈ Sinf, Γ v.1 ^ v.mult) * ∏ v ∈ Sinf, P v.1 ^ v.mult :=
          mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hΓnn v.1) _)
            (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hPnn v.1) _)
        have hCstnn : (0 : ℝ) ≤ Cst :=
          mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hΓnn v.1) _)
            (Finset.prod_nonneg fun v _ ↦ hΓnn v.1)
        calc (∏ v ∈ Sinf, (w v.1).onePointApprox (tgt σ v.1) bF ^ v.mult) *
              ∏ v ∈ Sfin, (w v.1).onePointApprox (tgt σ v.1) bF
            ≤ ((∏ v ∈ Sinf, Γ v.1 ^ v.mult) * ∏ v ∈ Sinf, P v.1 ^ v.mult) *
              ((∏ v ∈ Sfin, Γ v.1) * ∏ v ∈ Sfin, P v.1) := mul_le_mul hA hB h0 h1
          _ = Cst * ((∏ v ∈ Sinf, P v.1 ^ v.mult) * ∏ v ∈ Sfin, P v.1) := by
              rw [hCstdef]; ring
          _ = Cst * approxProd Sinf Sfin w L x := by rw [happrox]
          _ ≤ Cst * mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) :=
              mul_le_mul_of_nonneg_left hxle hCstnn
          _ = Cst * mulHeight₁ β ^ (-(2 + ε)) := by rw [hexp]
      refine ⟨Submodule.span K {pt β}, Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨σ, Finset.mem_univ _, Finset.mem_image.mpr
          ⟨β, (hfin σ).mem_toFinset.mpr hsol, rfl⟩⟩), ?_⟩
      refine Submodule.mem_span_singleton.mpr ⟨x i₀, ?_⟩
      funext i
      rcases huniv i with rfl | rfl
      · rw [Pi.smul_apply, hpt0, smul_eq_mul, mul_one]
      · rw [Pi.smul_apply, hpt1, smul_eq_mul, hβdef, mul_div_cancel₀ _ hxi]

/-- **The converse: Roth's theorem is the two-variable Subspace Theorem for the forms `X₀` and
`X₁ - α v X₀`.** The content is the implication, not the conclusion — the conclusion is Layer
3.2's own theorem — and the implication is what certifies that the two statements are the same
statement. The Subspace Theorem is taken as a hypothesis at the relevant data, for every `ε`;
`NumberField.finite_setOf_prod_min_one_le_card_two` discharges it from Layer 3.4. -/
theorem finite_setOf_prod_min_one_le_of_subspace (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ)
    (L : AbsoluteValue K ℝ → Fin 2 → Dual F (Fin 2 → F))
    (hL0 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 0 y = y 0)
    (hL1 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 1 y = y 1 - α u * y 0)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ T : Finset (Submodule K (Fin 2 → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : Fin 2 → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card (Fin 2) : ℝ) - ε) →
        ∃ V ∈ T, x ∈ V) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  classical
  have huniv : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i ↦ by omega
  set ε : ℝ := (κ - 2) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨T, hTproper, hTmem⟩ := hsub ε hε
  -- a line meets the affine chart in at most one point
  have hsmall : ∀ V : Submodule K (Fin 2 → K), V ≠ ⊤ →
      {β : K | (![1, β] : Fin 2 → K) ∈ V}.Subsingleton := by
    intro V hV β hβ β' hβ'
    by_contra hbb
    refine hV ?_
    have h1 : (![1, β] - ![1, β'] : Fin 2 → K) ∈ V := V.sub_mem hβ hβ'
    have heq : (![1, β] - ![1, β'] : Fin 2 → K) = (β - β') • ![0, 1] := by
      funext i
      fin_cases i <;> simp
    have he01 : (![0, 1] : Fin 2 → K) ∈ V := by
      have hs := V.smul_mem (β - β')⁻¹ h1
      rw [heq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hbb), one_smul] at hs
      exact hs
    have he10 : (![1, 0] : Fin 2 → K) ∈ V := by
      have hs := V.sub_mem hβ (V.smul_mem β he01)
      have heq2 : (![1, β] - β • ![0, 1] : Fin 2 → K) = ![1, 0] := by
        funext i
        fin_cases i <;> simp
      rwa [heq2] at hs
    refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
    have hy : y = y 0 • (![1, 0] : Fin 2 → K) + y 1 • ![0, 1] := by
      funext i
      fin_cases i <;> simp
    rw [hy]
    exact V.add_mem (V.smul_mem _ he10) (V.smul_mem _ he01)
  have hG : {β : K | ∃ V ∈ T, (![1, β] : Fin 2 → K) ∈ V}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet
      fun V hV ↦ (hsmall V (hTproper V hV)).finite) ?_
    intro β hβ
    obtain ⟨V, hV, hmem⟩ := hβ
    exact Set.mem_biUnion hV hmem
  -- the constant of the comparison
  set Cst : ℝ := (∏ v ∈ Sinf, (1 + w v.1 (α v.1)) ^ v.mult) * ∏ v ∈ Sfin, (1 + w v.1 (α v.1))
    with hCstdef
  have hone : ∀ u : AbsoluteValue K ℝ, (1 : ℝ) ≤ 1 + w u (α u) := fun u ↦ by
    linarith [(w u).nonneg (α u)]
  have hCst1 : (1 : ℝ) ≤ Cst := by
    rw [hCstdef]
    exact one_le_mul_of_one_le_of_one_le
      (Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (hone v.1))
      (Finset.one_le_prod₀ fun v _ ↦ hone v.1)
  set B : ℝ := Cst ^ ε⁻¹ with hBdef
  refine Set.Finite.subset ((finite_setOfPred_mulHeight₁_le (K := K) B).union hG) ?_
  intro β hβ
  rw [Set.mem_ofPred_eq] at hβ
  by_cases hbig : mulHeight₁ β ≤ B
  · exact Or.inl hbig
  refine Or.inr ?_
  push Not at hbig
  set x : Fin 2 → K := ![1, β] with hxdef
  have hx0 : x ≠ 0 := by
    intro hcon
    have := congrFun hcon 0
    rw [hxdef] at this
    simp at this
  -- the local comparison at one place
  have hlocal : ∀ u : AbsoluteValue K ℝ, (w u).LiesOver u →
      (∏ i : Fin 2, w u (L u i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j))
        ≤ (1 + w u (α u)) * min 1 (w u (algebraMap K F β - α u)) := by
    intro u hwu
    have hinst : (w u).LiesOver u := hwu
    have hx1 : x 0 = 1 := by rw [hxdef]; rfl
    have hx2 : x 1 = β := by rw [hxdef]; rfl
    have hM : (⨆ j, u (x j)) = max 1 (u β) := by
      rw [Height.iSup_eq_max_of_forall_eq_or huniv fun j ↦ u (x j), hx1, hx2, u.map_one]
    have hM1 : (1 : ℝ) ≤ max 1 (u β) := le_max_left _ _
    have hnum0 : w u (L u 0 fun j ↦ algebraMap K F (x j)) = 1 := by
      rw [hL0, hx1, map_one, AbsoluteValue.map_one]
    have hnum1 : w u (L u 1 fun j ↦ algebraMap K F (x j))
        = w u (algebraMap K F β - α u) := by
      rw [hL1, hx1, hx2, map_one, mul_one]
    have hA : (0 : ℝ) ≤ w u (α u) := (w u).nonneg _
    have hbnd : w u (algebraMap K F β - α u)
        ≤ (1 + w u (α u)) * max 1 (u β) * min 1 (w u (algebraMap K F β - α u)) := by
      have hβv : w u (algebraMap K F β) = u β :=
        AbsoluteValue.apply_algebraMap_of_liesOver (v := u) (w u) β
      have hle : w u (algebraMap K F β) ≤ max 1 (u β) := by rw [hβv]; exact le_max_right _ _
      have hsub' : w u (algebraMap K F β - α u) ≤ w u (algebraMap K F β) + w u (α u) :=
        (w u).sub_le_add _ _
      rcases le_or_gt (w u (algebraMap K F β - α u)) 1 with hcase | hcase
      · rw [min_eq_right hcase]
        exact le_mul_of_one_le_left ((w u).nonneg _)
          (one_le_mul_of_one_le_of_one_le (by linarith) hM1)
      · rw [min_eq_left hcase.le, mul_one]
        nlinarith
    rw [Fin.prod_univ_two, hnum0, hnum1, hM]
    have hMpos : (0 : ℝ) < max 1 (u β) := by linarith
    have hminnn : (0 : ℝ) ≤ min 1 (w u (algebraMap K F β - α u)) :=
      le_min zero_le_one ((w u).nonneg _)
    rw [div_mul_div_comm, one_mul, div_le_iff₀ (by positivity)]
    refine le_trans hbnd ?_
    have hc1 : (0 : ℝ) ≤ (1 + w u (α u)) * min 1 (w u (algebraMap K F β - α u)) * max 1 (u β) :=
      mul_nonneg (mul_nonneg (by linarith) hminnn) (by linarith)
    nlinarith [hc1, hM1]
  -- the global comparison
  have hheight : mulHeight x = mulHeight₁ β := by
    rw [Height.mulHeight_eq_mulHeight₁_div huniv x, hxdef]
    simp
  have hβpos : (0 : ℝ) < mulHeight₁ β := mulHeight₁_pos β
  have hCstle : Cst ≤ mulHeight₁ β ^ ε := by
    have hBκ : B ^ ε = Cst := by
      rw [hBdef, Real.rpow_inv_rpow (by linarith) (by linarith)]
    rw [← hBκ]
    exact Real.rpow_le_rpow (by positivity) hbig.le (by linarith)
  have hmin : ∀ u : AbsoluteValue K ℝ, (0 : ℝ) ≤ min 1 (w u (algebraMap K F β - α u)) :=
    fun u ↦ le_min zero_le_one ((w u).nonneg _)
  have hAinf : (∏ v ∈ Sinf, (∏ i : Fin 2,
        w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult)
      ≤ (∏ v ∈ Sinf, (1 + w v.1 (α v.1)) ^ v.mult) *
        ∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (Finset.prod_nonneg fun i _ ↦
      div_nonneg ((w v.1).nonneg _) (Real.iSup_nonneg fun j ↦ v.1.nonneg _)) _) fun v hv ↦ ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ ↦
      div_nonneg ((w v.1).nonneg _) (Real.iSup_nonneg fun j ↦ v.1.nonneg _))
      (hlocal v.1 (hwInf v hv)) _
  have hAfin : (∏ v ∈ Sfin, ∏ i : Fin 2,
        w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ≤ (∏ v ∈ Sfin, (1 + w v.1 (α v.1))) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ Finset.prod_nonneg fun i _ ↦
      div_nonneg ((w v.1).nonneg _) (Real.iSup_nonneg fun j ↦ v.1.nonneg _)) fun v hv ↦
      hlocal v.1 (hwFin v hv)
  have hfinal : approxProd Sinf Sfin w L x
      ≤ mulHeight x ^ (-(Fintype.card (Fin 2) : ℝ) - ε) := by
    have h0 : (0 : ℝ) ≤ ∏ v ∈ Sfin, ∏ i : Fin 2,
        w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) :=
      Finset.prod_nonneg fun v _ ↦ Finset.prod_nonneg fun i _ ↦
        div_nonneg ((w v.1).nonneg _) (Real.iSup_nonneg fun j ↦ v.1.nonneg _)
    have h1 : (0 : ℝ) ≤ (∏ v ∈ Sinf, (1 + w v.1 (α v.1)) ^ v.mult) *
        ∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult :=
      mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (by linarith [hone v.1]) _)
        (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hmin v.1) _)
    have hexp : mulHeight x ^ (-(Fintype.card (Fin 2) : ℝ) - ε)
        = mulHeight₁ β ^ (-(2 : ℝ) - ε) := by
      rw [hheight]
      norm_num
    calc approxProd Sinf Sfin w L x
        ≤ ((∏ v ∈ Sinf, (1 + w v.1 (α v.1)) ^ v.mult) *
            ∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
          ((∏ v ∈ Sfin, (1 + w v.1 (α v.1))) *
            ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))) := mul_le_mul hAinf hAfin h0 h1
      _ = Cst * ((∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
            ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1))) := by rw [hCstdef]; ring
      _ ≤ Cst * mulHeight₁ β ^ (-κ) :=
          mul_le_mul_of_nonneg_left hβ (by linarith)
      _ ≤ mulHeight₁ β ^ ε * mulHeight₁ β ^ (-κ) :=
          mul_le_mul_of_nonneg_right hCstle (Real.rpow_nonneg hβpos.le _)
      _ = mulHeight₁ β ^ (-(2 : ℝ) - ε) := by
          rw [← Real.rpow_add hβpos, hεdef]
          ring_nf
      _ = mulHeight x ^ (-(Fintype.card (Fin 2) : ℝ) - ε) := hexp.symm
  exact hTmem x hx0 hfinal

/-- **The roundtrip: Layer 3.2 recovered from Layer 3.4.** Roth's theorem over a number field is
the two-variable Subspace Theorem for the forms `X₀` and `X₁ - α v X₀`, which are linearly
independent whatever the targets. The conclusion is that of
`NumberField.finite_setOf_prod_min_one_le`; what this proof adds is that the Subspace Theorem's
shape specializes to it, which is the second half of Layer 3.4. -/
theorem finite_setOf_prod_min_one_le_card_two (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  classical
  set L : AbsoluteValue K ℝ → Fin 2 → Dual F (Fin 2 → F) := fun u i ↦
    if i = 0 then LinearMap.proj 0 else LinearMap.proj 1 - α u • LinearMap.proj 0 with hLdef
  have hL0 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 0 y = y 0 := by
    intro u y
    simp only [hLdef, ite_eq_left rfl]
    rfl
  have hL1 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 1 y = y 1 - α u * y 0 := by
    intro u y
    simp only [hLdef, ite_eq_right (by decide : ¬((1 : Fin 2) = 0))]
    simp
  have hLi : ∀ u : AbsoluteValue K ℝ, LinearIndependent F (L u) := by
    intro u
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have happ : ∀ y : Fin 2 → F, g 0 * L u 0 y + g 1 * L u 1 y = 0 := by
      intro y
      have h : (∑ i, g i • L u i) y = (0 : Dual F (Fin 2 → F)) y := by rw [hg]
      rw [LinearMap.sum_apply, Fin.sum_univ_two, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, smul_eq_mul, smul_eq_mul] at h
      exact h
    have hg1 : g 1 = 0 := by
      have h1 := happ ![0, 1]
      rw [hL0, hL1] at h1
      simpa using h1
    have hg0 : g 0 = 0 := by
      have h2 := happ ![1, 0]
      rw [hL0, hL1, hg1] at h2
      simpa using h2
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  refine finite_setOf_prod_min_one_le_of_subspace Sinf Sfin w hwInf hwFin α hκ L hL0 hL1 ?_
  intro ε hε
  exact exists_finset_submodule_of_approxProd_le_card_two (Fintype.card_fin 2) Sinf Sfin w
    hwInf hwFin L (fun v _ ↦ hLi v.1) (fun v _ ↦ hLi v.1) hε

end NumberField

/-! ### Acceptance criteria -/

/-- **Conformance with Layer 3.2.** The roundtrip lands on Roth's theorem as Layer 3.2 states
it — hypothesis for hypothesis, and with the same `mulHeight₁ β ^ (-κ)` on the right. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (Sinf : Finset (NumberField.InfinitePlace K))
    (Sfin : Finset (NumberField.FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le_card_two Sinf Sfin w hwInf hwFin α hκ

/-- ⚠ **The line at infinity is a solution, so it cannot be dropped from the exceptional set.**
For the coordinate forms `L v i = Xᵢ` the point `(0, 1)` makes one factor of `approxProd`
vanish, so it satisfies the hypothesis of Layer 3.4 for every `ε` and every height; and it lies
on no line `K ⬝ (1, β)`. The conclusion of Layer 3.4 is therefore not "finitely many `β`" but
"finitely many points of `ℙ¹(K)`", and the extra point is forced. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (v : NumberField.InfinitePlace K) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) :
    NumberField.approxProd {v} (∅ : Finset (NumberField.FinitePlace K)) w
      (fun _ (i : Fin 2) ↦ (LinearMap.proj i : Dual F (Fin 2 → F))) (![0, 1] : Fin 2 → K) = 0 := by
  rw [NumberField.approxProd, Finset.prod_empty, mul_one, Finset.prod_singleton]
  refine pow_eq_zero_iff NumberField.InfinitePlace.mult_ne_zero |>.mpr ?_
  refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 2)) ?_
  rw [show ((LinearMap.proj (0 : Fin 2) : Dual F (Fin 2 → F))
    fun j ↦ algebraMap K F ((![0, 1] : Fin 2 → K) j)) = 0 by simp]
  simp

/-- **No point of the affine chart is on the line at infinity.** -/
example {K : Type*} [Field K] (β : K) :
    (![0, 1] : Fin 2 → K) ∉ Submodule.span K {(![1, β] : Fin 2 → K)} := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
    mul_one] at h0 h1
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1
