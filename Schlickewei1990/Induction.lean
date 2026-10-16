/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Schlickewei1990.ProjectiveSolutions

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Option

/-!
# The induction (§7)

Schlickewei deduces Theorem 1.1 from Lemma 6.1 by induction on the number of terms. A solution of
`∑ α_o x_o = 0` (`n + 1` terms, no vanishing proper subsum) has its point `y' = (α_i x_i)_i` in
one of the proper subspaces `U` of Lemma 6.1. `U` lies in a hyperplane `∑ βᵢ yᵢ = 0`, so the
solution has a minimal vanishing subsum `∑_{i ∈ J} βᵢ αᵢ xᵢ = 0`. Then:

* `(xᵢ / x_{j₀})_{i ∈ J}` is a solution of that shorter equation;
* `(x_{j₀}, (x_o)_{o ∉ J})` is a solution of the equation with the block `J` merged into one
  term `γ z`, `γ = ∑_{i ∈ J} αᵢ xᵢ / x_{j₀}`, which has no vanishing proper subsum either.

Both have at most `n` terms (`#J ≥ 2`), and together they determine the solution. So an equation
of `n + 1` terms has at most `#T · 2ⁿ · Z(n)²` solutions (`ncard_normUnitSolutions_option_le`),
which is Schlickewei's `2ⁿ Z(n−1)²` per subspace.

The solutions are counted by their **normalized** representatives (`x k₀ = 1`,
`NumberField.normUnitSolutions`), so the induction never takes quotients. Every projective
solution has exactly one of them (`NumberField.ncard_projUnitSolutions_le`).

## Main definitions

* `NumberField.normUnitSolutions S α k₀`: the normalized solutions.
* `NumberField.unitCount L`: the bound of the recursion,
  `Z(m + 1) = Z(m) + L(m) 2^m Z(m)²`.

## Main results

* `NumberField.finite_normUnitSolutions`: finitely many, for every `α` (Layer 8.2).
* `NumberField.normUnitSolutions_subsingleton`: at most one for at most two terms.
* `NumberField.ncard_normUnitSolutions_le_comp_equiv`: reindexing.
* `NumberField.ncard_projUnitSolutions_le`: projective solutions against normalized ones.
* `NumberField.ncard_setOf_minimal_le`: one minimal relation costs `Z²`.
* `NumberField.ncard_normUnitSolutions_option_le`: **one step of the induction**.
* `NumberField.ncard_normUnitSolutions_le_unitCount`: **Lemma 6.1 implies Theorem 1.1**, for any
  bound `L` on the subspaces of Lemma 6.1.

## References

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107,
§7.

This is milestone S90.6 of `Schlickewei1990/README.md`.
-/

@[expose] public section

open Finset IsDedekindDomain

namespace NumberField

variable {K : Type} [Field K] [NumberField K]

/-- **The normalized projective solutions** of `∑ αₖ xₖ = 0`: the `S`-unit tuples with
`x k₀ = 1`, the sum `0` and no vanishing proper nonempty subsum. Each projective solution has
exactly one such representative. -/
def normUnitSolutions {κ : Type*} [Fintype κ] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (α : κ → K) (k₀ : κ) : Set (κ → Kˣ) :=
  {x | x k₀ = 1 ∧ (∀ k, x k ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
    ∑ k, α k * x k = 0 ∧ ∀ J : Finset κ, J.Nonempty → J ≠ univ → ∑ k ∈ J, α k * x k ≠ 0}

variable {κ : Type*} [Fintype κ] {S : Finset (HeightOneSpectrum (𝓞 K))} {α : κ → K} {k₀ : κ}

/-- With two indices or more, a zero coefficient is a vanishing subsum, so there are no
solutions. -/
theorem normUnitSolutions_eq_empty [Nontrivial κ] {k : κ} (hk : α k = 0) :
    normUnitSolutions S α k₀ = ∅ := by
  classical
  refine Set.eq_empty_of_forall_notMem fun x hx ↦
    hx.2.2.2 {k} (singleton_nonempty k) ?_ (by simp [hk])
  obtain ⟨k', hk'⟩ := exists_ne k
  exact fun h ↦ hk' (mem_singleton.1 (h ▸ mem_univ k'))

/-- **The normalized solutions are finitely many** (Layer 8.2, `NumberField.finite_unitSolutions`,
through `x ↦ (xₖ)_{k ≠ k₀}`). -/
theorem finite_normUnitSolutions (S : Finset (HeightOneSpectrum (𝓞 K))) (α : κ → K) (k₀ : κ) :
    (normUnitSolutions S α k₀).Finite := by
  classical
  rcases subsingleton_or_nontrivial κ with hκ | hκ
  · refine Set.Subsingleton.finite fun x hx y hy ↦ funext fun k ↦ ?_
    rw [Subsingleton.elim k k₀, hx.1, hy.1]
  by_cases h0 : ∃ k, α k = 0
  · obtain ⟨k, hk⟩ := h0
    rw [normUnitSolutions_eq_empty hk]
    exact Set.finite_empty
  push Not at h0
  have hfin := finite_unitSolutions S (fun k : {k // k ≠ k₀} ↦ -α k / α k₀)
    fun k ↦ div_ne_zero (neg_ne_zero.2 (h0 _)) (h0 _)
  refine Set.Finite.of_finite_image (f := fun x (k : {k // k ≠ k₀}) ↦ x k)
    (hfin.subset ?_) fun x hx y hy hxy ↦ funext fun k ↦ ?_
  · rintro _ ⟨x, ⟨h1, hu, hsum, hsub⟩, rfl⟩
    have hsplit : ∀ I : Finset {k // k ≠ k₀}, ∑ k ∈ I, -α k / α k₀ * (x k : K) =
        -(∑ k ∈ I.map (Function.Embedding.subtype _), α k * x k) / α k₀ := fun I ↦ by
      rw [sum_map, neg_div, sum_div, ← sum_neg_distrib]
      exact sum_congr rfl fun k _ ↦ by simp only [Function.Embedding.subtype_apply]; ring
    refine ⟨fun k ↦ hu k, ?_, fun I hI ↦ ?_⟩
    · rw [hsplit]
      have h := Fintype.sum_eq_add_sum_subtype_ne (fun k ↦ α k * (x k : K)) k₀
      rw [hsum, h1, Units.val_one, mul_one] at h
      rw [show (univ.map (Function.Embedding.subtype fun k ↦ k ≠ k₀)) =
          (univ : Finset {k // k ≠ k₀}).map (Function.Embedding.subtype _) from rfl, sum_map]
      simp only [Function.Embedding.subtype_apply]
      rw [div_eq_one_iff_eq (h0 k₀)]
      linear_combination h
    · rw [hsplit]
      refine div_ne_zero (neg_ne_zero.2 (hsub _ (hI.map) fun h ↦ ?_)) (h0 k₀)
      have : k₀ ∈ I.map (Function.Embedding.subtype _) := h ▸ mem_univ k₀
      simp at this
  · by_cases hk : k = k₀
    · rw [hk, hx.1, hy.1]
    · exact congrFun hxy ⟨k, hk⟩

/-- **With at most two terms there is at most one solution**: for two terms the equation
`α_{k₀} + α_k x_k = 0` fixes `x_k`, since `α_k = 0` would be a vanishing subsum. -/
theorem normUnitSolutions_subsingleton (hκ : Fintype.card κ ≤ 2) :
    (normUnitSolutions S α k₀).Subsingleton := by
  classical
  intro x hx y hy
  funext k
  by_cases hk : k = k₀
  · rw [hk, hx.1, hy.1]
  have huniv : (univ : Finset κ) = {k₀, k} := by
    refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    rw [card_univ, card_pair (Ne.symm hk)]
    exact hκ
  have hαk : α k ≠ 0 := fun h0 ↦ hx.2.2.2 {k} (singleton_nonempty k)
    (fun h ↦ hk (mem_singleton.1 (h ▸ mem_univ k₀)).symm) (by simp [h0])
  have hs : ∀ z ∈ normUnitSolutions S α k₀, α k₀ + α k * z k = 0 := fun z hz ↦ by
    have h := hz.2.2.1
    rwa [huniv, sum_pair (Ne.symm hk), hz.1, Units.val_one, mul_one] at h
  have h1 := hs x hx
  have h2 := hs y hy
  exact Units.ext (mul_left_cancel₀ hαk (by linear_combination h1 - h2))

/-- **Reindexing does not lose solutions**: along `e : κ' ≃ κ`, `x ↦ x ∘ e` maps the normalized
solutions injectively to those of `α ∘ e`. -/
theorem ncard_normUnitSolutions_le_comp_equiv {κ' : Type*} [Fintype κ'] (e : κ' ≃ κ) :
    (normUnitSolutions S α k₀).ncard ≤ (normUnitSolutions S (α ∘ e) (e.symm k₀)).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (fun x ↦ x ∘ e) ?_ ?_ (finite_normUnitSolutions _ _ _)
  · rintro x ⟨h1, hu, hsum, hsub⟩
    refine ⟨by simpa using h1, fun k ↦ hu _, ?_, fun J hJ hJu ↦ ?_⟩
    · rw [← hsum]
      exact Equiv.sum_comp e (fun k ↦ α k * (x k : K))
    · have h := hsub (J.map e.toEmbedding) (hJ.map) fun h ↦ hJu ?_
      · rwa [sum_map] at h
      · rw [← map_univ_equiv e] at h
        exact map_injective _ h
  · intro x _ y _ h
    funext k
    simpa using congrFun h (e.symm k)

/-- **Every projective solution has a normalized representative**, so there are at most as many
projective solutions as normalized ones. -/
theorem ncard_projUnitSolutions_le [Nonempty κ] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (α : κ → K) (k₀ : κ) :
    (projUnitSolutions S α).ncard ≤ (normUnitSolutions S α k₀).ncard := by
  classical
  have hfin := finite_normUnitSolutions S α k₀
  refine (Set.ncard_le_ncard (t := (fun x : κ → Kˣ ↦
      Projectivization.mk K (fun k ↦ (x k : K)) (coe_units_ne_zero x)) ''
        normUnitSolutions S α k₀) ?_ (hfin.image _)).trans (Set.ncard_image_le hfin)
  rintro _ ⟨x, hu, hsum, hsub, rfl⟩
  have hJ : ∀ J : Finset κ, ∑ k ∈ J, α k * ((x k * (x k₀)⁻¹ : Kˣ) : K) =
      (∑ k ∈ J, α k * x k) * ((x k₀)⁻¹ : Kˣ) := fun J ↦ by
    rw [sum_mul]
    exact sum_congr rfl fun k _ ↦ by rw [Units.val_mul]; ring
  refine ⟨fun k ↦ x k * (x k₀)⁻¹, ⟨mul_inv_cancel _, fun k ↦ mul_mem (hu k) (inv_mem (hu k₀)),
    ?_, fun J hJ0 hJu ↦ ?_⟩, ?_⟩
  · rw [hJ, hsum, zero_mul]
  · rw [hJ]
    exact mul_ne_zero (hsub J hJ0 hJu) (Units.ne_zero _)
  · refine (Projectivization.mk_eq_mk_iff K _ _ _ _).2 ⟨(x k₀)⁻¹, funext fun k ↦ ?_⟩
    simp [Units.smul_def, mul_comm]

section Step

variable {ι : Type} [Fintype ι] {α : Option ι → K}

/-- **A minimal relation `∑_{i ∈ J} bᵢ yᵢ = 0` costs at most `Z²` solutions** (Sch90 §7).
Fix `j₀ ∈ J`. A solution `x` is determined by the normalized solution `(x_i / x_{j₀})_{i ∈ J}` of
the shorter equation `∑_{i ∈ J} bᵢ αᵢ zᵢ = 0`, and by the normalized solution
`(x_{j₀}, (x_o)_{o ∉ J})` of the equation in which the block `J` is merged into one term,
`γ z + ∑_{o ∉ J} α_o z_o = 0` with `γ = ∑_{i ∈ J} αᵢ xᵢ / x_{j₀}`. Both have at most `n` terms,
since `#J ≥ 2`. -/
theorem ncard_setOf_minimal_le (b : ι → K) (J : Finset ι) {Z : ℕ}
    (IH : ∀ (κ' : Type) [Fintype κ'], Fintype.card κ' ≤ Fintype.card ι →
      ∀ (α' : κ' → K) (k₀' : κ'), (normUnitSolutions S α' k₀').ncard ≤ Z) :
    {x ∈ normUnitSolutions S α none | (∀ i ∈ J, b i ≠ 0) ∧ J.Nonempty ∧
      ∑ i ∈ J, b i * (α (some i) * x (some i)) = 0 ∧
      ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, b i * (α (some i) * x (some i)) ≠ 0}.ncard ≤
      Z ^ 2 := by
  classical
  set X := {x ∈ normUnitSolutions S α none | (∀ i ∈ J, b i ≠ 0) ∧ J.Nonempty ∧
      ∑ i ∈ J, b i * (α (some i) * x (some i)) = 0 ∧
      ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, b i * (α (some i) * x (some i)) ≠ 0} with hX
  by_cases hJ2 : 2 ≤ #J
  swap
  · -- a single nonzero term does not vanish
    suffices X = ∅ by rw [this, Set.ncard_empty]; exact Nat.zero_le _
    refine Set.eq_empty_of_forall_notMem fun x ⟨hx, hb, hJ, hsum, _⟩ ↦ ?_
    obtain ⟨j, rfl⟩ := card_eq_one.1 (show #J = 1 by have := hJ.card_pos; omega)
    have hj := hx.2.2.2 {some j} (singleton_nonempty _) fun h ↦ by
      have : (none : Option ι) ∈ ({some j} : Finset (Option ι)) := h ▸ mem_univ _
      simp at this
    rw [sum_singleton] at hsum hj
    exact mul_ne_zero (hb j (mem_singleton_self j)) hj hsum
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := card_pos.1 (by omega)
  set J' : Finset (Option ι) := J.map Function.Embedding.some with hJ'
  have hnone : none ∉ J' := by simp [hJ']
  set j₀' : {i // i ∈ J} := ⟨j₀, hj₀⟩
  set k₀' : Option {o : Option ι // o ∉ J'} := some ⟨none, hnone⟩
  -- the shorter equation on `J` and the merged one
  set αJ : {i // i ∈ J} → K := fun i ↦ b i * α (some i)
  set α' : ({i // i ∈ J} → Kˣ) → Option {o : Option ι // o ∉ J'} → K := fun ρ o ↦
    o.elim (∑ i : {i // i ∈ J}, α (some i) * ρ i) fun o ↦ α o
  set r : (Option ι → Kˣ) → {i // i ∈ J} → Kˣ := fun x i ↦ x (some i) / x (some j₀)
  set Φ : (Option ι → Kˣ) → Option {o : Option ι // o ∉ J'} → Kˣ := fun x o ↦
    o.elim (x (some j₀)) fun o ↦ x o
  have hcardJ : Fintype.card {i // i ∈ J} ≤ Fintype.card ι := by
    rw [Fintype.card_coe]
    exact card_le_univ J
  have hcard' : Fintype.card (Option {o : Option ι // o ∉ J'}) ≤ Fintype.card ι := by
    rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_option,
      hJ', card_map]
    have := card_le_univ J
    omega
  -- the pairs
  set Q : Set (({i // i ∈ J} → Kˣ) × (Option {o : Option ι // o ∉ J'} → Kˣ)) :=
    {q | q.1 ∈ normUnitSolutions S αJ j₀' ∧ q.2 ∈ normUnitSolutions S (α' q.1) k₀'}
  have hNJ := finite_normUnitSolutions S αJ j₀'
  have hQsub : Q ⊆ ↑(hNJ.toFinset.biUnion fun ρ ↦
      (finite_normUnitSolutions S (α' ρ) k₀').toFinset.image (Prod.mk ρ)) := by
    rintro ⟨ρ, w⟩ ⟨hρ, hw⟩
    simp only [coe_biUnion, Set.Finite.coe_toFinset, coe_image, Set.mem_iUnion, Set.mem_image,
      Prod.mk.injEq, exists_prop]
    exact ⟨ρ, hρ, w, hw, rfl, rfl⟩
  have hQ : Q.ncard ≤ Z ^ 2 := by
    rw [sq]
    calc Q.ncard ≤ _ := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hQsub
      _ ≤ hNJ.toFinset.card * Z := card_biUnion_le_card_mul _ _ _ fun ρ _ ↦
          card_image_le.trans (by
            rw [← Set.ncard_eq_toFinset_card _ (finite_normUnitSolutions _ _ _)]
            exact IH _ hcard' _ _)
      _ ≤ Z * Z := by
          rw [← Set.ncard_eq_toFinset_card _ hNJ]
          exact Nat.mul_le_mul_right _ (IH _ hcardJ _ _)
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun x ↦ (r x, Φ x)) ?_ ?_
    ((finite_toSet _).subset hQsub)) hQ
  · rintro x ⟨⟨h1, hu, hsum, hsub⟩, hb, -, hJsum, hJmin⟩
    -- sums over subsets of `J`, normalized
    have hr : ∀ I : Finset {i // i ∈ J}, ∑ i ∈ I, αJ i * (r x i : K) =
        (∑ i ∈ I.map (Function.Embedding.subtype _), b i * (α (some i) * x (some i))) /
          x (some j₀) := fun I ↦ by
      rw [sum_map, sum_div]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [αJ, r, Units.val_div_eq_div_val, Function.Embedding.subtype_apply]
      ring
    -- the merged term is the block
    have hγ : (∑ i : {i // i ∈ J}, α (some i) * (r x i : K)) * x (some j₀) =
        ∑ o ∈ J', α o * x o := by
      rw [hJ', sum_map, sum_mul, ← sum_coe_sort J]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [r, Units.val_div_eq_div_val, Function.Embedding.some_apply]
      field_simp
    -- sums over the indices off `J`
    have hoff : ∀ M : Finset {o : Option ι // o ∉ J'},
        ∑ o ∈ M, α' (r x) (some o) * (Φ x (some o) : K) =
          ∑ o ∈ M.map (Function.Embedding.subtype _), α o * x o := fun M ↦ by
      rw [sum_map]
      rfl
    have hsplit : ∀ M : Finset (Option {o : Option ι // o ∉ J'}), none ∈ M →
        ∑ o ∈ M, α' (r x) o * (Φ x o : K) =
          ∑ o ∈ J' ∪ M.eraseNone.map (Function.Embedding.subtype _), α o * x o := fun M hM ↦ by
      rw [sum_union (disjoint_left.2 fun o ho ho' ↦ by
        obtain ⟨p, -, rfl⟩ := mem_map.1 ho'
        exact p.2 ho), ← hoff, ← hγ]
      conv_lhs => rw [← insert_eq_of_mem hM, ← insertNone_eraseNone, sum_insertNone]
      rfl
    refine ⟨⟨div_self' (x (some j₀)), fun i ↦ div_mem (hu _) (hu _), ?_, fun I hI hIu ↦ ?_⟩,
      ⟨h1, fun o ↦ ?_, ?_, fun M hM hMu ↦ ?_⟩⟩
    · rw [hr, show (univ : Finset {i // i ∈ J}).map (Function.Embedding.subtype _) = J from by
        ext i; simp, hJsum, zero_div]
    · rw [hr]
      refine div_ne_zero (hJmin _ (fun i hi ↦ ?_) hI.map fun h ↦ hIu ?_) (Units.ne_zero _)
      · obtain ⟨i, -, rfl⟩ := mem_map.1 hi
        simp
      · refine eq_univ_of_forall fun i ↦ ?_
        have : (i : ι) ∈ I.map (Function.Embedding.subtype _) := by rw [h]; exact i.2
        simpa using this
    · cases o with
      | none => exact hu _
      | some o => exact hu _
    · rw [hsplit _ (mem_univ _), ← hsum]
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext o
      by_cases ho : o ∈ J'
      · simp [ho]
      · simp only [mem_union, ho, false_or, mem_univ, iff_true, mem_map]
        exact ⟨⟨o, ho⟩, by simp, rfl⟩
    · by_cases hn : none ∈ M
      · rw [hsplit _ hn]
        refine hsub _ ⟨_, mem_union_left _ (mem_map_of_mem _ hj₀)⟩ fun h ↦ hMu ?_
        refine eq_univ_of_forall fun o ↦ ?_
        cases o with
        | none => exact hn
        | some p =>
          have hp : (p : Option ι) ∈ J' ∪ M.eraseNone.map (Function.Embedding.subtype _) :=
            h ▸ mem_univ _
          rcases mem_union.1 hp with hp | hp
          · exact absurd hp p.2
          · obtain ⟨q, hq, hqp⟩ := mem_map.1 hp
            obtain rfl : q = p := Subtype.ext hqp
            exact mem_eraseNone.1 hq
      · rw [sum_eq_sum_eraseNone _ hn, hoff]
        refine hsub _ (nonempty_eraseNone hM hn).map fun h ↦ ?_
        have : some j₀ ∈ M.eraseNone.map (Function.Embedding.subtype _) := h ▸ mem_univ _
        obtain ⟨p, -, hp⟩ := mem_map.1 this
        apply p.2
        rw [show (p : Option ι) = some j₀ from hp]
        exact mem_map_of_mem _ hj₀
  · rintro x ⟨⟨hx1, -⟩, -⟩ y ⟨⟨hy1, -⟩, -⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hΦ⟩ := h
    have hj : x (some j₀) = y (some j₀) := congrFun hΦ none
    funext o
    by_cases ho : o ∈ J'
    · obtain ⟨i, hi, rfl⟩ := mem_map.1 ho
      have := congrFun hr ⟨i, hi⟩
      simp only [r, hj] at this
      simpa using this
    · exact congrFun hΦ (some ⟨o, ho⟩)

/-- **One step of the induction** (Sch90 §7). If the points `y'` of all the solutions of
`∑ α_o x_o = 0` lie in the proper subspaces of `T`, and every equation of at most `n` terms has at
most `Z` normalized solutions, then this one of `n + 1` terms has at most `#T · 2ⁿ · Z²`. Each
`U ∈ T` lies in a hyperplane `∑ βᵢ yᵢ = 0`; a solution in `U` has a minimal vanishing subsum `J`
of that relation (one of `2ⁿ` sets), and `ncard_setOf_minimal_le` counts each `(U, J)`. -/
theorem ncard_normUnitSolutions_option_le {T : Finset (Submodule K (ι → K))}
    (hT : ∀ U ∈ T, U ≠ ⊤)
    (hcov : ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
      ∑ o, α o * x o = 0 → ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U) {Z : ℕ}
    (IH : ∀ (κ' : Type) [Fintype κ'], Fintype.card κ' ≤ Fintype.card ι →
      ∀ (α' : κ' → K) (k₀' : κ'), (normUnitSolutions S α' k₀').ncard ≤ Z) :
    (normUnitSolutions S α none).ncard ≤ #T * 2 ^ Fintype.card ι * Z ^ 2 := by
  classical
  choose! β hβ0 hβ using fun U (hU : U ∈ T) ↦
    exists_ne_zero_forall_sum_mul_eq_zero_of_ne_top (hT U hU)
  set X : Submodule K (ι → K) → Finset ι → Set (Option ι → Kˣ) := fun U J ↦
    {x ∈ normUnitSolutions S α none | (∀ i ∈ J, β U i ≠ 0) ∧ J.Nonempty ∧
      ∑ i ∈ J, β U i * (α (some i) * x (some i)) = 0 ∧
      ∀ I ⊆ J, I.Nonempty → I ≠ J → ∑ i ∈ I, β U i * (α (some i) * x (some i)) ≠ 0} with hX
  have hfin := finite_normUnitSolutions S α none
  have hXfin : ∀ U J, (X U J).Finite := fun U J ↦ hfin.subset fun x hx ↦ hx.1
  have hsub : normUnitSolutions S α none ⊆ ↑(T.biUnion fun U ↦
      (univ : Finset (Finset ι)).biUnion fun J ↦ (hXfin U J).toFinset) := by
    intro x hx
    obtain ⟨U, hU, hyU⟩ := hcov x hx.2.1 hx.2.2.1
    have h0 := hβ U hU _ hyU
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 (hβ0 U hU)
    have hs0 : ∑ i ∈ univ.filter (fun i ↦ β U i ≠ 0), β U i * (α (some i) * x (some i)) = 0 := by
      rw [sum_filter_of_ne fun i _ h ↦ left_ne_zero_of_mul h]
      exact h0
    obtain ⟨J, hJs, hJ, hJ0, hJmin⟩ :=
      exists_subset_nonempty_sum_eq_zero_forall_ne_zero _ ⟨i₀, by simpa using hi₀⟩ hs0
    simp only [coe_biUnion, mem_coe, mem_univ, Set.Finite.coe_toFinset, Set.iUnion_true,
      Set.mem_iUnion, exists_prop]
    exact ⟨U, hU, J, hx, fun i hi ↦ (mem_filter.1 (hJs hi)).2, hJ, hJ0, hJmin⟩
  calc (normUnitSolutions S α none).ncard ≤ _ := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub
    _ ≤ #T * (2 ^ Fintype.card ι * Z ^ 2) := card_biUnion_le_card_mul _ _ _ fun U _ ↦
        (card_biUnion_le_card_mul _ _ _ fun J _ ↦ by
          rw [← Set.ncard_eq_toFinset_card _ (hXfin U J)]
          exact ncard_setOf_minimal_le _ _ IH).trans (by rw [card_univ, Fintype.card_finset])
    _ = _ := by ring

end Step

/-- **The bound of the induction**: `Z(0) = 1` and `Z(m + 1) = Z(m) + L(m) 2^m Z(m)²`, so that
`Z` is monotone and covers both the equations of at most two terms and the step. -/
def unitCount (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => unitCount L m + L m * 2 ^ m * unitCount L m ^ 2

theorem unitCount_mono (L : ℕ → ℕ) : Monotone (unitCount L) :=
  monotone_nat_of_le_succ fun _ ↦ Nat.le_add_right _ _

theorem one_le_unitCount (L : ℕ → ℕ) (m : ℕ) : 1 ≤ unitCount L m :=
  unitCount_mono L (Nat.zero_le m)

/-- **Lemma 6.1 implies Theorem 1.1** (Sch90 §7). If for every `n ≥ 2` the points `y'` of the
solutions of an equation of `n + 1` terms with nonzero coefficients lie in at most `L n` proper
subspaces, then every equation of `m` terms has at most `unitCount L m` normalized solutions. The
field and `S` stay fixed throughout, as they do in the paper. -/
theorem ncard_normUnitSolutions_le_unitCount (S : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℕ → ℕ)
    (hL : ∀ (ι : Type) [Fintype ι], 2 ≤ Fintype.card ι → ∀ α : Option ι → K, (∀ o, α o ≠ 0) →
      ∃ T : Finset (Submodule K (ι → K)), #T ≤ L (Fintype.card ι) ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x : Option ι → Kˣ, (∀ o, x o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
          ∑ o, α o * x o = 0 → ∃ U ∈ T, (fun i ↦ α (some i) * (x (some i) : K)) ∈ U)
    (κ : Type) [Fintype κ] (α : κ → K) (k₀ : κ) :
    (normUnitSolutions S α k₀).ncard ≤ unitCount L (Fintype.card κ) := by
  classical
  suffices H : ∀ N (κ : Type) [Fintype κ], Fintype.card κ ≤ N → ∀ (α : κ → K) (k₀ : κ),
      (normUnitSolutions S α k₀).ncard ≤ unitCount L N from H _ κ le_rfl α k₀
  intro N
  induction N with
  | zero =>
    intro κ _ hκ α k₀
    have := Fintype.card_pos_iff.2 ⟨k₀⟩
    omega
  | succ N ih =>
    intro κ _ hκ α k₀
    by_cases hN : Fintype.card κ ≤ N
    · exact (ih κ hN α k₀).trans (unitCount_mono L (Nat.le_succ N))
    by_cases h2 : Fintype.card κ ≤ 2
    · have := (finite_normUnitSolutions S α k₀).to_subtype
      exact ((Set.ncard_le_one_iff_subsingleton.2 (normUnitSolutions_subsingleton h2)).trans
        (one_le_unitCount L _))
    have : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    by_cases h0 : ∃ k, α k = 0
    · obtain ⟨k, hk⟩ := h0
      rw [normUnitSolutions_eq_empty hk, Set.ncard_empty]
      exact Nat.zero_le _
    push Not at h0
    set e := Equiv.optionSubtypeNe k₀
    have hι : Fintype.card {k // k ≠ k₀} = N := by
      have := Fintype.card_congr e
      rw [Fintype.card_option] at this
      omega
    obtain ⟨T, hT, hTtop, hcov⟩ := hL {k // k ≠ k₀} (by omega) (α ∘ e) fun o ↦ h0 _
    have hstep := ncard_normUnitSolutions_option_le hTtop hcov (Z := unitCount L N)
      fun κ' _ h α' k₀' ↦ ih κ' (hι ▸ h) α' k₀'
    calc (normUnitSolutions S α k₀).ncard
        ≤ (normUnitSolutions S (α ∘ e) (e.symm k₀)).ncard :=
          ncard_normUnitSolutions_le_comp_equiv e
      _ = (normUnitSolutions S (α ∘ e) none).ncard := by
          rw [Equiv.optionSubtypeNe_symm_self]
      _ ≤ #T * 2 ^ Fintype.card {k // k ≠ k₀} * unitCount L N ^ 2 := hstep
      _ ≤ L N * 2 ^ N * unitCount L N ^ 2 := by
          rw [hι]
          gcongr
          exact hι ▸ hT
      _ ≤ unitCount L (N + 1) := Nat.le_add_left _ _

end NumberField
