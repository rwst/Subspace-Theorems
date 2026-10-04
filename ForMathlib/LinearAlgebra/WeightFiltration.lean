/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Used only inside proofs.
import Mathlib.Tactic.Linarith

/-!
# The filtration of a supermodular weight on subspaces

Let `w` be a real function on the subspaces of a finite-dimensional vector space that is
*supermodular*, `w U₁ + w U₂ ≤ w (U₁ ⊓ U₂) + w (U₁ ⊔ U₂)`, and takes finitely many values. For
subspaces `U < V` put `μ(V, U) = (w V - w U) / (dim V - dim U)`, the slope of the segment from
`P(U) = (dim U, w U)` to `P(V)` (`Submodule.weightSlope w U V`). Then:

* among the proper subspaces of `V` minimizing `μ(V, ·)` there is a least one, the
  *destabilizing subspace* of `V` (EF13 Lemma 15.2 (i));
* for this `T` and any `U < V`, `μ(V, U ⊓ T) ≤ μ(V, U)` (EF13 Lemma 15.2 (ii));
* there is a unique filtration `0 = T₀ < T₁ < ⋯ < T_r = V` whose points `P(T_l)` are the vertices
  of the upper convex hull of the `P(U)`, `U ≤ V` (EF13 Lemma 15.4). It is built downward, each
  `T_{l-1}` being the destabilizing subspace of `T_l`.

This is an adaptation of the Harder–Narasimhan filtration of G. Faltings and G. Wüstholz,
*Diophantine approximations on projective spaces*, Invent. Math. **116** (1994), 109–138, made by
J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §15. There `w` is the weight `w_{L,c}` of a system of linear
forms with exponents, which is supermodular by EF13 Lemma 15.1.

## Main definitions

* `Submodule.IsSupermodularWeight w`: `w` is supermodular.
* `Submodule.weightSlope w U V`: the slope `μ(V, U)`.
* `Submodule.IsDestabilizing w V T`: `T` is the least proper subspace of `V` minimizing `μ(V, ·)`.
* `Submodule.IsWeightFiltration w V r T`: `T 0 = ⊥ < T 1 < ⋯ < T r = V` with strictly decreasing
  slopes, and every `P(U)`, `U ≤ V`, on or below each line through consecutive `P(T_l)`.

## Main results

* `Submodule.exists_isDestabilizing`, `Submodule.IsDestabilizing.unique`: EF13 Lemma 15.2 (i).
* `Submodule.weightSlope_inf_le`: EF13 Lemma 15.2 (ii).
* `Submodule.exists_isWeightFiltration`, `Submodule.IsWeightFiltration.unique`: EF13 Lemma 15.4.
* `Submodule.IsDestabilizing.map_eq`, `Submodule.IsWeightFiltration.map_eq`: a lattice automorphism
  of the subspaces that preserves dimensions and `w` and fixes `V` fixes the destabilizing subspace
  and the filtration. Applied to Galois conjugation this gives "defined over `K`" in EF13.

## Implementation notes

EF13 describes the filtration through the upper convex hull `C(V)` of the points `P(U)`. Here the
convex hull is not formed: the points `P(T_l)` are the vertices of the boundary of `C(V)` exactly
when the slopes `μ(T_{l+1}, T_l)` strictly decrease and every `P(U)` lies on or below each of the
lines through `P(T_l)` and `P(T_{l+1})` (the boundary is concave, so it is the minimum of these
lines). That is the definition of `IsWeightFiltration`.

EF13 takes `T` of minimal dimension among the minimizers; by Lemma 15.2 (ii) such a `T` is
contained in every minimizer, and `IsDestabilizing` records this stronger form, from which the
uniqueness is immediate.
-/

@[expose] public section

open Module

namespace Submodule

variable {k M : Type*} [DivisionRing k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- A real function on subspaces is **supermodular**: `w U₁ + w U₂ ≤ w (U₁ ⊓ U₂) + w (U₁ ⊔ U₂)`
(EF13 Lemma 15.1 for the weight `w_{L,c}`). -/
def IsSupermodularWeight (w : Submodule k M → ℝ) : Prop :=
  ∀ U₁ U₂ : Submodule k M, w U₁ + w U₂ ≤ w (U₁ ⊓ U₂) + w (U₁ ⊔ U₂)

/-- **The slope** `μ(V, U) = (w V - w U) / (dim V - dim U)` of EF13 (15.6): the slope of the
segment from `(dim U, w U)` to `(dim V, w V)`. -/
noncomputable def weightSlope (w : Submodule k M → ℝ) (U V : Submodule k M) : ℝ :=
  (w V - w U) / ((finrank k V : ℝ) - finrank k U)

variable {w : Submodule k M → ℝ} {U V T : Submodule k M}

omit [FiniteDimensional k M] in
theorem IsSupermodularWeight.add {w' : Submodule k M → ℝ} (hw : IsSupermodularWeight w)
    (hw' : IsSupermodularWeight w') : IsSupermodularWeight (fun U ↦ w U + w' U) := fun U₁ U₂ ↦ by
  have := hw U₁ U₂
  have := hw' U₁ U₂
  linarith

omit [FiniteDimensional k M] in
theorem IsSupermodularWeight.sum {α : Type*} (s : Finset α) {w : α → Submodule k M → ℝ}
    (hw : ∀ a ∈ s, IsSupermodularWeight (w a)) :
    IsSupermodularWeight (fun U ↦ ∑ a ∈ s, w a U) := fun U₁ U₂ ↦ by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a ha ↦ hw a ha U₁ U₂

theorem finrank_sub_finrank_pos (h : U < V) : (0 : ℝ) < finrank k V - finrank k U :=
  sub_pos.2 (Nat.cast_lt.2 (finrank_lt_finrank_of_lt h))

theorem weightSlope_mul (h : U < V) :
    weightSlope w U V * ((finrank k V : ℝ) - finrank k U) = w V - w U :=
  div_mul_cancel₀ _ (finrank_sub_finrank_pos h).ne'

theorem le_weightSlope_iff (h : U < V) {μ : ℝ} :
    μ ≤ weightSlope w U V ↔ μ * ((finrank k V : ℝ) - finrank k U) ≤ w V - w U :=
  le_div_iff₀ (finrank_sub_finrank_pos h)

theorem lt_weightSlope_iff (h : U < V) {μ : ℝ} :
    μ < weightSlope w U V ↔ μ * ((finrank k V : ℝ) - finrank k U) < w V - w U :=
  lt_div_iff₀ (finrank_sub_finrank_pos h)

theorem weightSlope_le_iff (h : U < V) {μ : ℝ} :
    weightSlope w U V ≤ μ ↔ w V - w U ≤ μ * ((finrank k V : ℝ) - finrank k U) :=
  div_le_iff₀ (finrank_sub_finrank_pos h)

/-- **EF13 Lemma 15.2 (ii)**: if `T < V` minimizes `μ(V, ·)`, then `μ(V, U ⊓ T) ≤ μ(V, U)` for
every `U < V`. -/
theorem weightSlope_inf_le (hw : IsSupermodularWeight w) (hT : T < V)
    (hmin : ∀ U < V, weightSlope w T V ≤ weightSlope w U V) (hU : U < V) :
    weightSlope w (U ⊓ T) V ≤ weightSlope w U V := by
  have hUT : U ⊓ T < V := lt_of_le_of_lt inf_le_right hT
  have hA : ∀ W ≤ V, weightSlope w T V * ((finrank k V : ℝ) - finrank k W) ≤ w V - w W := by
    intro W hW
    rcases hW.lt_or_eq with hW | rfl
    · exact (le_weightSlope_iff hW).1 (hmin W hW)
    · simp
  have h1 := hA (U ⊔ T) (sup_le hU.le hT.le)
  have h2 := weightSlope_mul (w := w) hT
  have h3 := weightSlope_mul (w := w) hU
  have h4 := hw U T
  have h5 : (finrank k ↥(U ⊔ T) : ℝ) + finrank k ↥(U ⊓ T) = finrank k U + finrank k T := by
    exact_mod_cast finrank_sup_add_finrank_inf_eq U T
  have h6 : (finrank k ↥(U ⊓ T) : ℝ) ≤ finrank k U := Nat.cast_le.2 (finrank_mono inf_le_left)
  have h7 := hmin U hU
  have h8 := congrArg (weightSlope w T V * ·) h5
  simp only [mul_add] at h8
  rw [weightSlope_le_iff hUT]
  nlinarith [mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 h6)]

/-- **The destabilizing subspace** `T` of `V` (EF13 Lemma 15.2 (i), and (2.21) for `V = Ωⁿ`): a
proper subspace minimizing `μ(V, ·)` and contained in every other minimizer. -/
structure IsDestabilizing (w : Submodule k M → ℝ) (V T : Submodule k M) : Prop where
  lt : T < V
  le : ∀ U < V, weightSlope w T V ≤ weightSlope w U V
  least : ∀ U < V, weightSlope w U V = weightSlope w T V → T ≤ U

/-- **EF13 Lemma 15.2 (i)**, existence: a nonzero subspace has a destabilizing subspace. -/
theorem exists_isDestabilizing (hw : IsSupermodularWeight w) (hfin : (Set.range w).Finite)
    (hV : V ≠ ⊥) : ∃ T, IsDestabilizing w V T := by
  classical
  set S := {x | ∃ U < V, weightSlope w U V = x}
  have hS : S.Finite := by
    refine (Set.Finite.image2 (fun a (b : ℕ) ↦ (w V - a) / ((finrank k V : ℝ) - b)) hfin
      (Set.finite_Iio (finrank k M + 1))).subset ?_
    rintro _ ⟨U, -, rfl⟩
    exact ⟨w U, ⟨U, rfl⟩, finrank k U, Nat.lt_succ_of_le (Submodule.finrank_le U), rfl⟩
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hmin⟩ :=
    Set.exists_min_image S id hS ⟨_, ⊥, bot_lt_iff_ne_bot.2 hV, rfl⟩
  have hmin' : ∀ U < V, weightSlope w U₀ V ≤ weightSlope w U V := fun U hU ↦ hmin _ ⟨U, hU, rfl⟩
  have hex : ∃ d, ∃ U < V, weightSlope w U V = weightSlope w U₀ V ∧ finrank k U = d :=
    ⟨_, U₀, hU₀, rfl, rfl⟩
  obtain ⟨T, hT, hTμ, hTd⟩ := Nat.find_spec hex
  have hTmin : ∀ U < V, weightSlope w T V ≤ weightSlope w U V := fun U hU ↦
    hTμ ▸ hmin' U hU
  refine ⟨T, hT, hTmin, fun U hU hUμ ↦ ?_⟩
  have hUT : U ⊓ T < V := lt_of_le_of_lt inf_le_right hT
  have h2 : weightSlope w (U ⊓ T) V = weightSlope w U₀ V :=
    le_antisymm ((weightSlope_inf_le hw hT hTmin hU).trans (hUμ.trans hTμ).le) (hmin' _ hUT)
  have h3 : Nat.find hex ≤ finrank k ↥(U ⊓ T) := Nat.find_min' hex ⟨_, hUT, h2, rfl⟩
  have h4 : U ⊓ T = T := eq_of_le_of_finrank_le inf_le_right (hTd.trans_le h3)
  exact h4 ▸ inf_le_left

omit [FiniteDimensional k M] in
/-- **EF13 Lemma 15.2 (i)**, uniqueness. -/
theorem IsDestabilizing.unique {T' : Submodule k M} (h : IsDestabilizing w V T)
    (h' : IsDestabilizing w V T') : T = T' :=
  le_antisymm (h.least _ h'.lt (le_antisymm (h'.le _ h.lt) (h.le _ h'.lt)))
    (h'.least _ h.lt (le_antisymm (h.le _ h'.lt) (h'.le _ h.lt)))

/-- Below the destabilizing subspace `T` of `V` the slopes are steeper: `μ(V, T) < μ(T, A)` for
`A < T`. -/
theorem IsDestabilizing.weightSlope_lt (h : IsDestabilizing w V T) {A : Submodule k M}
    (hA : A < T) : weightSlope w T V < weightSlope w A T := by
  have hAV : A < V := hA.trans h.lt
  have h1 : weightSlope w T V < weightSlope w A V :=
    lt_of_le_of_ne (h.le A hAV) fun he ↦ hA.not_ge (h.least A hAV he.symm)
  rw [lt_weightSlope_iff hAV] at h1
  rw [lt_weightSlope_iff hA]
  have h2 := weightSlope_mul (w := w) h.lt
  linarith

omit [FiniteDimensional k M] in
/-- **Transport of the destabilizing subspace** along an isomorphism of the lattices of subspaces
of two spaces that preserves dimensions and carries `w` to `w'`. -/
theorem IsDestabilizing.orderIso {M' : Type*} [AddCommGroup M'] [Module k M']
    {w' : Submodule k M' → ℝ} (h : IsDestabilizing w V T)
    (e' : Submodule k M ≃o Submodule k M') (he' : ∀ U, finrank k ↥(e' U) = finrank k U)
    (hw' : ∀ U, w' (e' U) = w U) : IsDestabilizing w' (e' V) (e' T) := by
  have hs : ∀ A B, weightSlope w' (e' A) (e' B) = weightSlope w A B := fun A B ↦ by
    simp only [weightSlope, he', hw']
  refine ⟨e'.lt_iff_lt.2 h.lt, fun U hU ↦ ?_, fun U hU hUμ ↦ ?_⟩
  · rw [← e'.apply_symm_apply U] at hU ⊢
    rw [hs, hs]
    exact h.le _ (e'.lt_iff_lt.1 hU)
  · rw [← e'.apply_symm_apply U] at hU hUμ ⊢
    rw [hs, hs] at hUμ
    exact e'.monotone (h.least _ (e'.lt_iff_lt.1 hU) hUμ)

section Map

variable (e : Submodule k M ≃o Submodule k M) (he : ∀ U, finrank k ↥(e U) = finrank k U)
  (hwe : ∀ U, w (e U) = w U)
include he hwe

omit [FiniteDimensional k M] in
theorem weightSlope_orderIso (A B : Submodule k M) :
    weightSlope w (e A) (e B) = weightSlope w A B := by
  simp only [weightSlope, he, hwe]

omit [FiniteDimensional k M] in
/-- A lattice automorphism of the subspaces preserving dimensions and `w` and fixing `V` maps the
destabilizing subspace of `V` to a destabilizing subspace. -/
theorem IsDestabilizing.map (h : IsDestabilizing w V T) (hV : e V = V) :
    IsDestabilizing w V (e T) := by
  have hV' : e.symm V = V := by rw [e.symm_apply_eq, hV]
  have hs : ∀ U, weightSlope w U V = weightSlope w (e.symm U) V := fun U ↦ by
    conv_lhs => rw [← e.apply_symm_apply U, ← hV]
    exact weightSlope_orderIso e he hwe _ _
  have hlt : ∀ U < V, e.symm U < V := fun U hU ↦ hV' ▸ e.symm.lt_iff_lt.2 hU
  refine ⟨hV ▸ e.lt_iff_lt.2 h.lt, fun U hU ↦ ?_, fun U hU hUμ ↦ ?_⟩
  · rw [hs U, hs (e T), e.symm_apply_apply]
    exact h.le _ (hlt U hU)
  · rw [hs U, hs (e T), e.symm_apply_apply] at hUμ
    rw [← e.apply_symm_apply U]
    exact e.monotone (h.least _ (hlt U hU) hUμ)

omit [FiniteDimensional k M] in
/-- **The destabilizing subspace is invariant** (EF13 Lemma 15.2 (i), "defined over `K`"). -/
theorem IsDestabilizing.map_eq (h : IsDestabilizing w V T) (hV : e V = V) : e T = T :=
  (h.map e he hwe hV).unique h

end Map

/-- **The filtration of `V` with respect to `w`** (EF13 Lemma 15.4): `T 0 = ⊥ < T 1 < ⋯ < T r = V`,
the slopes `μ(T_{l+1}, T_l)` strictly decrease, and for each `l < r` every point `(dim U, w U)`,
`U ≤ V`, lies on or below the line through `(dim T_l, w T_l)` and `(dim T_{l+1}, w T_{l+1})`.
So the `(dim T_l, w T_l)` are the vertices of the upper convex hull of the points
`(dim U, w U)`. Values of `T` beyond `r` are irrelevant. -/
structure IsWeightFiltration (w : Submodule k M → ℝ) (V : Submodule k M) (r : ℕ)
    (T : ℕ → Submodule k M) : Prop where
  zero : T 0 = ⊥
  top : T r = V
  lt : ∀ l < r, T l < T (l + 1)
  slope_lt : ∀ l, l + 2 ≤ r →
    weightSlope w (T (l + 1)) (T (l + 2)) < weightSlope w (T l) (T (l + 1))
  le : ∀ l < r, ∀ U ≤ V,
    w U ≤ w (T l) + weightSlope w (T l) (T (l + 1)) * ((finrank k U : ℝ) - finrank k (T l))

namespace IsWeightFiltration

variable {r : ℕ} {T : ℕ → Submodule k M}

omit [FiniteDimensional k M] in
theorem mono (h : IsWeightFiltration w V r T) {l l' : ℕ} (hl : l ≤ l') (hl' : l' ≤ r) :
    T l ≤ T l' := by
  induction l', hl using Nat.le_induction with
  | base => exact le_rfl
  | succ l' _ ih => exact (ih (by omega)).trans (h.lt l' (by omega)).le

omit [FiniteDimensional k M] in
theorem le_top (h : IsWeightFiltration w V r T) {l : ℕ} (hl : l ≤ r) : T l ≤ V :=
  h.top ▸ h.mono hl le_rfl

omit [FiniteDimensional k M] in
theorem bot_lt (h : IsWeightFiltration w V r T) (hr : 0 < r) : ⊥ < V :=
  h.zero ▸ (h.lt 0 hr).trans_le (h.le_top hr)

omit [FiniteDimensional k M] in
theorem weightSlope_anti (h : IsWeightFiltration w V r T) {l l' : ℕ} (hl : l ≤ l')
    (hl' : l' < r) :
    weightSlope w (T l') (T (l' + 1)) ≤ weightSlope w (T l) (T (l + 1)) := by
  induction l', hl using Nat.le_induction with
  | base => exact le_rfl
  | succ l' _ ih => exact (h.slope_lt l' (by omega)).le.trans (ih (by omega))

omit [FiniteDimensional k M] in
/-- Dropping the top: `T 0 < ⋯ < T s` is the filtration of `T s`. -/
theorem restrict {s : ℕ} (h : IsWeightFiltration w V (s + 1) T) :
    IsWeightFiltration w (T s) s T where
  zero := h.zero
  top := rfl
  lt l hl := h.lt l (by omega)
  slope_lt l hl := h.slope_lt l (by omega)
  le l hl U hU := h.le l (by omega) U (hU.trans (h.le_top (by omega)))

/-- The space preceding `V` in the filtration is the destabilizing subspace of `V`. -/
theorem isDestabilizing (hw : IsSupermodularWeight w) {s : ℕ}
    (h : IsWeightFiltration w V (s + 1) T) :
    IsDestabilizing w V (T s) := by
  have hlt : T s < V := h.top ▸ h.lt s (by omega)
  have hsV : weightSlope w (T s) (T (s + 1)) = weightSlope w (T s) V := by rw [h.top]
  have hle : ∀ U < V, weightSlope w (T s) V ≤ weightSlope w U V := by
    intro U hU
    rw [le_weightSlope_iff hU]
    have h1 := h.le s (by omega) U hU.le
    rw [hsV] at h1
    have h2 := weightSlope_mul (w := w) hlt
    linarith
  -- A minimizer has dimension at least `dim T s`.
  have hdim : ∀ U < V, weightSlope w U V = weightSlope w (T s) V →
      (finrank k (T s) : ℝ) ≤ finrank k U := by
    intro U hU hUμ
    refine not_lt.1 fun hd ↦ ?_
    rcases s with _ | t
    · rw [h.zero, finrank_bot, Nat.cast_zero] at hd
      exact (Nat.cast_nonneg _).not_gt hd
    · have hσ := h.slope_lt t (by omega)
      rw [h.top] at hσ
      have h1 := h.le t (by omega) U hU.le
      have h2 := weightSlope_mul (w := w) (h.lt t (by omega))
      have h3 := weightSlope_mul (w := w) hU
      have h4 := weightSlope_mul (w := w) hlt
      rw [hUμ] at h3
      nlinarith [mul_pos (sub_pos.2 hσ) (sub_pos.2 hd)]
  refine ⟨hlt, hle, fun U hU hUμ ↦ ?_⟩
  have hUT : U ⊓ T s < V := lt_of_le_of_lt inf_le_right hlt
  have h1 : weightSlope w (U ⊓ T s) V = weightSlope w (T s) V :=
    le_antisymm ((weightSlope_inf_le hw hlt hle hU).trans hUμ.le) (hle _ hUT)
  have h2 := hdim _ hUT h1
  have h3 : U ⊓ T s = T s := eq_of_le_of_finrank_le inf_le_right (by exact_mod_cast h2)
  exact h3 ▸ inf_le_left

/-- **EF13 Lemma 15.4**, uniqueness: two filtrations of `V` have the same length and agree up
to it. -/
theorem unique (hw : IsSupermodularWeight w) {r r' : ℕ} {T T' : ℕ → Submodule k M}
    (h : IsWeightFiltration w V r T) (h' : IsWeightFiltration w V r' T') :
    r = r' ∧ ∀ l ≤ r, T l = T' l := by
  induction r generalizing V r' with
  | zero =>
    have hV : V = ⊥ := h.top.symm.trans h.zero
    obtain rfl : r' = 0 := Nat.eq_zero_of_not_pos fun hr ↦ (h'.bot_lt hr).ne' hV
    exact ⟨rfl, fun l hl ↦ by rw [Nat.le_zero.1 hl, h.zero, h'.zero]⟩
  | succ s ih =>
    obtain ⟨s', rfl⟩ : ∃ s', r' = s' + 1 :=
      Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun hr ↦
        (h.bot_lt s.succ_pos).ne' (h'.top.symm.trans (hr ▸ h'.zero)))
    have hTs : T s = T' s' := (h.isDestabilizing hw).unique (h'.isDestabilizing hw)
    have h'' := h'.restrict
    rw [← hTs] at h''
    obtain ⟨rfl, hl⟩ := ih h.restrict h''
    refine ⟨rfl, fun l hl' ↦ ?_⟩
    rcases hl'.lt_or_eq with hl' | rfl
    · exact hl l (by omega)
    · rw [h.top, h'.top]

omit [FiniteDimensional k M] in
/-- The filtration is mapped to a filtration by a lattice automorphism of the subspaces preserving
dimensions and `w` and fixing `V`. -/
theorem map (h : IsWeightFiltration w V r T) (e : Submodule k M ≃o Submodule k M)
    (he : ∀ U, finrank k ↥(e U) = finrank k U) (hwe : ∀ U, w (e U) = w U) (hV : e V = V) :
    IsWeightFiltration w V r (fun l ↦ e (T l)) where
  zero := by simp [h.zero]
  top := by rw [h.top, hV]
  lt l hl := e.lt_iff_lt.2 (h.lt l hl)
  slope_lt l hl := by
    simpa only [weightSlope_orderIso e he hwe] using h.slope_lt l hl
  le l hl U hU := by
    have hV' : e.symm V = V := by rw [e.symm_apply_eq, hV]
    have hU' : e.symm U ≤ V := hV' ▸ e.symm.monotone hU
    have := h.le l hl _ hU'
    rw [weightSlope_orderIso e he hwe, he, hwe]
    rwa [← hwe, ← he, e.apply_symm_apply] at this

omit [FiniteDimensional k M] in
/-- **Transport of the filtration** along an isomorphism of the lattices of subspaces of two spaces
that preserves dimensions and carries `w` to `w'`. -/
theorem orderIso {M' : Type*} [AddCommGroup M'] [Module k M'] {w' : Submodule k M' → ℝ}
    (h : IsWeightFiltration w V r T) (e' : Submodule k M ≃o Submodule k M')
    (he' : ∀ U, finrank k ↥(e' U) = finrank k U) (hw' : ∀ U, w' (e' U) = w U) :
    IsWeightFiltration w' (e' V) r (fun l ↦ e' (T l)) where
  zero := by simp [h.zero]
  top := by rw [h.top]
  lt l hl := e'.lt_iff_lt.2 (h.lt l hl)
  slope_lt l hl := by
    simpa only [weightSlope, he', hw'] using h.slope_lt l hl
  le l hl U hU := by
    have hU' : e'.symm U ≤ V := by
      rw [← e'.symm_apply_apply V]
      exact e'.symm.monotone hU
    have := h.le l hl _ hU'
    rw [← e'.apply_symm_apply U]
    simpa only [weightSlope, he', hw'] using this

/-- **The filtration is invariant** (EF13 Lemma 15.4, "defined over `K`"). -/
theorem map_eq (hw : IsSupermodularWeight w) (h : IsWeightFiltration w V r T)
    (e : Submodule k M ≃o Submodule k M) (he : ∀ U, finrank k ↥(e U) = finrank k U)
    (hwe : ∀ U, w (e U) = w U) (hV : e V = V) {l : ℕ} (hl : l ≤ r) : e (T l) = T l :=
  ((h.map e he hwe hV).unique hw h).2 l hl

end IsWeightFiltration

/-- **EF13 Lemma 15.4**, existence: every subspace has a filtration with respect to a supermodular
weight with finitely many values. -/
theorem exists_isWeightFiltration (hw : IsSupermodularWeight w) (hfin : (Set.range w).Finite)
    (V : Submodule k M) : ∃ r T, IsWeightFiltration w V r T := by
  induction hn : finrank k V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact ⟨0, fun _ ↦ ⊥, rfl, rfl, by simp, by simp, by simp⟩
  obtain ⟨D, hD⟩ := exists_isDestabilizing hw hfin hV
  obtain ⟨r, T, hT⟩ := ih _ (hn ▸ finrank_lt_finrank_of_lt hD.lt) D rfl
  have hDr : T r = D := hT.top
  -- `μ(V, D)` is below every slope of the filtration of `D`.
  have hμ : ∀ l < r, weightSlope w D V < weightSlope w (T l) (T (l + 1)) := by
    intro l hl
    obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := Nat.exists_eq_add_one.2 (by omega)
    refine lt_of_lt_of_le ?_ (hT.weightSlope_anti (Nat.le_of_lt_succ hl) (by omega))
    rw [hDr]
    exact hD.weightSlope_lt (hDr ▸ hT.lt q (by omega))
  have hD' := weightSlope_mul (w := w) hD.lt
  have hDle : ∀ U ≤ V, w U ≤ w D + weightSlope w D V * ((finrank k U : ℝ) - finrank k D) := by
    intro U hU
    rcases hU.lt_or_eq with hU | rfl
    · have := (le_weightSlope_iff hU).1 (hD.le U hU)
      linarith
    · linarith
  obtain ⟨T', hT', hT'r⟩ : ∃ T' : ℕ → Submodule k M, (∀ l ≤ r, T' l = T l) ∧ T' (r + 1) = V :=
    ⟨fun l ↦ if l ≤ r then T l else V, fun l hl ↦ by simp [hl], by simp⟩
  refine ⟨r + 1, T', ?_, hT'r, ?_, ?_, ?_⟩
  · rw [hT' 0 (Nat.zero_le r), hT.zero]
  · intro l hl
    rcases (Nat.lt_succ_iff.1 hl).lt_or_eq with hl | rfl
    · rw [hT' l hl.le, hT' (l + 1) hl]
      exact hT.lt l hl
    · rw [hT' l le_rfl, hT'r, hDr]
      exact hD.lt
  · intro l hl
    rw [hT' l (by omega), hT' (l + 1) (by omega)]
    rcases (show l + 2 ≤ r ∨ l + 1 = r by omega) with hl | hl
    · rw [hT' (l + 2) hl]
      exact hT.slope_lt l hl
    · rw [show l + 2 = r + 1 by omega, hT'r, hl, hDr]
      exact hD.weightSlope_lt (hDr ▸ hl ▸ hT.lt l (by omega))
  · intro l hl U hU
    rcases (Nat.lt_succ_iff.1 hl).lt_or_eq with hl | rfl
    · rw [hT' l hl.le, hT' (l + 1) hl]
      set A := T l
      set σ := weightSlope w (T l) (T (l + 1))
      have hσ := hμ l hl
      have hfD := hT.le l hl D le_rfl
      -- The line through `P(T_l)`, `P(T_{l+1})` passes above `P(V)`.
      have hfV : w V ≤ w A + σ * ((finrank k V : ℝ) - finrank k A) := by
        have hDV : (finrank k D : ℝ) ≤ finrank k V := Nat.cast_le.2 (finrank_mono hD.lt.le)
        nlinarith [mul_nonneg (sub_nonneg.2 hσ.le) (sub_nonneg.2 hDV)]
      rcases hU.lt_or_eq with hU | rfl
      · have hUD : U ⊓ D < V := lt_of_le_of_lt inf_le_right hD.lt
        have hs := weightSlope_inf_le hw hD.lt hD.le hU
        have hfa := hT.le l hl (U ⊓ D) inf_le_right
        have h1 := weightSlope_mul (w := w) hUD
        have h2 := weightSlope_mul (w := w) hU
        have hax : (finrank k ↥(U ⊓ D) : ℝ) ≤ finrank k U :=
          Nat.cast_le.2 (finrank_mono inf_le_left)
        have hxn : (finrank k U : ℝ) ≤ finrank k V := Nat.cast_le.2 (finrank_mono hU.le)
        have han := finrank_sub_finrank_pos hUD
        set a : ℝ := (finrank k ↥(U ⊓ D) : ℝ)
        set x : ℝ := (finrank k U : ℝ)
        set n : ℝ := (finrank k V : ℝ)
        set s := weightSlope w (U ⊓ D) V
        -- `g y = w V - s (n - y) - (w A + σ (y - dim A))` is affine, `≤ 0` at `a` and `n`.
        have key : (n - a) * (w V - s * (n - x) - (w A + σ * (x - finrank k A))) ≤ 0 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hxn) (sub_nonneg.2 hfa),
            mul_nonneg (sub_nonneg.2 hax) (sub_nonneg.2 hfV)]
        have key' : w V - s * (n - x) - (w A + σ * (x - finrank k A)) ≤ 0 :=
          nonpos_of_mul_nonpos_right key han
        nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hxn)]
      · exact hfV
    · rw [hT' l le_rfl, hT'r, hDr]
      exact hDle U hU

end Submodule
