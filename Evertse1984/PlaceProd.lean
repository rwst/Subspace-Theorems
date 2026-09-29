/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SAdicHeight
public import Mathlib.NumberTheory.NumberField.House

-- Used only inside proofs.
import DiophantineApproximation.NormForm

/-!
# Products over a set of places, and the house of a tuple

Evertse (1984) writes every inequality with his normalized absolute values `‖·‖_v`, one for each
place `v` of the number field `K`, with `‖α‖_v = |α|_p ^ [K_v : ℚ_p]` on `ℚ`, so that the product
formula holds. In Mathlib's normalization this is `w α ^ mult w` at an infinite place `w` and
`FinitePlace.mk P α` at the finite place of a prime `P`.

`NumberField.placeProd S T g` is the product of `g v`, in this normalization, over the places `v`
of `T` that lie in `S∞ ∪ S`. Evertse's `T` is a subset of `S`; here `T` is any set of absolute
values, and only its places in `S∞ ∪ S` count. With `T = Set.univ` and `g v = v a` it is his
`∏_{v ∈ S} ‖a‖_v`, which is at least `1` for a nonzero algebraic integer `a`.

Evertse's size `‖x‖` of a tuple of algebraic integers is the largest absolute value of a
conjugate of a coordinate, `⨆ i, house (x i)`.

## Main definitions

* `NumberField.placeProd`: the product over the places of `T` in `S∞ ∪ S`.
* `NumberField.relevantPlaces`: the places of `S∞ ∪ S`, as absolute values.

## Main results

* `NumberField.placeProd_mul`, `NumberField.placeProd_le_placeProd`,
  `NumberField.placeProd_inter_mul_diff`: the product is multiplicative, monotone, and splits
  along any set `Q`.
* `NumberField.placeProd_inter_relevantPlaces`: only the places of `S∞ ∪ S` count.
* `NumberField.one_le_placeProd_univ`: the product formula for a nonzero algebraic integer.
* `NumberField.mulHeight_le_iSup_house_pow`: `H(x) ≤ ‖x‖ ^ [K : ℚ]` for algebraic integers.
* `NumberField.exists_pos_forall_le_of_finite`: finitely many cases, one constant.
* `NumberField.exists_subset_sum_eq_forall_ne_zero`: a minimal subsum has no vanishing subsum.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §1.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The product over the places of `T` in `S∞ ∪ S`** of `g`, in Evertse's normalization:
`g w ^ mult w` at an infinite place `w`, `g v` at the finite place `v` of a prime of `S`.
Places of `T` outside `S∞ ∪ S` do not count. -/
noncomputable def placeProd (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (AbsoluteValue K ℝ))
    (g : AbsoluteValue K ℝ → ℝ) : ℝ :=
  (∏ v : InfinitePlace K, T.mulIndicator g v.1 ^ v.mult) *
    ∏ P ∈ S, T.mulIndicator g (FinitePlace.mk P).1

/-- **The places of `S∞ ∪ S`**, as absolute values of `K`. -/
def relevantPlaces (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AbsoluteValue K ℝ) :=
  Set.range (fun v : InfinitePlace K ↦ v.1) ∪ (fun P ↦ (FinitePlace.mk P).1) '' (S : Set _)

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (AbsoluteValue K ℝ))

/-- There are finitely many places in `S∞ ∪ S`. -/
theorem finite_relevantPlaces : (relevantPlaces S).Finite :=
  (Set.finite_range _).union (S.finite_toSet.image _)

/-- **Only the places of `S∞ ∪ S` count.** -/
theorem placeProd_inter_relevantPlaces (g : AbsoluteValue K ℝ → ℝ) :
    placeProd S (T ∩ relevantPlaces S) g = placeProd S T g := by
  unfold placeProd
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    have hv : v.1 ∈ relevantPlaces S := by unfold relevantPlaces; exact Or.inl ⟨v, rfl⟩
    by_cases hT : v.1 ∈ T
    · rw [Set.mulIndicator_of_mem (Set.mem_inter hT hv), Set.mulIndicator_of_mem hT]
    · rw [Set.mulIndicator_of_notMem (fun h ↦ hT h.1), Set.mulIndicator_of_notMem hT]
  · refine Finset.prod_congr rfl fun P hP ↦ ?_
    have hv : (FinitePlace.mk P).1 ∈ relevantPlaces S := by
      unfold relevantPlaces; exact Or.inr ⟨P, hP, rfl⟩
    by_cases hT : (FinitePlace.mk P).1 ∈ T
    · rw [Set.mulIndicator_of_mem (Set.mem_inter hT hv), Set.mulIndicator_of_mem hT]
    · rw [Set.mulIndicator_of_notMem (fun h ↦ hT h.1), Set.mulIndicator_of_notMem hT]

/-- The product is multiplicative in the function. -/
theorem placeProd_mul (f g : AbsoluteValue K ℝ → ℝ) :
    placeProd S T (fun v ↦ f v * g v) = placeProd S T f * placeProd S T g := by
  simp only [placeProd, Set.mulIndicator_mul, mul_pow, Finset.prod_mul_distrib]
  ring

/-- Equal on `T`, equal products. -/
theorem placeProd_congr {f g : AbsoluteValue K ℝ → ℝ} (h : ∀ v ∈ T, f v = g v) :
    placeProd S T f = placeProd S T g := by
  unfold placeProd
  rw [Set.mulIndicator_congr h]

omit [NumberField K] in
private theorem mulIndicator_nonneg {f : AbsoluteValue K ℝ → ℝ} (hf : ∀ v ∈ T, 0 ≤ f v)
    (v : AbsoluteValue K ℝ) : 0 ≤ T.mulIndicator f v := by
  by_cases hv : v ∈ T
  · rw [Set.mulIndicator_of_mem hv]; exact hf v hv
  · rw [Set.mulIndicator_of_notMem hv]; exact zero_le_one

omit [NumberField K] in
private theorem mulIndicator_pos {f : AbsoluteValue K ℝ → ℝ} (hf : ∀ v ∈ T, 0 < f v)
    (v : AbsoluteValue K ℝ) : 0 < T.mulIndicator f v := by
  by_cases hv : v ∈ T
  · rw [Set.mulIndicator_of_mem hv]; exact hf v hv
  · rw [Set.mulIndicator_of_notMem hv]; exact zero_lt_one

/-- Nonnegative on `T`, nonnegative product. -/
theorem placeProd_nonneg {f : AbsoluteValue K ℝ → ℝ} (hf : ∀ v ∈ T, 0 ≤ f v) :
    0 ≤ placeProd S T f :=
  mul_nonneg (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (mulIndicator_nonneg T hf _) _)
    (Finset.prod_nonneg fun _ _ ↦ mulIndicator_nonneg T hf _)

/-- Positive on `T`, positive product. -/
theorem placeProd_pos {f : AbsoluteValue K ℝ → ℝ} (hf : ∀ v ∈ T, 0 < f v) :
    0 < placeProd S T f :=
  mul_pos (Finset.prod_pos fun _ _ ↦ pow_pos (mulIndicator_pos T hf _) _)
    (Finset.prod_pos fun _ _ ↦ mulIndicator_pos T hf _)

/-- **The product is monotone** in a function nonnegative on `T`. -/
theorem placeProd_le_placeProd {f g : AbsoluteValue K ℝ → ℝ} (hf : ∀ v ∈ T, 0 ≤ f v)
    (hfg : ∀ v ∈ T, f v ≤ g v) : placeProd S T f ≤ placeProd S T g := by
  have h0 := mulIndicator_nonneg T hf
  have h1 : ∀ v, T.mulIndicator f v ≤ T.mulIndicator g v := fun v ↦ by
    by_cases hv : v ∈ T
    · rw [Set.mulIndicator_of_mem hv, Set.mulIndicator_of_mem hv]; exact hfg v hv
    · rw [Set.mulIndicator_of_notMem hv, Set.mulIndicator_of_notMem hv]
  exact mul_le_mul
    (Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg (h0 _) _) fun _ _ ↦
      pow_le_pow_left₀ (h0 _) (h1 _) _)
    (Finset.prod_le_prod₀ (fun _ _ ↦ h0 _) fun _ _ ↦ h1 _) (Finset.prod_nonneg fun _ _ ↦ h0 _)
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg ((h0 _).trans (h1 _)) _)

/-- **The product splits along any set `Q`.** -/
theorem placeProd_inter_mul_diff (Q : Set (AbsoluteValue K ℝ)) (g : AbsoluteValue K ℝ → ℝ) :
    placeProd S (T ∩ Q) g * placeProd S (T \ Q) g = placeProd S T g := by
  have h : ∀ v, (T ∩ Q).mulIndicator g v * (T \ Q).mulIndicator g v = T.mulIndicator g v :=
    fun v ↦ by
      by_cases hT : v ∈ T <;> by_cases hQ : v ∈ Q <;> simp [hT, hQ]
  simp only [placeProd, ← h, mul_pow, Finset.prod_mul_distrib]
  ring

/-- **The product formula for a nonzero algebraic integer**: its sizes at the places of `S∞ ∪ S`
multiply to at least `1`. -/
theorem one_le_placeProd_univ {a : K} (ha : IsIntegral ℤ a) (ha0 : a ≠ 0) :
    1 ≤ placeProd S Set.univ (fun v ↦ v a) := by
  have h := mulHeight_le_prod_of_forall_mem_integer S (x := fun _ : Unit ↦ a)
    (fun h ↦ ha0 (congrFun h ())) fun _ ↦ mem_integer_of_isIntegral ha
  rw [mulHeight_eq_one_of_subsingleton] at h
  refine h.trans_eq ?_
  simp only [ciSup_const, placeProd, Set.mulIndicator_univ]
  rfl

/-- The house of a coordinate is at most the size of the tuple. -/
theorem house_le_iSup_house {ι : Type*} [Finite ι] (x : ι → K) (i : ι) :
    house (x i) ≤ ⨆ j, house (x j) :=
  le_ciSup (f := fun j ↦ house (x j)) (Finite.bddAbove_range _) i

/-- **The size of a tuple of algebraic integers with a nonzero coordinate is at least `1`.** -/
theorem one_le_iSup_house {ι : Type*} [Finite ι] {x : ι → K} {i : ι} (hi : IsIntegral ℤ (x i))
    (hi0 : x i ≠ 0) : 1 ≤ ⨆ j, house (x j) :=
  (one_le_house_of_isIntegral hi hi0).trans (house_le_iSup_house x i)

/-- **The height of a tuple of algebraic integers is at most its size to the degree**:
`H(x) ≤ ‖x‖ ^ [K : ℚ]`, Evertse's (4)(ii) in the easy direction. -/
theorem mulHeight_le_iSup_house_pow {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (x i)) :
    mulHeight x ≤ (⨆ i, house (x i)) ^ finrank ℚ K := by
  have h := mulHeight_le_prod_of_forall_mem_integer (∅ : Finset (HeightOneSpectrum (𝓞 K))) hx
    fun i ↦ mem_integer_of_isIntegral (hint i)
  rw [Finset.prod_empty, mul_one] at h
  refine h.trans ?_
  rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  have h0 : ∀ v : InfinitePlace K, 0 ≤ ⨆ i, v (x i) :=
    fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (h0 v) _) fun v _ ↦
    pow_le_pow_left₀ (h0 v) ?_ _
  exact ciSup_mono (Finite.bddAbove_range _) fun i ↦
    (v.norm_embedding_eq (x i)).symm.le.trans (norm_embedding_le_house _ _)

/-- **Finitely many cases, one constant.** If each of finitely many cases admits a positive
constant `C` with `C * f x ≤ g x`, then one positive constant serves them all. -/
theorem exists_pos_forall_le_of_finite {α β : Type*} {s : Set β} (hs : s.Finite)
    {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) {A : β → α → Prop}
    (hA : ∀ b ∈ s, ∃ C > 0, ∀ x, A b x → C * f x ≤ g x) :
    ∃ C > 0, ∀ x, (∃ b ∈ s, A b x) → C * f x ≤ g x := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun x ⟨b, hb, _⟩ ↦ absurd hb (by simp)⟩
  | insert a t _ ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih t.finite_toSet fun b hb ↦ hA b (by simp [Finset.mem_coe.mp hb])
    obtain ⟨C₂, hC₂, h₂⟩ := hA a (by simp)
    refine ⟨min C₁ C₂, lt_min hC₁ hC₂, fun x ⟨b, hb, hbx⟩ ↦ ?_⟩
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hf x)).trans (h₂ x hbx)
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hf x)).trans (h₁ x ⟨b, hb, hbx⟩)

omit [NumberField K] in
/-- **A minimal subsum has no vanishing subsum.** A sum over `s` equal to `y` contains a subsum
equal to `y` none of whose nonempty subsums vanishes. -/
theorem exists_subset_sum_eq_forall_ne_zero {ι : Type*} (a : ι → K) (s : Finset ι) :
    ∃ J ⊆ s, ∑ i ∈ J, a i = ∑ i ∈ s, a i ∧ ∀ I ⊆ J, I.Nonempty → ∑ i ∈ I, a i ≠ 0 := by
  classical
  obtain ⟨J, hJ, hmin⟩ := (s.powerset.filter fun J ↦ ∑ i ∈ J, a i = ∑ i ∈ s, a i).exists_min_image
    Finset.card ⟨s, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  refine ⟨J, hJ.1, hJ.2, fun I hIJ hI h0 ↦ ?_⟩
  have hlt : (J \ I).card < J.card := Finset.card_lt_card (Finset.sdiff_ssubset hIJ hI)
  have hsum : ∑ i ∈ J \ I, a i = ∑ i ∈ s, a i := by
    rw [← hJ.2, ← Finset.sum_sdiff hIJ, h0, add_zero]
  exact hlt.not_ge (hmin _ (by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.sdiff_subset.trans hJ.1, hsum⟩))

end NumberField
