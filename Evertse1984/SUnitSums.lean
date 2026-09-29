/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.PlaceProd
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.Basic

-- Used only inside proofs.
import Evertse1984.SumForms
import Mathlib.RingTheory.Localization.Integral

/-!
# Evertse's Theorem 2: a lower bound for sums of algebraic integers

**Theorem 2** (Evertse 1984, p. 228). Let `K` be a number field, `S` a finite set of places of
`K` containing the infinite ones, and `ε > 0`. There is a constant `C > 0`, depending only on
`ε`, `S`, `K` and `n`, such that for every nonempty `T ⊆ S` and every `x ∈ 𝓞_Kⁿ⁺¹` no nonempty
subsum of whose coordinates vanishes,

```text
(∏_{k=0}^{n} ∏_{v ∈ S} ‖x_k‖_v) · ∏_{v ∈ T} ‖x₀ + ⋯ + xₙ‖_v
    ≥ C · (∏_{v ∈ T} max(‖x₀‖_v, …, ‖xₙ‖_v)) · ‖x‖ ^ (-ε).
```

Here `‖·‖_v` is normalized for the product formula (`NumberField.placeProd`) and `‖x‖` is the
largest absolute value of a conjugate of a coordinate, `⨆ i, house (x i)`. It is the input of
Laurent's exponential Diophantine equations (1984, Lemma 7).

The proof is Evertse's, by induction on `n`. Points with the left side larger than
`(∏_{v ∈ T} max_k ‖x_k‖_v) · ‖x‖ ^ (-ε)` are fine. The others lie in finitely many proper
subspaces (`Evertse1984.SumForms`, from the Subspace Theorem), so the sum is a shorter sum
`x₀ + ⋯ + xₙ = ∑_{j ∈ J} β_j x_j` with one of finitely many coefficient vectors `β`, which can be
taken without vanishing subsums. The induction hypothesis, applied to `(δ β_j x_j)_{j ∈ J}` over
`T` and to the complementary coordinates over the places of `T` whose largest coordinate lies
outside `J`, gives the bound with `ε / 2` twice.

## Main definitions

* `NumberField.EvertseBound`: Evertse's inequality (14) for tuples indexed by `ι`, with a constant
  depending on `T`.
* `EvertseTheorem1`: **the statement of Evertse's Theorem 1**, finiteness of the admissible
  solutions of `x₀ + ⋯ + xₙ = 0`, proved in `Evertse1984.AdmissiblePoints`.

## Main results

* `NumberField.evertseBound`: the inequality, for each `T`, by induction.
* `NumberField.exists_pos_forall_placeProd_le`: **Theorem 2**, one constant for all `T`.

## Implementation notes

Evertse takes `T` to be a nonempty subset of `S`. Here `T` is any set of absolute values of `K`,
of which only the places in `S∞ ∪ S` count; for `T` without such places the inequality is the
product formula. The coordinates are elements of `K` that are algebraic integers.

In the step, the second application of the induction hypothesis is to the places of `T` whose
largest coordinate lies outside `J`, possibly none. Evertse treats "none" separately; here the
induction hypothesis covers it.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, Theorem 2 and §2. M. Laurent, *Équations diophantiennes exponentielles*, Invent. Math.
**78** (1984), 299–327, Lemma 7.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

universe u

variable {K : Type*} [Field K] [NumberField K]

/-- **Evertse's inequality (14) for tuples indexed by `ι`**: for every set `T` of places and every
`ε > 0` there is `C > 0` with

```text
C · (∏_{v ∈ T} max_i ‖x_i‖_v) · ‖x‖ ^ (-ε) ≤ (∏_i ∏_{v ∈ S∞ ∪ S} ‖x_i‖_v) · ∏_{v ∈ T} ‖∑_i x_i‖_v
```

for every tuple `x` of algebraic integers no nonempty subsum of which vanishes. -/
def EvertseBound (S : Finset (HeightOneSpectrum (𝓞 K))) (ι : Type*) [Fintype ι] : Prop :=
  ∀ (T : Set (AbsoluteValue K ℝ)) (ε : ℝ), 0 < ε → ∃ C > 0, ∀ x : ι → K,
    (∀ i, IsIntegral ℤ (x i)) → (∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, x i ≠ 0) →
      C * (placeProd S T (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)) ≤
        (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) * placeProd S T (fun v ↦ v (∑ i, x i))

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- **At most one coordinate**: the inequality holds with `C = 1`. With no coordinate the size is
`0` and the left side vanishes; with one, it is the product formula. -/
theorem evertseBound_of_subsingleton (ι : Type*) [Fintype ι] [Subsingleton ι] :
    EvertseBound S ι := by
  intro T ε hε
  refine ⟨1, one_pos, fun x hint hnv ↦ ?_⟩
  have hR : 0 ≤ (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
      placeProd S T (fun v ↦ v (∑ i, x i)) :=
    mul_nonneg (Finset.prod_nonneg fun i _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
      (placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [Real.iSup_of_isEmpty, Real.zero_rpow (neg_ne_zero.mpr hε.ne'), mul_zero, mul_zero]
    exact hR
  · have : Unique ι := uniqueOfSubsingleton i₀
    have hx0 : x i₀ ≠ 0 := by simpa using hnv {i₀} (by simp)
    simp only [ciSup_unique, Fintype.prod_unique, Fintype.sum_unique, one_mul,
      Subsingleton.elim default i₀]
    have hh : 1 ≤ house (x i₀) := one_le_house_of_isIntegral (hint i₀) hx0
    have hP : 0 ≤ placeProd S T (fun v ↦ v (x i₀)) :=
      placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _
    calc placeProd S T (fun v ↦ v (x i₀)) * house (x i₀) ^ (-ε)
        ≤ 1 * placeProd S T (fun v ↦ v (x i₀)) := by
          rw [one_mul]
          exact mul_le_of_le_one_right hP (Real.rpow_le_one_of_one_le_of_nonpos hh (by linarith))
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_placeProd_univ S (hint i₀) hx0) hP

/-- **The step of the induction, in one case.** Fix the shorter sum `∑_{j ∈ J} β_j x_j` and the
set `Q` of places whose largest coordinate lies in `J`. Then Evertse's inequality holds, with a
constant depending only on these data, for the points whose sum is that shorter sum without
vanishing subsums, and whose largest coordinates at the places of `T` lie in `J` exactly at the
places of `Q`. -/
theorem exists_pos_of_shorter_sum {ι : Type u} [Fintype ι] [DecidableEq ι]
    (IH : ∀ (κ : Type u) [Fintype κ], Fintype.card κ < Fintype.card ι → EvertseBound S κ)
    (T Q : Set (AbsoluteValue K ℝ)) (β : ι → K) {J : Finset ι} (hJ : J.Nonempty)
    (hJu : J ≠ Finset.univ) (hβ : ∀ i ∈ J, β i ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ x : ι → K, (∀ i, IsIntegral ℤ (x i)) →
      (∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, x i ≠ 0) →
      ∑ i, x i = ∑ i ∈ J, β i * x i → (∀ I ⊆ J, I.Nonempty → ∑ i ∈ I, β i * x i ≠ 0) →
      (∀ v ∈ T ∩ Q, ⨆ i : J, v (x i) = ⨆ i, v (x i)) →
      (∀ v ∈ T \ Q, ⨆ i : ↥Jᶜ, v (x i) = ⨆ i, v (x i)) →
      C * (placeProd S T (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)) ≤
        (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) * placeProd S T (fun v ↦ v (∑ i, x i)) := by
  classical
  -- a common denominator `δ` of the coefficients
  obtain ⟨D, hD, hDint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image β)
  set δ : K := (D : K) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hD
  have hγint : ∀ i, IsIntegral ℤ (δ * β i) := fun i ↦ by
    simpa [zsmul_eq_mul, hδ] using hDint (β i) (by simp)
  have hγ0 : ∀ i ∈ J, δ * β i ≠ 0 := fun i hi ↦ mul_ne_zero hδ0 (hβ i hi)
  have hδint : IsIntegral ℤ δ := by rw [hδ]; exact isIntegral_algebraMap
  -- the two applications of the induction hypothesis
  have hJne : Nonempty J := hJ.to_subtype
  have hJc : Jᶜ.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, Finset.compl_eq_empty_iff]
  have hJcne : Nonempty ↥Jᶜ := hJc.to_subtype
  have hcardJ : Fintype.card J < Fintype.card ι := by
    rw [Fintype.card_coe]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hJu)
  have hcardJc : Fintype.card ↥Jᶜ < Fintype.card ι := by
    rw [Fintype.card_coe]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (Finset.compl_ne_univ_iff_nonempty
      J |>.mpr hJ))
  obtain ⟨C₁, hC₁, h₁⟩ := IH J hcardJ T (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := IH ↥Jᶜ hcardJc (T \ Q) (ε / 2) (by positivity)
  -- the constants
  set m : AbsoluteValue K ℝ → ℝ := fun v ↦ ⨅ i : J, v (δ * β i) with hm
  have hmpos : ∀ v, 0 < m v := fun v ↦ by
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : J ↦ v (δ * β i))
    change 0 < ⨅ i : J, v (δ * β i)
    rw [← hi]
    exact AbsoluteValue.pos v (hγ0 i i.2)
  set Pm := placeProd S T m with hPm
  have hPm0 : 0 < Pm := placeProd_pos S T fun v _ ↦ hmpos v
  set A := ∏ i : J, placeProd S Set.univ (fun v ↦ v (δ * β i)) with hA
  have hA0 : 0 < A := Finset.prod_pos fun i _ ↦ placeProd_pos S _ fun v _ ↦
    AbsoluteValue.pos v (hγ0 i i.2)
  set Pδ := placeProd S T (fun v ↦ v δ) with hPδ
  have hPδ0 : 0 < Pδ := placeProd_pos S T fun v _ ↦ AbsoluteValue.pos v hδ0
  set B := ⨆ i : J, house (δ * β i) with hB
  have hB1 : 1 ≤ B := by
    obtain ⟨i⟩ := hJne
    exact one_le_iSup_house (x := fun i : J ↦ δ * β i) (i := i) (hγint i) (hγ0 i i.2)
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  set k : AbsoluteValue K ℝ → ℝ := fun v ↦ ∑ i ∈ J, v (β i - 1) with hk
  set K' := max 1 (placeProd S (T \ Q) k) with hK'
  have hK'0 : 0 < K' := zero_lt_one.trans_le (le_max_left _ _)
  set a := C₁ * Pm * B ^ (-(ε / 2)) with ha
  have ha0 : 0 < a := by positivity
  set b := A * Pδ with hb
  have hb0 : 0 < b := mul_pos hA0 hPδ0
  refine ⟨a / b * C₂ / K', by positivity, fun x hint hnv hsum hnvJ hmaxJ hmaxJc ↦ ?_⟩
  -- the basic facts about `x`
  have hx0 : ∀ i, x i ≠ 0 := fun i ↦ by simpa using hnv {i} (by simp)
  set M : AbsoluteValue K ℝ → ℝ := fun v ↦ ⨆ i, v (x i) with hM
  have hM0 : ∀ v, 0 < M v := fun v ↦ by
    obtain ⟨i⟩ := hJne
    exact (AbsoluteValue.pos v (hx0 i)).trans_le
      (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) i)
  set MJ : AbsoluteValue K ℝ → ℝ := fun v ↦ ⨆ i : J, v (x i) with hMJ
  have hMJ0 : ∀ v, 0 ≤ MJ v := fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  set h := ⨆ i, house (x i) with hh
  have hh1 : 1 ≤ h := by
    obtain ⟨i⟩ := hJne
    exact one_le_iSup_house (hint i) (hx0 i)
  have hh0 : 0 < h := zero_lt_one.trans_le hh1
  set h' := h ^ (-(ε / 2)) with hh'
  have hh'0 : 0 < h' := Real.rpow_pos_of_pos hh0 _
  set U := ∏ i, placeProd S Set.univ (fun v ↦ v (x i)) with hU
  set UJ := ∏ i : J, placeProd S Set.univ (fun v ↦ v (x i)) with hUJ
  set UJc := ∏ i : ↥Jᶜ, placeProd S Set.univ (fun v ↦ v (x i)) with hUJc
  have hUJc0 : 0 ≤ UJc :=
    Finset.prod_nonneg fun i _ ↦ placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _
  have hUsplit : UJ * UJc = U := by
    rw [hUJ, hUJc, hU, Finset.prod_coe_sort J (fun i ↦ placeProd S Set.univ (fun v ↦ v (x i))),
      Finset.prod_coe_sort Jᶜ (fun i ↦ placeProd S Set.univ (fun v ↦ v (x i))),
      Finset.prod_mul_prod_compl]
  set Psum := placeProd S T (fun v ↦ v (∑ i, x i)) with hPsum
  -- the first application: the shorter sum, scaled by `δ`
  set z : J → K := fun i ↦ δ * β i * x i with hz
  have hzint : ∀ i, IsIntegral ℤ (z i) := fun i ↦ (hγint i).mul (hint i)
  have hzsub : ∀ I : Finset J, ∑ i ∈ I, z i = δ * ∑ i ∈ I.map (Function.Embedding.subtype _),
      β i * x i := fun I ↦ by
    rw [Finset.sum_map, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hz, mul_assoc]
  have hmapJ : ∀ I : Finset J, I.map (Function.Embedding.subtype _) ⊆ J := fun I i hi ↦ by
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    exact j.2
  have hznv : ∀ I : Finset J, I.Nonempty → ∑ i ∈ I, z i ≠ 0 := fun I hI ↦ by
    rw [hzsub]
    exact mul_ne_zero hδ0 (hnvJ _ (hmapJ I) (hI.map))
  have H₁ := h₁ z hzint hznv
  have hzsum : ∑ i, z i = δ * ∑ i, x i := by
    rw [hzsub Finset.univ, hsum]
    congr 1
    exact Finset.sum_bij (fun i _ ↦ i) (fun i hi ↦ hmapJ Finset.univ hi)
      (fun _ _ _ _ h ↦ h) (fun i hi ↦ ⟨i, by simpa using hi, rfl⟩) fun _ _ ↦ rfl
  have hRHS₁ : (∏ i, placeProd S Set.univ (fun v ↦ v (z i))) *
      placeProd S T (fun v ↦ v (∑ i, z i)) = A * UJ * (Pδ * Psum) := by
    rw [hzsum]
    simp only [hz, map_mul, placeProd_mul, Finset.prod_mul_distrib, hA, hUJ, hPδ, hPsum]
  have hLM : Pm * placeProd S T MJ ≤ placeProd S T (fun v ↦ ⨆ i, v (z i)) := by
    rw [hPm, ← placeProd_mul]
    refine placeProd_le_placeProd S T (fun v _ ↦ mul_nonneg (hmpos v).le (hMJ0 v)) fun v _ ↦ ?_
    rw [hMJ, Real.mul_iSup_of_nonneg (hmpos v).le]
    refine ciSup_mono (Finite.bddAbove_range _) fun i ↦ ?_
    rw [hz, map_mul]
    exact mul_le_mul_of_nonneg_right
      (ciInf_le (f := fun i : J ↦ v (δ * β i)) (Finite.bddBelow_range _) i) (apply_nonneg _ _)
  have hzh : (⨆ i, house (z i)) ≤ B * h := ciSup_le fun i ↦
    (house_mul_le _ _).trans (mul_le_mul (le_ciSup (f := fun i : J ↦ house (δ * β i))
      (Finite.bddAbove_range _) i) (house_le_iSup_house x i.1) (house_nonneg _) hB0.le)
  have hzh0 : 0 < ⨆ i, house (z i) := by
    obtain ⟨i⟩ := hJne
    exact zero_lt_one.trans_le (one_le_iSup_house (hzint i) (mul_ne_zero (hγ0 i i.2) (hx0 i)))
  have hzrpow : B ^ (-(ε / 2)) * h' ≤ (⨆ i, house (z i)) ^ (-(ε / 2)) := by
    rw [hh', ← Real.mul_rpow hB0.le hh0.le]
    exact Real.rpow_le_rpow_of_nonpos hzh0 hzh (by linarith)
  have E₁ : a * UJc * placeProd S T MJ * h' ≤ b * (U * Psum) := by
    have H : C₁ * (Pm * placeProd S T MJ) * (B ^ (-(ε / 2)) * h') ≤ A * UJ * (Pδ * Psum) := by
      rw [← hRHS₁]
      calc C₁ * (Pm * placeProd S T MJ) * (B ^ (-(ε / 2)) * h')
          ≤ C₁ * placeProd S T (fun v ↦ ⨆ i, v (z i)) * (⨆ i, house (z i)) ^ (-(ε / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hLM hC₁.le) hzrpow
              (mul_pos (Real.rpow_pos_of_pos hB0 _) hh'0).le
              (mul_nonneg hC₁.le (placeProd_nonneg S _ fun v _ ↦
                Real.iSup_nonneg fun i ↦ apply_nonneg _ _))
        _ ≤ _ := by rw [mul_assoc]; exact H₁
    calc a * UJc * placeProd S T MJ * h'
        = UJc * (C₁ * (Pm * placeProd S T MJ) * (B ^ (-(ε / 2)) * h')) := by rw [ha]; ring
      _ ≤ UJc * (A * UJ * (Pδ * Psum)) := mul_le_mul_of_nonneg_left H hUJc0
      _ = b * (U * Psum) := by rw [hb, ← hUsplit]; ring
  -- the places of `T` where the largest coordinate lies in `J`
  have hsplitJ : placeProd S T MJ =
      placeProd S (T ∩ Q) M * placeProd S (T \ Q) MJ := by
    rw [← placeProd_inter_mul_diff S T Q MJ, placeProd_congr S (T ∩ Q) hmaxJ]
  -- the second application: the complementary coordinates
  set xc : ↥Jᶜ → K := fun i ↦ x i with hxc
  have hxcnv : ∀ I : Finset ↥Jᶜ, I.Nonempty → ∑ i ∈ I, xc i ≠ 0 := fun I hI ↦ by
    rw [show ∑ i ∈ I, xc i = ∑ i ∈ I.map (Function.Embedding.subtype _), x i by
      rw [Finset.sum_map]; rfl]
    exact hnv _ hI.map
  have H₂ := h₂ xc (fun i ↦ hint i) hxcnv
  have hcsum : ∑ i, xc i = ∑ i ∈ J, (β i - 1) * x i := by
    rw [hxc, Finset.sum_coe_sort Jᶜ (fun i ↦ x i)]
    have h := Finset.sum_compl_add_sum J x
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [← hsum]
    linear_combination h
  have hcle : placeProd S (T \ Q) (fun v ↦ v (∑ i, xc i)) ≤
      K' * placeProd S (T \ Q) MJ := by
    calc placeProd S (T \ Q) (fun v ↦ v (∑ i, xc i))
        ≤ placeProd S (T \ Q) (fun v ↦ k v * MJ v) := by
          refine placeProd_le_placeProd S _ (fun v _ ↦ apply_nonneg _ _) fun v _ ↦ ?_
          rw [hcsum, hk, Finset.sum_mul]
          refine (AbsoluteValue.sum_le _ _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
          rw [map_mul]
          exact mul_le_mul_of_nonneg_left
            (le_ciSup (f := fun i : J ↦ v (x i)) (Finite.bddAbove_range _) ⟨i, hi⟩)
            (apply_nonneg _ _)
      _ = placeProd S (T \ Q) k * placeProd S (T \ Q) MJ := placeProd_mul S _ _ _
      _ ≤ K' * placeProd S (T \ Q) MJ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (placeProd_nonneg S _ fun v _ ↦ hMJ0 v)
  have hch : (⨆ i, house (xc i)) ≤ h := ciSup_le fun i ↦ house_le_iSup_house x i.1
  have hch0 : 0 < ⨆ i, house (xc i) := by
    obtain ⟨i⟩ := hJcne
    exact zero_lt_one.trans_le (one_le_iSup_house (x := xc) (i := i) (hint i) (hx0 i))
  have E₂ : C₂ * placeProd S (T \ Q) M * h' ≤ K' * (UJc * placeProd S (T \ Q) MJ) := by
    have hMc : placeProd S (T \ Q) (fun v ↦ ⨆ i, v (xc i)) = placeProd S (T \ Q) M :=
      placeProd_congr S _ hmaxJc
    rw [hMc] at H₂
    calc C₂ * placeProd S (T \ Q) M * h'
        ≤ C₂ * placeProd S (T \ Q) M * (⨆ i, house (xc i)) ^ (-(ε / 2)) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hch0 hch (by linarith))
            (mul_nonneg hC₂.le (placeProd_nonneg S _ fun v _ ↦ (hM0 v).le))
      _ ≤ UJc * placeProd S (T \ Q) (fun v ↦ v (∑ i, xc i)) := by
          rw [← mul_assoc] at H₂; exact H₂
      _ ≤ UJc * (K' * placeProd S (T \ Q) MJ) := mul_le_mul_of_nonneg_left hcle hUJc0
      _ = K' * (UJc * placeProd S (T \ Q) MJ) := by ring
  -- the two combined
  have hP1 : 0 ≤ placeProd S (T ∩ Q) M := placeProd_nonneg S _ fun v _ ↦ (hM0 v).le
  have hsplitM : placeProd S T M = placeProd S (T ∩ Q) M * placeProd S (T \ Q) M :=
    (placeProd_inter_mul_diff S T Q M).symm
  have hhε : h ^ (-ε) = h' * h' := by
    rw [hh', ← Real.rpow_add hh0]
    congr 1
    ring
  have E₂' : C₂ * placeProd S (T \ Q) M * h' / K' ≤ UJc * placeProd S (T \ Q) MJ := by
    rw [div_le_iff₀ hK'0]
    linarith
  calc a / b * C₂ / K' * (placeProd S T M * h ^ (-ε))
      = a / b * placeProd S (T ∩ Q) M * h' * (C₂ * placeProd S (T \ Q) M * h' / K') := by
        rw [hsplitM, hhε]
        ring
    _ ≤ a / b * placeProd S (T ∩ Q) M * h' * (UJc * placeProd S (T \ Q) MJ) :=
        mul_le_mul_of_nonneg_left E₂' (mul_nonneg (mul_nonneg (by positivity) hP1) hh'0.le)
    _ = a * UJc * placeProd S T MJ * h' / b := by
        rw [hsplitJ]
        ring
    _ ≤ b * (U * Psum) / b := div_le_div_of_nonneg_right E₁ hb0.le
    _ = U * Psum := by field_simp

/-- **The step of the induction.** If Evertse's inequality holds in fewer variables, it holds for
`ι`, with at least two coordinates. Every point either satisfies it with `C = 1`, or lies in one of
finitely many proper subspaces, one family for each of the finitely many choices of largest
coordinates at the places of `T`; there its sum is a shorter sum without vanishing subsums, and
`NumberField.exists_pos_of_shorter_sum` applies. -/
theorem evertseBound_of_forall_lt {ι : Type u} [Fintype ι] [Nontrivial ι]
    (IH : ∀ (κ : Type u) [Fintype κ], Fintype.card κ < Fintype.card ι → EvertseBound S κ) :
    EvertseBound S ι := by
  classical
  intro T ε hε
  set T' := T ∩ relevantPlaces S with hT'
  have hT'fin : T'.Finite := (finite_relevantPlaces S).subset Set.inter_subset_right
  -- the choices of largest coordinates at the places of `T'`
  set Rs : Set (AbsoluteValue K ℝ → Option ι) := {r | ∀ v, (r v).isSome ↔ v ∈ T'} with hRs
  have hRsfin : Rs.Finite := by
    have : Finite T' := hT'fin.to_subtype
    refine (Set.finite_range fun g : T' → ι ↦
      fun v ↦ if h : v ∈ T' then some (g ⟨v, h⟩) else none).subset fun r hr ↦ ?_
    refine ⟨fun v ↦ (r v.1).get ((hr v.1).mpr v.2), funext fun v ↦ ?_⟩
    by_cases h : v ∈ T'
    · simp [h]
    · simp only [h, dite_false]
      exact (Option.not_isSome_iff_eq_none.mp fun h' ↦ h ((hr v).mp h')).symm
  have hf : ∀ x : ι → K, 0 ≤ placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε) :=
    fun x ↦ mul_nonneg (placeProd_nonneg S _ fun v _ ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
      (Real.rpow_nonneg (Real.iSup_nonneg fun i ↦ house_nonneg _) _)
  -- one choice of largest coordinates
  have key : ∀ r ∈ Rs, ∃ C > 0, ∀ x : ι → K,
      ((∀ i, IsIntegral ℤ (x i)) ∧ (∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, x i ≠ 0) ∧
        ∀ v i, r v = some i → v (x i) = ⨆ j, v (x j)) →
      C * (placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)) ≤
        (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
          placeProd S T' (fun v ↦ v (∑ i, x i)) := by
    intro r hr
    have hTr : {w | (r w).isSome} = T' := Set.ext fun v ↦ hr v
    obtain ⟨Ws, hWs, hcov⟩ := exists_finset_submodule_of_prod_placeProd_le S r hε
    rw [hTr] at hcov
    -- a relation on each subspace, written as a shorter sum
    have hrel : ∀ W ∈ Ws, ∃ β : ι → K, ∃ j, β j = 0 ∧ ∀ y ∈ W, ∑ i, y i = ∑ i, β i * y i := by
      intro W hW
      obtain ⟨f, hf0, hWf⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr (hWs W hW))
      set c : ι → K := fun i ↦ f fun j ↦ if i = j then 1 else 0 with hc
      obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
        by_contra! h
        exact hf0 (LinearMap.ext fun y ↦ by
          rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
          exact Finset.sum_eq_zero fun i _ ↦ by
            rw [smul_eq_mul, show (f fun j ↦ if i = j then 1 else 0) = 0 from h i, mul_zero])
      refine ⟨fun i ↦ 1 - c i / c j, j, by simp [hj], fun y hy ↦ ?_⟩
      have h0 : ∑ i, y i * c i = 0 := by
        have h := LinearMap.mem_ker.mp (hWf hy)
        rw [LinearMap.pi_apply_eq_sum_univ] at h
        simpa [smul_eq_mul, hc] using h
      calc ∑ i, y i = ∑ i, y i - (∑ i, y i * c i) / c j := by rw [h0, zero_div, sub_zero]
        _ = ∑ i, (1 - c i / c j) * y i := by
            rw [Finset.sum_div, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ ↦ by field_simp
    choose! β j hβj hβW using hrel
    -- the cases: a subspace and a shorter sum
    set Q : Finset ι → Set (AbsoluteValue K ℝ) := fun J ↦ {v | ∃ i ∈ J, r v = some i} with hQ
    have hA : ∀ p : Submodule K (ι → K) × Finset ι,
        p ∈ ((Ws ×ˢ Finset.univ : Finset (Submodule K (ι → K) × Finset ι)) : Set _) →
        ∃ C > 0, ∀ x : ι → K,
          ((∀ i, IsIntegral ℤ (x i)) ∧ (∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, x i ≠ 0) ∧
            ∑ i, x i = ∑ i ∈ p.2, β p.1 i * x i ∧
            (∀ I ⊆ p.2, I.Nonempty → ∑ i ∈ I, β p.1 i * x i ≠ 0) ∧
            (∀ v ∈ T' ∩ Q p.2, ⨆ i : p.2, v (x i) = ⨆ i, v (x i)) ∧
            (∀ v ∈ T' \ Q p.2, ⨆ i : ↥p.2ᶜ, v (x i) = ⨆ i, v (x i)) ∧
            (p.2.Nonempty ∧ p.2 ≠ Finset.univ ∧ ∀ i ∈ p.2, β p.1 i ≠ 0)) →
          C * (placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)) ≤
            (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
              placeProd S T' (fun v ↦ v (∑ i, x i)) := by
      intro p _
      by_cases hc : p.2.Nonempty ∧ p.2 ≠ Finset.univ ∧ ∀ i ∈ p.2, β p.1 i ≠ 0
      · obtain ⟨C, hC, hCx⟩ := exists_pos_of_shorter_sum S IH T' (Q p.2) (β p.1) hc.1 hc.2.1
          hc.2.2 hε
        exact ⟨C, hC, fun x hx ↦ hCx x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1
          hx.2.2.2.2.2.1⟩
      · exact ⟨1, one_pos, fun x hx ↦ absurd hx.2.2.2.2.2.2 hc⟩
    obtain ⟨C₀, hC₀, hC₀x⟩ := exists_pos_forall_le_of_finite (Finset.finite_toSet _) hf hA
    refine ⟨min 1 C₀, lt_min one_pos hC₀, fun x ⟨hint, hnv, hrx⟩ ↦ ?_⟩
    have hx0 : ∀ i, x i ≠ 0 := fun i ↦ by simpa using hnv {i} (by simp)
    by_cases hsmall : (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
        placeProd S T' (fun v ↦ v (∑ i, x i)) ≤
          placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)
    · obtain ⟨W, hW, hxW⟩ := hcov x hint hx0 hrx hsmall
      have hsumW := hβW W hW x hxW
      obtain ⟨J, -, hJsum, hJnv⟩ :=
        exists_subset_sum_eq_forall_ne_zero (fun i ↦ β W i * x i) Finset.univ
      have hJβ : ∀ i ∈ J, β W i ≠ 0 := fun i hi h0 ↦
        hJnv {i} (by simpa using hi) (by simp) (by simp [h0])
      have hjJ : j W ∉ J := fun h ↦ hJβ _ h (hβj W hW)
      have hJne : J.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        refine hnv Finset.univ Finset.univ_nonempty ?_
        rw [hsumW, ← hJsum, h, Finset.sum_empty]
      have hJu : J ≠ Finset.univ := fun h ↦ hjJ (h ▸ Finset.mem_univ _)
      have hmaxJ : ∀ v ∈ T' ∩ Q J, ⨆ i : J, v (x i) = ⨆ i, v (x i) := by
        rintro v ⟨-, i, hi, hri⟩
        have : Nonempty J := ⟨⟨i, hi⟩⟩
        refine le_antisymm (ciSup_le fun l ↦
          le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) l.1) ?_
        rw [← hrx v i hri]
        exact le_ciSup (f := fun l : J ↦ v (x l)) (Finite.bddAbove_range _) ⟨i, hi⟩
      have hmaxJc : ∀ v ∈ T' \ Q J, ⨆ i : ↥Jᶜ, v (x i) = ⨆ i, v (x i) := by
        rintro v ⟨hvT, hvQ⟩
        obtain ⟨i, hri⟩ := Option.isSome_iff_exists.mp ((hr v).mpr hvT)
        have hiJ : i ∈ Jᶜ := Finset.mem_compl.mpr fun hi ↦ hvQ ⟨i, hi, hri⟩
        have : Nonempty ↥Jᶜ := ⟨⟨i, hiJ⟩⟩
        refine le_antisymm (ciSup_le fun l ↦
          le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) l.1) ?_
        rw [← hrx v i hri]
        exact le_ciSup (f := fun l : ↥Jᶜ ↦ v (x l)) (Finite.bddAbove_range _) ⟨i, hiJ⟩
      refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (hf x)).trans
        (hC₀x x ⟨(W, J), by simp [hW], hint, hnv, hsumW.trans hJsum.symm, hJnv, hmaxJ, hmaxJc,
          hJne, hJu, hJβ⟩)
    · push Not at hsmall
      calc min 1 C₀ * (placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε))
          ≤ 1 * (placeProd S T' (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (hf x)
        _ ≤ _ := by rw [one_mul]; exact hsmall.le
  -- all choices at once
  obtain ⟨C, hC, hCx⟩ := exists_pos_forall_le_of_finite hRsfin hf key
  refine ⟨C, hC, fun x hint hnv ↦ ?_⟩
  rw [← placeProd_inter_relevantPlaces S T, ← placeProd_inter_relevantPlaces S T (fun v ↦ v _)]
  set rx : AbsoluteValue K ℝ → Option ι := fun v ↦ if v ∈ T' then
    some (Classical.choose (exists_eq_ciSup_of_finite (f := fun i ↦ v (x i)))) else none
    with hrx
  refine hCx x ⟨rx, fun v ↦ ?_, hint, hnv, fun v i h ↦ ?_⟩
  · by_cases hv : v ∈ T' <;> simp [hrx, hv]
  · by_cases hv : v ∈ T'
    · simp only [hrx, hv, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      exact Classical.choose_spec (exists_eq_ciSup_of_finite (f := fun i ↦ v (x i)))
    · simp [hrx, hv] at h

/-- **Evertse's inequality, for each `T`**, by induction on the number of coordinates. -/
theorem evertseBound (ι : Type u) [Fintype ι] : EvertseBound S ι := by
  suffices H : ∀ (n : ℕ) (κ : Type u) [Fintype κ], Fintype.card κ = n → EvertseBound S κ from
    H _ ι rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ hκ
    rcases subsingleton_or_nontrivial κ with hκs | hκn
    · exact evertseBound_of_subsingleton S κ
    · exact evertseBound_of_forall_lt S fun κ' _ h ↦ ih _ (hκ ▸ h) κ' rfl

/-- **Evertse's Theorem 2** (1984, p. 228). For a number field `K`, a finite set `S` of finite
places and `ε > 0` there is `C > 0` such that for every set `T` of places and every tuple `x` of
algebraic integers of `K` no nonempty subsum of which vanishes,

```text
(∏_k ∏_{v ∈ S∞ ∪ S} ‖x_k‖_v) · ∏_{v ∈ T} ‖∑_k x_k‖_v ≥ C · (∏_{v ∈ T} max_k ‖x_k‖_v) · ‖x‖ ^ (-ε),
```

the products over `T` taken over its places in `S∞ ∪ S`. -/
theorem exists_pos_forall_placeProd_le (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (T : Set (AbsoluteValue K ℝ)) (x : ι → K), (∀ i, IsIntegral ℤ (x i)) →
      (∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, x i ≠ 0) →
      C * placeProd S T (fun v ↦ ⨆ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε) ≤
        (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
          placeProd S T (fun v ↦ v (∑ i, x i)) := by
  have hf : ∀ p : Set (AbsoluteValue K ℝ) × (ι → K),
      0 ≤ placeProd S p.1 (fun v ↦ ⨆ i, v (p.2 i)) * (⨆ i, house (p.2 i)) ^ (-ε) :=
    fun p ↦ mul_nonneg (placeProd_nonneg S _ fun v _ ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
      (Real.rpow_nonneg (Real.iSup_nonneg fun i ↦ house_nonneg _) _)
  obtain ⟨C, hC, hCx⟩ := exists_pos_forall_le_of_finite
    (s := {T' | T' ⊆ relevantPlaces S}) (finite_relevantPlaces S).finite_subsets hf
    (g := fun p ↦ (∏ i, placeProd S Set.univ (fun v ↦ v (p.2 i))) *
      placeProd S p.1 (fun v ↦ v (∑ i, p.2 i)))
    (A := fun T' p ↦ p.1 ∩ relevantPlaces S = T' ∧ (∀ i, IsIntegral ℤ (p.2 i)) ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, p.2 i ≠ 0)
    fun T' _ ↦ by
      obtain ⟨C, hC, hCx⟩ := evertseBound S ι T' ε hε
      refine ⟨C, hC, fun p ⟨hT, hint, hnv⟩ ↦ ?_⟩
      rw [← placeProd_inter_relevantPlaces S p.1, ← placeProd_inter_relevantPlaces S p.1
        (fun v ↦ v _), hT]
      exact hCx p.2 hint hnv
  refine ⟨C, hC, fun T x hint hnv ↦ ?_⟩
  rw [mul_assoc]
  exact hCx (T, x) ⟨_, Set.inter_subset_right, rfl, hint, hnv⟩

end NumberField

open NumberField in
/-- **The statement of Evertse's Theorem 1** (1984, p. 227), proved from Theorem 2 as
`evertseTheorem1` in `Evertse1984.AdmissiblePoints`. For `c > 0` and `0 ≤ d < 1`, a point
`X ∈ ℙⁿ(K)` is `(c, d, S)`-*admissible* if its homogeneous coordinates can be chosen `S`-integers
with
`∏_k ∏_{v ∈ S∞ ∪ S} ‖x_k‖_v ≤ c · H(X) ^ d`. Only finitely many admissible `X` satisfy
`x₀ + ⋯ + xₙ = 0` with no vanishing nonempty proper subsum.

For `c = 1` and `d = 0` the admissible points are those with `S`-unit coordinates, and the
statement is the unit equation, `NumberField.finite_setOf_sum_unit_eq_one` of
`DiophantineApproximation` (Layer 8.2). -/
def EvertseTheorem1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (c d : ℝ), 0 < c → 0 ≤ d → d < 1 →
    {X : Projectivization K (ι → K) | ∃ (x : ι → K) (hx : x ≠ 0), Projectivization.mk K x hx = X ∧
      (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      ∏ i, NumberField.placeProd S Set.univ (fun v ↦ v (x i)) ≤ c * mulHeight x ^ d ∧
      ∑ i, x i = 0 ∧ ∀ I : Finset ι, I.Nonempty → I ≠ Finset.univ → ∑ i ∈ I, x i ≠ 0}.Finite
