/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004Thue.EqualDegrees

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import STForMathlib.RingTheory.MvPolynomial.FiniteZeros
import STForMathlib.RingTheory.MvPolynomial.GenericLinear
import STForMathlib.RingTheory.MvPolynomial.HomogeneousRegular

/-!
# Theorems 2 and 1

P. Corvaja and U. Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), §§1, 3.

* **Theorem 2** (`NumberField.exists_eval_eq_zero_of_prod_sub_mem_of_totalDegree_le`): Prop. 3.1
  without equal degrees. The `fᵢ` of degree `≤ δᵢ` are padded to `fᵢ ρᵢ^(δ - δᵢ)`, `δ = max δᵢ`,
  with linear forms `ρᵢ` in general position, and `g` to `g ∏ ρᵢ^(δ - δᵢ)`.
* **Theorem 1** (`NumberField.exists_eval_eq_zero_of_dvd_prod_sub`): Theorem 2 with `b = 1`,
  `t = s = n - 1`, at each irreducible factor `G` of `f₁ ⋯ f_r - g`.
* **Theorem 1 for `n = 2`** (`NumberField.finite_setOf_eval_prod_sub_eq_zero`): finitely many
  `S`-integral solutions, since `(G, q)` has height `2` for `q ∉ (G)`
  (`MvPolynomial.finite_setOf_forall_eval_eq_zero`). With `fᵢ` linear forms and `g` constant this
  is Thue's theorem; in general it allows `deg g < ∑ deg fᵢ - 2 max deg fᵢ`.

## Implementation notes

⚠ **"General position" in ideal form.** The paper asks that every
`ρ_{j₁} = ⋯ = ρ_{j_h} = f_{j_{h+1}} = ⋯ = f_{j_s} = 0` cut `Z` in dimension `n - b - s`, and that no
`s + 1` of the `fᵢ ρᵢ` have a common zero on `cl Z ∖ Z`, "for a generic choice of the `ρᵢ`".
Here the `ρᵢ` are chosen one after the other (`MvPolynomial.exists_mem_span_forall`), each
avoiding finitely many primes, and the two conditions are kept as:
* `ht (G^h, f^h_F, ρ_H) ≥ b + |F| + |H|` for disjoint `F`, `H` with `|F| + |H| ≤ t`;
* `X₀, G^h, f^h_F, ρ_H` cut the origin of `K[X]` in dimension `≤ s + 1 - |F| - |H|`
  (`MvPolynomial.originDim`).
The first starts from Lemma 2.1 (subfamilies of the `t`-sets have the right height,
`MvPolynomial.card_le_height_span_image`), the second from Krull's bound
(`MvPolynomial.originDim_le_card`). A prime containing `(G^h, (fᵢ ρᵢ^{aᵢ})^h)` contains, for each
`i`, `fᵢ^h` or `ρᵢ`, which gives Prop. 3.1's hypotheses for the padded family. No dimension
theory beyond Krull's height theorem is used: the paper's "`V(j₁, …, j_h)` has dimension
`n - b - h`" is replaced by the regular-sequence bound, and "`s ≥ n - b - 1`" is not needed.

⚠ **The hypotheses of Theorem 1, in ideal form.** "`X₀ g^h` and any `n - 1` of the `fᵢ^h` have
finitely many common zeros in `ℙⁿ`" is `ht (X₀ g^h, f^h_T) = n` for `|T| = n - 1`; "no `n` of the
`fᵢ^h` have a common zero at infinity" is "each `X_x` has a power in `(X₀, f^h_J)`", `|J| = n`.
The paper's proof ("it is immediate to verify") is the inclusion
`V(G^h, f^h_T) ⊆ V(X₀ g^h, f^h_T)`: `X₀^(Δ - e) g^h = ∏ fᵢ^h - (∏ fᵢ - g)^h` and `G^h` divides
`(∏ fᵢ - g)^h`, `Δ = ∑ deg fᵢ > e = deg g`. `(G^h, X₀)` has height `2` because `X₀` does not
divide `G^h` (`MvPolynomial.height_span_X_none_homogenization`).

⚠ **"Not Zariski-dense in `X`", per component.** The conclusion of Theorem 1 is given for every
irreducible `G ∣ f₁ ⋯ f_r - g`, which is what the paper's proof shows and is stronger than
non-density in `X`.
-/

@[expose] public section

open Finset

namespace NumberField

open Height IsDedekindDomain MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Theorem 2** (Corvaja–Zannier 2004). Let `Z = {G = 0} ⊆ 𝔸^{b + t}`, `(G)` prime, `(G^h, X₀)`
of height `b + 1`, and `f₁ ⋯ f_r = g` on `Z`, `deg fᵢ ≤ δᵢ`, `deg g ≤ e`. If any `t` of the
`fᵢ^h = homogenize δᵢ fᵢ` cut `cl Z` in finitely many points, no `s + 1` of them have a common
zero on `cl Z ∖ Z`, `t ≤ s`, and `∑ δᵢ > s (t + 1)/t · max δᵢ + e`, then one `q ∉ (G)` vanishes
at every `S`-integral point of `Z`. -/
theorem exists_eval_eq_zero_of_prod_sub_mem_of_totalDegree_le {σ : Type*} [Fintype σ]
    {b t r s e : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K))) {G : Fin b → MvPolynomial σ K}
    (hG : (Ideal.span (Set.range G)).IsPrime) (ht : 0 < t) (hcard : Fintype.card σ = b + t)
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1)
    {f : Fin r → MvPolynomial σ K} {g : MvPolynomial σ K} {δ : Fin r → ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ δ i) (hg : g.totalDegree ≤ e)
    (heq : ∏ i, f i - g ∈ Ideal.span (Set.range G))
    (hht : ∀ T : Finset (Fin r), T.card = t →
      (Ideal.span (Set.range (fun l ↦ homogenization (G l)) ∪
        (fun i ↦ homogenize (δ i) (f i)) '' T)).height = (b + t : ℕ))
    (hts : t ≤ s)
    (hinf : ∀ J : Finset (Fin r), J.card = s + 1 → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) (Set.range (fun l ↦ homogenization (G l)) ∪
        (fun i ↦ homogenize (δ i) (f i)) '' J)))
    (hr : s * (t + 1) * univ.sup δ + t * e < t * ∑ i, δ i) :
    ∃ q ∉ Ideal.span (Set.range G), ∀ P : σ → K,
      (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (∀ l, eval P (G l) = 0) → eval P q = 0 := by
  set D := univ.sup δ with hD
  have hδD : ∀ i, δ i ≤ D := fun i ↦ le_sup (mem_univ i)
  have hsum : ∑ i, δ i ≤ r * D :=
    calc ∑ i, δ i ≤ ∑ _i : Fin r, D := sum_le_sum fun i _ ↦ hδD i
      _ = r * D := by simp
  have hD0 : 0 < D := by
    by_contra h0
    have hD0 : D = 0 := by omega
    rw [hD0, mul_zero, Nat.le_zero] at hsum
    rw [hsum, mul_zero] at hr
    omega
  have hsr : s < r := by
    by_contra h
    push Not at h
    have h1 : t * ∑ i, δ i ≤ t * (r * D) := Nat.mul_le_mul_left _ hsum
    have h2 : t * (r * D) ≤ s * (t + 1) * D :=
      calc t * (r * D) ≤ t * (s * D) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)
        _ ≤ s * (t + 1) * D := by
          rw [show s * (t + 1) * D = t * (s * D) + s * D by ring]
          omega
    omega
  have htr : t ≤ r := hts.trans hsr.le
  set Gh : Fin b → MvPolynomial (Option σ) K := fun l ↦ homogenization (G l) with hGhdef
  set fh : Fin r → MvPolynomial (Option σ) K := fun i ↦ homogenize (δ i) (f i) with hfhdef
  set V : Set (Option σ) := Set.range some with hVdef
  have hV : V.ncard = b + t := by
    rw [Set.ncard_range_of_injective (Option.some_injective σ), Nat.card_eq_fintype_card, hcard]
  have hGh : ∀ l, (Gh l).IsHomogeneous (G l).totalDegree :=
    fun l ↦ isHomogeneous_homogenization _
  have hfh : ∀ i, (fh i).IsHomogeneous (δ i) := fun i ↦ isHomogeneous_homogenize (hf i)
  -- The forms have no constant term.
  have hGh0 : ∀ l, constantCoeff (Gh l) = 0 := by
    intro l
    refine constantCoeff_eq_zero_of_mem (R := insert (X none) (Set.range Gh)) ?_ ?_
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨l, rfl⟩))
    · rintro _ (rfl | ⟨l, rfl⟩)
      exacts [⟨1, isHomogeneous_X K none⟩, ⟨_, hGh l⟩]
    · intro htop
      rw [htop, Ideal.height_top] at hXh
      exact ENat.top_ne_natCast _ hXh
  have hfh0 : ∀ i, constantCoeff (fh i) = 0 := by
    intro i
    obtain ⟨T, hiT, hT⟩ := exists_superset_card_eq (s := {i}) (n := t)
      (by rw [card_singleton]; exact ht) (by simpa using htr)
    refine constantCoeff_eq_zero_of_mem (R := Set.range Gh ∪ fh '' T) ?_ ?_
      (Ideal.subset_span (Or.inr ⟨i, hiT (mem_singleton_self i), rfl⟩))
    · rintro _ (⟨l, rfl⟩ | ⟨j, -, rfl⟩)
      exacts [⟨_, hGh l⟩, ⟨_, hfh j⟩]
    · intro htop
      have := hht T hT
      rw [htop, Ideal.height_top] at this
      exact ENat.top_ne_natCast _ this
  -- The base cases: Lemma 2.1 for heights, Krull for the dimension at the origin.
  have hA0 : ∀ F : Finset (Fin r), F.card ≤ t →
      ((b + F.card : ℕ) : ℕ∞) ≤ (Ideal.span (Set.range Gh ∪ fh '' F)).height := by
    intro F hF
    obtain ⟨T, hFT, hT⟩ := exists_superset_card_eq hF (by simpa using htr)
    set u : Fin b ⊕ Fin r → MvPolynomial (Option σ) K := Sum.elim Gh fh
    have himg : ∀ A : Finset (Fin r),
        u '' ((univ.disjSum A : Finset (Fin b ⊕ Fin r)) : Set (Fin b ⊕ Fin r)) =
          Set.range Gh ∪ fh '' A := by
      intro A
      ext x
      simp only [Set.mem_image, mem_coe, mem_disjSum, mem_univ, true_and, Set.mem_union,
        Set.mem_range]
      constructor
      · rintro ⟨_, (⟨l, rfl⟩ | ⟨j, hj, rfl⟩), rfl⟩
        exacts [Or.inl ⟨l, rfl⟩, Or.inr ⟨j, hj, rfl⟩]
      · rintro (⟨l, rfl⟩ | ⟨j, hj, rfl⟩)
        exacts [⟨_, Or.inl ⟨l, rfl⟩, rfl⟩, ⟨_, Or.inr ⟨j, hj, rfl⟩, rfl⟩]
    have hu : ∀ i, ∃ n, (u i).IsHomogeneous n := fun i ↦ by
      cases i with
      | inl l => exact ⟨_, hGh l⟩
      | inr j => exact ⟨_, hfh j⟩
    have := card_le_height_span_image hu (disjSum_mono subset_rfl hFT)
      (by rw [himg, hht T hT, card_disjSum, card_univ, Fintype.card_fin, hT])
    rwa [himg, card_disjSum, card_univ, Fintype.card_fin] at this
  have hB0 : ∀ F : Finset (Fin r), F.card ≤ s + 1 →
      originDim (Ideal.span (insert (X none) (Set.range Gh ∪ fh '' F))) ≤
        ((s + 1 - F.card : ℕ) : WithBot ℕ∞) := by
    intro F hF
    obtain ⟨T, hFT, hT⟩ := exists_superset_card_eq hF (by simpa using hsr)
    refine (originDim_le_card ((T \ F).image fh) (fun x hx ↦ ?_) fun y ↦ ?_).trans ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.mp hx
      exact hfh0 i
    · have hle : Ideal.span (insert (X none) (Set.range Gh ∪ fh '' T)) ≤
          Ideal.span (insert (X none) (Set.range Gh ∪ fh '' F)) ⊔
            Ideal.span ((T \ F).image fh : Set (MvPolynomial (Option σ) K)) := by
        rw [Ideal.span_le]
        rintro _ (rfl | ⟨l, rfl⟩ | ⟨i, hi, rfl⟩)
        · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
        · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert_of_mem _ (Or.inl ⟨l, rfl⟩)))
        · by_cases hiF : i ∈ F
          · exact Ideal.mem_sup_left
              (Ideal.subset_span (Set.mem_insert_of_mem _ (Or.inr ⟨i, hiF, rfl⟩)))
          · exact Ideal.mem_sup_right (Ideal.subset_span
              (mem_coe.mpr (mem_image_of_mem fh (mem_sdiff.mpr ⟨hi, hiF⟩))))
      cases y with
      | none =>
        refine ⟨1, Ideal.mem_sup_left ?_⟩
        rw [pow_one]
        exact Ideal.subset_span (Set.mem_insert _ _)
      | some x =>
        obtain ⟨M, hM⟩ := hinf T hT x
        exact ⟨M, hle hM⟩
    · have : ((T \ F).image fh).card ≤ s + 1 - F.card :=
        card_image_le.trans (by rw [card_sdiff_of_subset hFT, hT])
      exact_mod_cast this
  -- The linear forms, one after the other.
  set I : Finset (Fin r) → Finset (Fin r) → (Fin r → MvPolynomial (Option σ) K) →
      Ideal (MvPolynomial (Option σ) K) :=
    fun F H ρ ↦ Ideal.span (Set.range Gh ∪ fh '' F ∪ ρ '' H) with hIdef
  set I₀ : Finset (Fin r) → Finset (Fin r) → (Fin r → MvPolynomial (Option σ) K) →
      Ideal (MvPolynomial (Option σ) K) :=
    fun F H ρ ↦ Ideal.span (insert (X none) (Set.range Gh ∪ fh '' F ∪ ρ '' H)) with hI₀def
  have hstep : ∀ m ≤ r, ∃ ρ : Fin r → MvPolynomial (Option σ) K,
      (∀ i, ρ i ∈ Submodule.span K (X '' V : Set (MvPolynomial (Option σ) K))) ∧
      ∀ F H : Finset (Fin r), Disjoint F H → (∀ i ∈ H, (i : ℕ) < m) →
        (F.card + H.card ≤ t → ((b + F.card + H.card : ℕ) : ℕ∞) ≤ (I F H ρ).height) ∧
        (F.card + H.card ≤ s + 1 →
          originDim (I₀ F H ρ) ≤ ((s + 1 - F.card - H.card : ℕ) : WithBot ℕ∞)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨0, fun _ ↦ zero_mem _, fun F H _ hH ↦ ?_⟩
      have : H = ∅ := eq_empty_of_forall_notMem fun i hi ↦ by simpa using hH i hi
      subst this
      simp only [I, I₀, coe_empty, Set.image_empty, Set.union_empty, card_empty, add_zero,
        Nat.sub_zero]
      exact ⟨hA0 F, hB0 F⟩
    | succ m IH =>
      intro hm
      obtain ⟨ρ, hρV, hρ⟩ := IH (by omega)
      obtain ⟨ρ', hρ'V, hρ'⟩ := exists_mem_span_forall V
        (fun x : Bool × Finset (Fin r) × Finset (Fin r) ↦
          cond x.1 (I x.2.1 x.2.2 ρ) (I₀ x.2.1 x.2.2 ρ))
      set i₀ : Fin r := ⟨m, hm⟩
      refine ⟨Function.update ρ i₀ ρ', fun i ↦ ?_, fun F H hFH hH ↦ ?_⟩
      · by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          exact hρ'V
        · rw [Function.update_of_ne hi]
          exact hρV i
      by_cases hi₀ : i₀ ∈ H
      · set H' := H.erase i₀
        have hH' : ∀ i ∈ H', (i : ℕ) < m := fun i hi ↦ by
          obtain ⟨hne, hiH⟩ := mem_erase.mp hi
          have h1 := hH i hiH
          have h2 : (i : ℕ) ≠ m := fun h ↦ hne (Fin.ext h)
          omega
        have hFH' : Disjoint F H' := disjoint_of_subset_right (erase_subset _ _) hFH
        have hcardH : H.card = H'.card + 1 := (card_erase_add_one hi₀).symm
        have himg : Function.update ρ i₀ ρ' '' ↑H = insert ρ' (ρ '' ↑H') := by
          rw [← insert_erase hi₀, coe_insert, Set.image_insert_eq, Function.update_self]
          congr 1
          refine Set.image_congr fun i hi ↦ Function.update_of_ne ?_ _ _
          exact (mem_erase.mp hi).1
        have hI : I F H (Function.update ρ i₀ ρ') = I F H' ρ ⊔ Ideal.span {ρ'} := by
          simp only [I]
          rw [himg, Set.union_insert, Ideal.span_insert, sup_comm]
        have hI₀ : I₀ F H (Function.update ρ i₀ ρ') = I₀ F H' ρ ⊔ Ideal.span {ρ'} := by
          simp only [I₀]
          rw [himg, Set.union_insert, Set.insert_comm, Ideal.span_insert, sup_comm]
        obtain ⟨hA, hB⟩ := hρ F H' hFH' hH'
        refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
        · rw [hI]
          have := (hρ' (true, F, H')).1 (b + F.card + H'.card) (hA (by omega)) (by omega)
          rwa [hcardH, ← add_assoc]
        · rw [hI₀]
          refine (hρ' (false, F, H')).2 (fun y hy ↦ ?_) (s - F.card - H'.card) ?_ |>.trans ?_
          · obtain rfl : y = none := by
              cases y with
              | none => rfl
              | some y => exact absurd ⟨y, rfl⟩ hy
            exact Ideal.subset_span (Set.mem_insert _ _)
          · refine (hB (by omega)).trans ?_
            exact_mod_cast (by omega : s + 1 - F.card - H'.card ≤ s - F.card - H'.card + 1)
          · exact_mod_cast (by omega : s - F.card - H'.card ≤ s + 1 - F.card - H.card)
      · have hH' : ∀ i ∈ H, (i : ℕ) < m := fun i hi ↦ by
          have h1 := hH i hi
          have h2 : (i : ℕ) ≠ m := fun h ↦ hi₀ (by rwa [show i₀ = i from Fin.ext h.symm])
          omega
        have himg : Function.update ρ i₀ ρ' '' ↑H = ρ '' ↑H :=
          Set.image_congr fun i hi ↦ Function.update_of_ne (by rintro rfl; exact hi₀ hi) _ _
        simp only [I, I₀, himg]
        exact hρ F H hFH hH'
  obtain ⟨ρ, hρV, hρ⟩ := hstep r le_rfl
  have hρ1 : ∀ i, (ρ i).IsHomogeneous 1 := fun i ↦ isHomogeneous_of_mem_span_X (hρV i)
  have hρ' : ∀ F H : Finset (Fin r), Disjoint F H →
      (F.card + H.card ≤ t → ((b + F.card + H.card : ℕ) : ℕ∞) ≤ (I F H ρ).height) ∧
      (F.card + H.card ≤ s + 1 →
        originDim (I₀ F H ρ) ≤ ((s + 1 - F.card - H.card : ℕ) : WithBot ℕ∞)) :=
    fun F H hFH ↦ hρ F H hFH fun i _ ↦ i.isLt
  -- The padding.
  set ρa : Fin r → MvPolynomial σ K := fun i ↦ dehomogenize (ρ i)
  have hρa : ∀ i, (ρa i).totalDegree ≤ 1 := fun i ↦ totalDegree_dehomogenize_le (hρ1 i)
  have hρah : ∀ i, homogenize 1 (ρa i) = ρ i := fun i ↦ homogenize_dehomogenize (hρ1 i)
  set a : Fin r → ℕ := fun i ↦ D - δ i
  have hpow : ∀ i, (ρa i ^ a i).totalDegree ≤ 1 * a i := fun i ↦
    (totalDegree_pow _ _).trans (by have := hρa i; nlinarith)
  set f' : Fin r → MvPolynomial σ K := fun i ↦ f i * ρa i ^ a i
  set g' : MvPolynomial σ K := g * ∏ i, ρa i ^ a i
  have hf'h : ∀ i, homogenize D (f' i) = fh i * ρ i ^ a i := by
    intro i
    have h1 : D = δ i + 1 * a i := by have := hδD i; simp only [a]; omega
    rw [h1, homogenize_mul (hf i) (hpow i), homogenize_pow (hρa i), hρah]
  -- A prime containing the padded forms contains each `fᵢ^h` or `ρᵢ`.
  have hsplit : ∀ (Q : Ideal (MvPolynomial (Option σ) K)), Q.IsPrime → ∀ (T : Finset (Fin r)),
      (∀ i ∈ T, homogenize D (f' i) ∈ Q) →
      ∀ i ∈ T, fh i ∉ Q → ρ i ∈ Q := by
    intro Q hQ T hT i hi hfi
    have := hT i hi
    rw [hf'h] at this
    exact hQ.mem_of_pow_mem _ ((hQ.mem_or_mem this).resolve_left hfi)
  refine exists_eval_eq_zero_of_prod_sub_mem (δ := D) (e := e + ∑ i, a i)
    (s := s) S hG hD0 ht hcard hXh (f := f') (g := g') (fun i ↦ ?_) ?_ ?_ (fun j ↦ ?_) hts
    (fun J hJ x ↦ ?_) ?_
  -- The degrees.
  · refine (totalDegree_mul _ _).trans ?_
    have := hpow i
    have := hδD i
    have := hf i
    simp only [a] at *
    omega
  · refine (totalDegree_mul _ _).trans (add_le_add hg ((totalDegree_finsetProd _ _).trans ?_))
    exact sum_le_sum fun i _ ↦ (hpow i).trans (by rw [one_mul])
  -- The equation.
  · have : ∏ i, f' i - g' = (∏ i, f i - g) * ∏ i, ρa i ^ a i := by
      simp only [f', g', prod_mul_distrib]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ heq
  -- Any `t` of the padded forms.
  · set T := univ.map j
    have hTcard : T.card = t := by simp [T]
    rw [range_append]
    have hrange : Set.range (fun k ↦ homogenize D (f' (j k))) =
        (fun i ↦ homogenize D (f' i)) '' T := by
      ext x
      simp [T]
    rw [hrange]
    set L := Ideal.span (Set.range Gh ∪ (fun i ↦ homogenize D (f' i)) '' ↑T)
    refine le_antisymm ?_ ?_
    · refine (Ideal.height_span_le_ncard_of_span_ne_top (Set.toFinite _) fun htop ↦ ?_).trans ?_
      · have hle : L ≤ RingHom.ker (constantCoeff : MvPolynomial (Option σ) K →+* K) := by
          rw [Ideal.span_le]
          rintro _ (⟨l, rfl⟩ | ⟨i, -, rfl⟩)
          · exact hGh0 l
          · rw [SetLike.mem_coe, RingHom.mem_ker, constantCoeff_eq]
            refine (isHomogeneous_homogenize (?_ : (f' i).totalDegree ≤ D)).coeff_eq_zero ?_
            · refine (totalDegree_mul _ _).trans ?_
              have := hpow i
              have := hδD i
              have := hf i
              simp only [a] at *
              omega
            · intro h
              simp [Finsupp.degree] at h
              omega
        exact (RingHom.ker_ne_top _) (top_le_iff.mp (le_of_eq_of_le htop.symm hle))
      · have h1 : (Set.range Gh).ncard ≤ b := by
          rw [← Set.image_univ]
          exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)
        have h2 : ((fun i ↦ homogenize D (f' i)) '' ↑T).ncard ≤ t := by
          rw [← hTcard, ← Set.ncard_coe_finset]
          exact Set.ncard_image_le (Set.toFinite _)
        exact_mod_cast (Set.ncard_union_le _ _).trans (add_le_add h1 h2)
    · rw [Ideal.height_eq_inf_minimalPrimes]
      refine le_iInf₂ fun Q hQ ↦ ?_
      have hQp := hQ.1.1
      set F := T.filter (fun i ↦ fh i ∈ Q)
      set H := T.filter (fun i ↦ fh i ∉ Q)
      have hFH : F.card + H.card = t := by rw [card_filter_add_card_filter_not, hTcard]
      have hle : I F H ρ ≤ Q := by
        rw [Ideal.span_le]
        rintro _ ((⟨l, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
        · exact hQ.1.2 (Ideal.subset_span (Or.inl ⟨l, rfl⟩))
        · exact (mem_filter.mp hi).2
        · obtain ⟨hiT, hfi⟩ := mem_filter.mp hi
          exact hsplit Q hQp T (fun i hi ↦ hQ.1.2 (Ideal.subset_span (Or.inr ⟨i, hi, rfl⟩)))
            i hiT hfi
      have := (hρ' F H (disjoint_filter_filter_not _ _ _)).1 hFH.le
      rw [add_assoc, hFH] at this
      exact this.trans (Ideal.height_mono hle)
  -- No `s + 1` of the padded forms at infinity.
  · have hrad : X (some x) ∈ (Ideal.span (insert (X none) (Set.range Gh ∪
        Set.range fun i : J ↦ homogenize D (f' i)))).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro Q ⟨hLQ, hQp⟩
      have hmem : ∀ i ∈ J, homogenize D (f' i) ∈ Q := fun i hi ↦
        hLQ (Ideal.subset_span (Set.mem_insert_of_mem _ (Or.inr ⟨⟨i, hi⟩, rfl⟩)))
      set F := J.filter (fun i ↦ fh i ∈ Q)
      set H := J.filter (fun i ↦ fh i ∉ Q)
      have hFH : F.card + H.card = s + 1 := by rw [card_filter_add_card_filter_not, hJ]
      have hle : I₀ F H ρ ≤ Q := by
        rw [Ideal.span_le]
        rintro _ (rfl | ((⟨l, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩))
        · exact hLQ (Ideal.subset_span (Set.mem_insert _ _))
        · exact hLQ (Ideal.subset_span (Set.mem_insert_of_mem _ (Or.inl ⟨l, rfl⟩)))
        · exact (mem_filter.mp hi).2
        · obtain ⟨hiJ, hfi⟩ := mem_filter.mp hi
          exact hsplit Q hQp J hmem i hiJ hfi
      have h0 := (hρ' F H (disjoint_filter_filter_not _ _ _)).2 hFH.le
      rw [show s + 1 - F.card - H.card = 0 by omega, Nat.cast_zero] at h0
      have hhom : ∀ r ∈ insert (X none) (Set.range Gh ∪ fh '' ↑F ∪ ρ '' ↑H),
          ∃ n, r.IsHomogeneous n := by
        rintro _ (rfl | ((⟨l, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩))
        exacts [⟨1, isHomogeneous_X K none⟩, ⟨_, hGh l⟩, ⟨_, hfh i⟩, ⟨1, hρ1 i⟩]
      obtain ⟨M, hM⟩ := pow_mem_of_originDim_nonpos hhom h0 (some x)
      exact hQp.mem_of_pow_mem M (hle hM)
    exact hrad
  -- The inequality.
  · have hrD : r * D = ∑ i, δ i + ∑ i, a i := by
      rw [← sum_add_distrib]
      calc r * D = ∑ _i : Fin r, D := by simp
        _ = _ := sum_congr rfl fun i _ ↦ by have := hδD i; simp only [a]; omega
    rw [hrD, mul_add, mul_add]
    have := Nat.add_lt_add_right hr (t * ∑ i, a i)
    linarith

open scoped Classical in
/-- **Theorem 1** (Corvaja–Zannier 2004). Let `n = |σ| ≥ 2`. If `X₀ g^h` and any `n - 1` of the
`fᵢ^h` have finitely many common zeros in `ℙⁿ`, no `n` of the `fᵢ^h` have a common zero at
infinity, and `∑ deg fᵢ > n max deg fᵢ + deg g`, then on each irreducible component `G = 0` of
`f₁ ⋯ f_r = g` one `q ∉ (G)` vanishes at every `S`-integral point: the `S`-integral solutions
are not Zariski-dense in any component. -/
theorem exists_eval_eq_zero_of_dvd_prod_sub {σ : Type*} [Fintype σ] {r : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hn : 2 ≤ Fintype.card σ)
    {f : Fin r → MvPolynomial σ K} {g : MvPolynomial σ K}
    (hfin : ∀ T : Finset (Fin r), T.card = Fintype.card σ - 1 →
      (Ideal.span (insert (X none * homogenization g)
        ((fun i ↦ homogenization (f i)) '' T))).height = Fintype.card σ)
    (hinf : ∀ J : Finset (Fin r), J.card = Fintype.card σ → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) ((fun i ↦ homogenization (f i)) '' J)))
    (hr : Fintype.card σ * univ.sup (fun i ↦ (f i).totalDegree) + g.totalDegree <
      ∑ i, (f i).totalDegree)
    {G : MvPolynomial σ K} (hG : Irreducible G) (hGF : G ∣ ∏ i, f i - g) :
    ∃ q ∉ Ideal.span {G}, ∀ P : σ → K,
      (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      eval P G = 0 → eval P q = 0 := by
  set n := Fintype.card σ with hndef
  set δ : Fin r → ℕ := fun i ↦ (f i).totalDegree with hδdef
  set e := g.totalDegree with hedef
  set fh : Fin r → MvPolynomial (Option σ) K := fun i ↦ homogenization (f i) with hfhdef
  have hG0 : G ≠ 0 := hG.ne_zero
  have hGdeg : 0 < G.totalDegree := totalDegree_pos_of_irreducible hG
  have hspan : Ideal.span (Set.range ![G]) = Ideal.span {G} := by
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  have hrangeh : (Set.range fun l ↦ homogenization (![G] l)) = {homogenization G} := by
    ext x
    simp
  -- The hypotheses of Theorem 2, with `b = 1`, `t = s = n - 1`.
  have hG' : (Ideal.span (Set.range ![G])).IsPrime := by
    rw [hspan]
    exact (Ideal.span_singleton_prime hG0).mpr hG.prime
  have hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (![G] l)))).height =
      (1 : ℕ) + 1 := by
    rw [hrangeh, height_span_X_none_homogenization hGdeg]
    rfl
  have heq : ∏ i, f i - g ∈ Ideal.span (Set.range ![G]) := by
    rw [hspan]
    exact Ideal.mem_span_singleton.mpr hGF
  have hΔ : e < ∑ i, δ i := by
    have : n * univ.sup δ + e < ∑ i, δ i := hr
    omega
  have hht : ∀ T : Finset (Fin r), T.card = n - 1 →
      (Ideal.span (Set.range (fun l ↦ homogenization (![G] l)) ∪
        (fun i ↦ homogenize (δ i) (f i)) '' T)).height = (1 + (n - 1) : ℕ) := by
    intro T hT
    have hA := hfin T hT
    set A := Ideal.span (insert (X none * homogenization g) (fh '' ↑T))
    have hAhom : ∀ y ∈ insert (X none * homogenization g) (fh '' ↑T),
        ∃ m, y.IsHomogeneous m := by
      rintro _ (rfl | ⟨i, -, rfl⟩)
      exacts [⟨_, (isHomogeneous_X K none).mul (isHomogeneous_homogenization g)⟩,
        ⟨_, isHomogeneous_homogenization (f i)⟩]
    have hAtop : A ≠ ⊤ := fun htop ↦ by
      rw [htop, Ideal.height_top] at hA
      exact ENat.top_ne_natCast _ hA
    rw [hrangeh]
    set L := Ideal.span ({homogenization G} ∪ (fun i ↦ homogenize (δ i) (f i)) '' ↑T)
    refine le_antisymm ?_ ?_
    · refine (Ideal.height_span_le_ncard_of_span_ne_top (Set.toFinite _) fun htop ↦ ?_).trans ?_
      · have hle : L ≤ RingHom.ker (constantCoeff : MvPolynomial (Option σ) K →+* K) := by
          rw [Ideal.span_le]
          rintro _ (h | ⟨i, hi, rfl⟩)
          · rw [Set.mem_singleton_iff.mp h]
            exact constantCoeff_homogenization hGdeg
          · exact constantCoeff_eq_zero_of_mem hAhom hAtop
              (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩))
        exact (RingHom.ker_ne_top _) (top_le_iff.mp (le_of_eq_of_le htop.symm hle))
      · have h2 : ((fun i ↦ homogenize (δ i) (f i)) '' ↑T).ncard ≤ n - 1 := by
          rw [← hT, ← Set.ncard_coe_finset]
          exact Set.ncard_image_le (Set.toFinite _)
        exact_mod_cast (Set.ncard_union_le _ _).trans (add_le_add (by simp) h2)
    · rw [Ideal.height_eq_inf_minimalPrimes]
      refine le_iInf₂ fun Q hQ ↦ ?_
      have hQp := hQ.1.1
      have hGQ : homogenization G ∈ Q := hQ.1.2 (Ideal.subset_span (Or.inl rfl))
      have hfQ : ∀ i ∈ T, fh i ∈ Q := fun i hi ↦
        hQ.1.2 (Ideal.subset_span (Or.inr ⟨i, hi, rfl⟩))
      -- `X₀^(Δ - e) g^h = ∏ fᵢ^h - (∏ fᵢ - g)^h` lies in `Q`.
      set Δ := ∑ i, δ i
      have hprod : homogenize Δ (∏ i, f i) = ∏ i, fh i :=
        homogenize_prod univ fun i ↦ le_rfl
      have hg : homogenize Δ g = homogenization g * X none ^ (Δ - e) := by
        rw [show Δ = e + (Δ - e) by omega]
        rw [homogenize_add_eq_X_pow_mul le_rfl, Nat.add_sub_cancel_left]
        rfl
      have hFQ : homogenize Δ (∏ i, f i - g) ∈ Q := by
        obtain ⟨H, hH⟩ := hGF
        by_cases hH0 : H = 0
        · rw [hH, hH0, mul_zero, map_zero]
          exact Q.zero_mem
        have hdeg : G.totalDegree + H.totalDegree ≤ Δ := by
          rw [← totalDegree_mul_of_isDomain hG0 hH0, ← hH]
          refine (totalDegree_sub _ _).trans (max_le ((totalDegree_finsetProd _ _).trans le_rfl)
            hΔ.le)
        rw [hH, show Δ = G.totalDegree + (Δ - G.totalDegree) by omega,
          homogenize_mul le_rfl (show H.totalDegree ≤ Δ - G.totalDegree by omega)]
        exact Ideal.mul_mem_right _ _ hGQ
      have hprodQ : ∏ i, fh i ∈ Q := by
        obtain ⟨i, hi⟩ : T.Nonempty := card_pos.mp (by omega)
        exact Q.mem_of_dvd (dvd_prod_of_mem fh (mem_univ i)) (hfQ i hi)
      have hgX : homogenization g * X none ^ (Δ - e) ∈ Q := by
        rw [← hg, ← sub_sub_cancel (homogenize Δ (∏ i, f i)) (homogenize Δ g), ← map_sub,
          hprod]
        exact Q.sub_mem hprodQ hFQ
      have hXg : X none * homogenization g ∈ Q := by
        rcases hQp.mem_or_mem hgX with h | h
        · exact Q.mul_mem_left _ h
        · exact Q.mul_mem_right _ (hQp.mem_of_pow_mem _ h)
      have hAQ : A ≤ Q := by
        rw [Ideal.span_le]
        rintro _ (rfl | ⟨i, hi, rfl⟩)
        exacts [hXg, hfQ i hi]
      calc (((1 + (n - 1) : ℕ)) : ℕ∞) = n := by congr 1; omega
        _ = A.height := hA.symm
        _ ≤ Q.height := Ideal.height_mono hAQ
  have hinf' : ∀ J : Finset (Fin r), J.card = n - 1 + 1 → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) (Set.range (fun l ↦ homogenization (![G] l)) ∪
        (fun i ↦ homogenize (δ i) (f i)) '' J)) := by
    intro J hJ x
    obtain ⟨M, hM⟩ := hinf J (by omega) x
    refine ⟨M, Ideal.span_mono ?_ hM⟩
    exact Set.insert_subset_insert Set.subset_union_right
  have hr' : (n - 1) * (n - 1 + 1) * univ.sup δ + (n - 1) * e < (n - 1) * ∑ i, δ i := by
    rw [show n - 1 + 1 = n by omega, mul_assoc, ← mul_add]
    exact Nat.mul_lt_mul_of_pos_left hr (by omega)
  obtain ⟨q, hq, hqP⟩ := exists_eval_eq_zero_of_prod_sub_mem_of_totalDegree_le S hG'
    (by omega : 0 < n - 1) (by omega : Fintype.card σ = 1 + (n - 1)) hXh
    (fun i ↦ le_rfl) le_rfl heq hht le_rfl hinf' hr'
  refine ⟨q, hspan ▸ hq, fun P hP hGP ↦ hqP P hP fun l ↦ ?_⟩
  rw [Fin.fin_one_eq_zero l]
  exact hGP

open scoped Classical in
/-- **Theorem 1 for `n = 2`: finiteness** (Corvaja–Zannier 2004). In the plane, under the
hypotheses of Theorem 1, `f₁ ⋯ f_r = g` has finitely many `S`-integral solutions: on each
irreducible component `G = 0` the solutions are zeros of some `q ∉ (G)`, and `(G, q)` has height
`2`, so finitely many zeros. With `fᵢ` linear forms and `g` constant this is Thue's theorem. -/
theorem finite_setOf_eval_prod_sub_eq_zero {σ : Type*} [Fintype σ] {r : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hn : Fintype.card σ = 2)
    {f : Fin r → MvPolynomial σ K} {g : MvPolynomial σ K}
    (hfin : ∀ i, (Ideal.span {X none * homogenization g, homogenization (f i)}).height = 2)
    (hinf : ∀ J : Finset (Fin r), J.card = 2 → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) ((fun i ↦ homogenization (f i)) '' J)))
    (hr : 2 * univ.sup (fun i ↦ (f i).totalDegree) + g.totalDegree < ∑ i, (f i).totalDegree) :
    {P : σ → K | (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      eval P (∏ i, f i - g) = 0}.Finite := by
  set F := ∏ i, f i - g
  -- The `fᵢ` are nonzero, so `F ≠ 0` by degrees.
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h0
    have h := hfin i
    rw [h0, show homogenization (0 : MvPolynomial σ K) = 0 from map_zero _, Set.pair_comm,
      Ideal.span_insert_zero] at h
    have hnu : ¬ IsUnit (X none * homogenization g : MvPolynomial (Option σ) K) := fun hu ↦ by
      have := (hu.map (constantCoeff : MvPolynomial (Option σ) K →+* K)).ne_zero
      simp at this
    have := (Ideal.height_span_singleton_le_one hnu).trans_lt (by norm_num : (1 : ℕ∞) < 2)
    rw [h] at this
    exact lt_irrefl _ this
  have hF0 : F ≠ 0 := by
    intro hF
    have hdeg : ∀ s : Finset (Fin r), (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [prod_insert ha, sum_insert ha, totalDegree_mul_of_isDomain (hf0 a)
          (prod_ne_zero_iff.mpr fun i _ ↦ hf0 i), ih]
    have : ∏ i, f i = g := sub_eq_zero.mp hF
    have h1 := hdeg univ
    rw [this] at h1
    omega
  -- One `q` per irreducible factor.
  have hq : ∀ G ∈ UniqueFactorizationMonoid.factors F, ∃ q ∉ Ideal.span {G}, ∀ P : σ → K,
      (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      eval P G = 0 → eval P q = 0 := fun G hG ↦
    exists_eval_eq_zero_of_dvd_prod_sub S hn.ge (fun T hT ↦ by
        obtain ⟨i, rfl⟩ := card_eq_one.mp (by omega : T.card = 1)
        rw [coe_singleton, Set.image_singleton, hn]
        exact_mod_cast hfin i)
      (fun J hJ ↦ hinf J (hJ.trans hn)) (by rw [hn]; exact hr)
      (UniqueFactorizationMonoid.irreducible_of_factor G hG)
      (UniqueFactorizationMonoid.dvd_of_mem_factors hG)
  choose! q hqG hqP using hq
  refine Set.Finite.subset (Set.Finite.biUnion
    (UniqueFactorizationMonoid.factors F).toFinset.finite_toSet fun G _ ↦
      finite_setOf_forall_eval_eq_zero (I := Ideal.span {G, q G}) ?_) ?_
  · rename_i hG
    have hG' := Multiset.mem_toFinset.mp hG
    rw [Nat.card_eq_fintype_card, hn]
    exact two_le_height_span_pair (UniqueFactorizationMonoid.prime_of_factor G hG') (hqG G hG')
  · rintro P ⟨hP, hFP⟩
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hF0
    have hprod : eval P (UniqueFactorizationMonoid.factors F).prod = 0 := by
      have h := congrArg (eval P) hu
      rw [map_mul, hFP] at h
      exact (mul_eq_zero.mp h).resolve_right ((u.isUnit.map (eval P)).ne_zero)
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
    obtain ⟨G, hG, hGP⟩ := hprod
    refine Set.mem_biUnion (Multiset.mem_toFinset.mpr hG) fun p hp ↦ ?_
    have hle : Ideal.span {G, q G} ≤ RingHom.ker (eval P) := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      exacts [hGP, hqP G hG P hP hGP]
    exact hle hp

end NumberField
