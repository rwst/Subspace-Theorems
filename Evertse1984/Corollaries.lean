/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.AdmissiblePoints
public import DiophantineApproximation.RationalPlaces
public import Mathlib.NumberTheory.Padics.PadicNorm

-- Used only inside proofs.
import DiophantineApproximation.NormForm
import Mathlib.NumberTheory.Height.NumberField

/-!
# Evertse's Corollaries 1 and 2

**Corollary 2** (Evertse 1984, p. 228). For `ε > 0` there is `C₁ > 0` such that for every `T` and
every `x ∈ 𝓞_Kⁿ⁺¹` with `x₀ x₁ ⋯ xₙ (x₀ + ⋯ + xₙ) ≠ 0`, vanishing subsums allowed,

```text
(∏_k ∏_{v ∈ S∞ ∪ S} ‖x_k‖_v) · ∏_{v ∈ T} ‖x₀ + ⋯ + xₙ‖_v
    ≥ C₁ · (∏_{v ∈ T} min_k ‖x_k‖_v) · ‖x‖^(-ε).
```

A minimal subsum `∑_{j ∈ J} x_j` equal to the whole sum has no vanishing subsum, so Theorem 2
applies to it; the coordinates outside `J` contribute at least `1` by the product formula, the
maximum over `J` is at least the minimum over all coordinates, and `‖x_J‖ ≤ ‖x‖`.

**Corollary 1** (Evertse 1984, p. 227). For `c > 0`, `0 ≤ d < 1` and a finite set `S₀` of primes
there are only finitely many `x ∈ ℤⁿ⁺¹` with `x₀ + ⋯ + xₙ = 0`, no vanishing nonempty proper
subsum, `gcd(x₀, …, xₙ) = 1` and

```text
∏_k (|x_k| ∏_{p ∈ S₀} |x_k|_p) ≤ c · ‖x‖ ^ d,   ‖x‖ = max_k |x_k|.
```

This is Theorem 1 over `ℚ`: for coprime integers `H(x) = ‖x‖` (Mathlib's
`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`), so the height is bounded, and there are finitely many
integer tuples of bounded size.

## Main results

* `NumberField.exists_pos_forall_placeProd_iInf_le`: **Corollary 2**.
* `Rat.placeProd_primes_apply`: the product over `S∞ ∪ S₀` over `ℚ`.
* `Rat.finite_setOf_sum_eq_zero_of_gcd_eq_one`: **Corollary 1**.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, Corollaries 1 and 2.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- **Evertse's Corollary 2**: Theorem 2 with vanishing subsums allowed, for nonzero coordinates
with nonzero sum, and the minimum in place of the maximum. -/
theorem exists_pos_forall_placeProd_iInf_le (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (T : Set (AbsoluteValue K ℝ)) (x : ι → K), (∀ i, IsIntegral ℤ (x i)) →
      (∀ i, x i ≠ 0) → ∑ i, x i ≠ 0 →
      C * placeProd S T (fun v ↦ ⨅ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε) ≤
        (∏ i, placeProd S Set.univ (fun v ↦ v (x i))) *
          placeProd S T (fun v ↦ v (∑ i, x i)) := by
  classical
  have hf : ∀ p : Set (AbsoluteValue K ℝ) × (ι → K),
      0 ≤ placeProd S p.1 (fun v ↦ ⨅ i, v (p.2 i)) * (⨆ i, house (p.2 i)) ^ (-ε) :=
    fun p ↦ mul_nonneg (placeProd_nonneg S _ fun v _ ↦ Real.iInf_nonneg fun i ↦ apply_nonneg _ _)
      (Real.rpow_nonneg (Real.iSup_nonneg fun i ↦ house_nonneg _) _)
  obtain ⟨C, hC, hCx⟩ := exists_pos_forall_le_of_finite (s := (Set.univ : Set (Finset ι)))
    Set.finite_univ hf
    (g := fun p ↦ (∏ i, placeProd S Set.univ (fun v ↦ v (p.2 i))) *
      placeProd S p.1 (fun v ↦ v (∑ i, p.2 i)))
    (A := fun J p ↦ (∀ i, IsIntegral ℤ (p.2 i)) ∧ (∀ i, p.2 i ≠ 0) ∧ J.Nonempty ∧
      ∑ i ∈ J, p.2 i = ∑ i, p.2 i ∧ ∀ I ⊆ J, I.Nonempty → ∑ i ∈ I, p.2 i ≠ 0)
    fun J _ ↦ by
      obtain ⟨C, hC, h2⟩ := exists_pos_forall_placeProd_le S J hε
      refine ⟨C, hC, fun ⟨T, x⟩ ⟨hint, hx0, hJ, hJsum, hJnv⟩ ↦ ?_⟩
      dsimp only
      have : Nonempty J := hJ.to_subtype
      set y : J → K := fun j ↦ x j with hy
      have hyint : ∀ j, IsIntegral ℤ (y j) := fun j ↦ hint j
      have hynv : ∀ I : Finset J, I.Nonempty → ∑ j ∈ I, y j ≠ 0 := by
        intro I hI
        have hmap : ∑ j ∈ I, y j = ∑ i ∈ I.map (Function.Embedding.subtype _), x i := by
          rw [Finset.sum_map]; rfl
        rw [hmap]
        refine hJnv _ (fun i hi ↦ ?_) hI.map
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
        exact j.2
      have key := h2 T y hyint hynv
      have hysum : ∑ j, y j = ∑ i, x i := by
        rw [← hJsum, hy, Finset.sum_coe_sort J x]
      rw [hysum] at key
      -- the coordinates outside `J` contribute at least `1`
      have hprod : ∏ j, placeProd S Set.univ (fun v ↦ v (y j)) ≤
          ∏ i, placeProd S Set.univ (fun v ↦ v (x i)) := by
        have hone : ∀ i, 1 ≤ placeProd S Set.univ (fun v ↦ v (x i)) :=
          fun i ↦ one_le_placeProd_univ S (hint i) (hx0 i)
        rw [hy, Finset.prod_coe_sort J (fun i ↦ placeProd S Set.univ (fun v ↦ v (x i))),
          ← Finset.prod_sdiff (Finset.subset_univ J)]
        refine le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ (zero_le_one.trans (hone i)))
          ?_
        calc (1 : ℝ) = ∏ _i ∈ Finset.univ \ J, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) fun i _ ↦ hone i
      -- the minimum over all coordinates is at most the maximum over `J`
      have hmin : placeProd S T (fun v ↦ ⨅ i, v (x i)) ≤ placeProd S T (fun v ↦ ⨆ j, v (y j)) := by
        obtain ⟨j₀⟩ := this
        refine placeProd_le_placeProd S T (fun v _ ↦ Real.iInf_nonneg fun i ↦ apply_nonneg _ _)
          fun v _ ↦ ?_
        exact (ciInf_le (Finite.bddBelow_range _) (j₀ : ι)).trans
          (le_ciSup (f := fun j ↦ v (y j)) (Finite.bddAbove_range _) j₀)
      -- `‖x_J‖ ≤ ‖x‖`
      obtain ⟨j₀⟩ := id this
      have hy1 : 1 ≤ ⨆ j, house (y j) := one_le_iSup_house (hyint j₀) (hx0 j₀)
      have hhouse : (⨆ i, house (x i)) ^ (-ε) ≤ (⨆ j, house (y j)) ^ (-ε) :=
        Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hy1)
          (ciSup_le fun j ↦ house_le_iSup_house x j) (neg_nonpos.mpr hε.le)
      calc C * (placeProd S T (fun v ↦ ⨅ i, v (x i)) * (⨆ i, house (x i)) ^ (-ε))
          ≤ C * placeProd S T (fun v ↦ ⨆ j, v (y j)) * (⨆ j, house (y j)) ^ (-ε) := by
            rw [← mul_assoc]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hmin hC.le) hhouse
              (Real.rpow_nonneg (Real.iSup_nonneg fun i ↦ house_nonneg _) _)
              (mul_nonneg hC.le (placeProd_nonneg S _ fun v _ ↦
                Real.iSup_nonneg fun j ↦ apply_nonneg _ _))
        _ ≤ _ := key
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod
              (placeProd_nonneg S _ fun v _ ↦ apply_nonneg _ _)
  refine ⟨C, hC, fun T x hint hx0 hsum ↦ ?_⟩
  obtain ⟨J, -, hJsum, hJnv⟩ := exists_subset_sum_eq_forall_ne_zero x Finset.univ
  have hJ : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hsum (by rw [← hJsum, Finset.sum_empty])
  rw [mul_assoc]
  exact hCx (T, x) ⟨J, Set.mem_univ _, hint, hx0, hJ, hJsum, hJnv⟩

end NumberField

namespace Rat

open NumberField

/-- The height-one primes of `𝓞 ℚ` at a finite set of primes. -/
noncomputable def heightOneSpectrumOfPrimes (S₀ : Finset Nat.Primes) :
    Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  open scoped Classical in S₀.image fun p ↦ (finitePlace p).maximalIdeal

/-- **The product over `S∞ ∪ S₀` over `ℚ`**: `|q| · ∏_{p ∈ S₀} |q|_p`. -/
theorem placeProd_primes_apply (S₀ : Finset Nat.Primes) (q : ℚ) :
    placeProd (heightOneSpectrumOfPrimes S₀) Set.univ (fun v ↦ v q) =
      |(q : ℝ)| * ∏ p ∈ S₀, (padicNorm (p : ℕ) q : ℝ) := by
  classical
  have hinj : Set.InjOn (fun p : Nat.Primes ↦ (finitePlace p).maximalIdeal) S₀ := by
    intro p _ p' _ h
    apply finitePlace_injective
    rw [← FinitePlace.mk_maximalIdeal (finitePlace p), ← FinitePlace.mk_maximalIdeal
      (finitePlace p')]
    exact congrArg FinitePlace.mk h
  have hmult : (InfinitePlace.mult (default : InfinitePlace ℚ)) = 1 := by
    have h := InfinitePlace.sum_mult_eq (K := ℚ)
    rwa [Fintype.sum_unique, Module.finrank_self] at h
  simp only [placeProd, Set.mulIndicator_univ]
  unfold heightOneSpectrumOfPrimes
  rw [Fintype.prod_unique, hmult, pow_one, Finset.prod_image hinj]
  congr 1
  · rw [← Rat.cast_abs]; exact Rat.infinitePlace_apply _ q
  · refine Finset.prod_congr rfl fun p _ ↦ ?_
    change FinitePlace.mk (finitePlace p).maximalIdeal q = _
    rw [FinitePlace.mk_maximalIdeal, finitePlace_apply]

/-- **Evertse's Corollary 1**: Theorem 1 over `ℚ`. For `0 ≤ d < 1` and a finite set `S₀` of
primes, only finitely many integer tuples `x` with `x₀ + ⋯ + xₙ = 0`, no vanishing nonempty
proper subsum and `gcd(x₀, …, xₙ) = 1` satisfy `∏_k (|x_k| ∏_{p ∈ S₀} |x_k|_p) ≤ c · ‖x‖ ^ d`,
where `‖x‖ = max_k |x_k|`. The hypothesis `c > 0` of the paper is not needed. -/
theorem finite_setOf_sum_eq_zero_of_gcd_eq_one (ι : Type*) [Fintype ι] (S₀ : Finset Nat.Primes)
    {c d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    {x : ι → ℤ | ∑ i, x i = 0 ∧
      (∀ I : Finset ι, I.Nonempty → I ≠ Finset.univ → ∑ i ∈ I, x i ≠ 0) ∧
      Finset.univ.gcd x = 1 ∧
      ∏ k, ((|x k| : ℝ) * ∏ p ∈ S₀, (padicNorm (p : ℕ) (x k) : ℝ)) ≤
        c * ((⨆ k, |x k| : ℤ) : ℝ) ^ d}.Finite := by
  obtain ⟨B, hB⟩ := exists_forall_admissible_mulHeight_le (heightOneSpectrumOfPrimes S₀) ι
    (c := c) hd0 hd1
  refine (Set.Finite.pi (t := fun _ : ι ↦ Set.Icc (-⌈B⌉) ⌈B⌉)
    fun _ ↦ Set.finite_Icc _ _).subset ?_
  rintro x ⟨hsum, hnv, hgcd, hadm⟩
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.gcd_empty] at hgcd
    exact zero_ne_one hgcd
  set y : ι → ℚ := ((↑) : ℤ → ℚ) ∘ x with hy
  have hy0 : y ≠ 0 := by
    intro h
    have hx : x = 0 := funext fun i ↦ by
      have := congrFun h i
      simpa [hy] using this
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)] at hgcd
    exact zero_ne_one hgcd
  have hH := mulHeight_eq_max_abs_of_gcd_eq_one hgcd
  have hyH := hB y hy0 (fun i ↦ mem_integer_of_isIntegral (isIntegral_algebraMap (x := x i)))
    (by
      rw [hH]
      refine (le_of_eq (Finset.prod_congr rfl fun k _ ↦ ?_)).trans hadm
      rw [placeProd_primes_apply]
      simp [hy])
    (by simp [hy, ← Int.cast_sum, hsum])
    (fun I hI hIu ↦ by
      simpa [hy, ← Int.cast_sum] using hnv I hI hIu)
  rw [hH] at hyH
  intro k _
  have hk : (|x k| : ℝ) ≤ B := by
    refine le_trans ?_ hyH
    exact_mod_cast le_ciSup (f := fun k ↦ |x k|) (Finite.bddAbove_range _) k
  have hk' : |x k| ≤ ⌈B⌉ := by exact_mod_cast hk.trans (Int.le_ceil B)
  exact abs_le.mp hk'

end Rat
