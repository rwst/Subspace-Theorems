/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSystemCount
public import DiophantineApproximation.LinearFormSubspaces

-- Used only inside proofs.
import ArithmeticHeights.Extension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic

/-!
# The quantitative Subspace Theorem for real forms in `1, α, α²`

The bound on `δ` in (6.1) uses the quantitative Subspace Theorem three times, always for forms
whose coefficients are `b₀ + b₁ α + b₂ α²` with integers `bᵢ`, and always at integer points. This
file states what is used (`Real.SubspaceBound α a`: the solutions lie in at most
`K δ^{-a} (1 + log δ⁻¹)²` proper subspaces, above a threshold polynomial in `δ⁻¹` and linear in the
logarithms of the data) and proves it with `a = 3` from the repository's Evertse–Ferretti count
(`NumberField.exists_finset_submodule_of_efSystemThreshold_le`, `NumberField.efLargeCount_le_ef`).

## Main definitions

* `Real.quadVal α b`: `b₀ + b₁ α + b₂ α²`.
* `Real.SubspaceBound α a`: the quantitative Subspace Theorem for such forms in `2 ≤ n ≤ 4`
  variables, with `δ^{-a}` subspaces.

## Main results

* `Real.subspaceBound_three`: **Evertse–Ferretti 2013**: `Real.SubspaceBound α 3` for every real
  algebraic `α`.
* `Real.SubspaceBound.mono`: a larger exponent is weaker; Evertse–Schlickewei 2002's
  `δ^{-n-4}` gives `Real.SubspaceBound α 8` in `n ≤ 4` variables.

## Implementation notes

⚠ **The forms are normalized here, not by the caller.** The repository's count is for systems
under Evertse's normalization (2.4): one constant `C ≤ |det|^{1/n}` for all forms and an exponent
equal to `1`. The caller gives any constant `C ≥ 1` and a lower bound `γ` for `|det|`; the forms
whose exponent is within `τ = δ / 2n` of `1` keep their exponent, the others are multiplied by a
power of `2` and their exponent is raised by `τ`. That costs half of `δ` and a threshold linear in
`log C` and `log γ⁻¹`.
-/

@[expose] public section

open Module Finset Height NumberField IsDedekindDomain Polynomial

namespace Real

/-- `b₀ + b₁ α + b₂ α²`. -/
noncomputable def quadVal (α : ℝ) (b : Fin 3 → ℤ) : ℝ := b 0 + b 1 * α + b 2 * α ^ 2

/-- **A Galois number field containing `α`**, inside `ℂ`: the splitting field of the minimal
polynomial. -/
theorem exists_isGalois_mem {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ∃ E : IntermediateField ℚ ℂ, IsGalois ℚ E ∧ FiniteDimensional ℚ E ∧ (α : ℂ) ∈ E := by
  have hint : IsIntegral ℚ (α : ℂ) := (hα.algebraMap (A := ℂ)).isIntegral
  set f := minpoly ℚ (α : ℂ)
  have hsplit : IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet ℂ)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet ℂ)) :=
    IsSplittingField.finiteDimensional _ f
  refine ⟨IntermediateField.adjoin ℚ (f.rootSet ℂ), ?_, hfd, ?_⟩
  · exact isGalois_iff.2 ⟨inferInstance, Normal.of_isSplittingField f⟩
  · exact IntermediateField.subset_adjoin _ _
      ((mem_rootSet).2 ⟨minpoly.ne_zero hint, minpoly.aeval ℚ _⟩)

end Real

namespace Height

/-- **The affine height of an integer point** is its sup norm. -/
theorem mulHeightAff_intCast {ι : Type*} [Finite ι] {x : ι → ℤ} (hx : x ≠ 0) :
    mulHeightAff (fun i ↦ (x i : ℚ)) = ⨆ i, |(x i : ℝ)| := by
  have := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have h1 : (1 : ℝ) ≤ ⨆ i, |(x i : ℝ)| := by
    refine le_trans ?_ (Finite.le_ciSup_of_le i₀ le_rfl)
    have : (1 : ℤ) ≤ |x i₀| := Int.one_le_abs hi₀
    exact_mod_cast this
  refine le_antisymm ?_ (ciSup_le fun i ↦ ?_)
  · -- the tuple `(1, x)` is an integer tuple
    set y : Option ι → ℤ := fun o ↦ o.elim 1 x
    have hy : (fun o ↦ (y o : ℚ)) ≠ 0 := fun h ↦ by simpa [y] using congrFun h none
    have h := Rat.mulHeight_intCast_le_iSup Rat.infinitePlace hy
    have heq : (fun o : Option ι ↦ ((y o : ℤ) : ℚ)) = fun o : Option ι ↦ o.elim 1
        fun i ↦ (x i : ℚ) := by
      funext o; cases o <;> simp [y]
    rw [heq] at h
    refine h.trans (ciSup_le fun o ↦ ?_)
    cases o with
    | none => simpa [y] using h1
    | some i =>
      simp only [y, Option.elim_some, Rat.infinitePlace_apply, Rat.cast_abs, Rat.cast_intCast]
      exact Finite.le_ciSup_of_le i le_rfl
  · have h := mulHeight₁_le_mulHeightAff (fun i ↦ (x i : ℚ)) i
    rw [Rat.mulHeight₁_eq_max] at h
    refine le_trans ?_ h
    have : |(x i : ℝ)| = ((x i).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    exact_mod_cast le_max_left (((x i : ℚ)).num.natAbs) ((x i : ℚ)).den |>.trans' (by simp)

end Height

namespace NumberField

open Height

/-- **The height of `c₀ + c₁ β + c₂ β²`** for integers `|cᵢ| ≤ B` in a number field `E`. -/
theorem absMulHeight₁_sum_le {E : Type*} [Field E] [NumberField E] (β : E) (c : Fin 3 → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hc : ∀ m, |(c m : ℝ)| ≤ B) :
    absMulHeight₁ (∑ m : Fin 3, (c m : E) * β ^ (m : ℕ)) ≤
      3 ^ finrank ℚ E * B ^ (3 * finrank ℚ E) * mulHeight₁ β ^ 3 := by
  set d := finrank ℚ E
  have hd : 0 < d := finrank_pos
  set y := ∑ m : Fin 3, (c m : E) * β ^ (m : ℕ)
  -- the absolute height is at most the relative one
  have habs : absMulHeight₁ y ≤ mulHeight₁ y := by
    have h := absMulHeight₁_pow_finrank y
    have h0 : 0 ≤ absMulHeight₁ y := by
      rw [absMulHeight₁_eq]; exact Real.rpow_nonneg (mulHeight₁_nonneg y) _
    have h1 : 1 ≤ absMulHeight₁ y := by
      by_contra hlt
      push Not at hlt
      have : absMulHeight₁ y ^ d < 1 := pow_lt_one₀ h0 hlt hd.ne'
      rw [h] at this
      exact absurd (one_le_mulHeight₁ y) (not_le.mpr this)
    rw [← h]
    exact le_self_pow₀ h1 hd.ne'
  refine habs.trans ?_
  -- the integer coefficients
  have hint (m : Fin 3) : mulHeight₁ (c m : E) ≤ B ^ d := by
    have h := mulHeight₁_pow_finrank (K := ℚ) (L := E) ((c m : ℤ) : ℚ)
    rw [map_intCast] at h
    rw [← h, Rat.mulHeight₁_eq_max]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ d
    rw [Nat.cast_max]
    refine max_le ?_ ?_
    · have : (((c m : ℚ)).num.natAbs : ℝ) = |(c m : ℝ)| := by
        rw [Rat.num_intCast, Nat.cast_natAbs, Int.cast_abs]
      rw [this]; exact hc m
    · rw [Rat.den_intCast]; simpa using hB
  have hterm (m : Fin 3) :
      mulHeight₁ ((c m : E) * β ^ (m : ℕ)) ≤ B ^ d * mulHeight₁ β ^ (m : ℕ) := by
    calc _ ≤ mulHeight₁ (c m : E) * mulHeight₁ (β ^ (m : ℕ)) := mulHeight₁_mul_le _ _
      _ = mulHeight₁ (c m : E) * mulHeight₁ β ^ (m : ℕ) := by rw [mulHeight₁_pow]
      _ ≤ B ^ d * mulHeight₁ β ^ (m : ℕ) :=
          mul_le_mul_of_nonneg_right (hint m) (pow_nonneg (mulHeight₁_nonneg β) _)
  have hsum := mulHeight₁_sum_le (K := E) (s := (univ : Finset (Fin 3))) univ_nonempty
    (fun m ↦ (c m : E) * β ^ (m : ℕ))
  rw [totalWeight_eq_finrank, card_univ, Fintype.card_fin] at hsum
  calc mulHeight₁ y ≤ (3 : ℝ) ^ d * ∏ m : Fin 3, mulHeight₁ ((c m : E) * β ^ (m : ℕ)) := by
        exact_mod_cast hsum
    _ ≤ 3 ^ d * ∏ m : Fin 3, (B ^ d * mulHeight₁ β ^ (m : ℕ)) :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun m _ ↦ mulHeight₁_nonneg _)
          fun m _ ↦ hterm m) (by positivity)
    _ = 3 ^ d * B ^ (3 * d) * mulHeight₁ β ^ 3 := by
        simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
        ring

/-- **The threshold of Q4.2, in closed form**, for the systems used here: `R = n`, `K = ℚ` and
`[E : ℚ] = d`. -/
theorem domainThreshold_le_div {n d c : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) (hd : 1 ≤ d) {δ L : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 ≤ L) :
    domainThreshold n d (n * d) (efEps d δ) (efSpread d n δ) (c * n ^ 2 * (d * L)) ≤
      ((1 + 10 * ((n * d + n).choose n : ℝ)) * (23 + 64 * c * L) + 60) / δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  rw [domainThreshold, domainDelta_efEps (by omega) (by omega) hδ, efSystemDelta, efSpread]
  set ch : ℝ := ((n * d + n).choose n : ℝ)
  have hch : 0 ≤ ch := Nat.cast_nonneg _
  -- `n! ≤ 24` and `n ≤ 4`
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfact : Real.log (n.factorial : ℝ) ≤ 23 := by
    have h24 : (n.factorial : ℝ) ≤ 24 := by
      have : n.factorial ≤ 24 := by interval_cases n <;> decide
      exact_mod_cast this
    linarith [Real.log_le_sub_one_of_pos hfpos]
  have hfact0 : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hlogn : Real.log n ≤ 3 := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- the leading factor is at most `1`
  have key : (d : ℝ) / (2 * (d * (1 + δ / n) / 2)) = 1 / (1 + δ / n) := by
    field_simp
  rw [key]
  have hA0 : 0 < 1 / (1 + δ / n) := by positivity
  have hA1 : 1 / (1 + δ / n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 0 ≤ δ / n := by positivity
    linarith
  set G := Real.log (n.factorial : ℝ) + n * (c * n ^ 2 * (d * L)) / d
  have hGeq : G = Real.log (n.factorial : ℝ) + n ^ 3 * c * L := by
    simp only [G]
    field_simp
  have hG0 : 0 ≤ G := by rw [hGeq]; positivity
  have hGle : G ≤ 23 + 64 * c * L := by
    rw [hGeq]
    have : (n : ℝ) ^ 3 ≤ 64 := by
      calc (n : ℝ) ^ 3 ≤ 4 ^ 3 := by gcongr
        _ = 64 := by norm_num
    have : (n : ℝ) ^ 3 * c * L ≤ 64 * c * L := by gcongr
    linarith
  have t2 : Real.log n / (δ / (4 * (n + δ))) ≤ 60 / δ := by
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hδ]
    nlinarith
  have t3 : ch * G / (n * (δ / (4 * (n + δ)))) ≤ 10 * ch * G / δ := by
    have hq : 0 < n * (δ / (4 * (n + δ))) := by positivity
    have h : δ ≤ 10 * (n * (δ / (4 * (n + δ)))) := by
      rw [show 10 * (n * (δ / (4 * (n + δ)))) = 10 * n * δ / (4 * (n + δ)) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    rw [div_le_div_iff₀ hq hδ]
    calc ch * G * δ ≤ ch * G * (10 * (n * (δ / (4 * (n + δ))))) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hch hG0)
      _ = 10 * ch * G * (n * (δ / (4 * (n + δ)))) := by ring
  have hGδ : G ≤ G / δ := le_div_self hG0 hδ hδ1
  calc 1 / (1 + δ / n) * (G + Real.log n / (δ / (4 * (n + δ))) +
        ch * G / (n * (δ / (4 * (n + δ)))))
      ≤ 1 * (G / δ + 60 / δ + 10 * ch * G / δ) := by
        gcongr
    _ = ((1 + 10 * ch) * G + 60) / δ := by ring
    _ ≤ ((1 + 10 * ch) * (23 + 64 * c * L) + 60) / δ := by
        gcongr

end NumberField

namespace Real

open NumberField

/-- **The quantitative Subspace Theorem for forms in `1, α, α²`, with `δ^{-a}` subspaces.** For
`2 ≤ n ≤ 4` there is `K` such that: for forms `∑_k quadVal α (P i k) X_k` with integer data
`|P i k m| ≤ B` and determinant at least `γ` in absolute value, a constant `C ≥ 1` and exponents
`e i ≤ 1`, one of them `1`, of sum at most `-δ`, the nonzero integer points `x` with
`|∑_k quadVal α (P i k) x_k| ≤ C |x|^{e i}` for all `i` and
`log |x| ≥ K δ^{-K} (1 + log B + log C + log γ⁻¹)` lie in at most `K δ^{-a} (1 + log δ⁻¹)²` proper
subspaces of `ℚⁿ`. -/
def SubspaceBound (α a : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 0 < K ∧
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ i, e i ≤ 1) →
      (∃ i, e i = 1) → ∑ i, e i ≤ -δ →
    ∃ T : Finset (Submodule ℚ (Fin n → ℚ)), (#T : ℝ) ≤ K * δ⁻¹ ^ a * (1 + log δ⁻¹) ^ 2 ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        K * δ⁻¹ ^ K * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        ∃ U ∈ T, (fun k ↦ (x k : ℚ)) ∈ U

/-- A larger exponent is a weaker statement. -/
theorem SubspaceBound.mono {α a b : ℝ} (h : SubspaceBound α a) (hab : a ≤ b) :
    SubspaceBound α b := by
  intro n hn2 hn4
  obtain ⟨K, hK, hT⟩ := h n hn2 hn4
  refine ⟨K, hK, fun P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum ↦ ?_⟩
  obtain ⟨T, hcard, hT, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum
  refine ⟨T, hcard.trans ?_, hT, hmem⟩
  have h1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have := Real.rpow_le_rpow_of_exponent_le h1 hab
  gcongr

/-- **EF13's count in closed form**, at `R = n` forms and `δ / 2`. -/
theorem efLargeCount_half_le {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      efLargeCount n d n (δ / 2) ≤ K * δ⁻¹ ^ (3 : ℝ) * (1 + log δ⁻¹) ^ 2 := by
  set m : ℝ := ((n * d : ℕ) : ℝ)
  have hm : 2 ≤ m := by
    have : 2 ≤ n * d := by nlinarith
    simp only [m]
    exact_mod_cast this
  have hlog6 : 1 ≤ Real.log 6 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hl1 : 0 ≤ Real.log (6 * m) := Real.log_nonneg (by linarith)
  have hl3 : 1 ≤ Real.log (3 * m) :=
    hlog6.trans (Real.log_le_log (by norm_num) (by linarith))
  have hl2 : 0 ≤ Real.log (2 * Real.log (3 * m)) := Real.log_nonneg (by linarith)
  set c0 : ℝ := 2 * 10 ^ 13 * 4 ^ n * (n : ℝ) ^ 14
  refine ⟨c0 * 8 * (Real.log (6 * m) + 1) * (Real.log (2 * Real.log (3 * m)) + 1),
    by positivity, fun δ hδ hδ1 ↦ ?_⟩
  have hδ2 : 0 < δ / 2 := by positivity
  have h := efLargeCount_le_ef (n := n) (e := d) (r := n) hn hd (by omega) hδ2 (by linarith)
  have hinv : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).2 hδ1)
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  -- the two logarithms
  have e1 : Real.log (3 * m / (δ / 2)) = Real.log (6 * m) + Real.log δ⁻¹ := by
    rw [← Real.log_mul (by positivity) hδi.ne']
    congr 1
    field_simp
    ring
  have e2 : Real.log (Real.log (3 * m) / (δ / 2)) =
      Real.log (2 * Real.log (3 * m)) + Real.log δ⁻¹ := by
    rw [← Real.log_mul (by positivity) hδi.ne']
    congr 1
    field_simp
  have f1 : Real.log (3 * m / (δ / 2)) ≤ (Real.log (6 * m) + 1) * (1 + Real.log δ⁻¹) := by
    rw [e1]; nlinarith
  have f2 : Real.log (Real.log (3 * m) / (δ / 2)) ≤
      (Real.log (2 * Real.log (3 * m)) + 1) * (1 + Real.log δ⁻¹) := by
    rw [e2]; nlinarith
  have f10 : 0 ≤ Real.log (3 * m / (δ / 2)) := by rw [e1]; positivity
  have hcube : c0 / (δ / 2) ^ 3 = c0 * 8 * δ⁻¹ ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    ring
  calc efLargeCount n d n (δ / 2)
      ≤ c0 / (δ / 2) ^ 3 * Real.log (3 * m / (δ / 2)) *
          Real.log (Real.log (3 * m) / (δ / 2)) := by
        simpa [m, c0] using h
    _ ≤ c0 / (δ / 2) ^ 3 * ((Real.log (6 * m) + 1) * (1 + Real.log δ⁻¹)) *
          ((Real.log (2 * Real.log (3 * m)) + 1) * (1 + Real.log δ⁻¹)) := by
        gcongr
        rw [e2]; positivity
    _ = c0 * 8 * (Real.log (6 * m) + 1) * (Real.log (2 * Real.log (3 * m)) + 1) *
          δ⁻¹ ^ (3 : ℝ) * (1 + Real.log δ⁻¹) ^ 2 := by
        rw [hcube]; ring


section Places

/-- The places of a system over `ℚ` with no finite places: `∞` only. -/
abbrev PlacesQ := InfinitePlace ℚ ⊕ ↥(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))

instance : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) :=
  ⟨fun s ↦ Finset.notMem_empty _ s.2⟩

theorem prod_placesQ (f : PlacesQ → ℝ) : ∏ p, f p = f (.inl Rat.infinitePlace) := by
  rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_empty, mul_one]
  rfl

theorem sum_placesQ (f : PlacesQ → ℝ) : ∑ p, f p = f (.inl Rat.infinitePlace) := by
  rw [Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_empty, add_zero]
  rfl

theorem mult_placeQ (v : InfinitePlace ℚ) : v.mult = 1 := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace

end Places

/-- The forms `y ↦ ∑ k, M i k y k` make up the linear map of the matrix `M`. -/
theorem pi_sumForm_eq_toLin' {F : Type*} [Field F] {n : ℕ} (M : Fin n → Fin n → F) :
    LinearMap.pi (fun i ↦ Module.Dual.sumForm (M i)) = Matrix.toLin' (Matrix.of M) := by
  ext y i
  simp [Module.Dual.sumForm_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

section Forms

variable {E : Type} [Field E] (σ : E →+* ℂ)

/-- The absolute value of `E` through the embedding `σ`. -/
noncomputable def absC : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ).comp σ.injective

theorem absC_apply (z : E) : absC σ z = ‖σ z‖ := rfl

theorem absC_liesOver [CharZero E] : (absC σ).LiesOver Rat.infinitePlace.1 := by
  refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
  rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, absC_apply, eq_ratCast, map_ratCast,
    ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
  simp

variable {n : ℕ} (β : E) (lam : Fin n → ℕ) (P : Fin n → Fin n → Fin 3 → ℤ)

/-- **The scaled rows** `lam i · (P i j 0 + P i j 1 β + P i j 2 β²)` over `E`. -/
noncomputable def qRow (i j : Fin n) : E :=
  ∑ m : Fin 3, (((lam i : ℤ) * P i j m : ℤ) : E) * β ^ (m : ℕ)

/-- **The scaled forms**, the same at every place. -/
noncomputable def qForms : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E) :=
  fun _ i ↦ Module.Dual.sumForm (qRow β lam P i)

variable {σ β} {α : ℝ} (hβ : σ β = α)
include hβ

theorem σ_qRow (i j : Fin n) :
    σ (qRow β lam P i j) = (((lam i : ℝ) * quadVal α (P i j) : ℝ) : ℂ) := by
  rw [qRow]
  simp only [map_sum, map_mul, map_pow, map_intCast, hβ]
  simp only [Fin.sum_univ_three, quadVal, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one]
  push_cast
  ring

theorem systemValue_qForms [NumberField E] (v : InfinitePlace ℚ) (i : Fin n) (x : Fin n → ℤ) :
    systemValue (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun _ ↦ absC σ) (qForms β lam P)
      (.inl v) i (fun k ↦ (x k : ℚ)) = lam i * |∑ k, quadVal α (P i k) * x k| := by
  simp only [systemValue, systemAbs, systemMult, mult_placeQ, pow_one, qForms]
  rw [absC_apply, Module.Dual.sumForm_apply, map_sum]
  have : ∑ k, σ (qRow β lam P i k * algebraMap ℚ E (x k : ℚ)) =
      (((lam i : ℝ) * ∑ k, quadVal α (P i k) * x k : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, σ_qRow lam P hβ, eq_ratCast, map_ratCast]
    push_cast
    ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast]

theorem systemDet_qForms :
    systemDet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun _ ↦ absC σ) (qForms β lam P) =
      |(Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)).det| := by
  rw [systemDet, prod_placesQ]
  simp only [systemAbs, systemMult, mult_placeQ, pow_one]
  rw [show qForms β lam P (systemPlace ∅ (.inl Rat.infinitePlace)) =
    fun i ↦ Module.Dual.sumForm (qRow β lam P i) from rfl,
    pi_sumForm_eq_toLin', LinearMap.det_toLin', absC_apply, RingHom.map_det]
  have : σ.mapMatrix (Matrix.of (qRow β lam P)) =
      Complex.ofRealHom.mapMatrix (Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)) := by
    ext i j
    simp [σ_qRow lam P hβ]
  rw [this, ← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]

end Forms

/-- **The scaling.** For `C ≥ 1 ≥ γ > 0` there is `k` with `C ^ n / γ ≤ 2 ^ k` and
`k log 2 ≤ 1 + n log C + log γ⁻¹`. -/
theorem exists_two_pow {C γ : ℝ} (hC : 1 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n : ℕ) :
    ∃ k : ℕ, C ^ n / γ ≤ 2 ^ k ∧
      (k : ℝ) * Real.log 2 ≤ 1 + n * Real.log C + Real.log γ⁻¹ := by
  have hCn : 1 ≤ C ^ n / γ := by
    rw [le_div_iff₀ hγ]; nlinarith [one_le_pow₀ (n := n) hC]
  refine ⟨⌈Real.logb 2 (C ^ n / γ)⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil (Real.logb 2 (C ^ n / γ))
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)] at h
    simpa [Real.rpow_natCast] using h
  · have hlogb0 : 0 ≤ Real.logb 2 (C ^ n / γ) := Real.logb_nonneg (by norm_num) hCn
    have h := Nat.ceil_lt_add_one hlogb0
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.logb 2 (C ^ n / γ) * Real.log 2 = n * Real.log C + Real.log γ⁻¹ := by
      rw [Real.logb, div_mul_cancel₀ _ hl2.ne', Real.log_div (by positivity) hγ.ne',
        Real.log_pow, Real.log_inv]
      ring
    have hl21 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    nlinarith


/-! ### The normalization -/

/-- **The scaling factors**: `1` on the forms whose exponent is within `δ / 2n` of `1`, `2 ^ k` on
the others. -/
noncomputable def normLam {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (k : ℕ) (i : Fin n) : ℕ :=
  if 1 - δ / (2 * n) < e i then 1 else 2 ^ k

/-- **The raised exponents**: `e i` on the forms within `δ / 2n` of `1`, `e i + δ / 2n` on the
others. -/
noncomputable def normExp {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (i : Fin n) : ℝ :=
  if 1 - δ / (2 * n) < e i then e i else e i + δ / (2 * n)

theorem normLam_pos {n : ℕ} (e : Fin n → ℝ) (δ : ℝ) (k : ℕ) (i : Fin n) :
    0 < normLam e δ k i := by
  unfold normLam
  split_ifs <;> positivity

/-- Some exponent is not within `δ / 2n` of `1`, since the sum is negative. -/
theorem exists_not_lt_normCut {n : ℕ} (hn : 2 ≤ n) {e : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsum : ∑ i, e i ≤ -δ) : ∃ i, ¬ 1 - δ / (2 * n) < e i := by
  by_contra! h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  have hlt : ∑ _i : Fin n, (1 - δ / (2 * n)) < ∑ i, e i :=
    Finset.sum_lt_sum_of_nonempty hne fun i _ ↦ h i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have : (n : ℝ) * (1 - δ / (2 * n)) = n - δ / 2 := by field_simp
  linarith

theorem two_pow_le_prod_normLam {n : ℕ} (hn : 2 ≤ n) {e : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsum : ∑ i, e i ≤ -δ) (k : ℕ) : 2 ^ k ≤ ∏ i, normLam e δ k i := by
  obtain ⟨i, hi⟩ := exists_not_lt_normCut hn hδ hsum
  calc 2 ^ k = normLam e δ k i := by simp [normLam, hi]
    _ ≤ ∏ j, normLam e δ k j :=
        Finset.single_le_prod (fun j _ ↦ normLam_pos e δ k j) (mem_univ i)

theorem det_scaled {n : ℕ} (lam : Fin n → ℕ) (α : ℝ) (P : Fin n → Fin n → Fin 3 → ℤ) :
    (Matrix.of fun i j ↦ (lam i : ℝ) * quadVal α (P i j)).det =
      (∏ i, (lam i : ℝ)) * (Matrix.of fun i j ↦ quadVal α (P i j)).det := by
  have h := Matrix.det_mul_column (fun i ↦ (lam i : ℝ)) (Matrix.of fun i j ↦ quadVal α (P i j))
  simpa only [Matrix.of_apply] using h

/-- **The scaled determinant is at least `C ^ n`.** -/
theorem pow_le_det_normLam {n : ℕ} (hn : 2 ≤ n) {α : ℝ} {P : Fin n → Fin n → Fin 3 → ℤ}
    {γ : ℝ} (hγ : 0 < γ) (hdet : γ ≤ |(Matrix.of fun i j ↦ quadVal α (P i j)).det|) {C : ℝ}
    {k : ℕ} (hk : C ^ n / γ ≤ 2 ^ k) {e : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsum : ∑ i, e i ≤ -δ) :
    C ^ n ≤ |(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| := by
  rw [det_scaled, abs_mul, abs_of_nonneg (by positivity)]
  have hp : (2 : ℝ) ^ k ≤ ∏ i, (normLam e δ k i : ℝ) := by
    exact_mod_cast two_pow_le_prod_normLam hn hδ hsum k
  rw [div_le_iff₀ hγ] at hk
  exact hk.trans (mul_le_mul hp hdet hγ.le (by positivity))

theorem le_rpow_inv_of_pow_le {C D : ℝ} {n : ℕ} (hn : 0 < n) (hC : 0 ≤ C) (h : C ^ n ≤ D) :
    C ≤ D ^ (n : ℝ)⁻¹ :=
  calc C = (C ^ n) ^ (n : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hC hn.ne').symm
    _ ≤ D ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) h (by positivity)

section Normalized

variable {E : Type} [Field E] [NumberField E] {σ : E →+* ℂ} {β : E} {α : ℝ} (hβ : σ β = α)
  {n : ℕ} (P : Fin n → Fin n → Fin 3 → ℤ) (e : Fin n → ℝ) (δ : ℝ) (k : ℕ)

include hβ in
/-- **The scaled forms make up a normalized system**, of weight `-δ / 2`. -/
theorem isNormalizedSystem_qForms (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B)
    (hP : ∀ i j m, |(P i j m : ℝ)| ≤ B) {γ : ℝ} (hγ : 0 < γ)
    (hdet : γ ≤ |(Matrix.of fun i j ↦ quadVal α (P i j)).det|) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he1 : ∀ i, e i ≤ 1) (he : ∃ i, e i = 1) (hsum : ∑ i, e i ≤ -δ) :
    IsNormalizedSystem (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun _ ↦ absC σ)
      (qForms β (normLam e δ k) P)
      (fun _ ↦ |(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^ (n : ℝ)⁻¹)
      (fun _ ↦ normExp e δ)
      (3 ^ finrank ℚ E * (2 ^ k * B) ^ (3 * finrank ℚ E) * mulHeight₁ β ^ 3)
      (finrank ℚ E) n (δ / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hτ : 0 < δ / (2 * n) := by positivity
  have hexp (v : InfinitePlace ℚ) : systemExponent (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (.inl v) = 1 := by
    simp only [systemExponent, mult_placeQ, Module.finrank_self, Nat.cast_one, div_one]
  exact {
    height_le := fun p i j ↦ by
      have hk1 : (1 : ℝ) ≤ 2 ^ k * B :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
      have : qForms β (normLam e δ k) P (systemPlace ∅ p) i (Pi.basisFun E (Fin n) j) =
          qRow β (normLam e δ k) P i j := by
        change Module.Dual.sumForm (qRow β (normLam e δ k) P i) (Pi.basisFun E (Fin n) j) = _
        simp [Pi.basisFun_apply, Pi.single_apply]
      rw [this, qRow]
      refine absMulHeight₁_sum_le β (fun m ↦ (normLam e δ k i : ℤ) * P i j m) hk1 fun m ↦ ?_
      have hl : ((normLam e δ k i : ℕ) : ℝ) ≤ 2 ^ k := by
        unfold normLam
        split_ifs
        · exact_mod_cast Nat.one_le_two_pow
        · push_cast; exact le_rfl
      push_cast
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul hl (hP i j m) (abs_nonneg _) (by positivity)
    degree_le := fun p i j ↦ minpoly.natDegree_le _
    ncard_le := by
      have hsub : (Set.range fun q : PlacesQ × Fin n ↦
          qForms β (normLam e δ k) P (systemPlace ∅ q.1) q.2) ⊆
          Set.range fun i ↦ Module.Dual.sumForm (qRow β (normLam e δ k) P i) := by
        rintro _ ⟨q, rfl⟩
        exact ⟨q.2, rfl⟩
      refine (Set.ncard_le_ncard hsub (Set.finite_range _)).trans ?_
      rw [← Set.image_univ]
      refine le_trans Set.ncard_image_le ?_
      simp
    const_pos := fun _ ↦ by
      refine Real.rpow_pos_of_pos (abs_pos.2 ?_) _
      rw [det_scaled]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_) (abs_pos.1 (hγ.trans_le hdet))
      exact Nat.cast_ne_zero.2 (normLam_pos e δ k i).ne'
    const_le := by
      rw [systemConst, prod_placesQ, systemDet_qForms (normLam e δ k) P hβ, Fintype.card_fin]
    delta_pos := by positivity
    delta_le_one := by linarith
    weight_le := by
      rw [systemWeight, sum_placesQ]
      show ∑ i, normExp e δ i ≤ -(δ / 2)
      have h (i : Fin n) : normExp e δ i ≤ e i + δ / (2 * n) := by
        unfold normExp
        split_ifs
        · linarith
        · exact le_rfl
      calc ∑ i, normExp e δ i ≤ ∑ i, (e i + δ / (2 * n)) := Finset.sum_le_sum fun i _ ↦ h i
        _ = ∑ i, e i + δ / 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            field_simp
        _ ≤ -(δ / 2) := by linarith
    exponent_le := fun p i ↦ by
      rcases p with v | v
      · rw [hexp]
        unfold normExp
        split_ifs with h
        · exact he1 i
        · linarith [not_lt.1 h]
      · exact isEmptyElim v
    exists_exponent_eq := fun p ↦ by
      obtain ⟨i, hi⟩ := he
      refine ⟨i, ?_⟩
      rcases p with v | v
      · rw [hexp]
        have : 1 - δ / (2 * n) < e i := by rw [hi]; linarith
        unfold normExp
        simp only [this, ↓reduceIte]
        exact hi
      · exact isEmptyElim v }

include hβ in
/-- **The solutions are solutions of the scaled system**, once `2 ^ k ≤ |x| ^ (δ / 2n)`. -/
theorem mem_systemSet_qForms {x : Fin n → ℤ} (hx : x ≠ 0) {C c₀ : ℝ} (hC : C ≤ c₀)
    (hk : (2 : ℝ) ^ k ≤ (⨆ j, |(x j : ℝ)|) ^ (δ / (2 * n)))
    (hsol : ∀ i, |∑ j, quadVal α (P i j) * x j| ≤ C * (⨆ j, |(x j : ℝ)|) ^ e i) :
    (fun j ↦ (x j : ℚ)) ∈ systemSet (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (fun _ ↦ absC σ)
      (qForms β (normLam e δ k) P) (fun _ ↦ c₀) (fun _ ↦ normExp e δ) := by
  have hX : 1 ≤ ⨆ j, |(x j : ℝ)| := by
    rw [← Height.mulHeightAff_intCast hx]
    exact one_le_mulHeightAff _
  refine ⟨fun j ↦ intCast_mem _ (x j), fun p i ↦ ?_⟩
  rcases p with v | v
  swap
  · exact isEmptyElim v
  rw [systemValue_qForms (normLam e δ k) P hβ v i x, Height.mulHeightAff_intCast hx]
  set X := ⨆ j, |(x j : ℝ)|
  have hX0 : 0 < X := by linarith
  have hv := hsol i
  unfold normLam normExp
  by_cases h : 1 - δ / (2 * n) < e i
  · simp only [h, ↓reduceIte, Nat.cast_one, one_mul]
    exact hv.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hX0.le _))
  · simp only [h, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.rpow_add hX0]
    calc (2 : ℝ) ^ k * |∑ j, quadVal α (P i j) * x j|
        ≤ X ^ (δ / (2 * n)) * (C * X ^ e i) :=
          mul_le_mul hk hv (abs_nonneg _) (by positivity)
      _ = C * (X ^ e i * X ^ (δ / (2 * n))) := by ring
      _ ≤ c₀ * (X ^ e i * X ^ (δ / (2 * n))) := mul_le_mul_of_nonneg_right hC (by positivity)

end Normalized

/-! ### The threshold -/

/-- The constant of the threshold, for `2 ≤ n ≤ 4` variables over a field of degree `d`. -/
noncomputable def thrConst (n d : ℕ) : ℝ :=
  2 * ((1 + 10 * ((n * d + n).choose n : ℝ)) * (23 + 64 * d) + 60) + 48 + 2 * (100 + 16 * d)

theorem thrConst_nonneg (n d : ℕ) : 0 ≤ thrConst n d := by
  unfold thrConst
  positivity

/-- `log n! ≤ 23` and `log n ≤ 3` for `n ≤ 4`. -/
theorem log_factorial_le {n : ℕ} (hn4 : n ≤ 4) : Real.log (n.factorial : ℝ) ≤ 23 := by
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h24 : (n.factorial : ℝ) ≤ 24 := by
    have : n.factorial ≤ 24 := by interval_cases n <;> decide
    exact_mod_cast this
  linarith [Real.log_le_sub_one_of_pos hfpos]

theorem scalarConst_rat : scalarConst ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) = 2 := by
  rw [scalarConst, Module.finrank_self, Finset.prod_empty, NumberField.discr_rat]
  norm_num

/-- **The threshold of the scaled system** is at most `thrConst n d (1 + log H) / δ`. -/
theorem efSystemThreshold_le_thrConst {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) {w : AbsoluteValue ℚ ℝ → AbsoluteValue E ℝ}
    (hw : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    {L : AbsoluteValue ℚ ℝ → Fin n → Dual E (Fin n → E)} {C : PlacesQ → ℝ}
    {c : PlacesQ → Fin n → ℝ} {H : ℝ} {D : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) w L C c H D n (δ / 2))
    (hH : 1 ≤ H) (hδ1 : δ ≤ 1) :
    efSystemThreshold E ∅ w L n H (δ / 2) ≤ thrConst n (finrank ℚ E) * (1 + log H) / δ := by
  have hδ2 : 0 < δ / 2 := hN.delta_pos
  have hδ : 0 < δ := by linarith
  have hΛ : 0 ≤ log H := Real.log_nonneg hH
  set d := finrank ℚ E with hd
  have hd1 : 1 ≤ d := finrank_pos
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  have hlogn : Real.log n ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hT := thrConst_nonneg n d
  have hTge : 48 + 2 * (100 + 16 * (d : ℝ)) ≤ thrConst n d := by
    unfold thrConst
    have : (0 : ℝ) ≤ ((n * d + n).choose n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h := efSystemThreshold_le hw (fun v hv ↦ absurd hv (Finset.notMem_empty v)) hN
  refine h.trans (max_le ?_ (max_le ?_ ?_))
  · -- the domain threshold
    have hc : #(systemPlacesOver E (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) = 0 := by
      have := card_systemPlacesOver_le (E := E) (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      simpa using this
    have hcd : (Fintype.card (InfinitePlace E) : ℝ) ≤ d := by
      exact_mod_cast card_infinitePlace_le_finrank (E := E)
    rw [hc, Fintype.card_fin, Nat.cast_zero, add_zero]
    refine (domainThreshold_le_div (c := Fintype.card (InfinitePlace E)) hn hn4 hd1 hδ2
      (by linarith) hΛ).trans ?_
    rw [div_div_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have hch : (0 : ℝ) ≤ ((n * d + n).choose n : ℝ) := Nat.cast_nonneg _
    have e1 : 23 + 64 * (Fintype.card (InfinitePlace E) : ℝ) * log H ≤
        (23 + 64 * d) * (1 + log H) := by nlinarith
    have e2 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 1 + 10 *
      ((n * d + n).choose n : ℝ))
    unfold thrConst
    nlinarith
  · -- the gap principle
    simp only [Fintype.card_fin, Module.finrank_self, Nat.cast_one, one_mul]
    rw [show 2 * (n : ℝ) / (δ / 2) * Real.log n = 4 * n * Real.log n / δ by field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have : (n : ℝ) * Real.log n ≤ 4 * 3 := mul_le_mul hn4' hlogn hlogn0 (by norm_num)
    nlinarith
  · -- the scalar
    have ht : ((Fintype.card (InfinitePlace ℚ) + #(∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : ℕ)
        : ℝ) ≤ 1 := by
      have := card_infinitePlace_le_finrank (E := ℚ)
      rw [Module.finrank_self] at this
      simp only [Finset.card_empty, add_zero]
      exact_mod_cast this
    have hl2 : Real.log (scalarConst ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) ≤ 1 := by
      rw [scalarConst_rat]
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hl20 : 0 ≤ Real.log (scalarConst ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) := by
      rw [scalarConst_rat]; exact Real.log_nonneg (by norm_num)
    rw [systemHeightThreshold, Fintype.card_fin, div_div_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    set t := ((Fintype.card (InfinitePlace ℚ) + #(∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : ℕ)
      : ℝ)
    have ht0 : 0 ≤ t := Nat.cast_nonneg _
    set G := Real.log (n.factorial : ℝ) + n * (d * log H)
    have hG0 : 0 ≤ G := by
      have : 0 ≤ Real.log (n.factorial : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
      positivity
    have hG : G ≤ 23 + 4 * d * log H := by
      have : (n : ℝ) * (d * log H) ≤ 4 * (d * log H) :=
        mul_le_mul_of_nonneg_right hn4' (by positivity)
      linarith [log_factorial_le hn4]
    have htG : t * G ≤ G := by nlinarith
    have hnμ : (n : ℝ) * Real.log (scalarConst ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) ≤ 4 :=
      by nlinarith
    nlinarith

/-! ### Evertse–Ferretti -/

/-- **The quantitative Subspace Theorem of Evertse–Ferretti 2013 for forms in `1, α, α²`**:
`δ^{-3} (1 + log δ⁻¹)²` subspaces. The forms are taken over the Galois closure of `α` in `ℂ`, scaled
to a normalized system of weight `-δ / 2` (`Real.isNormalizedSystem_qForms`), and counted by
`NumberField.exists_finset_submodule_of_efSystemThreshold_le`. -/
theorem subspaceBound_three {α : ℝ} (hα : IsAlgebraic ℚ α) : SubspaceBound α 3 := by
  intro n hn hn4
  obtain ⟨E, hgal, hfd, hmem⟩ := exists_isGalois_mem hα
  have : NumberField E := { }
  set d := finrank ℚ E with hd
  have hd1 : 1 ≤ d := finrank_pos
  set β : E := ⟨(α : ℂ), hmem⟩
  set σ : E →+* ℂ := E.val.toRingHom
  have hβ : σ β = α := rfl
  have hw : ∀ v : InfinitePlace ℚ, ((fun _ ↦ absC σ) v.1 : AbsoluteValue E ℝ).LiesOver v.1 :=
    fun v ↦ Subsingleton.elim Rat.infinitePlace v ▸ absC_liesOver σ
  obtain ⟨K₁, hK₁, hcount⟩ := efLargeCount_half_le (d := d) hn hd1
  set Mβ := mulHeight₁ β
  have hMβ : 1 ≤ Mβ := one_le_mulHeight₁ β
  have hlM : 0 ≤ log Mβ := Real.log_nonneg hMβ
  set c₁ : ℝ := 1 + 17 * d + 3 * log Mβ with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  set M := thrConst n d
  have hM0 : 0 ≤ M := thrConst_nonneg n d
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  set Kc := max (max K₁ (M * c₁ + 2 * n ^ 2)) 1 with hKc
  refine ⟨Kc, by positivity,
    fun P B hB hP γ hγ hγ1 hdet C hC e δ hδ hδ1 he1 he hsum ↦ ?_⟩
  obtain ⟨k, hk, hklog⟩ := exists_two_pow hC hγ hγ1 n
  have hN := isNormalizedSystem_qForms hβ P e δ k hn hB hP hγ hdet hδ hδ1 he1 he hsum
  obtain ⟨T, hT, htop, hTmem⟩ := exists_finset_submodule_of_efSystemThreshold_le ∅
    (fun _ ↦ absC σ) hw (fun v hv ↦ absurd hv (Finset.notMem_empty v)) hN
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  refine ⟨T, ?_, htop, fun x hx hsol hlarge ↦ ?_⟩
  · -- the count
    rw [Fintype.card_fin] at hT
    refine hT.trans ((hcount δ hδ hδ1).trans ?_)
    have : K₁ ≤ Kc := (le_max_left _ _).trans (le_max_left _ _)
    gcongr
  -- the data
  have hlB : 0 ≤ log B := Real.log_nonneg hB
  have hlC : 0 ≤ log C := Real.log_nonneg hC
  have hlγ : 0 ≤ log γ⁻¹ := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
  set Ξ := 1 + log B + log C + log γ⁻¹ with hΞ
  have hΞ1 : 1 ≤ Ξ := by linarith
  have hk' : (k : ℝ) * log 2 ≤ n * Ξ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hn1) hlγ, mul_nonneg hn0.le hlB,
      mul_nonneg (sub_nonneg.2 hn1) hlC]
  -- the point
  set X := ⨆ j, |(x j : ℝ)| with hX
  have hX1 : 1 ≤ X := by
    rw [hX, ← Height.mulHeightAff_intCast hx]
    exact one_le_mulHeightAff _
  have hX0 : 0 < X := by linarith
  have hbig : (M * c₁ + 2 * n ^ 2) * δ⁻¹ * Ξ ≤ log X := by
    refine le_trans ?_ hlarge
    have h1 : M * c₁ + 2 * n ^ 2 ≤ Kc := (le_max_right _ _).trans (le_max_left _ _)
    have h2 : δ⁻¹ ≤ δ⁻¹ ^ Kc :=
      calc δ⁻¹ = δ⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ δ⁻¹ ^ Kc := Real.rpow_le_rpow_of_exponent_le hδi (le_max_right _ _)
    have : 0 ≤ M * c₁ + 2 * n ^ 2 := by positivity
    gcongr
  have hsplit : (M * c₁ + 2 * n ^ 2) * δ⁻¹ * Ξ =
      M * c₁ * δ⁻¹ * Ξ + 2 * n ^ 2 * δ⁻¹ * Ξ := by ring
  have hMc : 0 ≤ M * c₁ * δ⁻¹ * Ξ := by positivity
  have h2n : 2 * n ^ 2 * δ⁻¹ * Ξ ≤ log X := by linarith
  -- `2 ^ k ≤ |x| ^ (δ / 2n)`
  have h2k : (2 : ℝ) ^ k ≤ X ^ (δ / (2 * n)) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hX0]
    calc (k : ℝ) * log 2 ≤ n * Ξ := hk'
      _ = δ / (2 * n) * (2 * n ^ 2 * δ⁻¹ * Ξ) := by field_simp
      _ ≤ δ / (2 * n) * log X := mul_le_mul_of_nonneg_left h2n (by positivity)
  -- the constant
  have hCc : C ≤ |(Matrix.of fun i j ↦ (normLam e δ k i : ℝ) * quadVal α (P i j)).det| ^
      (n : ℝ)⁻¹ :=
    le_rpow_inv_of_pow_le (by omega) (by linarith) (pow_le_det_normLam hn hγ hdet hk hδ hsum)
  -- the height of the coefficients
  set Hc : ℝ := 3 ^ d * (2 ^ k * B) ^ (3 * d) * Mβ ^ 3 with hHc
  have hkB : (1 : ℝ) ≤ 2 ^ k * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB
  have hHc1 : 1 ≤ Hc := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ hkB)) (one_le_pow₀ hMβ)
  have hlogHc : 1 + log Hc ≤ c₁ * Ξ := by
    have hl3 : log 3 ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
    have hl2kB : log ((2 : ℝ) ^ k * B) = k * log 2 + log B := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
    have : log Hc = d * log 3 + (3 * d) * (k * log 2 + log B) + 3 * log Mβ := by
      rw [hHc, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, hl2kB]
      push_cast
      ring
    have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hΞ0 : 0 ≤ Ξ - 1 := sub_nonneg.2 hΞ1
    have ha : (d : ℝ) * log 3 ≤ 2 * d * Ξ := by
      have h1 := mul_le_mul_of_nonneg_left hl3 (by positivity : (0 : ℝ) ≤ d)
      have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d) hΞ0
      linarith
    have hb : 3 * (d : ℝ) * (k * log 2 + log B) ≤ 3 * d * (5 * Ξ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := mul_le_mul_of_nonneg_right hn4' (by linarith : (0 : ℝ) ≤ Ξ)
      linarith
    have hc := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hlM) hΞ0
    rw [this, hc₁]
    linarith
  have hthr := efSystemThreshold_le_thrConst hn hn4 hw hN hHc1 hδ1
  have hthr' := hthr.trans <| show M * (1 + log Hc) / δ ≤ log X by
    calc M * (1 + log Hc) / δ = M * (1 + log Hc) * δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ M * (c₁ * Ξ) * δ⁻¹ := by gcongr
      _ = M * c₁ * δ⁻¹ * Ξ := by ring
      _ ≤ log X := by
          have : 0 ≤ 2 * (n : ℝ) ^ 2 * δ⁻¹ * Ξ := by positivity
          linarith
  obtain ⟨U, hU, hxU⟩ := hTmem _ (mem_systemSet_qForms hβ P e δ k hx hCc h2k hsol)
    (by rwa [Height.mulHeightAff_intCast hx])
  exact ⟨U, hU, hxU⟩

end Real
