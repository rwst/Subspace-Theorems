/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.SpecialFunctions.Exp

-- Used only inside proofs.
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Sym.Card
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn

/-!
# Counting the monomials of a multihomogeneous polynomial

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, (13.4), (13.5) and Lemmas 13.2, 13.3.

For a tuple `r = (r_1, …, r_m)` of positive integers, `U(r)` is the set of exponent tuples
`j = (j_{hl})` with `Σ_l j_{hl} = r_h` for each block `h`, that is, of the monomials of a
polynomial in `m` blocks of `N` variables that is homogeneous of degree `r_h` in the `h`-th block.
Its size is `V = ∏_h C(r_h + N - 1, N - 1) ≤ N^{Σ r_h} ≤ (eN)^{Σ r_h}` (EF13 (13.4), (13.5)).

EF13 Lemma 13.3 says that for reals `|c_{hl}| ≤ γ` (EF13's `c_{hl}` carry a hat), at most
`e^{-mε²/2} V` of the `j ∈ U(r)` satisfy `Σ_h r_h⁻¹ Σ_l j_{hl} c_{hl} ≥ N⁻¹ Σ_{h,l} c_{hl} + mγε`.
EF13 deduce it from Hoeffding's inequality (EF13 Lemma 13.2) for the uniform distribution on
`U(r)`, under which the blocks are independent. We run the underlying Chernoff argument
directly on the finite sums: the uniform average of `exp (t S)` for `S = Σ_h Y_h`, with `Y_h`
depending on the `h`-th block only, factors into a product of averages over the blocks. Each
factor is bounded by Hoeffding's lemma, which Mathlib proves for probability measures
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) and `Finset.sum_exp_mul_le_of_sum_eq_zero`
restates for finite averages.

## Main definitions

* `Finset.blockCompositions r`: EF13's `U(r)`, as a finset of `ι → κ → ℕ`.

## Main results

* `Finset.sum_exp_mul_le_of_sum_eq_zero`: Hoeffding's lemma for a finite average.
* `Finset.card_piAntidiag_univ`, `Finset.card_blockCompositions`: EF13 (13.4).
* `Finset.card_blockCompositions_le`, `Finset.card_blockCompositions_le_exp`: EF13 (13.5).
* `Finset.card_filter_blockCompositions_le`: EF13 Lemma 13.3.
-/

@[expose] public section

open Real

namespace Finset

/-- **Hoeffding's lemma** for a finite average: if `f` takes values in `[a, b]` on `s` and sums
to zero over `s`, then the sum of `exp (t f)` over `s` is at most `#s · exp ((b - a)² t² / 8)`. -/
theorem sum_exp_mul_le_of_sum_eq_zero {α : Type*} {s : Finset α} {f : α → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ s, f x ∈ Set.Icc a b) (h0 : ∑ x ∈ s, f x = 0) (t : ℝ) :
    ∑ x ∈ s, exp (t * f x) ≤ #s * exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  open MeasureTheory ProbabilityTheory in
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let _ : MeasurableSpace s := ⊤
  have : Nonempty s := hs.to_subtype
  have : MeasurableSingletonClass s := ⟨fun _ ↦ trivial⟩
  let μ : Measure s := uniformOn Set.univ
  have hμ : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have hint (g : s → ℝ) : μ[g] = (∑ x : s, g x) / #s := by
    rw [integral_fintype .of_finite]
    simp [μ, uniformOn_univ, Measure.real, div_eq_inv_mul, mul_sum]
  have key := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (X := fun x : s ↦ f x) (μ := μ)
    (a := a) (b := b) Measurable.of_discrete.aemeasurable
    (ae_of_all _ fun x ↦ hf x x.2) (by rw [hint, ← h0, sum_coe_sort s f]; simp [h0])).mgf_le t
  rw [mgf, hint, sum_coe_sort s fun x ↦ exp (t * f x)] at key
  have hpos : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  rw [div_le_iff₀ hpos, mul_comm] at key
  convert key using 3
  simp only [NNReal.coe_pow, NNReal.coe_div, div_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs,
    NNReal.coe_ofNat]
  ring

section Compositions

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The number of compositions of `r` into `N` parts indexed by `κ` is the number of multisets of
size `r` from `N` elements, `C(r + N - 1, N - 1)`. -/
theorem card_piAntidiag_univ (r : ℕ) :
    #(piAntidiag (univ : Finset κ) r) = (Fintype.card κ).multichoose r := by
  rw [← card_univ, ← card_finsuppAntidiag_nat_eq_multichoose]
  refine card_nbij' (Finsupp.equivFunOnFinite.symm) (⇑) (fun f hf ↦ ?_) (fun f hf ↦ ?_)
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  · simpa using hf
  · simpa using hf

/-- The number of multisets of size `k` from `n` elements is at most `n ^ k`. -/
theorem _root_.Nat.multichoose_le_pow (n k : ℕ) : n.multichoose k ≤ n ^ k := by
  rw [← Fintype.card_fin n, ← Sym.card_sym_eq_multichoose, ← card_vector]
  refine Fintype.card_le_of_surjective Sym.ofVector fun s ↦ ?_
  obtain ⟨⟨l⟩, hl⟩ := s
  exact ⟨⟨l, hl⟩, rfl⟩

/-- The sum of the `l`-th parts over all compositions of `r` does not depend on `l`, so it is
`r / N` times the number of compositions. -/
theorem card_mul_sum_piAntidiag_univ (r : ℕ) (l : κ) :
    Fintype.card κ * ∑ x ∈ piAntidiag (univ : Finset κ) r, (x l : ℝ) =
      r * #(piAntidiag (univ : Finset κ) r) := by
  have hsymm (l' : κ) : ∑ x ∈ piAntidiag (univ : Finset κ) r, (x l' : ℝ) =
      ∑ x ∈ piAntidiag (univ : Finset κ) r, (x l : ℝ) := by
    let σ := Equiv.swap l l'
    refine sum_nbij' (· ∘ σ) (· ∘ σ) (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun x _ ↦ ?_)
      (fun x _ ↦ ?_) (fun x _ ↦ ?_)
    · simpa [Function.comp_def, Equiv.sum_comp σ x] using hx
    · simpa [Function.comp_def, Equiv.sum_comp σ x] using hx
    · ext; simp [σ]
    · ext; simp [σ]
    · simp [σ]
  calc Fintype.card κ * ∑ x ∈ piAntidiag (univ : Finset κ) r, (x l : ℝ)
      = ∑ l' : κ, ∑ x ∈ piAntidiag (univ : Finset κ) r, (x l' : ℝ) := by
        simp [hsymm]
    _ = ∑ x ∈ piAntidiag (univ : Finset κ) r, (r : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun x hx ↦ ?_
        rw [mem_piAntidiag] at hx
        exact_mod_cast hx.1
    _ = r * #(piAntidiag (univ : Finset κ) r) := by simp [mul_comm]

variable [Fintype ι] [DecidableEq ι]

/-- EF13's `U(r)`: the tuples `j = (j_{hl})` of nonnegative integers with `Σ_l j_{hl} = r_h` for
every block `h`, that is, the exponents of the monomials of multidegree `r` in `#ι` blocks of
`#κ` variables. -/
def blockCompositions (r : ι → ℕ) : Finset (ι → κ → ℕ) :=
  Fintype.piFinset fun h ↦ piAntidiag univ (r h)

theorem mem_blockCompositions {r : ι → ℕ} {j : ι → κ → ℕ} :
    j ∈ blockCompositions r ↔ ∀ h, ∑ l, j h l = r h := by
  simp [blockCompositions]

/-- EF13 (13.4): `#U(r) = ∏_h C(r_h + N - 1, N - 1)`. -/
theorem card_blockCompositions (r : ι → ℕ) :
    #(blockCompositions (κ := κ) r) = ∏ h, (Fintype.card κ).multichoose (r h) := by
  simp [blockCompositions, card_piAntidiag_univ]

/-- `#U(r) ≤ N ^ {Σ r_h}`. -/
theorem card_blockCompositions_le (r : ι → ℕ) :
    #(blockCompositions (κ := κ) r) ≤ Fintype.card κ ^ ∑ h, r h := by
  rw [card_blockCompositions, ← prod_pow_eq_pow_sum]
  exact prod_le_prod fun h _ ↦ Nat.multichoose_le_pow _ _

/-- EF13 (13.5): `#U(r) ≤ (eN) ^ {Σ r_h}`. -/
theorem card_blockCompositions_le_exp (r : ι → ℕ) :
    (#(blockCompositions (κ := κ) r) : ℝ) ≤ (exp 1 * Fintype.card κ) ^ ∑ h, r h := by
  calc (#(blockCompositions (κ := κ) r) : ℝ) ≤ (Fintype.card κ : ℝ) ^ ∑ h, r h := by
        exact_mod_cast card_blockCompositions_le r
    _ ≤ (exp 1 * Fintype.card κ) ^ ∑ h, r h := by
        gcongr
        exact le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_exp zero_le_one)

/-- **EF13 Lemma 13.3.** If `|c_{hl}| ≤ γ`, then at most `e^{-mε²/2} #U(r)` of the `j ∈ U(r)`
satisfy `Σ_h r_h⁻¹ Σ_l j_{hl} c_{hl} ≥ N⁻¹ Σ_{h,l} c_{hl} + mγε`, where `m = #ι`, `N = #κ`. -/
theorem card_filter_blockCompositions_le [Nonempty κ] {r : ι → ℕ} (hr : ∀ h, r h ≠ 0)
    {c : ι → κ → ℝ} {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) (hc : ∀ h l, |c h l| ≤ γ) :
    (#{j ∈ blockCompositions r | (∑ h, ∑ l, c h l) / Fintype.card κ +
        Fintype.card ι * γ * ε ≤ ∑ h, (∑ l, (j h l : ℝ) * c h l) / r h} : ℝ) ≤
      exp (-(Fintype.card ι * ε ^ 2 / 2)) * #(blockCompositions (κ := κ) r) := by
  set N : ℝ := (Fintype.card κ : ℝ)
  set m : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  -- The centred block averages `Y_h = X_h - μ_h`.
  set Y : ι → (κ → ℕ) → ℝ := fun h x ↦ (∑ l, (x l : ℝ) * c h l) / r h - (∑ l, c h l) / N
  have hY0 (h : ι) : ∑ x ∈ piAntidiag univ (r h), Y h x = 0 := by
    have hr' : (r h : ℝ) ≠ 0 := by exact_mod_cast hr h
    have hS (l : κ) : ∑ x ∈ piAntidiag univ (r h), (x l : ℝ) =
        r h * #(piAntidiag (univ : Finset κ) (r h)) / N := by
      rw [eq_div_iff hN.ne', mul_comm]
      exact card_mul_sum_piAntidiag_univ (r h) l
    have hsum : ∑ x ∈ piAntidiag univ (r h), ∑ l, (x l : ℝ) * c h l =
        ∑ l, c h l * (r h * #(piAntidiag (univ : Finset κ) (r h)) / N) := by
      rw [sum_comm]
      exact sum_congr rfl fun l _ ↦ by rw [← sum_mul, hS, mul_comm]
    simp only [Y, sum_sub_distrib, ← sum_div, hsum, sum_const, nsmul_eq_mul, ← sum_mul]
    field_simp
    ring
  have hYmem (h : ι) (x) (hx : x ∈ piAntidiag univ (r h)) :
      Y h x ∈ Set.Icc (-γ - (∑ l, c h l) / N) (γ - (∑ l, c h l) / N) := by
    have hr' : (0 : ℝ) < r h := by exact_mod_cast Nat.pos_of_ne_zero (hr h)
    have hsum : ∑ l, (x l : ℝ) = r h := by
      rw [mem_piAntidiag] at hx; exact_mod_cast hx.1
    have habs : |∑ l, (x l : ℝ) * c h l| ≤ r h * γ := by
      calc |∑ l, (x l : ℝ) * c h l| ≤ ∑ l, (x l : ℝ) * γ := by
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_)
            rw [abs_mul, Nat.abs_cast]
            exact mul_le_mul_of_nonneg_left (hc h l) (Nat.cast_nonneg _)
        _ = r h * γ := by rw [← sum_mul, hsum]
    have := abs_le.1 habs
    constructor
    · simp only [Y]; gcongr
      rw [le_div_iff₀ hr']; linarith
    · simp only [Y]; gcongr
      rw [div_le_iff₀ hr']; linarith
  -- Hoeffding's lemma for each block, with `t = ε / γ`.
  set t := ε / γ
  have hblock (h : ι) : ∑ x ∈ piAntidiag univ (r h), exp (t * Y h x) ≤
      #(piAntidiag (univ : Finset κ) (r h)) * exp (γ ^ 2 * t ^ 2 / 2) := by
    refine (sum_exp_mul_le_of_sum_eq_zero (hYmem h) (hY0 h) t).trans_eq ?_
    congr 2
    ring
  -- The Chernoff bound.
  have hcond (j : ι → κ → ℕ) : ((∑ h, ∑ l, c h l) / N + m * γ * ε ≤
      ∑ h, (∑ l, (j h l : ℝ) * c h l) / r h) ↔ m * γ * ε ≤ ∑ h, Y h (j h) := by
    simp only [Y, sum_sub_distrib, ← sum_div]
    constructor <;> intro h <;> linarith
  have ht : 0 ≤ t := div_nonneg hε hγ.le
  calc (#{j ∈ blockCompositions r | (∑ h, ∑ l, c h l) / N + m * γ * ε ≤
        ∑ h, (∑ l, (j h l : ℝ) * c h l) / r h} : ℝ)
      ≤ ∑ j ∈ blockCompositions r, exp (t * (∑ h, Y h (j h) - m * γ * ε)) := by
        rw [card_filter, Nat.cast_sum]
        refine sum_le_sum fun j _ ↦ ?_
        split_ifs with hj
        · rw [hcond] at hj
          simpa using one_le_exp (mul_nonneg ht (sub_nonneg.2 hj))
        · simpa using (exp_pos _).le
    _ = exp (-(t * (m * γ * ε))) * ∏ h, ∑ x ∈ piAntidiag univ (r h), exp (t * Y h x) := by
        rw [blockCompositions, prod_univ_sum, mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← exp_sum, ← exp_add, mul_sub, mul_sum]
        ring_nf
    _ ≤ exp (-(t * (m * γ * ε))) *
          ∏ h, (#(piAntidiag (univ : Finset κ) (r h)) * exp (γ ^ 2 * t ^ 2 / 2)) := by
        gcongr with h
        exact hblock h
    _ = exp (-(m * ε ^ 2 / 2)) * #(blockCompositions (κ := κ) r) := by
        rw [prod_mul_distrib, prod_const, ← exp_nat_mul, card_blockCompositions, ← mul_assoc,
          mul_comm _ (exp _), ← mul_assoc, ← exp_add]
        simp only [card_piAntidiag_univ, Nat.cast_prod, card_univ]
        congr 2
        simp only [t, m]
        field_simp
        ring

end Compositions

end Finset
