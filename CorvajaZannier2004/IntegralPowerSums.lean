/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.LinearRelationFinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import CorvajaZannier2004.GaloisSetting
import CorvajaZannier2004.SubspaceStep
import CorvajaZannier2004.TwoTermRelation
import DiophantineApproximation.UnitEquation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Trace.Basic

/-!
# Lemma 4 of Corvaja–Zannier: integral power sums force integrality

**Lemma 4** (Corvaja–Zannier 2004, p. 7). Let `α` be algebraic, `Ξ ⊆ ℕ` infinite, and `q n`
positive integers with `log q n = o(n)` along `Ξ` and `Tr_{ℚ(α)/ℚ}(q n αⁿ) ∈ ℤ ∖ {0}` for
`n ∈ Ξ`. Then `α` is an `h`-th root of a rational number or an algebraic integer.

## Main results

* `NumberField.FinitePlace.inv_pow_finrank_le`: a nonzero integer `q` has `w q ≥ |q| ^ (-[K:ℚ])`
  at every finite place `w`.
* `NumberField.exists_one_lt_finitePlace_of_not_isIntegral`: a non-integral element is large at
  some finite place.
* `NumberField.isIntegral_of_mul_sum_pow_eq_intCast`: Lemma 4 inside a number field, with the
  trace written as the sum over the automorphisms (the trace when `K` is Galois), and the stronger
  conclusion that `α` is an algebraic integer.
* `isIntegral_of_trace_mul_pow`: Lemma 4 for a complex algebraic `α`, with `Tr_{ℚ(α)/ℚ}` and the
  stronger conclusion; `isIntegral_or_exists_pow_eq_ratCast` is the conclusion as printed.

## Implementation notes

⚠ **The stronger conclusion.** The paper's first alternative, `α ^ h ∈ ℚ`, comes from the case
`d = 1` of its proof, where Lemma 1 has a single term. There the hypothesis of Lemma 1 bounds the
height, which contradicts `log q n = o(n)` just as well: `Tr(q αⁿ) = q λ (α ^ h) ^ m` cannot be
an integer when `α ^ h` is not integral at `w`. So `α` is always an algebraic integer.

⚠ **No Skolem–Mahler–Lech.** Lemma 1 gives `∑ aᵢ βᵢᵐ = 0` for infinitely many `m`, the `βᵢ`
the distinct values of `σ(α) ^ h`. The paper applies Skolem–Mahler–Lech; Lemma 2 (the unit
equation) already gives `a βᵢᵐ + b βⱼᵐ = 0` for two distinct `m`, so `βᵢ / βⱼ` is a root of unity.

⚠ **The residue class.** The paper groups the embeddings by their restriction to `ℚ(α ^ h)`; here
the automorphisms are grouped by the value `σ(α) ^ h`, which is the same partition and needs no
subfield. `h` is the product of the orders of the ratios `σ(α) / τ(α)` of finite order, not the
exponent of the torsion of `Kˣ`; all the proof uses is that such a ratio has `h`-th power `1`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Lemma 4.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A nonzero integer is not too small at a finite place**: `w q ≥ |q| ^ (-[K:ℚ])`, by the
product formula, every other finite place contributing at most `1`. -/
theorem FinitePlace.inv_pow_finrank_le (w : FinitePlace K) {q : ℤ} (hq : q ≠ 0) :
    |(q : ℝ)|⁻¹ ^ finrank ℚ K ≤ w (q : K) := by
  classical
  have hq' : (q : K) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hprod := FinitePlace.prod_eq_inv_abs_norm hq'
  have hnorm : Algebra.norm ℚ (q : K) = (q : ℚ) ^ finrank ℚ K := by
    rw [← map_intCast (algebraMap ℚ K), Algebra.norm_algebraMap]
  rw [hnorm] at hprod
  have hle : ∀ v : FinitePlace K, v (q : K) ≤ 1 := fun v ↦ by
    rw [← FinitePlace.mk_maximalIdeal v]
    exact FinitePlace.mk_intCast_le_one _ q
  have hf := FinitePlace.hasFiniteMulSupport hq'
  calc |(q : ℝ)|⁻¹ ^ finrank ℚ K = ∏ᶠ v : FinitePlace K, v (q : K) := by
        rw [hprod]
        push_cast
        rw [abs_pow, inv_pow]
    _ ≤ w (q : K) := by
        rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := insert w hf.toFinset)
          fun v hv ↦ Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hv),
          ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self _ _)]
        exact mul_le_of_le_one_right (apply_nonneg _ _)
          (Finset.prod_le_one₀ (fun v _ ↦ apply_nonneg _ _) fun v _ ↦ hle v)

/-- **A non-integral element is large at some finite place.** -/
theorem exists_one_lt_finitePlace_of_not_isIntegral {x : K} (hx : ¬ IsIntegral ℤ x) :
    ∃ P : HeightOneSpectrum (𝓞 K), 1 < FinitePlace.mk P x := by
  by_contra h
  push Not at h
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x fun v ↦
    (FinitePlace.mk_apply_le_one_iff v x).mp (h v)
  exact hx y.2

omit [NumberField K] in
/-- **Two powers in a two-term relation for infinitely many exponents have a root of unity as
ratio.** -/
theorem exists_pow_div_eq_one_of_infinite {β₁ β₂ a b : K} (hβ₁ : β₁ ≠ 0) (hβ₂ : β₂ ≠ 0)
    (ha : a ≠ 0) (h : {m : ℕ | a * β₁ ^ m + b * β₂ ^ m = 0}.Infinite) :
    ∃ k : ℕ, 0 < k ∧ (β₁ / β₂) ^ k = 1 := by
  have hval : ∀ m ∈ {m : ℕ | a * β₁ ^ m + b * β₂ ^ m = 0}, (β₁ / β₂) ^ m = -b / a := by
    intro m hm
    have hm' : a * β₁ ^ m + b * β₂ ^ m = 0 := hm
    rw [div_pow, div_eq_div_iff (pow_ne_zero _ hβ₂) ha]
    linear_combination hm'
  obtain ⟨m₁, hm₁⟩ := h.nonempty
  obtain ⟨m₂, hm₂, hlt⟩ := h.exists_gt m₁
  refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, ?_⟩
  have h₁ := hval m₁ hm₁
  have h₂ := hval m₂ hm₂
  have hne : (β₁ / β₂) ^ m₁ ≠ 0 := pow_ne_zero _ (div_ne_zero hβ₁ hβ₂)
  rw [← Nat.sub_add_cancel hlt.le, pow_add, ← h₁] at h₂
  exact mul_right_cancel₀ hne (h₂.trans (one_mul _).symm)

/-- **Lemma 4 of Corvaja–Zannier** (p. 7), inside a number field and with the stronger
conclusion. Let `a ∈ K`, `Ξ ⊆ ℕ` infinite and `q n > 0` with `log q n = o(n)` along `Ξ` (every
`η > 0` has `q n ≤ exp (η n)` for all but finitely many `n ∈ Ξ`). If
`q n ∑_σ σ(a) ^ n ∈ ℤ ∖ {0}` for `n ∈ Ξ`, `σ` over the automorphisms of `K`, then `a` is an
algebraic integer. For `K` Galois the sum is `Tr_{K/ℚ}`, a multiple of `Tr_{ℚ(a)/ℚ}`; the proof
does not use that `K` is Galois. -/
theorem isIntegral_of_mul_sum_pow_eq_intCast {a : K} {Ξ : Set ℕ} (hΞ : Ξ.Infinite)
    {q : ℕ → ℕ} (hq : ∀ n ∈ Ξ, 0 < q n)
    (hlog : ∀ η : ℝ, 0 < η → {n ∈ Ξ | Real.exp (η * n) < q n}.Finite)
    (htr : ∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧ (q n : K) * ∑ σ : K ≃ₐ[ℚ] K, σ a ^ n = t) :
    IsIntegral ℤ a := by
  classical
  by_contra hint
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hint isIntegral_zero
  have hσ0 : ∀ σ : K ≃ₐ[ℚ] K, σ a ≠ 0 := fun σ ↦ (map_ne_zero σ).mpr ha0
  have hσint : ∀ σ : K ≃ₐ[ℚ] K, ¬ IsIntegral ℤ (σ a) := fun σ h ↦ hint <| by
    have := h.map ((σ.symm : K →ₐ[ℚ] K).restrictScalars ℤ)
    simpa using this
  -- the exponent `h`
  set ρ : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) → K := fun p ↦ p.1 a / p.2 a with hρ
  set h : ℕ := ∏ p ∈ Finset.univ.filter (fun p ↦ IsOfFinOrder (ρ p)), orderOf (ρ p) with hhdef
  have hh : 0 < h := Finset.prod_pos fun p hp ↦ (Finset.mem_filter.mp hp).2.orderOf_pos
  have hsep : ∀ σ₁ σ₂ : K ≃ₐ[ℚ] K, ∀ k : ℕ, 0 < k →
      ((σ₁ a) ^ h / (σ₂ a) ^ h) ^ k = 1 → (σ₁ a) ^ h = (σ₂ a) ^ h := by
    intro σ₁ σ₂ k hk hpow
    have hfin : IsOfFinOrder (ρ (σ₁, σ₂)) := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨h * k, Nat.mul_pos hh hk, by rw [pow_mul, hρ, div_pow]; exact hpow⟩
    have h1 : ρ (σ₁, σ₂) ^ h = 1 := orderOf_dvd_iff_pow_eq_one.mp
      (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfin⟩))
    rw [hρ, div_pow] at h1
    exact (div_eq_one_iff_eq (pow_ne_zero _ (hσ0 σ₂))).mp h1
  -- a residue class `r` modulo `h` meeting `Ξ` infinitely often
  obtain ⟨r, hr⟩ : ∃ r : ℕ, {n ∈ Ξ | n % h = r}.Infinite := by
    by_contra hne
    push Not at hne
    refine hΞ (((Set.finite_Iio h).biUnion fun r _ ↦ hne r).subset fun n hn ↦ ?_)
    exact Set.mem_biUnion (Set.mem_Iio.mpr (Nat.mod_lt n hh)) ⟨hn, rfl⟩
  set Ξ' := {m : ℕ | r + h * m ∈ Ξ} with hΞ'
  have hΞ'inf : Ξ'.Infinite := by
    refine Set.Infinite.of_image (fun m ↦ r + h * m) (hr.mono fun n hn ↦ ?_)
    refine ⟨n / h, ?_, ?_⟩
    · change r + h * (n / h) ∈ Ξ
      rw [← hn.2, Nat.mod_add_div]
      exact hn.1
    · change r + h * (n / h) = n
      rw [← hn.2, Nat.mod_add_div]
  -- the distinct values `β` of `σ(a) ^ h`, and their coefficients `λ β`
  set B := Finset.univ.image fun σ : K ≃ₐ[ℚ] K ↦ σ a ^ h with hB
  set lam : K → K := fun β ↦ ∑ σ ∈ Finset.univ.filter (fun σ : K ≃ₐ[ℚ] K ↦ σ a ^ h = β),
    σ a ^ r with hlam
  set I := B.filter fun β ↦ lam β ≠ 0 with hI
  have hsplit : ∀ m : ℕ, ∑ σ : K ≃ₐ[ℚ] K, σ a ^ (r + h * m) = ∑ β ∈ I, lam β * β ^ m := by
    intro m
    rw [hI, Finset.sum_filter_of_ne fun β _ hβ ↦ left_ne_zero_of_mul hβ,
      ← Finset.sum_fiberwise_of_maps_to (g := fun σ : K ≃ₐ[ℚ] K ↦ σ a ^ h) (t := B)
        fun σ _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ σ)]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [hlam, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    rw [← (Finset.mem_filter.mp hσ).2, pow_add, pow_mul]
  have hBmem : ∀ β ∈ I, ∃ σ : K ≃ₐ[ℚ] K, σ a ^ h = β := fun β hβ ↦ by
    obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hβ).1
    exact ⟨σ, hσ⟩
  have hβ0 : ∀ β ∈ I, β ≠ 0 := fun β hβ ↦ by
    obtain ⟨σ, rfl⟩ := hBmem β hβ
    exact pow_ne_zero _ (hσ0 σ)
  have hlam0 : ∀ β ∈ I, lam β ≠ 0 := fun β hβ ↦ (Finset.mem_filter.mp hβ).2
  -- `I` is nonempty, since the trace does not vanish
  obtain ⟨β₀, hβ₀⟩ : I.Nonempty := by
    obtain ⟨m, hm⟩ := hΞ'inf.nonempty
    obtain ⟨t, ht0, ht⟩ := htr _ hm
    rw [hsplit] at ht
    by_contra hI0
    rw [Finset.not_nonempty_iff_eq_empty.mp hI0, Finset.sum_empty, mul_zero] at ht
    exact ht0 (Int.cast_eq_zero.mp ht.symm)
  -- a finite place at which `β₀` is large
  obtain ⟨P, hP⟩ : ∃ P : HeightOneSpectrum (𝓞 K), 1 < FinitePlace.mk P β₀ := by
    obtain ⟨σ, rfl⟩ := hBmem β₀ hβ₀
    exact exists_one_lt_finitePlace_of_not_isIntegral fun hi ↦
      hσint σ (IsIntegral.of_pow hh hi)
  set c := FinitePlace.mk P β₀ with hc
  have hlogc : 0 < Real.log c := Real.log_pos hP
  -- a finite set `S`, containing `P`, of which every `σ(a)` is a unit
  choose T hT using fun σ : K ≃ₐ[ℚ] K ↦ exists_finset_mem_unit (Units.mk0 (σ a) (hσ0 σ))
  set S := insert P (Finset.univ.biUnion T) with hS
  have hPS : P ∈ S := Finset.mem_insert_self _ _
  -- the points `(β ^ m)_{β ∈ I}` and their coefficients
  set y : ℕ → I → Kˣ := fun m β ↦ Units.mk0 β.1 (hβ0 β.1 β.2) ^ m with hy
  have hyS : ∀ m, ∀ β : I, y m β ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    intro m β
    obtain ⟨σ, hσ⟩ := hBmem β.1 β.2
    have hσS : Units.mk0 (σ a) (hσ0 σ) ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K :=
      mem_unit_of_subset (Finset.coe_subset.mpr ((Finset.subset_biUnion_of_mem T
        (Finset.mem_univ σ)).trans (Finset.subset_insert _ _))) (hT σ)
    have hβ : Units.mk0 β.1 (hβ0 β.1 β.2) = Units.mk0 (σ a) (hσ0 σ) ^ h :=
      Units.ext (by simp [hσ])
    exact Subgroup.pow_mem _ (hβ ▸ Subgroup.pow_mem _ hσS h) m
  -- the height of the points
  set D := finrank ℚ K with hD
  have hDpos : 0 < D := Module.finrank_pos
  set Pm := ∏ β : I, mulHeight₁ (β : K) with hPm
  have hPmpos : 0 < Pm := Finset.prod_pos fun β _ ↦ mulHeight₁_pos _
  set N := ⌈Real.log Pm⌉₊ + 1 with hN
  have hPmN : Pm ≤ Real.exp N := by
    calc Pm = Real.exp (Real.log Pm) := (Real.exp_log hPmpos).symm
      _ ≤ Real.exp N :=
          Real.exp_le_exp.mpr ((Nat.le_ceil _).trans (by rw [hN]; push_cast; linarith))
  have hmul : ∀ m, mulHeight (fun β ↦ (y m β : K)) ≤ Real.exp m ^ N := by
    intro m
    have hne : (fun β ↦ (y m β : K)) ≠ 0 := fun h0 ↦
      (y m ⟨β₀, hβ₀⟩).ne_zero (congrFun h0 ⟨β₀, hβ₀⟩)
    refine (mulHeight_le_prod_mulHeight₁ S hne fun β ↦
      Set.mem_integer_of_mem_unit (hyS m β)).trans ?_
    simp only [hy, Units.val_pow_eq_pow_val, Units.val_mk0, mulHeight₁_pow]
    rw [Finset.prod_pow, ← Real.exp_nat_mul, mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hPmpos.le hPmN m
  -- the exponents
  set ε := Real.log c / 2 with hε
  have hεpos : 0 < ε := by positivity
  set η := Real.log c / (4 * D * (r + h)) with hη
  have hηpos : 0 < η := by
    have : (0 : ℝ) < r + h := by exact_mod_cast Nat.add_pos_right r hh
    positivity
  set Ξ'' := {m ∈ Ξ' | 1 ≤ m ∧ (q (r + h * m) : ℝ) ≤ Real.exp (η * (r + h * m : ℕ))} with hΞ''
  have hΞ''inf : Ξ''.Infinite := by
    have hbad : {m ∈ Ξ' | ¬ (1 ≤ m ∧ (q (r + h * m) : ℝ) ≤
        Real.exp (η * (r + h * m : ℕ)))}.Finite := by
      refine ((Set.finite_Iio 1).union ((hlog η hηpos).preimage (f := fun m : ℕ ↦ r + h * m)
        (Set.injOn_of_injective fun m₁ m₂ (hm : r + h * m₁ = r + h * m₂) ↦
          Nat.eq_of_mul_eq_mul_left hh (Nat.add_left_cancel hm)))).subset fun m hm ↦ ?_
      · rcases not_and_or.mp hm.2 with h1 | h1
        · exact Or.inl (Set.mem_Iio.mpr (not_le.mp h1))
        · exact Or.inr ⟨hm.1, not_le.mp h1⟩
    refine (hΞ'inf.sdiff hbad).mono fun m hm ↦ ⟨hm.1, ?_⟩
    by_contra h1
    exact hm.2 ⟨hm.1, h1⟩
  -- the hypothesis of Lemma 1 at `P`
  have hlemma : ∀ m ∈ Ξ'', FinitePlace.mk P (∑ β : I, lam β * y m β) <
      (⨆ β : I, FinitePlace.mk P (y m β : K)) * Real.exp m ^ (-ε) := by
    rintro m ⟨hm, hm1, hqm⟩
    obtain ⟨t, ht0, ht⟩ := htr _ hm
    have hq0 : (q (r + h * m) : K) ≠ 0 := Nat.cast_ne_zero.mpr (hq _ hm).ne'
    have hsum : ∑ β : I, lam β * y m β = (t : K) / q (r + h * m) := by
      rw [eq_div_iff hq0, mul_comm, ← ht, hsplit, ← Finset.sum_coe_sort I]
      simp [hy]
    -- the left side is at most `q ^ D`
    have hleft : FinitePlace.mk P (∑ β : I, lam β * y m β) ≤
        (q (r + h * m) : ℝ) ^ D := by
      rw [hsum, map_div₀]
      have hqpos : (0 : ℝ) < q (r + h * m) := by exact_mod_cast hq _ hm
      have hlow := FinitePlace.inv_pow_finrank_le (FinitePlace.mk P)
        (q := (q (r + h * m) : ℤ)) (by exact_mod_cast (hq _ hm).ne')
      push_cast at hlow
      rw [abs_of_pos hqpos, inv_pow] at hlow
      have hwpos : 0 < FinitePlace.mk P (q (r + h * m) : K) := FinitePlace.pos_iff.mpr hq0
      rw [div_le_iff₀ hwpos]
      calc FinitePlace.mk P (t : K) ≤ 1 := FinitePlace.mk_intCast_le_one P t
        _ ≤ _ := by
          rw [← div_le_iff₀' (by positivity), one_div]
          exact hlow
    -- and `q ^ D ≤ exp (m log c / 4)`
    have hqD : (q (r + h * m) : ℝ) ^ D ≤ Real.exp (m * Real.log c / 4) := by
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      calc (q (r + h * m) : ℝ) ^ D ≤ Real.exp (η * (r + h * m : ℕ)) ^ D :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hqm D
        _ = Real.exp (D * (η * (r + h * m : ℕ))) := (Real.exp_nat_mul _ D).symm
        _ ≤ Real.exp (m * Real.log c / 4) := by
          refine Real.exp_le_exp.mpr ?_
          have hrh : (0 : ℝ) < r + h := by exact_mod_cast Nat.add_pos_right r hh
          have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
          have hn : ((r + h * m : ℕ) : ℝ) ≤ (r + h) * m := by
            push_cast
            nlinarith
          rw [hη]
          calc (D : ℝ) * (Real.log c / (4 * D * (r + h)) * ((r + h * m : ℕ) : ℝ))
              = Real.log c / 4 * (((r + h * m : ℕ) : ℝ) / (r + h)) := by
                field_simp
            _ ≤ Real.log c / 4 * m := by
                gcongr
                rw [div_le_iff₀ hrh]
                linarith
            _ = m * Real.log c / 4 := by ring
    -- the right side is at least `exp (m log c / 2)`
    have hright : Real.exp (m * Real.log c / 2) ≤
        (⨆ β : I, FinitePlace.mk P (y m β : K)) * Real.exp m ^ (-ε) := by
      have hsup : c ^ m ≤ ⨆ β : I, FinitePlace.mk P (y m β : K) := by
        refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ⟨β₀, hβ₀⟩)
        simp [hy, hc]
      calc Real.exp (m * Real.log c / 2) = c ^ m * Real.exp m ^ (-ε) := by
            rw [← Real.exp_mul, ← Real.exp_log (zero_lt_one.trans hP), ← Real.exp_nat_mul,
              ← Real.exp_add, Real.log_exp, hε]
            congr 1
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsup (Real.rpow_nonneg (Real.exp_pos _).le _)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    calc FinitePlace.mk P (∑ β : I, lam β * y m β) ≤ Real.exp (m * Real.log c / 4) :=
          hleft.trans hqD
      _ < Real.exp (m * Real.log c / 2) := Real.exp_lt_exp.mpr (by nlinarith)
      _ ≤ _ := hright
  -- Lemma 1 at `P`: a relation among the `β ^ m`
  have : Nonempty I := ⟨⟨β₀, hβ₀⟩⟩
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_infinite_setOf_sum_eq_zero_of_mem_of_tendsto S y
    (fun β ↦ lam β) (fun β ↦ hlam0 β.1 β.2) hPS hεpos hΞ''inf (fun m _ ↦ hyS m)
    (fun m ↦ Real.exp m) (fun m ↦ Real.one_le_exp (Nat.cast_nonneg m))
    (fun B ↦ (Set.finite_Iic ⌈B⌉₊).subset fun m hm ↦ by
      have h1 := Real.add_one_le_exp (m : ℝ)
      exact Nat.cast_le.mp (((by linarith [hm.2] : (m : ℝ) ≤ B).trans (Nat.le_ceil B)).trans_eq
        rfl)) (Nat.succ_pos _) (fun m _ ↦ hmul m) hlemma
  -- Lemma 2 on the support of the relation
  set J := {β : I // b β ≠ 0}
  obtain ⟨β₁⟩ : Nonempty J := by
    obtain ⟨β, hβ⟩ := Function.ne_iff.mp hb0
    exact ⟨⟨β, hβ⟩⟩
  have : Nonempty J := ⟨β₁⟩
  obtain ⟨j₁, j₂, hj, a', b', ha', hb', hinf⟩ := exists_ne_infinite_setOf_add_eq_zero S
    (fun (j : J) m ↦ y m j.1) (fun j ↦ b j.1) (fun j ↦ j.2) hb (fun m hm j ↦ hyS m j.1)
    (fun m hm ↦ by
      calc ∑ j : J, b j.1 * (y m j.1 : K)
          = ∑ β ∈ Finset.univ.filter (fun β : I ↦ b β ≠ 0), b β * (y m β : K) :=
            (Finset.sum_subtype _ (fun β ↦ by simp) (fun β : I ↦ b β * (y m β : K))).symm
        _ = ∑ β : I, b β * (y m β : K) :=
            Finset.sum_filter_of_ne fun β _ h0 ↦ left_ne_zero_of_mul h0
        _ = 0 := hm.2)
  -- the ratio of two distinct `β` is a root of unity, so they are equal
  obtain ⟨σ₁, hσ₁⟩ := hBmem j₁.1.1 j₁.1.2
  obtain ⟨σ₂, hσ₂⟩ := hBmem j₂.1.1 j₂.1.2
  obtain ⟨k, hk, hk1⟩ := exists_pow_div_eq_one_of_infinite (β₁ := j₁.1.1) (β₂ := j₂.1.1)
    (b := b') (hβ0 _ j₁.1.2) (hβ0 _ j₂.1.2) ha' (hinf.mono fun m hm ↦ by simpa [hy] using hm.2)
  apply hj
  have heq := hsep σ₁ σ₂ k hk (by rw [hσ₁, hσ₂]; exact hk1)
  rw [hσ₁, hσ₂] at heq
  exact Subtype.ext (Subtype.ext heq)

end NumberField

open Filter Topology IntermediateField Module

/-- **Lemma 4 of Corvaja–Zannier** (p. 7), with the stronger conclusion. Let `α` be a complex
algebraic number, `Ξ ⊆ ℕ` infinite and `q n > 0` with `log q n / n → 0` along `Ξ`. If
`Tr_{ℚ(α)/ℚ}(q n αⁿ) ∈ ℤ ∖ {0}` for `n ∈ Ξ`, then `α` is an algebraic integer. -/
theorem isIntegral_of_trace_mul_pow {α : ℂ} (hα : IsAlgebraic ℚ α) {Ξ : Set ℕ}
    (hΞ : Ξ.Infinite) {q : ℕ → ℕ} (hq : ∀ n ∈ Ξ, 0 < q n)
    (hlog : Tendsto (fun n : ℕ ↦ Real.log (q n) / n) (atTop ⊓ 𝓟 Ξ) (𝓝 0))
    (htr : ∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧
      Algebra.trace ℚ ℚ⟮α⟯ (q n * AdjoinSimple.gen ℚ α ^ n) = t) :
    IsIntegral ℤ α := by
  classical
  obtain ⟨K, _, _, _, φ, hφ⟩ := NumberField.exists_isGalois_ringHom_mem_range {α} (by simpa)
  obtain ⟨a, ha⟩ := hφ α (Finset.mem_singleton_self _)
  -- `ℚ(a) ≅ ℚ(α)`, generator to generator
  set f : K →ₐ[ℚ] ℂ := φ.toRatAlgHom with hf
  have hfa : f a = α := ha
  have hmap : ℚ⟮a⟯.map f = ℚ⟮α⟯ := by rw [adjoin_map, Set.image_singleton, hfa]
  set e : ℚ⟮a⟯ ≃ₐ[ℚ] ℚ⟮α⟯ := (equivMap ℚ⟮a⟯ f).trans (equivOfEq hmap) with he
  have hegen : e (AdjoinSimple.gen ℚ a) = AdjoinSimple.gen ℚ α := Subtype.ext (by
    simp only [he, AlgEquiv.trans_apply]
    exact hfa)
  -- `∑_σ σ(a) ^ n = [K:ℚ(a)] Tr_{ℚ(a)/ℚ}(aⁿ)`
  have htrK : ∀ n : ℕ, ∑ σ : K ≃ₐ[ℚ] K, σ a ^ n = algebraMap ℚ K
      (finrank ℚ⟮a⟯ K • Algebra.trace ℚ ℚ⟮a⟯ (AdjoinSimple.gen ℚ a ^ n)) := fun n ↦ by
    have h1 : Algebra.trace ℚ K (a ^ n) =
        finrank ℚ⟮a⟯ K • Algebra.trace ℚ ℚ⟮a⟯ (AdjoinSimple.gen ℚ a ^ n) := by
      rw [← Algebra.trace_trace (S := ℚ⟮a⟯),
        show a ^ n = algebraMap ℚ⟮a⟯ K (AdjoinSimple.gen ℚ a ^ n) by
          rw [map_pow, AdjoinSimple.algebraMap_gen],
        Algebra.trace_algebraMap, LinearMap.map_smul_of_tower]
    rw [← h1, trace_eq_sum_automorphisms]
    simp [map_pow]
  -- `log q n = o(n)`
  have hlog' : ∀ η : ℝ, 0 < η → {n ∈ Ξ | Real.exp (η * n) < q n}.Finite := by
    intro η hη
    have hev := hlog.eventually (gt_mem_nhds hη)
    rw [eventually_inf_principal, eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine (Set.finite_lt_nat (N + 1)).subset fun n hn ↦ ?_
    by_contra hnN
    rw [Set.mem_ofPred_eq, not_lt] at hnN
    have h1 := hN n (by omega) hn.1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hq0 : (0 : ℝ) < q n := by exact_mod_cast hq n hn.1
    rw [div_lt_iff₀ hn0] at h1
    have h2 := (Real.lt_log_iff_exp_lt hq0).mpr hn.2
    linarith
  -- the traces
  have htr' : ∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧ (q n : K) * ∑ σ : K ≃ₐ[ℚ] K, σ a ^ n = t := by
    intro n hn
    obtain ⟨t, ht0, ht⟩ := htr n hn
    set y := AdjoinSimple.gen ℚ a ^ n with hy
    have hta : Algebra.trace ℚ ℚ⟮a⟯ ((q n : ℚ⟮a⟯) * y) = t := by
      rw [← Algebra.trace_eq_of_algEquiv e, map_mul, hy, map_pow, hegen, map_natCast, ht]
    have hlin : Algebra.trace ℚ ℚ⟮a⟯ ((q n : ℚ⟮a⟯) * y) = q n * Algebra.trace ℚ ℚ⟮a⟯ y := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    refine ⟨finrank ℚ⟮a⟯ K * t,
      mul_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') ht0, ?_⟩
    rw [htrK, ← hy, nsmul_eq_mul, map_mul, map_natCast, mul_left_comm, ← map_natCast
      (algebraMap ℚ K) (q n), ← map_mul, ← hlin, hta, map_intCast]
    push_cast
    ring
  have hint := NumberField.isIntegral_of_mul_sum_pow_eq_intCast hΞ hq hlog' htr'
  have := hint.map (f.restrictScalars ℤ)
  rwa [AlgHom.restrictScalars_apply, hfa] at this

/-- **Lemma 4 of Corvaja–Zannier** (p. 7), as printed: under the hypotheses of
`isIntegral_of_trace_mul_pow`, `α` is an `h`-th root of a rational number or an algebraic
integer. The proof gives the second alternative. -/
theorem isIntegral_or_exists_pow_eq_ratCast {α : ℂ} (hα : IsAlgebraic ℚ α) {Ξ : Set ℕ}
    (hΞ : Ξ.Infinite) {q : ℕ → ℕ} (hq : ∀ n ∈ Ξ, 0 < q n)
    (hlog : Tendsto (fun n : ℕ ↦ Real.log (q n) / n) (atTop ⊓ 𝓟 Ξ) (𝓝 0))
    (htr : ∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧
      Algebra.trace ℚ ℚ⟮α⟯ (q n * AdjoinSimple.gen ℚ α ^ n) = t) :
    (∃ h : ℕ, 0 < h ∧ ∃ r : ℚ, α ^ h = r) ∨ IsIntegral ℤ α :=
  Or.inr (isIntegral_of_trace_mul_pow hα hΞ hq hlog htr)
