/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.LinearFormSubspaces

/-!
# One linear form with algebraic coefficients

**Layer 7.1** (Bombieri–Gubler, Theorem 7.3.2). For complex algebraic numbers `α 0, …, α n` and
`ε > 0`, only finitely many integer points `x ∈ ℤⁿ⁺¹` satisfy

```text
0 < ‖∑ i, α i * x i‖ ≤ mulHeight x ^ (-n - ε).
```

This is the first consequence the Subspace Theorem has for numbers rather than for points, and
it is the whole of Layer 7.1. The Subspace Theorem enters once per variable:
`DiophantineApproximation/LinearFormSubspaces.lean` puts the solutions into finitely many proper
rational subspaces, and on each of them one variable is eliminated, which is the induction this
file carries out.

## Main results

* `Complex.finite_setOf_norm_sum_mul_le`: Layer 7.1 for an arbitrary finite index type, with the
  exponent `-(#ι - 1) - ε`.
* `Complex.finite_setOf_norm_sum_mul_le_fin`: the same in `n + 1` variables, the shape
  Bombieri–Gubler state.

## Implementation notes

⚠ **Eliminating a variable is what the finitely many subspaces are for.** A proper subspace of
`ℚⁿ⁺¹` lies in the kernel of a nonzero form `∑ i, c i X i`; choosing `k` with `c k ≠ 0` and
dropping the `k`-th coordinate turns `∑ i, α i x i` into `∑ i ≠ k, (α i - α k * c i / c k) x i`,
whose coefficients are again algebraic. The restriction `x ↦ x|_{i ≠ k}` is injective on that
subspace, because the relation determines `x k`, and it does not raise the height, because
removing coordinates lowers every local factor (`Height.mulHeight_comp_le`). Since the exponent
`-(#ι - 1) - ε` weakens by one when `#ι` drops by one, and the height only drops, the reduced
point satisfies the reduced inequality with the *same* `ε`: no room has to be reserved for the
induction.

⚠ **The reduced index type is the subtype `{i // i ≠ k}`, never `Fin n`.** The recursion is on
`Fintype.card ι ≤ n` — a bound, not an equality — so ordinary induction on `n` suffices, and no
statement has to be transported along an equivalence `{i // i ≠ k} ≃ Fin (#ι - 1)`.

⚠ **Three cases stand outside the induction step.** If every `α i` vanishes the set is empty,
and it has to be treated separately because the Subspace Theorem step needs some `α j ≠ 0`. If
there are no variables the value is `0`, so the set is empty again. If there is one variable the
Subspace Theorem is unavailable — it needs `[Nontrivial ι]` — but it is also unnecessary: the
height of a one-coordinate point is `1` by the product formula, so the inequality reads
`‖α j‖ * |x j| ≤ 1` and bounds `x j` outright. That last case is where the theorem's content
degenerates to Liouville's inequality in its crudest form.

⚠ **The statement is stronger than the classical one, because the height is not the sup norm.**
Bombieri–Gubler write `|x| ^ (-n - ε)` with `|x| = max |x i|`; over `ℚ` the projective height of
an integer point is `max |x i|` divided by the greatest common divisor of the coordinates, so
`mulHeight x ≤ |x|` and the set counted here *contains* the classical one. The gain is a factor
`gcd(x) ^ (n + ε)`, and it is free: Layer 6.3 is a statement about projective points, and it is
the sup norm, not the height, that had to be introduced by hand in the proof.

⚠ **The exponent `-n - ε` cannot be improved to `-n`.** By the box principle every
`x` with `|x|` large enough admits a nonzero value below `|x| ^ (-n)`, so the theorem is sharp;
that direction is Layer 1.3's business and is not formalized here. What *is* recorded below is
the other sharpness: the hypothesis `0 < ‖∑ i, α i x i‖` cannot be dropped, whatever the
exponent.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.3.2 and Remark 7.3.3.

This is part of Layer 7.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height

universe u

namespace Complex

/-- **Layer 7.1**, the induction on the number of variables. The recursion is on a bound for
the cardinality of the index type, so that ordinary induction on a natural number suffices. -/
private theorem finite_setOf_norm_sum_le_aux : ∀ (n : ℕ) {ι : Type u} [Fintype ι] {α : ι → ℂ},
    (∀ i, IsAlgebraic ℚ (α i)) → Fintype.card ι ≤ n → ∀ {ε : ℝ}, 0 < ε →
      {x : ι → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
        ‖∑ i, α i * (x i : ℂ)‖
          ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε)}.Finite := by
  intro n
  induction n with
  | zero =>
      intro ι _ α hα hcard ε hε
      have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      refine Set.Finite.subset Set.finite_empty fun x hx ↦ ?_
      exact absurd hx.1 (by simp)
  | succ n ih =>
      intro ι _ α hα hcard ε hε
      classical
      by_cases hall : ∀ i, α i = 0
      · refine Set.Finite.subset Set.finite_empty fun x hx ↦ ?_
        exact absurd hx.1 (by simp [hall])
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hne : Nonempty ι := ⟨j⟩
      rcases le_or_gt (Fintype.card ι) 1 with hc1 | hc2
      · have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hc1
        have hcard1 : Fintype.card ι = 1 := le_antisymm hc1 Fintype.card_pos
        refine Set.Finite.of_finite_image (f := fun x : ι → ℤ ↦ x j) ?_ ?_
        · refine Set.Finite.subset (Set.finite_Icc (-⌈‖α j‖⁻¹⌉) ⌈‖α j‖⁻¹⌉) ?_
          rintro m ⟨x, hx, rfl⟩
          obtain ⟨hpos, hle⟩ := hx
          have hsum : (∑ i, α i * (x i : ℂ)) = α j * (x j : ℂ) :=
            Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun b _ hb ↦
              absurd (Subsingleton.elim b j) hb
          have hxj : ((x j : ℤ) : ℚ) ≠ 0 := by
            intro h0
            rw [hsum] at hpos
            have hz : ((x j : ℤ) : ℂ) = 0 := by exact_mod_cast h0
            rw [hz, mul_zero, norm_zero] at hpos
            exact lt_irrefl 0 hpos
          have hH : mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) = 1 := by
            have heq : (fun i ↦ ((x i : ℤ) : ℚ)) = ((x j : ℤ) : ℚ) • (1 : ι → ℚ) := by
              funext i
              rw [Subsingleton.elim i j]
              simp
            rw [heq, mulHeight_smul_eq_mulHeight _ hxj, mulHeight_one]
          rw [hsum, hH, hcard1] at hle
          norm_num at hle
          have hαj : 0 < ‖α j‖ := norm_pos_iff.mpr hj
          have habs : |((x j : ℤ) : ℝ)| ≤ ‖α j‖⁻¹ := by
            rw [← one_div, le_div_iff₀ hαj, mul_comm]
            exact hle
          have hceil : |x j| ≤ ⌈‖α j‖⁻¹⌉ := by
            have : |((x j : ℤ) : ℝ)| ≤ ((⌈‖α j‖⁻¹⌉ : ℤ) : ℝ) := habs.trans (Int.le_ceil _)
            exact_mod_cast this
          simpa only [Set.mem_Icc] using abs_le.mp hceil
        · intro x _ y _ h
          funext i
          rw [Subsingleton.elim i j]
          exact h
      · have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hc2
        obtain ⟨T, hTproper, hTmem⟩ := Complex.exists_finset_submodule_of_norm_sum_le hα hj hε
        have hx0 : ∀ x : ι → ℤ, 0 < ‖∑ i, α i * (x i : ℂ)‖ → (fun i ↦ ((x i : ℤ) : ℚ)) ≠ 0 := by
          intro x hpos h0
          have hxi : ∀ i, x i = 0 := fun i ↦ by
            have h := congrFun h0 i
            simp only [Pi.zero_apply] at h
            exact_mod_cast h
          simp [hxi] at hpos
        have hcover : {x : ι → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
            ‖∑ i, α i * (x i : ℂ)‖
              ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε)}
            ⊆ ⋃ V ∈ (T : Set (Submodule ℚ (ι → ℚ))),
                {x : ι → ℤ | (0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
                  ‖∑ i, α i * (x i : ℂ)‖
                    ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε))
                  ∧ (fun i ↦ ((x i : ℤ) : ℚ)) ∈ V} := by
          intro x hx
          obtain ⟨V, hV, hmem⟩ := hTmem x (hx0 x hx.1) hx.2
          exact Set.mem_biUnion hV ⟨hx, hmem⟩
        refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun V hV ↦ ?_) hcover
        obtain ⟨f, hf0, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
          (lt_top_iff_ne_top.mpr (hTproper V hV)) inferInstance
        set c : ι → ℚ := fun i ↦ f (fun t ↦ if i = t then 1 else 0) with hcdef
        have hfx : ∀ y : ι → ℚ, f y = ∑ i, y i * c i := by
          intro y
          rw [LinearMap.pi_apply_eq_sum_univ f y]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]
        obtain ⟨k, hck⟩ : ∃ k, c k ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hf0 (LinearMap.ext fun y ↦ by simp [hfx y, hcon])
        have hrel : ∀ x : ι → ℤ, (fun i ↦ ((x i : ℤ) : ℚ)) ∈ V →
            ∑ i, ((x i : ℤ) : ℚ) * c i = 0 := by
          intro x hxV
          have hmap : f (fun i ↦ ((x i : ℤ) : ℚ)) ∈ Submodule.map f V :=
            Submodule.mem_map_of_mem hxV
          rw [hfV, Submodule.mem_bot] at hmap
          rw [← hfx]
          exact hmap
        set β : {i : ι // i ≠ k} → ℂ := fun i ↦ α i.1 - α k * ((c i.1 / c k : ℚ) : ℂ) with hβdef
        have hβ : ∀ i, IsAlgebraic ℚ (β i) := fun i ↦
          (((hα i.1).isIntegral).sub (((hα k).isIntegral).mul isIntegral_algebraMap)).isAlgebraic
        have hcard' : Fintype.card {i : ι // i ≠ k} ≤ n := by
          have h1 : Fintype.card {i : ι // i ≠ k} = Fintype.card ι - 1 := by
            simp [Fintype.card_subtype_compl]
          omega
        have hckC : ((c k : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hck
        refine Set.Finite.of_finite_image (f := fun x : ι → ℤ ↦ fun i : {i : ι // i ≠ k} ↦ x i.1)
          (Set.Finite.subset (ih hβ hcard' hε) ?_) ?_
        · rintro _ ⟨x, ⟨⟨hpos, hle⟩, hxV⟩, rfl⟩
          have hrelC : ∑ i ∈ Finset.univ.erase k, ((x i : ℤ) : ℂ) * ((c i : ℚ) : ℂ)
              = -(((x k : ℤ) : ℂ) * ((c k : ℚ) : ℂ)) := by
            have h1 : ((∑ i, ((x i : ℤ) : ℚ) * c i : ℚ) : ℂ) = 0 := by rw [hrel x hxV]; simp
            push_cast at h1
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1
            exact eq_neg_of_add_eq_zero_right h1
          have hsum : ∑ i : {i : ι // i ≠ k}, β i * ((x i.1 : ℤ) : ℂ)
              = ∑ i, α i * ((x i : ℤ) : ℂ) := by
            have hsub : ∑ i : {i : ι // i ≠ k}, β i * ((x i.1 : ℤ) : ℂ)
                = ∑ i ∈ Finset.univ.erase k,
                    (α i - α k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ) :=
              (Finset.sum_subtype _ (fun i ↦ by simp)
                (fun i ↦ (α i - α k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ))).symm
            have hterm : ∀ i ∈ Finset.univ.erase k,
                (α i - α k * ((c i / c k : ℚ) : ℂ)) * ((x i : ℤ) : ℂ)
                  = α i * ((x i : ℤ) : ℂ)
                    - (α k / ((c k : ℚ) : ℂ)) * (((x i : ℤ) : ℂ) * ((c i : ℚ) : ℂ)) := by
              intro i _
              push_cast
              ring
            rw [hsub, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hrelC,
              ← Finset.add_sum_erase _ (fun i ↦ α i * ((x i : ℤ) : ℂ)) (Finset.mem_univ k)]
            field_simp
            ring
          have hheight : mulHeight (fun i : {i : ι // i ≠ k} ↦ ((x i.1 : ℤ) : ℚ))
              ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) :=
            mulHeight_comp_le (fun i : {i : ι // i ≠ k} ↦ i.1) (fun i ↦ ((x i : ℤ) : ℚ))
          have hH1 : (1 : ℝ) ≤ mulHeight (fun i : {i : ι // i ≠ k} ↦ ((x i.1 : ℤ) : ℚ)) :=
            one_le_mulHeight _
          have he0 : (-(Fintype.card ι - 1 : ℝ) - ε) ≤ 0 := by
            have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hc2
            linarith
          have hcards : (Fintype.card {i : ι // i ≠ k} : ℝ) = (Fintype.card ι : ℝ) - 1 := by
            have h1 : Fintype.card {i : ι // i ≠ k} = Fintype.card ι - 1 := by
              simp [Fintype.card_subtype_compl]
            have h2 : 1 ≤ Fintype.card ι := by omega
            rw [h1, Nat.cast_sub h2, Nat.cast_one]
          refine ⟨by rw [hsum]; exact hpos, ?_⟩
          rw [hsum]
          calc ‖∑ i, α i * ((x i : ℤ) : ℂ)‖
              ≤ mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε) := hle
            _ ≤ mulHeight (fun i : {i : ι // i ≠ k} ↦ ((x i.1 : ℤ) : ℚ))
                  ^ (-(Fintype.card ι - 1 : ℝ) - ε) :=
                Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hH1) hheight he0
            _ ≤ mulHeight (fun i : {i : ι // i ≠ k} ↦ ((x i.1 : ℤ) : ℚ))
                  ^ (-(Fintype.card {i : ι // i ≠ k} - 1 : ℝ) - ε) := by
                refine Real.rpow_le_rpow_of_exponent_le hH1 ?_
                rw [hcards]
                linarith
        · rintro x ⟨-, hxV⟩ y ⟨-, hyV⟩ hxy
          funext i
          by_cases hik : i = k
          · rw [hik]
            have h1 := hrel x hxV
            have h2 := hrel y hyV
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1 h2
            have heq : ∑ t ∈ Finset.univ.erase k, ((x t : ℤ) : ℚ) * c t
                = ∑ t ∈ Finset.univ.erase k, ((y t : ℤ) : ℚ) * c t :=
              Finset.sum_congr rfl fun t ht ↦ by
                rw [show x t = y t from congrFun hxy ⟨t, (Finset.mem_erase.mp ht).1⟩]
            rw [heq] at h1
            have hxy' : ((x k : ℤ) : ℚ) * c k = ((y k : ℤ) : ℚ) * c k := by linarith
            exact_mod_cast mul_right_cancel₀ hck hxy'
          · exact congrFun hxy ⟨i, hik⟩

/-- **Layer 7.1** (Bombieri–Gubler, Theorem 7.3.2). **One linear form with algebraic
coefficients.** For complex algebraic `α i` and `ε > 0`, only finitely many integer points `x`
satisfy `0 < ‖∑ i, α i * x i‖ ≤ H(x) ^ (-n - ε)`, where `n + 1` is the number of variables and
`H` is the projective height of `x` over `ℚ`. The hypothesis is that the value is nonzero, not
that the coefficients are linearly independent. -/
theorem finite_setOf_norm_sum_mul_le {ι : Type*} [Fintype ι] {α : ι → ℂ}
    (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : ι → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
      ‖∑ i, α i * (x i : ℂ)‖
        ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(Fintype.card ι - 1 : ℝ) - ε)}.Finite :=
  finite_setOf_norm_sum_le_aux (Fintype.card ι) hα le_rfl hε

/-- **Layer 7.1 in `n + 1` variables**, the shape Bombieri–Gubler state: the exponent is
`-n - ε` for `x ∈ ℤⁿ⁺¹`. -/
theorem finite_setOf_norm_sum_mul_le_fin {n : ℕ} {α : Fin (n + 1) → ℂ}
    (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : Fin (n + 1) → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
      ‖∑ i, α i * (x i : ℂ)‖
        ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(n : ℝ) - ε)}.Finite := by
  have h := finite_setOf_norm_sum_mul_le hα hε
  have hexp : (-((Fintype.card (Fin (n + 1)) : ℝ) - 1) - ε) = -(n : ℝ) - ε := by
    rw [Fintype.card_fin]
    push_cast
    ring
  rwa [hexp] at h

/-!
## Acceptance criteria
-/

/-- Layer 7.1 in the shape the roadmap states it. -/
example {n : ℕ} (α : Fin (n + 1) → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i)) {ε : ℝ} (hε : 0 < ε) :
    {x : Fin (n + 1) → ℤ | 0 < ‖∑ i, α i * (x i : ℂ)‖ ∧
      ‖∑ i, α i * (x i : ℂ)‖
        ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(n : ℝ) - ε)}.Finite :=
  finite_setOf_norm_sum_mul_le_fin hα hε

/-- **The nonvanishing hypothesis cannot be dropped.** The form `X 0 - X 1` vanishes on the
diagonal, and every point of the diagonal satisfies the inequality with room to spare, so
without `0 < ‖∑ i, α i * x i‖` the set is infinite — for coefficients as algebraic as `1` and
`-1`. This is why Bombieri–Gubler's Theorem 7.3.2 asks for a nonzero value and not for
independent coefficients. -/
example (ε : ℝ) :
    {x : Fin 2 → ℤ | ‖∑ i, (![1, -1] : Fin 2 → ℂ) i * (x i : ℂ)‖
      ≤ mulHeight (fun i ↦ (x i : ℚ)) ^ (-(1 : ℝ) - ε)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ ↦ (fun _ ↦ (m : ℤ) : Fin 2 → ℤ)) (fun m m' hmm ↦ ?_) fun m ↦ ?_
  · have h : ((m : ℤ)) = ((m' : ℤ)) := congrFun hmm 0
    exact_mod_cast h
  · have h0 : (∑ i, (![1, -1] : Fin 2 → ℂ) i * ((m : ℤ) : ℂ)) = 0 := by
      rw [Fin.sum_univ_two]
      simp
    rw [Set.mem_ofPred_eq, h0, norm_zero]
    positivity

end Complex
