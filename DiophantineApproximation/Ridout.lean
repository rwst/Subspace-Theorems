/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RationalPlaces
public import DiophantineApproximation.RothInfinity
public import DiophantineApproximation.RothRational

/-!
# Ridout's theorem and the `p`-adic form of Roth's theorem

The two forms of Roth's theorem over `ℚ` that carry finite places. **Ridout's theorem**
(Ridout 1958) says that for a real algebraic `ξ`, finite sets `S₁`, `S₂` of primes and `ε > 0`
only finitely many `p / q` in lowest terms satisfy

```text
|ξ - p / q| * ∏ l ∈ S₁, |p| l * ∏ l ∈ S₂, |q| l ≤ max |p| q ^ (-2 - ε);
```

the **`p`-adic form** (Bombieri–Gubler 6.2.6) says that for `α` in a number field `F`, an
absolute value `w` of `F` over `padicNorm p` and `ε > 0`, only finitely many rational integers
`n` satisfy `w (n - α) ≤ |n| ^ (-1 - ε)`.

Both are Layer 3.3's `OnePoint` form of Roth's theorem for a choice of data, read through Layer
3.3's dictionary between the finite places of `ℚ` and the `p`-adic absolute values.

## Main results

* `Rat.finite_setOf_onePointApprox_mul_prod_le`: Roth's theorem over `ℚ` with a target in
  `OnePoint F` at the infinite place and at each prime of a finite set. Every classical form is
  an instance of this one.
* `Rat.finite_setOf_ridout`: Ridout's theorem.
* `Rat.finite_setOf_apply_intCast_sub_le`: the `p`-adic form.

## Implementation notes

⚠ **The `p`-adic form gains its exponent at the infinite place.** With one place the best Roth's
theorem gives is `2 + ε`; the exponent `1 + ε` comes from putting the target `∞` at the infinite
place, where an integer `n` has local factor exactly `H(n)⁻¹`. Without that target the statement
is false as written for small `ε`, and it is why Layer 3.3's `OnePoint` form is needed and not
Layer 3.2 alone.

⚠ **A prime in `S₁ ∩ S₂` carries two factors, and Roth's theorem carries one target per place.**
The two are reconciled by the coprimality of `p` and `q`: such a prime divides at most one of
them, so on each of the `2 ^ |S₁ ∩ S₂|` classes cut out by *which* it divides, one of the two
factors is `1` and a single target — `0` or `∞` — accounts for both. The solution set is the
union of those finitely many classes, each finite by Roth's theorem. This is the only place in
Layer 3.3 where the solution set is split.

⚠ **The exponent is `-2 - ε` against the naive height, not `-2 - ε` against the denominator.**
Over `ℚ` the multiplicative height of `p / q` in lowest terms is `max |p| q`, and that is what
`Rat.mulHeight₁_eq_max` puts into the statement; no constant is left over.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.2.4 and Corollary 6.2.6; D. Ridout, *The `p`-adic generalization of the
Thue–Siegel–Roth theorem*, Mathematika 5 (1958).

This is part of Layer 3.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height NumberField AbsoluteValue OnePoint IntermediateField

namespace Rat

variable {F : Type*} [Field F] [NumberField F]

/-- **Roth's theorem over `ℚ`, with a target at every place of `S`.** The infinite place carries
the target `a` and each prime `ℓ ∈ P` the target `tf ℓ`, both in `OnePoint F`; the height is the
naive one. This is the shape every classical form of Roth's theorem is an instance of. -/
theorem finite_setOf_onePointApprox_mul_prod_le
    (P : Finset Nat.Primes) (wf : Nat.Primes → AbsoluteValue F ℝ)
    (hwf : ∀ ℓ ∈ P, (wf ℓ).LiesOver (AbsoluteValue.padic (ℓ : ℕ)))
    (winf : AbsoluteValue F ℝ) (hwinf : winf.LiesOver Rat.infinitePlace.1)
    (a : OnePoint F) (tf : Nat.Primes → OnePoint F) {κ : ℝ} (hκ : 2 < κ) :
    {β : ℚ | winf.onePointApprox a (algebraMap ℚ F β)
        * ∏ ℓ ∈ P, (wf ℓ).onePointApprox (tf ℓ) (algebraMap ℚ F β)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-κ)}.Finite := by
  classical
  -- the extension and the target, as functions on all absolute values of `ℚ`
  have key : ∀ u : AbsoluteValue ℚ ℝ, ∃ x : AbsoluteValue F ℝ × OnePoint F,
      (∀ ℓ : Nat.Primes, (Rat.finitePlace ℓ).1 = u → x = (wf ℓ, tf ℓ)) ∧
        (u = Rat.infinitePlace.1 → x = (winf, a)) := by
    intro u
    by_cases hu : ∃ ℓ : Nat.Primes, (Rat.finitePlace ℓ).1 = u
    · obtain ⟨ℓ, rfl⟩ := hu
      refine ⟨(wf ℓ, tf ℓ), fun ℓ' hℓ' ↦ ?_, fun hc ↦ ?_⟩
      · rw [finitePlace_injective (Subtype.ext hℓ')]
      · exact absurd (by rw [← hc, finitePlace_val]) (infinitePlace_val_ne_padic ℓ)
    · exact ⟨(winf, a), fun ℓ hℓ ↦ absurd ⟨ℓ, hℓ⟩ hu, fun _ ↦ rfl⟩
  choose g hgf hginf using key
  have hwinf' : (g Rat.infinitePlace.1).1 = winf := congrArg Prod.fst (hginf _ rfl)
  have hainf : (g Rat.infinitePlace.1).2 = a := congrArg Prod.snd (hginf _ rfl)
  have hwfin : ∀ ℓ : Nat.Primes, (g (Rat.finitePlace ℓ).1).1 = wf ℓ :=
    fun ℓ ↦ congrArg Prod.fst (hgf _ ℓ rfl)
  have hafin : ∀ ℓ : Nat.Primes, (g (Rat.finitePlace ℓ).1).2 = tf ℓ :=
    fun ℓ ↦ congrArg Prod.snd (hgf _ ℓ rfl)
  have hroth := NumberField.finite_setOf_prod_onePointApprox_le (K := ℚ) (F := F)
    {Rat.infinitePlace} (P.image Rat.finitePlace) (fun u ↦ (g u).1)
    (fun v hv ↦ by
      rw [Finset.mem_singleton.mp hv]
      simp only [hwinf']
      exact hwinf)
    (fun v hv ↦ by
      obtain ⟨l, hlP, rfl⟩ := Finset.mem_image.mp hv
      rw [hwfin l, finitePlace_val]
      exact hwf l hlP)
    (fun u ↦ (g u).2) hκ
  refine hroth.subset fun β hβ ↦ ?_
  rw [Set.mem_ofPred_eq] at hβ ⊢
  rw [Finset.prod_singleton,
    NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
    Finset.prod_image fun x _ y _ h ↦ finitePlace_injective h, mulHeight₁_eq_max, Nat.cast_max]
  simp only [hwinf', hainf, hwfin, hafin]
  exact hβ

/-- **The `p`-adic form of Roth's theorem** (Bombieri–Gubler 6.2.6). For a target `α` in a number
field `F`, an absolute value `w` of `F` over the `p`-adic absolute value of `ℚ`, and `ε > 0`,
only finitely many rational integers `n` satisfy `w (n - α) ≤ |n| ^ (-1 - ε)`. The exponent is
`1 + ε` and not `2 + ε` because an integer is already extremal at the infinite place: the target
`∞` there contributes exactly `H(n)⁻¹`. -/
theorem finite_setOf_apply_intCast_sub_le (p : Nat.Primes) (w : AbsoluteValue F ℝ)
    (hw : w.LiesOver (AbsoluteValue.padic (p : ℕ))) (α : F) {ε : ℝ} (hε : 0 < ε) :
    {n : ℤ | w ((n : F) - α) ≤ |(n : ℝ)| ^ (-1 - ε)}.Finite := by
  obtain ⟨winf0, hwinf⟩ := NumberField.exists_liesOver_infinitePlace (K := ℚ) (F := F)
    Rat.infinitePlace
  have hX := finite_setOf_onePointApprox_mul_prod_le (F := F) {p} (fun _ ↦ w)
    (fun l hl ↦ by rwa [Finset.mem_singleton.mp hl]) winf0.1 hwinf (∞ : OnePoint F)
    (fun _ ↦ (α : OnePoint F)) (κ := 2 + ε) (by linarith)
  simp only [Finset.prod_singleton, onePointApprox_infty, onePointApprox_coe] at hX
  have hinf : ∀ q : ℚ, winf0.1 (algebraMap ℚ F q) = ((|q| : ℚ) : ℝ) := fun q ↦ by
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := Rat.infinitePlace.1) winf0.1 q,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
  refine Set.Finite.subset ((Set.finite_Icc (-1 : ℤ) 1).union
    (Set.Finite.preimage (f := fun n : ℤ ↦ (n : ℚ)) Int.cast_injective.injOn hX)) ?_
  intro n hn
  rw [Set.mem_ofPred_eq] at hn
  by_cases hsmall : |n| ≤ 1
  · refine Or.inl ?_
    rw [Set.mem_Icc]
    exact ⟨neg_le_of_abs_le hsmall, le_of_abs_le hsmall⟩
  refine Or.inr ?_
  rw [Set.mem_preimage, Set.mem_ofPred_eq]
  push Not at hsmall
  have hn0 : n ≠ 0 := by
    intro hcon
    rw [hcon] at hsmall
    simp at hsmall
  have hnat : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
  have hn1 : (1 : ℝ) < |(n : ℝ)| := by
    have h : ((1 : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by exact_mod_cast hsmall
    rwa [Int.cast_abs, Int.cast_one] at h
  have habs0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  have hmap : algebraMap ℚ F ((n : ℚ)) = (n : F) := map_intCast (algebraMap ℚ F) n
  have hheight : ((max ((n : ℚ)).num.natAbs ((n : ℚ)).den : ℕ) : ℝ) = |(n : ℝ)| := by
    rw [Rat.num_intCast, Rat.den_intCast, max_eq_left hnat, Nat.cast_natAbs, Int.cast_abs]
  have hval : winf0.1 ((n : F)) = |(n : ℝ)| := by
    rw [← hmap, hinf]
    push_cast
    ring
  rw [← Nat.cast_max, hheight, hmap, hval, max_eq_right hn1.le]
  have hinvpow : |(n : ℝ)|⁻¹ = |(n : ℝ)| ^ (-1 : ℝ) := by
    rw [Real.rpow_neg habs0.le, Real.rpow_one]
  calc |(n : ℝ)|⁻¹ * min 1 (w ((n : F) - α))
      ≤ |(n : ℝ)|⁻¹ * |(n : ℝ)| ^ (-1 - ε) :=
        mul_le_mul_of_nonneg_left (le_trans (min_le_right _ _) hn) (by positivity)
    _ = |(n : ℝ)| ^ (-(2 + ε)) := by
        rw [hinvpow, ← Real.rpow_add habs0]
        congr 1
        ring

/-- **Ridout's theorem** (Ridout 1958). For a real algebraic number `ξ`, finite sets `S₁`, `S₂` of
primes and `ε > 0`, only finitely many rationals `β = p / q` in lowest terms satisfy

```text
|ξ - p / q| * ∏ l ∈ S₁, |p|_l * ∏ l ∈ S₂, |q|_l ≤ max |p| q ^ (-2 - ε).
```

The targets are `0` at the primes of `S₁` and `∞` at those of `S₂`; a prime of `S₁ ∩ S₂` divides
at most one of `p` and `q`, so the solutions split into `2 ^ |S₁ ∩ S₂|` classes on each of which
one target suffices, and each class is finite by Roth's theorem. -/
theorem finite_setOf_ridout {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) (S₁ S₂ : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    {β : ℚ | |ξ - (β : ℝ)| * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite := by
  classical
  have hint : IsIntegral ℚ ξ := halg.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
  have hnf : NumberField ℚ⟮ξ⟯ := {}
  set winf : AbsoluteValue ℚ⟮ξ⟯ ℝ := AbsoluteValue.abs.comp (algebraMap ℚ⟮ξ⟯ ℝ).injective
    with hwinfdef
  have hwapply : ∀ x : ℚ⟮ξ⟯, winf x = |(algebraMap ℚ⟮ξ⟯ ℝ) x| := fun x ↦ rfl
  have hwinf : winf.LiesOver Rat.infinitePlace.1 := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def]
    simp only [AbsoluteValue.comp_apply]
    rw [hwapply, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
    simp
  set a : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hadef
  have ha : (algebraMap ℚ⟮ξ⟯ ℝ) a = ξ := rfl
  -- an absolute value of `ℚ⟮ξ⟯` over every `p`-adic absolute value of `ℚ`
  have hex : ∀ l : Nat.Primes,
      ∃ x : AbsoluteValue ℚ⟮ξ⟯ ℝ, x.LiesOver (AbsoluteValue.padic (l : ℕ)) := fun l ↦ by
    obtain ⟨x, hx⟩ := NumberField.exists_liesOver_finitePlace (K := ℚ) (F := ℚ⟮ξ⟯)
      (Rat.finitePlace l)
    exact ⟨x, by rwa [Rat.finitePlace_val] at hx⟩
  choose wf hwf using hex
  have hnumval : ∀ (l : Nat.Primes) (β : ℚ),
      (wf l).onePointApprox (((0 : ℚ⟮ξ⟯) : OnePoint ℚ⟮ξ⟯)) (algebraMap ℚ ℚ⟮ξ⟯ β)
        = ((padicNorm (l : ℕ) β.num : ℚ) : ℝ) := fun l β ↦ by
    have hinst : (wf l).LiesOver (AbsoluteValue.padic (l : ℕ)) := hwf l
    rw [AbsoluteValue.onePointApprox_coe, sub_zero,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := AbsoluteValue.padic (l : ℕ)) (wf l) β,
      Rat.min_one_padic_apply]
  have hdenval : ∀ (l : Nat.Primes) (β : ℚ),
      (wf l).onePointApprox (∞ : OnePoint ℚ⟮ξ⟯) (algebraMap ℚ ℚ⟮ξ⟯ β)
        = ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) := fun l β ↦ by
    have hinst : (wf l).LiesOver (AbsoluteValue.padic (l : ℕ)) := hwf l
    rw [AbsoluteValue.onePointApprox_infty,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := AbsoluteValue.padic (l : ℕ)) (wf l) β,
      Rat.max_one_padic_apply_inv]
  have harchval : ∀ β : ℚ,
      winf.onePointApprox ((a : ℚ⟮ξ⟯) : OnePoint ℚ⟮ξ⟯) (algebraMap ℚ ℚ⟮ξ⟯ β)
        = min 1 |ξ - (β : ℝ)| := fun β ↦ by
    rw [AbsoluteValue.onePointApprox_coe, hwapply, map_sub, ha,
      ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ, abs_sub_comm]
    simp
  -- one application of Roth's theorem for each way the primes of `S₁ ∩ S₂` can divide `p`
  have hX : ∀ E : Finset Nat.Primes,
      {β : ℚ | winf.onePointApprox ((a : ℚ⟮ξ⟯) : OnePoint ℚ⟮ξ⟯) (algebraMap ℚ ℚ⟮ξ⟯ β)
          * ∏ l ∈ S₁ ∪ S₂, (wf l).onePointApprox
              (if l ∈ S₁ \ S₂ ∪ E then ((0 : ℚ⟮ξ⟯) : OnePoint ℚ⟮ξ⟯) else ∞)
              (algebraMap ℚ ℚ⟮ξ⟯ β)
        ≤ (max β.num.natAbs β.den : ℝ) ^ (-(2 + ε))}.Finite := fun E ↦
    Rat.finite_setOf_onePointApprox_mul_prod_le (S₁ ∪ S₂) wf (fun l _ ↦ hwf l) winf hwinf _ _
      (by linarith)
  refine Set.Finite.subset
    (Set.Finite.biUnion (S₁ ∩ S₂).powerset.finite_toSet fun E _ ↦ hX E) ?_
  intro β hβ
  rw [Set.mem_ofPred_eq] at hβ
  set E : Finset Nat.Primes := (S₁ ∩ S₂).filter (fun l ↦ ((l : ℕ) : ℤ) ∣ β.num) with hEdef
  have hEmem : E ∈ (S₁ ∩ S₂).powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  refine Set.mem_biUnion hEmem ?_
  rw [Set.mem_ofPred_eq, harchval]
  -- the product over the places of `S₁ ∪ S₂` is Ridout's two products
  have hprod : (∏ l ∈ S₁ ∪ S₂, (wf l).onePointApprox
        (if l ∈ S₁ \ S₂ ∪ E then ((0 : ℚ⟮ξ⟯) : OnePoint ℚ⟮ξ⟯) else ∞) (algebraMap ℚ ℚ⟮ξ⟯ β))
      = (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) := by
    have h1 : (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
        = ∏ l ∈ S₁ ∪ S₂, (if l ∈ S₁ then ((padicNorm (l : ℕ) β.num : ℚ) : ℝ) else 1) := by
      rw [← Finset.prod_subset (Finset.subset_union_left (s₁ := S₁) (s₂ := S₂))
        fun x _ hx ↦ ite_eq_right hx]
      exact Finset.prod_congr rfl fun l hl ↦ (ite_eq_left hl).symm
    have h2 : (∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ))
        = ∏ l ∈ S₁ ∪ S₂, (if l ∈ S₂ then ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) else 1) := by
      rw [← Finset.prod_subset (Finset.subset_union_right (s₁ := S₁) (s₂ := S₂))
        fun x _ hx ↦ ite_eq_right hx]
      exact Finset.prod_congr rfl fun l hl ↦ (ite_eq_left hl).symm
    rw [h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hden1 : ((l : ℕ) : ℤ) ∣ β.num → ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) = 1 := fun hdvd ↦ by
      have hnat : (l : ℕ) ∣ β.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd)
      have hnd : ¬ (l : ℕ) ∣ β.den := fun hc ↦
        l.2.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hnat β.reduced) hc)
      rw [(padicNorm.nat_eq_one_iff _).mpr hnd]
      norm_num
    have hnum1 : ¬ ((l : ℕ) : ℤ) ∣ β.num → ((padicNorm (l : ℕ) β.num : ℚ) : ℝ) = 1 :=
      fun hdvd ↦ by
        rw [(padicNorm.int_eq_one_iff _).mpr hdvd]
        norm_num
    by_cases h1S : l ∈ S₁ <;> by_cases h2S : l ∈ S₂
    · have hmem : l ∈ S₁ \ S₂ ∪ E ↔ ((l : ℕ) : ℤ) ∣ β.num := by
        simp only [Finset.mem_union, Finset.mem_sdiff, hEdef, Finset.mem_filter, Finset.mem_inter]
        tauto
      by_cases hdvd : ((l : ℕ) : ℤ) ∣ β.num
      · rw [ite_eq_left (hmem.mpr hdvd), hnumval, ite_eq_left h1S, ite_eq_left h2S,
          hden1 hdvd, mul_one]
      · rw [ite_eq_right (fun hc ↦ hdvd (hmem.mp hc)), hdenval, ite_eq_left h1S,
          ite_eq_left h2S, hnum1 hdvd, one_mul]
    · have hmem : l ∈ S₁ \ S₂ ∪ E :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1S, h2S⟩)
      rw [ite_eq_left hmem, hnumval, ite_eq_left h1S, ite_eq_right h2S, mul_one]
    · have hmem : l ∉ S₁ \ S₂ ∪ E := by
        simp only [Finset.mem_union, Finset.mem_sdiff, hEdef, Finset.mem_filter, Finset.mem_inter]
        tauto
      rw [ite_eq_right hmem, hdenval, ite_eq_right h1S, ite_eq_left h2S, one_mul]
    · exact absurd (Finset.mem_union.mp hl) (by tauto)
  rw [hprod]
  have hnn1 : (0 : ℝ) ≤ ∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ) :=
    Finset.prod_nonneg fun l _ ↦ by exact_mod_cast padicNorm.nonneg (p := (l : ℕ)) _
  have hnn2 : (0 : ℝ) ≤ ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) :=
    Finset.prod_nonneg fun l _ ↦ by exact_mod_cast padicNorm.nonneg (p := (l : ℕ)) _
  have hexp : (-(2 + ε) : ℝ) = -2 - ε := by ring
  rw [hexp]
  calc min 1 |ξ - (β : ℝ)|
        * ((∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
          * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ))
      ≤ |ξ - (β : ℝ)| * ((∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
          * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg hnn1 hnn2)
    _ = |ξ - (β : ℝ)| * (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ))
          * ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ) := by ring
    _ ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε) := hβ

/-! ### Acceptance criteria -/

/-- **Conformance: Roth's theorem is Ridout's with no primes.** -/
example {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) {ε : ℝ} (hε : 0 < ε) :
    {β : ℚ | |ξ - (β : ℝ)| ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite := by
  have h := finite_setOf_ridout halg ∅ ∅ hε
  simpa using h

/-- **Sharpness: the `p`-adic form is false at `ε = 0`.** With the target `0` in `F = ℚ` the
powers of `p` satisfy `|p ^ k| p = |p ^ k| ^ (-1)` with equality, so the bounded set is infinite
and the hypothesis `0 < ε` is load-bearing. -/
example (p : Nat.Primes) :
    {n : ℤ | AbsoluteValue.padic (p : ℕ) ((n : ℚ) - (0 : ℚ))
      ≤ |(n : ℝ)| ^ (-1 - (0 : ℝ))}.Infinite := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
    linarith
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ (((p : ℕ) ^ k : ℕ) : ℤ)) (fun a b hab ↦ ?_) (fun k ↦ ?_)
  · simp only at hab
    have h : ((p : ℕ)) ^ a = ((p : ℕ)) ^ b := by exact_mod_cast hab
    exact Nat.pow_right_injective hp2 h
  · rw [Set.mem_ofPred_eq, sub_zero]
    have hcast : (((((p : ℕ) ^ k : ℕ) : ℤ)) : ℚ) = (((p : ℕ) : ℚ)) ^ k := by push_cast; ring
    have hcastR : |(((((p : ℕ) ^ k : ℕ) : ℤ)) : ℝ)| = (((p : ℕ) : ℝ)) ^ k := by
      rw [abs_of_nonneg (by positivity)]
      push_cast
      ring
    rw [hcast, map_pow, hcastR, AbsoluteValue.padic_eq_padicNorm,
      padicNorm.padicNorm_p_of_prime]
    rw [show (-1 - (0 : ℝ)) = -1 by ring, Real.rpow_neg_one, ← inv_pow]
    push_cast
    exact le_rfl

end Rat

end
