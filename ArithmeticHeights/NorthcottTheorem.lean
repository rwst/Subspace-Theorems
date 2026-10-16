/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.MahlerMeasure

import ArithmeticHeights.Northcott
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Northcott's theorem

**There are only finitely many algebraic numbers of bounded absolute height and bounded degree.**
This is the theorem the literature calls Northcott's; Mathlib's
`NumberField.finite_setOfPred_mulHeight₁_le` fixes the field the numbers live in, and so bounds
the degree by a constant that is invisible in the statement.

The proof is the Mahler-measure bridge of Layer 1.2 read as a bound. An algebraic number `x` of
degree at most `D` and absolute height at most `B` has a primitive integer minimal polynomial `f`
of degree at most `D` and Mahler measure `M(f) = H(x) ^ deg f ≤ B ^ D`, of which there are
finitely many by Mathlib's `Polynomial.finite_mahlerMeasure_le`; and `x` is one of the at most `D`
roots of `f`.

## Main results

* `NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le`: the theorem, over any field of
  characteristic zero, with `NumberField.finite_setOfPred_absLogHeight₁_le_of_finrank_le` its
  logarithmic form.
* `Projectivization.finite_setOfPred_absMulHeight_le_of_finrank_le`: the projective form, for a
  field all of whose elements are algebraic — a point of `ℙⁿ` whose height and whose coordinate
  ratios' degrees are bounded is one of finitely many. Its logarithmic form is
  `Projectivization.finite_setOfPred_absLogHeight_le_of_finrank_le`.
* `NumberField.ncard_setOfPred_absMulHeight₁_le_of_finrank_le` and
  `Projectivization.ncard_setOfPred_absMulHeight_le_of_finrank_le`: **the counted forms**, at
  most `northcottCount D (max B 1 ^ D)` numbers and its `#ι`-th power of points. The count
  depends on `D` and `B` only, because Mathlib's `Polynomial.card_mahlerMeasure_le_prod` counts
  the integer polynomials of bounded degree and Mahler measure.
* `Projectivization.ncard_setOfPred_mulHeight_le`: over a number field `K`, at most
  `northcottCount [K : ℚ] (max X 1) ^ #ι` points of relative height at most `X`, uniformly in `K`
  of a given degree.

## Implementation notes

The statement is about the **absolute** height and is not a `Northcott` instance: the `Northcott`
typeclass of `Mathlib/Order/Northcott.lean` asks for `{a | h a ≤ B}` to be finite for a function
`h` on a fixed type, and here the set is cut out by two conditions, only one of which is a height.
Layer 1.1 supplies the instances that do fit that shape.

⚠ Neither bound may be dropped, and neither may the integrality hypothesis.

* Without the degree bound the set is infinite: every root of unity has absolute height `1`, and
  there is one of every order. This is refuted among the examples below, where it also serves as
  the easy half of Kronecker's theorem of Layer 1.4.
* Without the height bound the set is infinite: over `ℂ` the rational numbers alone have degree
  `1`. Also refuted below.
* Without `IsIntegral ℚ x` the set is infinite over any field with a transcendental element —
  such an element has the junk height `1` and, `ℚ⟮x⟯` being infinite-dimensional, the junk degree
  `0`, so it satisfies **both** bounds. This too is refuted below, in the form that does not
  require exhibiting a transcendental number: every non-integral element lies in the set.

The degree of a point of projective space is measured by its coordinate **ratios**, which do not
depend on the representative. That is weaker than bounding the degree of the field they generate,
so the projective statement below is stronger than the one Hindry–Silverman state; the proof is
theirs either way, and identical to the proof of Layer 1.1: normalize a coordinate to `1`, and
read off that every coordinate of the normalized representative is a ratio, hence of bounded
degree, and of height at most that of the point.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 1.6.8. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer
GTM 201 (2000), Theorem B.2.3, whose first statement — for `ℙⁿ` over the field of all algebraic
numbers, with bounds on the height and on the degree — is the projective form proved here.

This is Layer 1.3 of the `ArithmeticHeights` roadmap.
-/

public section

open IntermediateField Module NumberField Polynomial

namespace NumberField

variable {K : Type*} [Field K] [CharZero K]

/-- **Northcott's theorem.** For a bound `B` on the absolute multiplicative height and a bound `D`
on the degree, there are only finitely many algebraic numbers meeting both.

Neither bound can be dropped, and neither can the integrality hypothesis; see the examples at the
end of the file. -/
theorem finite_setOfPred_absMulHeight₁_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {x : K | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.Finite := by
  have hB1 : (1 : ℝ) ≤ max B 1 := le_max_right _ _
  have hN : (((max B 1) ^ D).toNNReal : ℝ) = (max B 1) ^ D :=
    Real.coe_toNNReal _ (by positivity)
  have hFin : {p : ℤ[X] | p.natDegree ≤ D ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ ((max B 1) ^ D).toNNReal ∧ p ≠ 0}.Finite :=
    (Polynomial.finite_mahlerMeasure_le D _).subset fun p hp ↦ ⟨hp.1, hp.2.1⟩
  refine Set.Finite.subset (hFin.biUnion
    (t := fun p ↦ {y : K | (p.map (Int.castRingHom K)).IsRoot y}) fun p hp ↦
      finite_setOfPred_isRoot ((Polynomial.map_eq_zero_iff
        (Int.castRingHom K).injective_int).not.mpr hp.2.2)) ?_
  rintro x ⟨hx, hxB, hxD⟩
  obtain ⟨f, hf, hdeg, hroot, hM⟩ := exists_isPrimitive_absMulHeight₁_pow_natDegree hx
  have hmem : f ∈ {p : ℤ[X] | p.natDegree ≤ D ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ ((max B 1) ^ D).toNNReal ∧ p ≠ 0} := by
    refine ⟨hdeg ▸ hxD, ?_, hf.ne_zero⟩
    rw [hN, ← hM]
    calc absMulHeight₁ x ^ f.natDegree ≤ (max B 1) ^ f.natDegree :=
          pow_le_pow_left₀ (zero_le_one.trans (one_le_absMulHeight₁ x))
            (hxB.trans (le_max_left _ _)) _
      _ ≤ (max B 1) ^ D := pow_le_pow_right₀ hB1 (hdeg ▸ hxD)
  exact Set.mem_biUnion hmem
    (by rwa [Set.mem_ofPred_eq, IsRoot, ← eval₂_eq_eval_map, ← algebraMap_int_eq, ← aeval_def])

/-- The logarithmic form of `NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le`. -/
theorem finite_setOfPred_absLogHeight₁_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {x : K | IsIntegral ℚ x ∧ absLogHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.Finite :=
  (finite_setOfPred_absMulHeight₁_le_of_finrank_le (Real.exp B) D).subset fun _ hx ↦
    ⟨hx.1, Real.le_exp_of_log_le hx.2.1, hx.2.2⟩

/-- **The count in Northcott's theorem**: `D` roots for each integer polynomial of degree at most
`D` and Mahler measure at most `M`, of which there are at most
`∏_{i ≤ D} (2 ⌊binom D i · M⌋ + 1)` (Mathlib's `Polynomial.card_mahlerMeasure_le_prod`). It
depends on `D` and `M` only, not on the field. -/
noncomputable def northcottCount (D : ℕ) (M : NNReal) : ℕ :=
  D * ∏ i : Fin (D + 1), (2 * ⌊D.choose i * M⌋₊ + 1)

/-- **Northcott's theorem, counted.** There are at most `northcottCount D (max B 1 ^ D)`
algebraic numbers of absolute height at most `B` and degree at most `D`, in any field of
characteristic zero. The proof is that of `finite_setOfPred_absMulHeight₁_le_of_finrank_le`, with
the roots counted. -/
theorem ncard_setOfPred_absMulHeight₁_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {x : K | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.ncard ≤
      northcottCount D ((max B 1) ^ D).toNNReal := by
  classical
  set M : NNReal := ((max B 1) ^ D).toNNReal
  have hM : (M : ℝ) = (max B 1) ^ D := Real.coe_toNNReal _ (by positivity)
  set P := {p : ℤ[X] | p.natDegree ≤ D ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ M}
  have hP : P.Finite := finite_mahlerMeasure_le D M
  have hsub : {x : K | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D} ⊆
      ↑(hP.toFinset.biUnion fun p ↦ (p.map (Int.castRingHom K)).roots.toFinset) := by
    rintro x ⟨hx, hxB, hxD⟩
    obtain ⟨f, hf, hdeg, hroot, hMf⟩ := exists_isPrimitive_absMulHeight₁_pow_natDegree hx
    simp only [Finset.coe_biUnion, Set.Finite.coe_toFinset, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset, exists_prop]
    refine ⟨f, ⟨hdeg ▸ hxD, ?_⟩, ?_⟩
    · rw [hM, ← hMf]
      calc absMulHeight₁ x ^ f.natDegree ≤ (max B 1) ^ f.natDegree :=
            pow_le_pow_left₀ (zero_le_one.trans (one_le_absMulHeight₁ x))
              (hxB.trans (le_max_left _ _)) _
        _ ≤ (max B 1) ^ D := pow_le_pow_right₀ (le_max_right _ _) (hdeg ▸ hxD)
    · rw [mem_roots ((Polynomial.map_eq_zero_iff (Int.castRingHom K).injective_int).not.mpr
        hf.ne_zero), IsRoot, ← eval₂_eq_eval_map, ← algebraMap_int_eq, ← aeval_def]
      exact hroot
  calc _ ≤ (hP.toFinset.biUnion fun p ↦ (p.map (Int.castRingHom K)).roots.toFinset).card := by
        rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub
    _ ≤ hP.toFinset.card * D := by
        refine Finset.card_biUnion_le_card_mul _ _ _ fun p hp ↦ ?_
        rw [Set.Finite.mem_toFinset] at hp
        exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
          ((natDegree_map_le).trans hp.1))
    _ ≤ northcottCount D M := by
        rw [northcottCount, mul_comm D, ← Set.ncard_eq_toFinset_card P hP]
        exact Nat.mul_le_mul_right _ (card_mahlerMeasure_le_prod D M)

end NumberField

namespace Projectivization

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Finite ι]

/-- **Northcott's theorem on projective space** (Hindry–Silverman, Theorem B.2.3). A point of
`ℙ(ι → K)` whose absolute height is at most `B` and all of whose coordinate ratios have degree at
most `D` is one of finitely many.

The ratios `rep i / rep j` do not depend on the representative, and bounding their degrees is
weaker than bounding the degree of the field they generate, which is how the statement is usually
made. -/
theorem finite_setOfPred_absMulHeight_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {P : Projectivization K (ι → K) | absMulHeight P ≤ B ∧
      ∀ i j, finrank ℚ ℚ⟮P.rep i / P.rep j⟯ ≤ D}.Finite := by
  have hpi : {v : ι → K | ∀ i, NumberField.absMulHeight₁ (v i) ≤ B ∧
      finrank ℚ ℚ⟮v i⟯ ≤ D}.Finite := by
    refine (Set.Finite.pi fun _ : ι ↦
      NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le B D).subset fun v hv i _ ↦ ?_
    exact ⟨(Algebra.IsAlgebraic.isAlgebraic (v i)).isIntegral, (hv i).1, (hv i).2⟩
  have hsub : (Subtype.val ⁻¹' {v : ι → K | ∀ i, NumberField.absMulHeight₁ (v i) ≤ B ∧
      finrank ℚ ℚ⟮v i⟯ ≤ D} : Set {w : ι → K // w ≠ 0}).Finite :=
    hpi.preimage Subtype.val_injective.injOn
  refine (hsub.image (mk' K)).subset ?_
  rintro P ⟨hPB, hPD⟩
  obtain ⟨v, hv, i₀, hi₀, hratio, rfl⟩ := exists_rep_apply_eq_one P
  have hvint : ∀ i, IsIntegral ℚ (v i) := fun i ↦
    (Algebra.IsAlgebraic.isAlgebraic (v i)).isIntegral
  refine ⟨⟨v, hv⟩, fun i ↦ ⟨?_, ?_⟩, rfl⟩
  · exact (NumberField.absMulHeight₁_le_absMulHeight hvint hi₀ i).trans
      (by rwa [absMulHeight_mk] at hPB)
  · change finrank ℚ ℚ⟮v i⟯ ≤ D
    rw [hratio i]
    exact hPD i i₀

/-- The logarithmic form of
`Projectivization.finite_setOfPred_absMulHeight_le_of_finrank_le`. -/
theorem finite_setOfPred_absLogHeight_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {P : Projectivization K (ι → K) | absLogHeight P ≤ B ∧
      ∀ i j, finrank ℚ ℚ⟮P.rep i / P.rep j⟯ ≤ D}.Finite := by
  refine (finite_setOfPred_absMulHeight_le_of_finrank_le (Real.exp B) D).subset fun P hP ↦
    ⟨Real.le_exp_of_log_le ?_, hP.2⟩
  rw [← absLogHeight_eq_log_absMulHeight]
  exact hP.1


/-- **Northcott's theorem on projective space, counted.** There are at most
`northcottCount D (max B 1 ^ D) ^ #ι` points of `ℙ(ι → K)` of absolute height at most `B` whose
coordinate ratios have degree at most `D`: the normalized representative of
`finite_setOfPred_absMulHeight_le_of_finrank_le` has every coordinate in the set counted by
`NumberField.ncard_setOfPred_absMulHeight₁_le_of_finrank_le`. -/
theorem ncard_setOfPred_absMulHeight_le_of_finrank_le (B : ℝ) (D : ℕ) :
    {P : Projectivization K (ι → K) | absMulHeight P ≤ B ∧
      ∀ i j, finrank ℚ ℚ⟮P.rep i / P.rep j⟯ ≤ D}.ncard ≤
        northcottCount D ((max B 1) ^ D).toNNReal ^ Nat.card ι := by
  set A := {x : K | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}
  have hA : A.Finite := finite_setOfPred_absMulHeight₁_le_of_finrank_le B D
  set V : Set {w : ι → K // w ≠ 0} := Subtype.val ⁻¹' Set.univ.pi fun _ : ι ↦ A
  have hV : V.Finite := (Set.Finite.pi fun _ ↦ hA).preimage Subtype.val_injective.injOn
  have hsub : {P : Projectivization K (ι → K) | absMulHeight P ≤ B ∧
      ∀ i j, finrank ℚ ℚ⟮P.rep i / P.rep j⟯ ≤ D} ⊆ mk' K '' V := by
    rintro P ⟨hPB, hPD⟩
    obtain ⟨v, hv, i₀, hi₀, hratio, rfl⟩ := exists_rep_apply_eq_one P
    have hvint : ∀ i, IsIntegral ℚ (v i) := fun i ↦
      (Algebra.IsAlgebraic.isAlgebraic (v i)).isIntegral
    refine ⟨⟨v, hv⟩, fun i _ ↦ ⟨hvint i, ?_, ?_⟩, rfl⟩
    · exact (NumberField.absMulHeight₁_le_absMulHeight hvint hi₀ i).trans
        (by rwa [absMulHeight_mk] at hPB)
    · change finrank ℚ ℚ⟮v i⟯ ≤ D
      rw [hratio i]
      exact hPD i i₀
  have hAc : Nat.card A ≤ northcottCount D ((max B 1) ^ D).toNNReal := by
    rw [Nat.card_coe_set_eq]
    exact NumberField.ncard_setOfPred_absMulHeight₁_le_of_finrank_le B D
  have : Finite A := hA
  calc _ ≤ (mk' K '' V).ncard := Set.ncard_le_ncard hsub (hV.image _)
    _ ≤ V.ncard := Set.ncard_image_le hV
    _ ≤ Nat.card (ι → A) := by
        rw [← Nat.card_coe_set_eq]
        exact Nat.card_le_card_of_injective (fun w i ↦ ⟨w.1.1 i, w.2 i trivial⟩)
          fun w w' h ↦ Subtype.ext (Subtype.ext (funext fun i ↦ congrArg Subtype.val
            (congrFun h i)))
    _ ≤ _ := by
        rw [Nat.card_fun]
        exact Nat.pow_le_pow_left hAc _
end Projectivization

namespace Projectivization

section NumberFieldBase

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- Over a number field `K` of degree `d`, a point of relative height at most `X` has absolute
height at most `max X 1 ^ (1 / d)`, and every coordinate ratio has degree at most `d`. -/
private theorem setOfPred_mulHeight_le_subset (X : ℝ) :
    {P : Projectivization K (ι → K) | mulHeight P ≤ X} ⊆
      {P | absMulHeight P ≤ max X 1 ^ ((finrank ℚ K : ℝ))⁻¹ ∧
        ∀ i j, finrank ℚ ℚ⟮P.rep i / P.rep j⟯ ≤ finrank ℚ K} := by
  intro P hP
  refine ⟨?_, fun i j ↦ (ℚ⟮P.rep i / P.rep j⟯).toSubalgebra.toSubmodule.finrank_le⟩
  rw [absMulHeight_eq]
  exact Real.rpow_le_rpow (Projectivization.mulHeight_pos P).le
    (Set.mem_ofPred.1 hP |>.trans (le_max_left _ _)) (by positivity)

/-- **Northcott's theorem over a number field, counted uniformly in the field.** The points of
`ℙ(ι → K)` of relative height at most `X` number at most
`northcottCount [K : ℚ] (max X 1) ^ #ι`, a bound that sees `K` only through its degree (Sch90,
Lemma 5.1, with another constant). -/
theorem ncard_setOfPred_mulHeight_le (X : ℝ) :
    {P : Projectivization K (ι → K) | mulHeight P ≤ X}.ncard ≤
      northcottCount (finrank ℚ K) (max X 1).toNNReal ^ Nat.card ι := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hB : 1 ≤ max X 1 ^ ((finrank ℚ K : ℝ))⁻¹ :=
    Real.one_le_rpow (le_max_right _ _) (by positivity)
  have hBd : max (max X 1 ^ ((finrank ℚ K : ℝ))⁻¹) 1 ^ finrank ℚ K = max X 1 := by
    rw [max_eq_left hB, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ hd, Real.rpow_one]
  refine (Set.ncard_le_ncard (setOfPred_mulHeight_le_subset X)
    (finite_setOfPred_absMulHeight_le_of_finrank_le (K := K) (ι := ι) _ _)).trans ?_
  have h := ncard_setOfPred_absMulHeight_le_of_finrank_le (K := K) (ι := ι)
    (max X 1 ^ ((finrank ℚ K : ℝ))⁻¹) (finrank ℚ K)
  rwa [hBd] at h

end NumberFieldBase

end Projectivization

/-!
### Worked examples

The acceptance criteria the roadmap attaches to this layer: that both bounds are needed, and that
the integrality hypothesis is needed. Each is refuted by an explicit infinite family.
-/

section Examples

open Complex

/-- **Rejection test: the degree bound cannot be dropped.** The roots of unity all have absolute
height `1`, and there is one of every order, so `{x : ℂ | H(x) ≤ 1}` is infinite.

This is the easy half of Kronecker's theorem, Layer 1.4: it falls straight out of Layer 1.2 and
Mathlib's `Polynomial.cyclotomic_mahlerMeasure_eq_one`. -/
example : {x : ℂ | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ 1}.Infinite := by
  have hprim (n : ℕ) :
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (n + 1))) (n + 1) := by
    exact_mod_cast Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ Complex.exp (2 * Real.pi * Complex.I / (n + 1))) ?_ ?_
  · intro m n hmn
    have h : Complex.exp (2 * Real.pi * Complex.I / (m + 1))
        = Complex.exp (2 * Real.pi * Complex.I / (n + 1)) := hmn
    exact Nat.succ_injective ((h ▸ hprim m).unique (hprim n))
  · intro n
    have hpos : 0 < n + 1 := n.succ_pos
    refine ⟨((hprim n).isIntegral hpos).tower_top, ?_⟩
    have hfp : (cyclotomic (n + 1) ℤ).IsPrimitive := (cyclotomic.monic _ _).isPrimitive
    have hmap : (cyclotomic (n + 1) ℤ).map (Int.castRingHom ℚ)
        = C 1 * minpoly ℚ (Complex.exp (2 * Real.pi * Complex.I / (n + 1))) := by
      rw [map_cyclotomic, C_1, one_mul, cyclotomic_eq_minpoly_rat (hprim n) hpos]
    have hM := absMulHeight₁_pow_natDegree hfp one_ne_zero hmap
    rw [← algebraMap_int_eq, cyclotomic_mahlerMeasure_eq_one (R := ℤ)] at hM
    have hd : (cyclotomic (n + 1) ℤ).natDegree ≠ 0 := by
      rw [natDegree_cyclotomic]
      exact (Nat.totient_pos.mpr hpos).ne'
    exact not_lt.mp fun hlt ↦ absurd hM (one_lt_pow₀ hlt hd).ne'

/-- **Rejection test: the height bound cannot be dropped.** The rational numbers all have degree
`1`. -/
example : {x : ℂ | IsIntegral ℚ x ∧ finrank ℚ ℚ⟮x⟯ ≤ 1}.Infinite := by
  have hcast (n : ℕ) : ((n : ℂ)) = algebraMap ℚ ℂ (n : ℚ) := by push_cast; ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (n : ℂ))
    (fun _ _ h ↦ Nat.cast_injective h) fun n ↦ ⟨?_, ?_⟩
  · rw [hcast n]
    exact isIntegral_algebraMap
  · have hmem : (n : ℂ) ∈ (⊥ : IntermediateField ℚ ℂ) :=
      IntermediateField.mem_bot.mpr ⟨(n : ℚ), (hcast n).symm⟩
    rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem, IntermediateField.finrank_bot]

/-- **Rejection test: the integrality hypothesis cannot be dropped.** A transcendental element
satisfies *both* bounds, at every `B ≥ 1` and every `D`, because both quantities take junk values
on it: the height is `1` by definition, and `ℚ⟮x⟯` is infinite-dimensional, so its `finrank` is
`0`. Over `ℂ` — or any field with a transcendental element — the set without the hypothesis is
therefore infinite. -/
example {K : Type*} [Field K] [CharZero K] {x : K} (hx : ¬ IsIntegral ℚ x) {B : ℝ} (hB : 1 ≤ B)
    (D : ℕ) : absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D := by
  refine ⟨?_, ?_⟩
  · rw [← absMulHeight_eq_absMulHeight₁,
      absMulHeight_eq_one_of_not_isIntegral fun h ↦ hx (by simpa using h 0)]
    exact hB
  · rw [Module.finrank_of_infinite_dimensional fun _ ↦ hx
      ((Algebra.IsIntegral.isIntegral (AdjoinSimple.gen ℚ x)).map ℚ⟮x⟯.val)]
    exact Nat.zero_le D

/-- **Conformance.** The roadmap pins the statement over `ℂ`; it is the special case of the
above. -/
example (B : ℝ) (D : ℕ) :
    {x : ℂ | IsIntegral ℚ x ∧ absMulHeight₁ x ≤ B ∧ finrank ℚ ℚ⟮x⟯ ≤ D}.Finite :=
  NumberField.finite_setOfPred_absMulHeight₁_le_of_finrank_le B D

end Examples

end
