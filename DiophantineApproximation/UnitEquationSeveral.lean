/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.UnitEquation
public import DiophantineApproximation.LinearFormSubspaces
public import Mathlib.GroupTheory.Finiteness

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import DiophantineApproximation.AffineProd
import DiophantineApproximation.RationalPlaces
import DiophantineApproximation.RepetitionSubspaces
import DiophantineApproximation.SAdicHeight
import Mathlib.Tactic.LinearCombination

/-!
# The unit equation in several variables

**Layer 8.2** (Evertse; van der Poorten–Schlickewei; Bombieri–Gubler, Theorem 7.4.2 and
Corollary 7.4.3). For a number field `K`, a finite set `S` of finite places and `a : ι → Kˣ`, the
equation `∑ i, a i * x i = 1` has finitely many solutions in `S`-units with **no vanishing
subsum**. Without that condition, every solution has a term `a i * x i` in a fixed finite set.
The same holds with `x i` in a finitely generated subgroup of `Kˣ`.

Route, by induction on the number `n` of variables. Absorb the coefficients by enlarging `S`, so
that the equation is `∑ i, x i = 1`. At every place of `S∞ ∪ S` take the `n + 1` forms `X i` and
`∑ i, X i`, which are in general position. At a solution the central quantity of Vojta's
refinement (Layer 6.5) is **exactly** `H(x) ^ (-n - 1)`, as in Layer 8.1, so the solutions lie in
finitely many proper subspaces. On a proper subspace a relation `∑ i, c i * x i = 0` with
`c j ≠ 0` turns the equation into `∑ i, b i * x i = 1` with `b j = 0`; a minimal subsum equal to
`1` has no vanishing subsum and fewer variables, so by induction some coordinate `x k` lies in a
finite set. Fixing `x k = u`, the other coordinates solve `∑ i ≠ k, x i = 1 - u`, where `u ≠ 1`
because no subsum vanishes, again with fewer variables.

## Main results

* `NumberField.finite_setOf_sum_unit_eq_one`: **the milestone**.
* `NumberField.finite_setOf_sum_mem_eq_one`: the same for a finitely generated subgroup.
* `NumberField.exists_finite_forall_exists_mul_mem`: Corollary 7.4.3, vanishing subsums allowed.
* `NumberField.generalProd_sumEquationForms_eq`: the central quantity at a solution.

## Implementation notes

⚠ **The induction has two steps, not one.** The subspace step shortens the equation only after
passing to a minimal subsum, and that controls only the coordinates of the subsum. One coordinate
is enough: fixing it leaves an equation in `n - 1` variables whose right-hand side `1 - u` is
nonzero precisely because the complementary subsum does not vanish.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§7.4; J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number Theory*, Cambridge
University Press (2015), Chapter 6.

This is Layer 8.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height IsDedekindDomain Module Module.Dual

namespace NumberField

universe u

variable {K : Type*} [Field K] {ι : Type u} [Fintype ι]

/-- **The forms of the unit equation in `n` variables**: the sum form `∑ i, X i` at `none` and the
coordinate form `X i` at `some i`. -/
noncomputable def sumEquationForms : Option ι → Dual K (ι → K) :=
  fun o ↦ o.elim (sumForm fun _ ↦ 1) LinearMap.proj

/-- The form at `none` is `∑ i, X i`. -/
@[simp] theorem sumEquationForms_none (y : ι → K) : sumEquationForms none y = ∑ i, y i := by
  simp [sumEquationForms]

/-- The form at `some i` is `X i`. -/
@[simp] theorem sumEquationForms_some (i : ι) (y : ι → K) :
    sumEquationForms (some i) y = y i :=
  rfl

/-- **The `n + 1` forms are in general position**: any `n` of them are linearly independent. -/
theorem isGeneralPosition_sumEquationForms :
    IsGeneralPosition K (univ : Finset (Option ι)) (sumEquationForms (K := K)) := by
  classical
  intro s _ hs
  rw [Nat.card_eq_fintype_card] at hs
  by_cases hn : none ∈ s
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀, some i₀ ∉ s := by
      by_contra! h
      have hsub : (univ : Finset (Option ι)) ⊆ s := fun o _ ↦ by
        cases o with
        | none => exact hn
        | some i => exact h i
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_option] at this
      omega
    let g : s → ι := fun k ↦ (k : Option ι).getD i₀
    have hg : Function.Injective g := by
      rintro ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ h
      · rfl
      · change i₀ = j at h
        subst h
        exact absurd hj hi₀
      · change i = i₀ at h
        subst h
        exact absurd hi hi₀
      · change i = j at h
        subst h
        rfl
    have hM : (fun k : s ↦ sumEquationForms (K := K) k) =
        projWithSum (fun _ ↦ (1 : K)) i₀ ∘ g := by
      funext ⟨o, ho⟩
      cases o with
      | none => exact (projWithSum_self _ _).symm
      | some i =>
        have hi : i ≠ i₀ := fun h ↦ hi₀ (h ▸ ho)
        exact (projWithSum_of_ne hi).symm
    rw [hM]
    exact (linearIndependent_projWithSum (a := fun _ ↦ (1 : K)) (j := i₀) one_ne_zero).comp g hg
  · have hsome : ∀ k : s, (k : Option ι).isSome := fun k ↦
      Option.isSome_iff_ne_none.mpr fun h ↦ hn (h ▸ k.2)
    let g : s → ι := fun k ↦ (k : Option ι).get (hsome k)
    have hg : Function.Injective g := by
      rintro ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ h
      · exact absurd hi hn
      · exact absurd hi hn
      · exact absurd hj hn
      · change i = j at h
        subst h
        rfl
    have hM : (fun k : s ↦ sumEquationForms (K := K) k) =
        (fun i ↦ (LinearMap.proj i : Dual K (ι → K))) ∘ g := by
      funext ⟨o, ho⟩
      cases o with
      | none => exact absurd ho hn
      | some i => rfl
    rw [hM]
    exact Rat.linearIndependent_proj.comp g hg

omit [Fintype ι] in
/-- **A minimal subsum.** If `∑ i ∈ J, b i * z i = 1`, some `J' ⊆ J` has the same sum and no
nonempty subset of `J'` has a vanishing sum. -/
theorem exists_subset_sum_eq_one_forall_ne_zero {b z : ι → K} {J : Finset ι}
    (h : ∑ i ∈ J, b i * z i = 1) :
    ∃ J' ⊆ J, ∑ i ∈ J', b i * z i = 1 ∧
      ∀ I ⊆ J', I.Nonempty → ∑ i ∈ I, b i * z i ≠ 0 := by
  classical
  obtain ⟨J', hJ', hmin⟩ := Finset.exists_min_image
    (J.powerset.filter fun J' ↦ ∑ i ∈ J', b i * z i = 1) Finset.card
    ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self J, h⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ'
  refine ⟨J', hJ'.1, hJ'.2, fun I hI hIne hI0 ↦ ?_⟩
  have hsd : ∑ i ∈ J' \ I, b i * z i = 1 := by
    have := Finset.sum_sdiff hI (f := fun i ↦ b i * z i)
    rw [hI0, add_zero, hJ'.2] at this
    exact this
  have hle := hmin (J' \ I) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset.trans hJ'.1), hsd⟩)
  exact absurd (Finset.card_lt_card (Finset.sdiff_ssubset hI hIne)) (not_lt.mpr hle)

/-- **A proper subspace shortens the equation.** If `W ≠ ⊤`, there are coefficients `b` with some
`b j = 0` such that every point of `W` on `∑ i, y i = 1` also lies on `∑ i, b i * y i = 1`. -/
theorem exists_sum_mul_eq_one_of_ne_top {W : Submodule K (ι → K)} (hW : W ≠ ⊤) :
    ∃ b : ι → K, ∃ j, b j = 0 ∧ ∀ y ∈ W, ∑ i, y i = 1 → ∑ i, b i * y i = 1 := by
  classical
  obtain ⟨f, hf0, hWf⟩ := W.exists_le_ker_of_lt_top hW.lt_top
  set c : ι → K := fun i ↦ f fun j ↦ if i = j then 1 else 0 with hc
  have hfc : ∀ y, f y = ∑ i, c i * y i := fun y ↦ by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext fun y ↦ by simp [hfc, h])
  refine ⟨fun i ↦ 1 - c i / c j, j, by simp [div_self hj], fun y hy hsum ↦ ?_⟩
  have hfy : f y = 0 := LinearMap.mem_ker.mp (hWf hy)
  calc ∑ i, (1 - c i / c j) * y i = ∑ i, y i - (∑ i, c i * y i) / c j := by
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = 1 := by rw [← hfc, hfy, hsum, zero_div, sub_zero]

variable [NumberField K]

/-- **The solutions of the unit equation in `S`-units with no vanishing subsum**: the `S`-unit
vectors `x` with `∑ i, a i * x i = 1` and `∑ i ∈ I, a i * x i ≠ 0` for every nonempty `I`. -/
def unitSolutions (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → K) : Set (ι → Kˣ) :=
  {x | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧ ∑ i, a i * x i = 1 ∧
    ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, a i * x i ≠ 0}

/-- Membership in `unitSolutions`, unfolded. -/
theorem mem_unitSolutions {S : Finset (HeightOneSpectrum (𝓞 K))} {a : ι → K} {x : ι → Kˣ} :
    x ∈ unitSolutions S a ↔ (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
      ∑ i, a i * x i = 1 ∧ ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, a i * x i ≠ 0 :=
  Iff.rfl

open scoped Classical in
/-- **The central quantity at a solution of the unit equation.** With the `n + 1` forms at every
infinite place and every place of `S`, the local numerators multiply to `1` by the `S`-product
formula and the denominators to `H(x) ^ (n + 1)`, so Vojta's quantity is `H(x) ^ (-n - 1)`. -/
theorem generalProd_sumEquationForms_eq (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ι → Kˣ}
    (hx : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hsum : ∑ i, (x i : K) = 1) :
    generalProd univ (S.image FinitePlace.mk) (fun v ↦ v) (fun _ ↦ univ)
        (fun _ ↦ sumEquationForms) (fun i ↦ (x i : K)) =
      (mulHeight (fun i ↦ (x i : K)) ^ (Fintype.card ι + 1))⁻¹ := by
  have hsum' := hsum
  set z : ι → K := fun i ↦ (x i : K) with hz
  set n := Fintype.card ι with hn
  have hloc : ∀ (v : AbsoluteValue K ℝ) (d : ℝ),
      (∏ k ∈ (univ : Finset (Option ι)),
          v (sumEquationForms k fun j ↦ algebraMap K K (z j)) / d)
        = (∏ i, v (x i : K)) * (d ^ (n + 1))⁻¹ := by
    intro v d
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Fintype.prod_option,
      sumEquationForms_none, sumEquationForms_some, hz, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_option]
    rw [hsum', map_one]
    ring
  have himg : ∀ f : FinitePlace K → ℝ,
      ∏ v ∈ S.image FinitePlace.mk, f v = ∏ v ∈ S, f (FinitePlace.mk v) :=
    fun f ↦ Finset.prod_image fun a _ b _ h ↦ FinitePlace.mk_injective h
  have hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive z :=
    (Set.isPrimitive_iff _ z).mpr ⟨fun i ↦ Set.mem_integer_of_mem_unit (hx i), fun _ ↦ 1,
      fun _ ↦ one_mem _, by simpa [hz] using hsum⟩
  have hH := mulHeight_eq_prod_of_isPrimitive S hprim
  have hnum : (∏ v : InfinitePlace K, (∏ i, v.1 (x i : K)) ^ v.mult) *
      ∏ v ∈ S, ∏ i, (FinitePlace.mk v).1 (x i : K) = 1 := by
    simp_rw [← Finset.prod_pow]
    rw [Finset.prod_comm, Finset.prod_comm (s := S), ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ ↦ prod_apply_eq_one_of_mem_unit S (hx i)
  rw [generalProd, himg]
  simp only [hloc]
  have e1 : ∏ v : InfinitePlace K, ((⨆ j, v (z j)) ^ (n + 1))⁻¹ ^ v.mult =
      ((∏ v : InfinitePlace K, (⨆ j, v (z j)) ^ v.mult) ^ (n + 1))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun _ _ ↦ by rw [inv_pow, pow_right_comm]
  have e2 : ∏ v ∈ S, ((⨆ j, FinitePlace.mk v (z j)) ^ (n + 1))⁻¹ =
      ((∏ v ∈ S, ⨆ j, FinitePlace.mk v (z j)) ^ (n + 1))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [e1, e2, hH]
  set P := ∏ v : InfinitePlace K, (⨆ j, v (z j)) ^ v.mult
  set Q := ∏ v ∈ S, ⨆ j, FinitePlace.mk v (z j)
  linear_combination ((P * Q) ^ (n + 1))⁻¹ * hnum

open scoped Classical in
/-- **The subspace step**: the `S`-unit points on `∑ i, x i = 1` lie in finitely many proper
subspaces, by Layer 6.5 with the `n + 1` forms and `ε = 1`. -/
theorem exists_finset_submodule_of_sum_eq_one [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → Kˣ, (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
        ∑ i, (x i : K) = 1 → ∃ W ∈ T, (fun i ↦ (x i : K)) ∈ W := by
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_generalProd_le (F := K) (ι := ι)
    (κ := Option ι) univ (S.image FinitePlace.mk) (fun v ↦ v)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ ↦ univ) (fun _ ↦ sumEquationForms)
    (fun _ _ ↦ isGeneralPosition_sumEquationForms)
    (fun _ _ ↦ isGeneralPosition_sumEquationForms) one_pos
  refine ⟨T, hT, fun x hx hsum ↦ hmem _ ?_ ?_⟩
  · obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact fun h ↦ Units.ne_zero (x i) (congrFun h i)
  · have hH0 : (0 : ℝ) < mulHeight (fun i ↦ (x i : K)) :=
      lt_of_lt_of_le zero_lt_one (one_le_mulHeight _)
    rw [generalProd_sumEquationForms_eq S hx hsum,
      show -(Fintype.card ι : ℝ) - 1 = -((Fintype.card ι + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hH0.le, Real.rpow_natCast]

omit [Fintype ι] in
/-- **Finitely many values on a finite family of shortened equations.** If the equation
`∑ i ∈ J', b i * y i = 1` has finitely many solutions with no vanishing subsum for every `J' ⊆ J`,
then every `S`-unit solution of `∑ i ∈ J, b i * y i = 1` has a coordinate in `J` from a finite
set of pairs. -/
theorem exists_finite_forall_exists_apply_eq (S : Finset (HeightOneSpectrum (𝓞 K))) (b : ι → K)
    (J : Finset ι) (h : ∀ J' ⊆ J, (unitSolutions S fun i : J' ↦ b i).Finite) :
    ∃ G : Set (ι × Kˣ), G.Finite ∧ ∀ y : ι → Kˣ,
      (∀ i, y i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
      ∑ i ∈ J, b i * y i = 1 → ∃ p ∈ G, p.1 ∈ J ∧ y p.1 = p.2 := by
  classical
  refine ⟨⋃ J' ∈ J.powerset, (fun q : (J' → Kˣ) × J' ↦ ((q.2 : ι), q.1 q.2)) ''
    (unitSolutions S (fun i : J' ↦ b i) ×ˢ Set.univ), ?_, fun y hy hsum ↦ ?_⟩
  · exact J.powerset.finite_toSet.biUnion fun J' hJ' ↦
      ((h J' (Finset.mem_powerset.mp hJ')).prod Set.finite_univ).image _
  obtain ⟨J', hJ'J, hJ'1, hJ'0⟩ := exists_subset_sum_eq_one_forall_ne_zero hsum
  obtain ⟨k, hk⟩ : J'.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h ↦ by
    simp [h] at hJ'1
  have hsol : (fun i : J' ↦ y i) ∈ unitSolutions S (fun i : J' ↦ b i) := by
    refine mem_unitSolutions.mpr ⟨fun i ↦ hy i, ?_, fun I hI ↦ ?_⟩
    · rw [Finset.sum_coe_sort J' (fun i ↦ b i * y i)]
      exact hJ'1
    · have := hJ'0 (I.map (Function.Embedding.subtype _)) (fun i hi ↦ by
        obtain ⟨⟨j, hj⟩, -, rfl⟩ := Finset.mem_map.mp hi
        exact hj) (hI.map)
      rwa [Finset.sum_map] at this
  exact ⟨(k, y k), Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hJ'J))
    ⟨((fun i : J' ↦ y i), ⟨k, hk⟩), ⟨hsol, Set.mem_univ _⟩, rfl⟩, hJ'J hk, rfl⟩

/-- **Absorbing the coefficients**: if the normalized equations `∑ i, x i = 1` have finitely many
solutions for every `S`, so has `∑ i, a i * x i = 1` for nonzero `a`. -/
theorem finite_unitSolutions_of_forall_one
    (h : ∀ S, (unitSolutions S fun _ : ι ↦ (1 : K)).Finite)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    (unitSolutions S a).Finite := by
  classical
  choose T hT using fun i ↦ exists_finset_mem_unit (Units.mk0 (a i) (ha i))
  set S' := S ∪ univ.biUnion T
  refine Set.Finite.of_finite_image (f := fun x i ↦ Units.mk0 (a i) (ha i) * x i)
    ((h S').subset ?_) fun x _ y _ hxy ↦ funext fun i ↦ mul_left_cancel (congrFun hxy i)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxu, hsum, hnv⟩ := mem_unitSolutions.mp hx
  refine mem_unitSolutions.mpr ⟨fun i ↦ Subgroup.mul_mem _ (mem_unit_of_subset
    (Finset.coe_subset.mpr ((Finset.subset_biUnion_of_mem T (mem_univ i)).trans
      Finset.subset_union_right)) (hT i))
    (mem_unit_of_subset (Finset.coe_subset.mpr Finset.subset_union_left) (hxu i)),
    by simpa using hsum, fun I hI ↦ by simpa using hnv I hI⟩

/-- **Fixing one coordinate.** Given the theorem in fewer variables, the solutions of
`∑ i, x i = 1` with no vanishing subsum and a prescribed value `x k = u` are finitely many: the
other coordinates solve `∑ i ≠ k, x i = 1 - u`, and `u ≠ 1` because that subsum does not vanish. -/
theorem finite_setOf_apply_eq [Nontrivial ι]
    (IH : ∀ (κ : Type u) [Fintype κ], Fintype.card κ < Fintype.card ι →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : κ → K), (∀ i, a i ≠ 0) →
        (unitSolutions S a).Finite)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ι) (u : Kˣ) :
    {y ∈ unitSolutions S fun _ ↦ (1 : K) | y k = u}.Finite := by
  classical
  by_cases hu : (u : K) = 1
  · refine Set.Finite.subset Set.finite_empty fun y ⟨hy, hyk⟩ ↦ ?_
    obtain ⟨-, hsum, hnv⟩ := mem_unitSolutions.mp hy
    obtain ⟨i, hi⟩ := exists_ne k
    refine hnv (univ.erase k) ⟨i, Finset.mem_erase.mpr ⟨hi, mem_univ i⟩⟩ ?_
    rw [← Finset.add_sum_erase _ _ (mem_univ k), hyk, hu, one_mul] at hsum
    linear_combination hsum
  have hu' : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hfin := IH {i // i ≠ k} (Fintype.card_subtype_lt (p := (· ≠ k)) (not_not.mpr rfl)) S
    (fun _ ↦ (1 - (u : K))⁻¹) fun _ ↦ inv_ne_zero hu'
  refine Set.Finite.of_finite_image (f := fun (y : ι → Kˣ) (i : {i // i ≠ k}) ↦ y i)
    (hfin.subset ?_) ?_
  · rintro _ ⟨y, ⟨hy, hyk⟩, rfl⟩
    obtain ⟨hyu, hsum, hnv⟩ := mem_unitSolutions.mp hy
    have hs : ∑ i : {i // i ≠ k}, (y i : K) = 1 - u := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ k, hyk] at hsum
      simp only [one_mul] at hsum
      linear_combination hsum
    refine mem_unitSolutions.mpr ⟨fun i ↦ hyu i, ?_, fun I hI ↦ ?_⟩
    · rw [← Finset.mul_sum, hs, inv_mul_cancel₀ hu']
    · rw [← Finset.mul_sum]
      refine mul_ne_zero (inv_ne_zero hu') ?_
      have := hnv (I.map (Function.Embedding.subtype _)) hI.map
      simpa [Finset.sum_map] using this
  · rintro y ⟨-, hyk⟩ y' ⟨-, hy'k⟩ h
    funext i
    by_cases hi : i = k
    · rw [hi, hyk, hy'k]
    · exact congrFun h ⟨i, hi⟩

/-- **The induction step, normalized.** Given the theorem in fewer variables, the equation
`∑ i, x i = 1` has finitely many `S`-unit solutions with no vanishing subsum. -/
theorem finite_unitSolutions_one_of_forall_lt [Nontrivial ι]
    (IH : ∀ (κ : Type u) [Fintype κ], Fintype.card κ < Fintype.card ι →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : κ → K), (∀ i, a i ≠ 0) →
        (unitSolutions S a).Finite)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : (unitSolutions S fun _ : ι ↦ (1 : K)).Finite := by
  classical
  obtain ⟨T, hT, hmem⟩ := exists_finset_submodule_of_sum_eq_one (ι := ι) S
  have hex : ∀ W : Submodule K (ι → K), ∃ b : ι → K, ∃ j, W ≠ ⊤ →
      b j = 0 ∧ ∀ y ∈ W, ∑ i, y i = 1 → ∑ i, b i * y i = 1 := fun W ↦ by
    by_cases hW : W = ⊤
    · exact ⟨0, Classical.arbitrary ι, fun h ↦ absurd hW h⟩
    · obtain ⟨b, j, h⟩ := exists_sum_mul_eq_one_of_ne_top hW
      exact ⟨b, j, fun _ ↦ h⟩
  choose b j hb using hex
  have hG : ∀ W ∈ T, ∃ G : Set (ι × Kˣ), G.Finite ∧ ∀ y : ι → Kˣ,
      (∀ i, y i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
      ∑ i ∈ univ.filter (b W · ≠ 0), b W i * y i = 1 →
        ∃ p ∈ G, p.1 ∈ univ.filter (b W · ≠ 0) ∧ y p.1 = p.2 := fun W hW ↦
    exists_finite_forall_exists_apply_eq S (b W) _ fun J' hJ' ↦
      IH J' (Fintype.card_subtype_lt (p := (· ∈ J')) (x := j W) fun h ↦
        (Finset.mem_filter.mp (hJ' h)).2 (hb W (hT W hW)).1) S _
        fun i ↦ (Finset.mem_filter.mp (hJ' i.2)).2
  choose! G hGfin hGmem using hG
  refine ((T.finite_toSet.biUnion fun W hW ↦ hGfin W hW).biUnion fun p _ ↦
    finite_setOf_apply_eq IH S p.1 p.2).subset fun y hy ↦ ?_
  obtain ⟨hyu, hsum, -⟩ := mem_unitSolutions.mp hy
  have hsum' : ∑ i, (y i : K) = 1 := by simpa using hsum
  obtain ⟨W, hWT, hyW⟩ := hmem y hyu hsum'
  have hbW := (hb W (hT W hWT)).2 _ hyW hsum'
  obtain ⟨p, hpG, -, hp⟩ := hGmem W hWT y hyu (by
    rw [Finset.sum_filter_of_ne fun i _ h ↦ left_ne_zero_of_mul h]
    exact hbW)
  exact Set.mem_biUnion (Set.mem_biUnion hWT hpG) ⟨hy, hp⟩

/-- **The induction step**: given the theorem in fewer variables, it holds for `ι`. -/
theorem finite_unitSolutions_of_forall_lt
    (IH : ∀ (κ : Type u) [Fintype κ], Fintype.card κ < Fintype.card ι →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : κ → K), (∀ i, a i ≠ 0) →
        (unitSolutions S a).Finite)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    (unitSolutions S a).Finite := by
  rcases subsingleton_or_nontrivial ι with hι | hι
  · refine Set.Subsingleton.finite fun x hx y hy ↦ funext fun i ↦ Units.ext ?_
    obtain ⟨-, hx1, -⟩ := mem_unitSolutions.mp hx
    obtain ⟨-, hy1, -⟩ := mem_unitSolutions.mp hy
    rw [Fintype.sum_subsingleton _ i] at hx1 hy1
    exact mul_left_cancel₀ (ha i) (hx1.trans hy1.symm)
  · exact finite_unitSolutions_of_forall_one
      (fun S ↦ finite_unitSolutions_one_of_forall_lt IH S) S a ha

/-- **The unit equation with nonzero coefficients**: finitely many solutions in `S`-units with no
vanishing subsum. -/
theorem finite_unitSolutions (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → K)
    (ha : ∀ i, a i ≠ 0) : (unitSolutions S a).Finite := by
  suffices H : ∀ (n : ℕ) (κ : Type u) [Fintype κ], Fintype.card κ = n →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (a : κ → K), (∀ i, a i ≠ 0) →
        (unitSolutions S a).Finite from H _ ι rfl S a ha
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ hκ S a ha
    exact finite_unitSolutions_of_forall_lt (fun κ' _ h S a ha ↦ ih _ (hκ ▸ h) κ' rfl S a ha)
      S a ha

/-- **The unit equation in several variables** (Evertse; van der Poorten–Schlickewei;
Bombieri–Gubler, Theorem 7.4.2). For `a : ι → Kˣ`, finitely many `S`-unit vectors `x` satisfy
`∑ i, a i * x i = 1` with no vanishing subsum. -/
theorem finite_setOf_sum_unit_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) ∧
      ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite :=
  finite_unitSolutions S (fun i ↦ (a i : K)) fun i ↦ (a i).ne_zero

/-- **A finitely generated subgroup of `Kˣ` consists of `S`-units** for some finite `S`. -/
theorem exists_finset_le_unit {Γ : Subgroup Kˣ} (hΓ : Γ.FG) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), Γ ≤ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
  classical
  obtain ⟨s, rfl, hs⟩ := (Subgroup.fg_iff Γ).mp hΓ
  choose T hT using exists_finset_mem_unit (K := K)
  exact ⟨hs.toFinset.biUnion T, (Subgroup.closure_le _).mpr fun g hg ↦ mem_unit_of_subset
    (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem T (hs.mem_toFinset.mpr hg))) (hT g)⟩

/-- **The unit equation over a finitely generated subgroup** (Bombieri–Gubler, Theorem 7.4.2):
finitely many `x` with coordinates in `Γ` satisfy `∑ i, a i * x i = 1` with no vanishing
subsum. -/
theorem finite_setOf_sum_mem_eq_one (Γ : Subgroup Kˣ) (hΓ : Γ.FG) (a : ι → Kˣ) :
    {x : ι → Kˣ | (∀ i, x i ∈ Γ) ∧ ∑ i, (a i : K) * x i = 1 ∧
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (a i : K) * x i ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := exists_finset_le_unit hΓ
  exact (finite_setOf_sum_unit_eq_one S a).subset fun x ⟨hx, h1, h2⟩ ↦
    ⟨fun i ↦ hS (hx i), h1, h2⟩

/-- **Vanishing subsums allowed** (Bombieri–Gubler, Corollary 7.4.3): there is a finite set
`Φ ⊆ K` such that every `S`-unit solution of `∑ i, a i * x i = 1` has a term `a i * x i ∈ Φ`. -/
theorem exists_finite_forall_exists_mul_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ι → Kˣ) :
    ∃ Φ : Set K, Φ.Finite ∧ ∀ x : ι → Kˣ,
      (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) →
      ∑ i, (a i : K) * x i = 1 → ∃ i, (a i : K) * x i ∈ Φ := by
  obtain ⟨G, hG, hmem⟩ := exists_finite_forall_exists_apply_eq S (fun i ↦ (a i : K)) univ
    fun J' _ ↦ finite_unitSolutions S _ fun i ↦ (a i).ne_zero
  refine ⟨(fun p : ι × Kˣ ↦ (a p.1 : K) * p.2) '' G, hG.image _, fun x hx hsum ↦ ?_⟩
  obtain ⟨p, hpG, -, hp⟩ := hmem x hx hsum
  exact ⟨p.1, p, hpG, by rw [hp]⟩

end NumberField

/-! ### Acceptance criteria -/

open NumberField

open scoped Classical in
/-- The `{2, 3}`-units of `ℚ`, as height-one primes of `𝓞 ℚ`. -/
private noncomputable def S23 : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  {(Rat.finitePlace ⟨2, Nat.prime_two⟩).maximalIdeal,
    (Rat.finitePlace ⟨3, Nat.prime_three⟩).maximalIdeal}

/-- A divisor of `72 = 2³ 3²`, with either sign, is a `{2, 3}`-unit. -/
private theorem mk0_mem_S23_unit {n : ℕ} (hn : n ∣ 72) (σ : ℚ)
    (hσ : σ = 1 ∨ σ = -1) (hσn : σ * n ≠ 0) :
    Units.mk0 (σ * n) hσn ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
  refine (Set.mk0_mem_unit_iff_finitePlace _ hσn).mpr fun v hv ↦ ?_
  obtain ⟨p, hp, hvp⟩ := Rat.exists_prime_padic_eq (FinitePlace.mk v)
  have hmem : ∀ q : Nat.Primes, (q : ℕ) = p →
      v = (Rat.finitePlace q).maximalIdeal := fun q hq ↦ by
    subst hq
    rw [← FinitePlace.maximalIdeal_mk v]
    congr 1
    exact Subtype.ext (by rw [hvp, Rat.finitePlace_val])
  have hp2 : p ≠ 2 := fun h ↦ hv (by rw [hmem ⟨2, Nat.prime_two⟩ h.symm]; simp [S23])
  have hp3 : p ≠ 3 := fun h ↦ hv (by rw [hmem ⟨3, Nat.prime_three⟩ h.symm]; simp [S23])
  have hndvd : ¬ p ∣ n := fun hpn ↦ by
    have h72 : p ∣ 2 ^ 3 * 3 ^ 2 := hpn.trans hn
    rcases (Nat.Prime.dvd_mul hp.out).mp h72 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
        (hp.out.dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp
        (hp.out.dvd_of_dvd_pow h))
  have hnorm : padicNorm p (σ * n) = 1 := by
    rcases hσ with rfl | rfl
    · rw [one_mul]; exact (padicNorm.nat_eq_one_iff n).mpr hndvd
    · rw [neg_one_mul, padicNorm.neg]; exact (padicNorm.nat_eq_one_iff n).mpr hndvd
  change (FinitePlace.mk v).1 (σ * n) = 1
  rw [hvp]
  change ((padicNorm p (σ * n) : ℚ) : ℝ) = 1
  exact_mod_cast hnorm

/-- The `{2, 3}`-unit `n`, for a positive divisor `n` of `72`. -/
private noncomputable def u23 (n : ℕ) (hn : n ∣ 72) : ℚˣ :=
  Units.mk0 (1 * n) (by
    have : n ≠ 0 := fun h ↦ by simp [h] at hn
    positivity)

private theorem u23_mem {n : ℕ} (hn : n ∣ 72) :
    u23 n hn ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ :=
  mk0_mem_S23_unit hn 1 (Or.inl rfl) _

/-- **Conformance: `1/2 + 1/3 + 1/6 = 1` is a solution in `{2, 3}`-units with no vanishing
subsum**, so the finite set of the milestone for three variables is not empty. -/
example : (fun i ↦ ![(u23 2 (by norm_num))⁻¹, (u23 3 (by norm_num))⁻¹, (u23 6 (by norm_num))⁻¹] i)
    ∈ {x : Fin 3 → ℚˣ | (∀ i, x i ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) ∧
      ∑ i, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i = 1 ∧
      ∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i ≠ 0} := by
  have hval : ∀ i, (0 : ℚ) < ((1 : Fin 3 → ℚˣ) i : ℚ) *
      (![(u23 2 (by norm_num))⁻¹, (u23 3 (by norm_num))⁻¹, (u23 6 (by norm_num))⁻¹] i : ℚˣ) := by
    intro i
    fin_cases i <;> simp [u23]
  refine ⟨fun i ↦ ?_, ?_, fun I hI ↦ (Finset.sum_pos (fun i _ ↦ hval i) hI).ne'⟩
  · fin_cases i
    · exact Subgroup.inv_mem _ (u23_mem _)
    · exact Subgroup.inv_mem _ (u23_mem _)
    · exact Subgroup.inv_mem _ (u23_mem _)
  · simp [Fin.sum_univ_three, u23]
    norm_num

/-- The `{2, 3}`-unit equation in three variables has finitely many solutions with no vanishing
subsum. -/
example : {x : Fin 3 → ℚˣ | (∀ i, x i ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) ∧
    ∑ i, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i = 1 ∧
    ∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i ≠ 0}.Finite :=
  NumberField.finite_setOf_sum_unit_eq_one S23 1

/-- Rejection: **the vanishing subsums are load-bearing.** `(2 ^ k, -2 ^ k, 1)` solves
`x₁ + x₂ + x₃ = 1` in `{2, 3}`-units for every `k`. -/
example : {x : Fin 3 → ℚˣ | (∀ i, x i ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) ∧
    ∑ i, (x i : ℚ) = 1}.Infinite := by
  have hm : (-1 : ℚ) * (1 : ℕ) ≠ 0 := by norm_num
  set m := Units.mk0 _ hm
  have hmS : m ∈ (S23 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ :=
    mk0_mem_S23_unit (one_dvd 72) (-1) (Or.inr rfl) hm
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ ![u23 2 (by norm_num) ^ k, m * u23 2 (by norm_num) ^ k, 1])
    (fun k l h ↦ ?_) fun k ↦ ⟨fun i ↦ ?_, ?_⟩
  · have := congrArg (fun x : Fin 3 → ℚˣ ↦ (x 0 : ℚ)) h
    simp only [Matrix.cons_val_zero, Units.val_pow_eq_pow_val, u23, Units.val_mk0] at this
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast this)
  · fin_cases i
    · exact Subgroup.pow_mem _ (u23_mem _) k
    · exact Subgroup.mul_mem _ hmS (Subgroup.pow_mem _ (u23_mem _) k)
    · exact Subgroup.one_mem _
  · simp [Fin.sum_univ_three, m, u23]

/-- A finitely generated subgroup: the subgroup of `ℚˣ` generated by `2` and `3`. -/
example : {x : Fin 3 → ℚˣ | (∀ i, x i ∈ Subgroup.closure
      ({u23 2 (by norm_num), u23 3 (by norm_num)} : Set ℚˣ)) ∧
    ∑ i, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i = 1 ∧
    ∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, ((1 : Fin 3 → ℚˣ) i : ℚ) * x i ≠ 0}.Finite :=
  NumberField.finite_setOf_sum_mem_eq_one _ ((Subgroup.fg_iff _).mpr
    ⟨_, rfl, Set.toFinite _⟩) 1
