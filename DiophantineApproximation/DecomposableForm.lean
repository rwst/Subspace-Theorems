/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.UnitEquation

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import DiophantineApproximation.RationalPlaces
import Mathlib.Algebra.Polynomial.Roots

/-!
# Triangularly connected decomposable forms

**Layer 8.3** (Győry–Papp; Evertse–Győry, *Unit Equations in Diophantine Number Theory*, Ch. 9).
Two linear forms `l j`, `l j'` of a finite family on a `K`-vector space are **joined by a
triangle** when some form of the family is `a • l j + b • l j'` with `a, b ≠ 0`, and the family
is **triangularly connected** when the graph of triangles is connected. For such a family with
common kernel `0`, over a number field `K` and a finite set `S` of finite places:

* the points at which every form takes an `S`-unit value are `S`-unit multiples of finitely many
  points (`NumberField.exists_finite_forall_eq_smul`);
* for `G = c ∏ j, l j ^ e j` with every `e j ≥ 1`, the points with `S`-integral coordinates and
  `G x = m`, `m ≠ 0`, are finitely many (`NumberField.finite_setOf_mul_prod_eq`);
* the points with `S`-integral coordinates and `G x` an `S`-unit are finitely many modulo
  `S`-units (`NumberField.exists_finite_forall_mul_prod_mem_unit`).

Route: along a triangle `l k = a • l j + b • l j'`, at a point where all three forms take
`S`-unit values, `a (l j x / l k x) + b (l j' x / l k x) = 1` is a unit equation in two variables
(Layer 8.1), so the ratio `l j' x / l j x` takes finitely many values; along a path of triangles
the ratios multiply, so by connectivity every ratio `l j x / l j₀ x` does, and since the common
kernel is `0` the vector of ratios determines `(l j₀ x)⁻¹ • x`. For `G`: enlarge `S` until `c` is
a unit and the coefficients of the forms are integral; then every `l j x` is integral with a
product of powers that is a unit, so every `l j x` is a unit, and `G (u • y) = u ^ E * G y` with
`E = ∑ j, e j` leaves finitely many `u` for each `y`, or — for the unit version — a single class
of `u` modulo `S`-units, since an `E`-th power of `u / u'` that is an `S`-unit makes `u / u'` one.

## Implementation notes

⚠ **Pairwise non-proportionality is not needed.** The roadmap asks for it; the argument never uses
it, since a triangle with a repeated or proportional form is still a unit equation, and 8.1 has
no hypothesis on its coefficients beyond being nonzero.

⚠ **The unit version needs no discreteness of valuations.** Enlarging `S` loses the `S`-unit
scaling, which one might recover from bounds on valuations at the added places; instead two
solutions `u • y` and `u' • y` on the same line satisfy `(u / u') ^ E ∈ S.unit K`, and an
absolute value whose `E`-th power is `1` is `1`.

⚠ **Only the split case.** Forms whose linear factors are defined over a finite extension of `K`
(needed for Thue's equation, Layer 8.4) are not included; passing to the extension belongs to
8.4, where it is first used.

## References

J.-H. Evertse and K. Győry, *Unit Equations in Diophantine Number Theory*, Cambridge University
Press (2015), Chapter 9; K. Győry and Z. Z. Papp, *Norm form equations and explicit lower bounds
for linear forms with algebraic coefficients* (1983).

This is Layer 8.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset IsDedekindDomain Module

namespace Module.Dual

variable {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Two forms joined by a triangle**: some form of the family is `a • l j + b • l j'` with
`a, b ≠ 0`. -/
def TriangleAdj (l : κ → Dual K V) (j j' : κ) : Prop :=
  ∃ k, ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ l k = a • l j + b • l j'

theorem TriangleAdj.symm {l : κ → Dual K V} {j j' : κ} (h : TriangleAdj l j j') :
    TriangleAdj l j' j := by
  obtain ⟨k, a, b, ha, hb, h⟩ := h
  exact ⟨k, b, a, hb, ha, by rw [h, add_comm]⟩

/-- **A triangularly connected family of forms**: the graph of triangles is connected. -/
def IsTriangularlyConnected (l : κ → Dual K V) : Prop :=
  ∀ j j', Relation.ReflTransGen (TriangleAdj l) j j'

end Module.Dual

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {V κ : Type*} [AddCommGroup V] [Module K V]

/-- **One triangle is one unit equation.** Along a triangle, at the points where every form takes
an `S`-unit value, the ratio of the two forms takes finitely many values (Layer 8.1). -/
theorem finite_setOf_div_of_triangleAdj (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K V} {j j' : κ} (h : Dual.TriangleAdj l j j') :
    {r : K | ∃ x : V, (∀ j, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = l j x) ∧
      r = l j' x / l j x}.Finite := by
  obtain ⟨k, a, b, ha, hb, hk⟩ := h
  refine ((finite_setOf_unit_add_unit_eq_one S (Units.mk0 a ha) (Units.mk0 b hb)).image
    fun p ↦ (p.2 : K) / p.1).subset ?_
  rintro r ⟨x, hx, rfl⟩
  obtain ⟨u, hu, hux⟩ := hx j
  obtain ⟨u', hu', hux'⟩ := hx j'
  obtain ⟨w, hw, hwx⟩ := hx k
  have hw0 : l k x ≠ 0 := hwx ▸ w.ne_zero
  have hu0 : l j x ≠ 0 := hux ▸ u.ne_zero
  refine ⟨(u / w, u' / w), ⟨div_mem hu hw, div_mem hu' hw, ?_⟩, ?_⟩
  · have hkx : l k x = a * l j x + b * l j' x := by simp [hk]
    simp only [Units.val_mk0, Units.val_div_eq_div_val, hux, hux', hwx]
    field_simp
    rw [hkx]
  · simp only [Units.val_div_eq_div_val, hux, hux', hwx]
    field_simp

/-- **Ratios along a path of triangles** take finitely many values. -/
theorem finite_setOf_div_of_reflTransGen (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K V} {j j' : κ} (h : Relation.ReflTransGen (Dual.TriangleAdj l) j j') :
    {r : K | ∃ x : V, (∀ j, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = l j x) ∧
      r = l j' x / l j x}.Finite := by
  induction h with
  | refl =>
    refine (Set.finite_singleton 1).subset ?_
    rintro r ⟨x, hx, rfl⟩
    obtain ⟨u, -, hu⟩ := hx j
    simp [← hu]
  | @tail b c _ hadj ih =>
    refine (ih.image2 (· * ·) (finite_setOf_div_of_triangleAdj S hadj)).subset ?_
    rintro r ⟨x, hx, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, _, ⟨x, hx, rfl⟩, ?_⟩
    obtain ⟨u, -, hu⟩ := hx b
    have : l b x ≠ 0 := hu ▸ u.ne_zero
    simp only
    field_simp

/-- **Finitely many points up to `S`-units.** For a triangularly connected finite family of forms
with common kernel `0`, the points at which every form takes an `S`-unit value are `S`-unit
multiples of finitely many points. -/
theorem exists_finite_forall_eq_smul (S : Finset (HeightOneSpectrum (𝓞 K))) [Finite κ]
    {l : κ → Dual K V} (hl : ⨅ j, LinearMap.ker (l j) = ⊥)
    (hc : Dual.IsTriangularlyConnected l) :
    ∃ F : Set V, F.Finite ∧ ∀ x : V,
      (∀ j, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = l j x) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, x = (u : K) • y := by
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨j₀⟩⟩
  · have h0 : ∀ x : V, x = 0 := fun x ↦ by
      have : x ∈ ⨅ j, LinearMap.ker (l j) := Submodule.mem_iInf _ |>.mpr fun j ↦ isEmptyElim j
      rwa [hl, Submodule.mem_bot] at this
    exact ⟨{0}, Set.finite_singleton 0, fun x _ ↦ ⟨1, one_mem _, 0, rfl, by simp [h0 x]⟩⟩
  have hinj : Function.Injective (LinearMap.pi l) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_pi, hl]
  refine ⟨LinearMap.pi l ⁻¹' Set.pi Set.univ fun j ↦ {r : K | ∃ x : V,
      (∀ j, ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (u : K) = l j x) ∧
      r = l j x / l j₀ x},
    (Set.Finite.pi fun j ↦ finite_setOf_div_of_reflTransGen S (hc j₀ j)).preimage hinj.injOn,
    fun x hx ↦ ?_⟩
  obtain ⟨u, hu, hux⟩ := hx j₀
  refine ⟨u, hu, (u : K)⁻¹ • x, fun j _ ↦ ⟨x, hx, ?_⟩, ?_⟩
  · simp [LinearMap.pi_apply, hux, div_eq_inv_mul]
  · rw [smul_smul, mul_inv_cancel₀ u.ne_zero, one_smul]

/-- `S`-integers stay `S`-integers when `S` grows. -/
theorem mem_integer_of_subset {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') {x : K}
    (hx : x ∈ S.integer K) : x ∈ S'.integer K :=
  fun v hv ↦ hx v fun hvS ↦ hv (h hvS)

/-- **Finitely many elements of `K` are `S`-integers for some finite `S`**, containing a given
one. -/
theorem exists_finset_forall_mem_integer {α : Type*} [Finite α]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (z : α → K) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ T ∧
      ∀ a, z a ∈ (T : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  classical
  have := Fintype.ofFinite α
  have h : ∀ a, ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      z a ∈ (T : Set (HeightOneSpectrum (𝓞 K))).integer K := fun a ↦ by
    rcases eq_or_ne (z a) 0 with h0 | h0
    · exact ⟨∅, h0 ▸ Subalgebra.zero_mem _⟩
    · obtain ⟨T, hT⟩ := exists_finset_mem_unit (Units.mk0 _ h0)
      exact ⟨T, Set.mem_integer_of_mem_unit hT⟩
  choose T hT using h
  refine ⟨S ∪ univ.biUnion T, subset_union_left, fun a ↦ mem_integer_of_subset ?_ (hT a)⟩
  intro v hv
  simp only [coe_union, coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_union,
    Set.mem_iUnion, SetLike.mem_coe]
  exact Or.inr ⟨a, hv⟩

/-- A form with `S`-integral coefficients takes `S`-integral values at `S`-integral points. -/
theorem apply_mem_integer {ι : Type*} [Finite ι] [DecidableEq ι]
    {S : Set (HeightOneSpectrum (𝓞 K))} {l : Dual K (ι → K)}
    (hl : ∀ i, l (fun i' ↦ if i = i' then 1 else 0) ∈ S.integer K) {x : ι → K}
    (hx : ∀ i, x i ∈ S.integer K) : l x ∈ S.integer K := by
  have := Fintype.ofFinite ι
  rw [LinearMap.pi_apply_eq_sum_univ]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _ (hx i) (hl i)

omit [NumberField K] in
/-- **Homogeneity**: `G (u • y) = u ^ E * G y` for `G = c ∏ j, l j ^ e j` and `E = ∑ j, e j`. -/
theorem mul_prod_apply_smul [Fintype κ] (c : K) (l : κ → Dual K V) (e : κ → ℕ) (u : K) (y : V) :
    c * ∏ j, l j (u • y) ^ e j = u ^ (∑ j, e j) * (c * ∏ j, l j y ^ e j) := by
  simp only [map_smul, smul_eq_mul, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
  ring

omit [NumberField K] in
/-- For nonnegative reals at most `1`, a product of positive powers equal to `1` has every factor
equal to `1`. -/
theorem _root_.Real.eq_one_of_prod_pow_eq_one [Fintype κ] {a : κ → ℝ} (h0 : ∀ j, 0 ≤ a j)
    (h1 : ∀ j, a j ≤ 1) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) (h : ∏ j, a j ^ e j = 1) (j : κ) :
    a j = 1 := by
  classical
  by_contra hne
  have hlt : a j ^ e j < 1 := pow_lt_one₀ (h0 j) (lt_of_le_of_ne (h1 j) hne) (he j)
  have hle : ∏ i ∈ univ.erase j, a i ^ e i ≤ 1 :=
    prod_le_one₀ (fun i _ ↦ pow_nonneg (h0 i) _) fun i _ ↦ pow_le_one₀ (h0 i) (h1 i)
  rw [← mul_prod_erase univ _ (mem_univ j)] at h
  nlinarith [pow_nonneg (h0 j) (e j)]

/-- **Integral factors of a unit are units**: if `c * ∏ j, z j ^ e j` is an `S`-unit, `c` is one,
every `z j` is `S`-integral and every `e j ≥ 1`, then every `z j` is an `S`-unit. -/
theorem exists_mem_unit_of_mul_prod [Fintype κ] {S : Set (HeightOneSpectrum (𝓞 K))}
    {z : κ → K} (hz : ∀ j, z j ∈ S.integer K) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) {c w : Kˣ}
    (hc : c ∈ S.unit K) (hw : w ∈ S.unit K) (h : (c : K) * ∏ j, z j ^ e j = w) (j : κ) :
    ∃ u ∈ S.unit K, (u : K) = z j := by
  have hz0 : z j ≠ 0 := by
    intro h0
    rw [prod_eq_zero (mem_univ j) (by simp [h0, he j]), mul_zero] at h
    exact w.ne_zero h.symm
  refine ⟨Units.mk0 _ hz0, (Set.mk0_mem_unit_iff_finitePlace _ hz0).mpr fun v hv ↦ ?_, rfl⟩
  refine Real.eq_one_of_prod_pow_eq_one (a := fun j ↦ FinitePlace.mk v (z j))
    (fun _ ↦ apply_nonneg _ _) (fun j ↦ (Set.mem_integer_iff_finitePlace _ _).mp (hz j) v hv) he
    ?_ j
  have := congrArg (FinitePlace.mk v) h
  simp only [map_mul, map_prod, map_pow, (Set.mem_unit_iff_finitePlace _ c).mp hc v hv,
    (Set.mem_unit_iff_finitePlace _ w).mp hw v hv, one_mul] at this
  exact this

omit [NumberField K] in
/-- `r ^ E * g = m` with `m ≠ 0` and `E ≠ 0` has finitely many solutions. -/
theorem finite_setOf_pow_mul_eq {E : ℕ} (hE : E ≠ 0) (g : K) {m : K} (hm : m ≠ 0) :
    {r : K | r ^ E * g = m}.Finite := by
  classical
  rcases eq_or_ne g 0 with rfl | hg
  · convert Set.finite_empty
    ext r
    simp [hm.symm]
  refine (Polynomial.nthRoots E (m / g)).toFinset.finite_toSet.subset fun r hr ↦ ?_
  simp only [Multiset.coe_toFinset,
    Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hE)]
  exact eq_div_of_mul_eq hg hr

/-- A form with `S'`-integral coefficients for some finite `S' ⊇ S`, together with a unit `c`. -/
theorem exists_finset_integer_coeff {ι : Type*} [Finite ι] [DecidableEq ι] [Finite κ]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (l : κ → Dual K (ι → K)) (c : Kˣ) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ T ∧
      c ∈ (T : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      ∀ j i, l j (fun i' ↦ if i = i' then 1 else 0) ∈
        (T : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  classical
  obtain ⟨Tc, hTc⟩ := exists_finset_mem_unit c
  obtain ⟨T, hST, hT⟩ := exists_finset_forall_mem_integer (S ∪ Tc)
    fun p : κ × ι ↦ l p.1 fun i' ↦ if p.2 = i' then 1 else 0
  exact ⟨T, subset_union_left.trans hST,
    mem_unit_of_subset (coe_subset.mpr (subset_union_right.trans hST)) hTc, fun j i ↦ hT (j, i)⟩

variable {ι : Type*} [Finite ι] [Fintype κ]

/-- **Decomposable form equations** (Győry–Papp). For a triangularly connected finite family of
forms with common kernel `0` and `G = c ∏ j, l j ^ e j` with every `e j ≥ 1`, the equation
`G x = m`, `m ≠ 0`, has finitely many solutions with `S`-integral coordinates. -/
theorem finite_setOf_mul_prod_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K (ι → K)} (hl : ⨅ j, LinearMap.ker (l j) = ⊥)
    (hc : Dual.IsTriangularlyConnected l) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) (c : K) {m : K}
    (hm : m ≠ 0) :
    {x : ι → K | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
      c * ∏ j, l j x ^ e j = m}.Finite := by
  classical
  rcases eq_or_ne c 0 with rfl | hc0
  · convert Set.finite_empty
    ext x
    simp [hm.symm]
  obtain ⟨T₁, hST₁, hcT, hlT⟩ := exists_finset_integer_coeff S l (Units.mk0 c hc0)
  obtain ⟨Tm, hTm⟩ := exists_finset_mem_unit (Units.mk0 m hm)
  set T := T₁ ∪ Tm
  have hT₁ : (T₁ : Set (HeightOneSpectrum (𝓞 K))) ⊆ T := coe_subset.mpr subset_union_left
  obtain ⟨F, hF, hFx⟩ := exists_finite_forall_eq_smul T hl hc
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h0 : ∀ x : ι → K, x = 0 := fun x ↦ by
      have : x ∈ ⨅ j, LinearMap.ker (l j) := Submodule.mem_iInf _ |>.mpr fun j ↦ isEmptyElim j
      rwa [hl, Submodule.mem_bot] at this
    exact (Set.finite_singleton 0).subset fun x _ ↦ h0 x
  have hE : ∑ j, e j ≠ 0 := by
    obtain ⟨j⟩ := hκ
    exact fun h ↦ he j (sum_eq_zero_iff.mp h j (mem_univ j))
  refine (hF.biUnion fun y _ ↦ (finite_setOf_pow_mul_eq hE (c * ∏ j, l j y ^ e j) hm).image
    fun r ↦ r • y).subset ?_
  rintro x ⟨hx, hxm⟩
  have hadm := exists_mem_unit_of_mul_prod
    (fun j ↦ apply_mem_integer (fun i ↦ mem_integer_of_subset hT₁ (hlT j i))
      fun i ↦ mem_integer_of_subset ((coe_subset.mpr hST₁).trans hT₁) (hx i))
    he (mem_unit_of_subset hT₁ hcT)
    (mem_unit_of_subset (coe_subset.mpr subset_union_right) hTm) (w := Units.mk0 m hm) hxm
  obtain ⟨u, -, y, hy, rfl⟩ := hFx x hadm
  exact Set.mem_biUnion hy ⟨u, by rwa [mul_prod_apply_smul] at hxm, rfl⟩

/-- **Decomposable form equations modulo units** (Győry–Papp). For a triangularly connected finite
family of forms with common kernel `0` and `G = c ∏ j, l j ^ e j` with every `e j ≥ 1`, the
points with `S`-integral coordinates at which `G` takes an `S`-unit value are `S`-unit multiples
of finitely many of them. -/
theorem exists_finite_forall_mul_prod_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K)))
    {l : κ → Dual K (ι → K)} (hl : ⨅ j, LinearMap.ker (l j) = ⊥)
    (hc : Dual.IsTriangularlyConnected l) {e : κ → ℕ} (he : ∀ j, e j ≠ 0) (c : K) :
    ∃ F : Set (ι → K), F.Finite ∧
      F ⊆ {x | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
        ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = c * ∏ j, l j x ^ e j} ∧
      ∀ x : ι → K, (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = c * ∏ j, l j x ^ e j) →
        ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ y ∈ F, x = (u : K) • y := by
  classical
  set X := {x : ι → K | (∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
    ∃ w ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, (w : K) = c * ∏ j, l j x ^ e j} with hX
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨∅, Set.finite_empty, Set.empty_subset _, fun x _ ⟨w, _, hw⟩ ↦ ?_⟩
    simp at hw
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have h0 : ∀ x : ι → K, x = 0 := fun x ↦ by
      have : x ∈ ⨅ j, LinearMap.ker (l j) := Submodule.mem_iInf _ |>.mpr fun j ↦ isEmptyElim j
      rwa [hl, Submodule.mem_bot] at this
    exact ⟨X, (Set.finite_singleton 0).subset fun x _ ↦ h0 x, subset_rfl,
      fun x hx hw ↦ ⟨1, one_mem _, x, ⟨hx, hw⟩, by simp⟩⟩
  have hE : ∑ j, e j ≠ 0 := by
    obtain ⟨j⟩ := hκ
    exact fun h ↦ he j (sum_eq_zero_iff.mp h j (mem_univ j))
  obtain ⟨T, hST, hcT, hlT⟩ := exists_finset_integer_coeff S l (Units.mk0 c hc0)
  have hST' : (S : Set (HeightOneSpectrum (𝓞 K))) ⊆ T := coe_subset.mpr hST
  obtain ⟨F, hF, hFx⟩ := exists_finite_forall_eq_smul T hl hc
  set P : (ι → K) → Prop := fun y ↦ ∃ x ∈ X, ∃ r : Kˣ, x = (r : K) • y
  let g : (ι → K) → (ι → K) := fun y ↦ if h : P y then h.choose else y
  have hg : ∀ y, P y → g y ∈ X ∧ ∃ r : Kˣ, g y = (r : K) • y := fun y h ↦ by
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec
  refine ⟨g '' {y ∈ F | P y}, (hF.subset fun y hy ↦ hy.1).image g, ?_, fun x hx hxw ↦ ?_⟩
  · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact (hg y hy).1
  obtain ⟨w, hwS, hw⟩ := hxw
  have hadm := exists_mem_unit_of_mul_prod
    (fun j ↦ apply_mem_integer (hlT j) fun i ↦ mem_integer_of_subset hST' (hx i))
    he hcT (mem_unit_of_subset hST' hwS) (w := w) (by simpa using hw.symm)
  obtain ⟨u', -, y, hy, rfl⟩ := hFx x hadm
  have hPy : P y := ⟨_, ⟨hx, w, hwS, hw⟩, u', rfl⟩
  obtain ⟨⟨-, w', hw'S, hw'⟩, r, hr⟩ := hg y hPy
  refine ⟨u' / r, (Set.mem_unit_iff_finitePlace _ _).mpr fun v hv ↦ ?_, g y,
    ⟨y, ⟨hy, hPy⟩, rfl⟩, ?_⟩
  · rw [hr, mul_prod_apply_smul] at hw'
    rw [mul_prod_apply_smul] at hw
    have hrel : ((u' / r : Kˣ) : K) ^ (∑ j, e j) * w' = w := by
      rw [hw, hw', Units.val_div_eq_div_val, div_pow]
      field_simp
    have := congrArg (FinitePlace.mk v) hrel
    rw [map_mul, map_pow, (Set.mem_unit_iff_finitePlace _ w').mp hw'S v hv,
      (Set.mem_unit_iff_finitePlace _ w).mp hwS v hv, mul_one] at this
    exact (pow_eq_one_iff_of_nonneg (apply_nonneg _ _) hE).mp this
  · rw [hr, smul_smul, Units.val_div_eq_div_val, div_mul_cancel₀ _ r.ne_zero]

end NumberField

/-! ### Acceptance criteria -/

open NumberField

/-- The coordinate forms on `ℚ²`. -/
private def pr (i : Fin 2) : Dual ℚ (Fin 2 → ℚ) := LinearMap.proj i

/-- The forms `X`, `Y` and `X + Y` on `ℚ²`, the smallest triangle. -/
private def L3 : Fin 3 → Dual ℚ (Fin 2 → ℚ) := ![pr 0, pr 1, pr 0 + pr 1]

private theorem ker_L3 : ⨅ j, LinearMap.ker (L3 j) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  have h := Submodule.mem_iInf _ |>.mp hx
  have h0 : x 0 = 0 := by simpa [L3, pr] using h 0
  have h1 : x 1 = 0 := by simpa [L3, pr] using h 1
  rw [Submodule.mem_bot]
  ext i
  fin_cases i <;> simp [h0, h1]

private theorem isTriangularlyConnected_L3 : Dual.IsTriangularlyConnected L3 := by
  have h01 : Dual.TriangleAdj L3 0 1 :=
    ⟨2, 1, 1, one_ne_zero, one_ne_zero, LinearMap.ext fun v ↦ by simp [L3, pr]⟩
  have h02 : Dual.TriangleAdj L3 0 2 :=
    ⟨1, -1, 1, by norm_num, one_ne_zero, LinearMap.ext fun v ↦ by simp [L3, pr]⟩
  have h12 : Dual.TriangleAdj L3 1 2 :=
    ⟨0, -1, 1, by norm_num, one_ne_zero, LinearMap.ext fun v ↦ by simp [L3, pr]⟩
  intro j j'
  fin_cases j <;> fin_cases j'
  exacts [.refl, .single h01, .single h02, .single h01.symm, .refl, .single h12,
    .single h02.symm, .single h12.symm, .refl]

/-- **Conformance: `x y (x + y) = 2` has the integer solution `(1, 1)`**, so the finite set of the
milestone is not empty. -/
example : ![(1 : ℚ), 1] ∈ {x : Fin 2 → ℚ |
    (∀ i, x i ∈
      ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) ∧
    1 * ∏ j, L3 j x ^ 1 = 2} := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i <;> exact Subalgebra.one_mem _
  · simp [L3, pr, Fin.prod_univ_three]
    norm_num

/-- **`x y (x + y) = 2` has finitely many integer solutions**: the milestone for the smallest
triangle, with `S` empty. -/
example : {x : Fin 2 → ℚ |
    (∀ i, x i ∈
      ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) ∧
    1 * ∏ j, L3 j x ^ 1 = 2}.Finite :=
  NumberField.finite_setOf_mul_prod_eq ∅ ker_L3 isTriangularlyConnected_L3 (fun _ ↦ one_ne_zero)
    1 two_ne_zero

open scoped Classical in
/-- The `{2}`-units of `ℚ`, as height-one primes of `𝓞 ℚ`. -/
private noncomputable def S2 : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  {(Rat.finitePlace ⟨2, Nat.prime_two⟩).maximalIdeal}

/-- **Modulo `{2}`-units, finitely many `{2}`-integral points make `x y (x + y)` a `{2}`-unit.** -/
example : ∃ F : Set (Fin 2 → ℚ), F.Finite ∧
    F ⊆ {x | (∀ i, x i ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) ∧
      ∃ w ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ, (w : ℚ) = 1 * ∏ j, L3 j x ^ 1} ∧
    ∀ x : Fin 2 → ℚ, (∀ i, x i ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) →
      (∃ w ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ, (w : ℚ) = 1 * ∏ j, L3 j x ^ 1) →
      ∃ u ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ, ∃ y ∈ F, x = (u : ℚ) • y :=
  NumberField.exists_finite_forall_mul_prod_mem_unit S2 ker_L3 isTriangularlyConnected_L3
    (fun _ ↦ one_ne_zero) 1

/-- The forms `X` and `Y` on `ℚ²`, which make no triangle. -/
private def L2 : Fin 2 → Dual ℚ (Fin 2 → ℚ) := ![pr 0, pr 1]

/-- `X` and `Y` are **not** triangularly connected: a triangle through both would be a third form
`a X + b Y` with `a, b ≠ 0`. -/
example : ¬ Dual.IsTriangularlyConnected L2 := by
  have hadj : ∀ j j', Dual.TriangleAdj L2 j j' → j = j' := by
    rintro j j' ⟨k, a, b, ha, hb, hk⟩
    by_contra hne
    have h0 : L2 k ![1, 0] = a * L2 j ![1, 0] + b * L2 j' ![1, 0] := by
      simpa using LinearMap.congr_fun hk ![1, 0]
    have h1 : L2 k ![0, 1] = a * L2 j ![0, 1] + b * L2 j' ![0, 1] := by
      simpa using LinearMap.congr_fun hk ![0, 1]
    clear hk
    have hkey : L2 k ![1, 0] = 0 ∨ L2 k ![0, 1] = 0 := by
      fin_cases k <;> simp [L2, pr]
    rcases hkey with h | h <;> [rw [h] at h0; rw [h] at h1] <;>
      fin_cases j <;> fin_cases j' <;> simp [L2, pr] at hne h0 h1 <;> simp_all
  intro h
  have key : ∀ {a b : Fin 2}, Relation.ReflTransGen (Dual.TriangleAdj L2) a b → a = b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
  exact absurd (key (h 0 1)) (by decide)

/-- `2 ^ k` is a `{2}`-unit. -/
private theorem two_pow_mem_S2_unit (k : ℕ) :
    Units.mk0 ((2 : ℚ) ^ k) (by positivity) ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
  have h2 : Units.mk0 (2 : ℚ) two_ne_zero ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
    refine (Set.mk0_mem_unit_iff_finitePlace _ two_ne_zero).mpr fun v hv ↦ ?_
    obtain ⟨p, hp, hvp⟩ := Rat.exists_prime_padic_eq (FinitePlace.mk v)
    have hmem : ∀ q : Nat.Primes, (q : ℕ) = p →
        v = (Rat.finitePlace q).maximalIdeal := fun q hq ↦ by
      subst hq
      rw [← FinitePlace.maximalIdeal_mk v]
      congr 1
      exact Subtype.ext (by rw [hvp, Rat.finitePlace_val])
    have hp2 : p ≠ 2 := fun h ↦ hv (by rw [hmem ⟨2, Nat.prime_two⟩ h.symm]; simp [S2])
    have hnorm : padicNorm p ((2 : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff 2).mpr fun hpd ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hpd)
    change (FinitePlace.mk v).1 ((2 : ℕ) : ℚ) = 1
    rw [hvp]
    change ((padicNorm p ((2 : ℕ) : ℚ) : ℚ) : ℝ) = 1
    exact_mod_cast hnorm
  convert Subgroup.pow_mem _ h2 k
  ext
  simp

/-- Rejection: **the triangles are load-bearing.** `x y = 1` has the infinitely many
`{2}`-integral solutions `(2 ^ k, 2 ^ (-k))`. -/
example : {x : Fin 2 → ℚ | (∀ i, x i ∈ (S2 : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) ∧
    1 * ∏ j, L2 j x ^ 1 = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ ![(2 : ℚ) ^ k, ((2 : ℚ) ^ k)⁻¹]) (fun k l h ↦ ?_) fun k ↦ ⟨fun i ↦ ?_, ?_⟩
  · have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast this)
  · fin_cases i
    · exact Set.mem_integer_of_mem_unit (two_pow_mem_S2_unit k)
    · exact Set.mem_integer_of_mem_unit (Subgroup.inv_mem _ (two_pow_mem_S2_unit k))
  · simp [L2, pr]
