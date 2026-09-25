/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SUnitTheorem
public import DiophantineApproximation.SIntegerLocalization

-- Used only inside proofs.
import DiophantineApproximation.UnitEquation
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Square classes of `S`-integers

The arithmetic input of Siegel's theorem on the hyperelliptic equation, Layer 8.5 of the
`DiophantineApproximation` roadmap: if a product of pairwise coprime `S`-integers is an `S`-unit
times a square, then each factor is, up to one of **finitely many** constants, a square. Three
statements carry it.

* `NumberField.exists_finite_superset_forall_mem_unit`: every finite `S` and every finite set of
  elements are contained in a finite `S'` for which those elements that are nonzero are
  `S'`-units and the ring of `S'`-integers is a principal ideal domain (Layer 0.3).
* `NumberField.exists_finset_forall_eq_mul_sq`: the `S`-units modulo squares are finite — every
  `S`-unit is one of finitely many constants times a square.
* `NumberField.exists_eq_mul_sq_of_pow_mul_prod_eq`: over a principal ring of `S`-integers, if
  `z ^ m * ∏ w = u c ^ 2` with `m` odd, `u` an `S`-unit and every `w - z` an `S`-unit, then `z` is
  an `S`-unit times a square.

Two facts about places close the file: an element whose square is an `S`-integer is one, and an
`S`-integral factor of an `S`-unit with an `S`-integral cofactor is an `S`-unit.

## Implementation notes

⚠ **No ideal is factored and no valuation is counted.** The book shows that `x - α` has even
valuation at every prime outside `S` and takes a square root of the ideal it generates, which
needs the factorization of fractional ideals and the class group of `S.integer K`. Here the whole
argument happens in the principal ring `S.integer K` made by Layer 0.3: the factors are coprime
there because their differences are units — a Bézout identity written in `K` — and Mathlib's
`exists_associated_pow_of_mul_eq_pow'` does the rest. No prime of `S.integer K` is ever named.

⚠ **The finiteness of the square classes is two Mathlib theorems.** The `S`-units are finitely
generated (`ArithmeticHeights` 6.5, `Set.unit_fg`), and in a finitely generated commutative group
the squares have finite index (`Subgroup.finiteIndex_range_powMonoidHom_of_fg`); the constants
are representatives of the cosets. The unit theorem's *rank* is not used.

⚠ **An odd power is as good as a first power**, and the multiplicity of a root costs nothing:
`z ^ (2 k + 1) = v d ^ 2` gives `z = v (d / z ^ k) ^ 2` once `z ≠ 0`, and `z = 0` is `v · 0 ^ 2`.
The square root lives in `K`, not in `S.integer K`, and nothing downstream asks for more.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The `S`-integers grow with `S`.** -/
theorem mem_integer_of_subset {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') {x : K}
    (hx : x ∈ S.integer K) : x ∈ S'.integer K :=
  (Set.mem_integer_iff_finitePlace _ x).mpr fun v hv ↦
    (Set.mem_integer_iff_finitePlace _ x).mp hx v fun hvS ↦ hv (h hvS)

/-- **Making finitely many elements units and the `S`-integers principal.** Every finite `S` and
every finite set `s` of elements are contained in a finite `S'` for which the nonzero elements of
`s` are `S'`-units and `S'.integer K` is a principal ideal domain. -/
theorem exists_finite_superset_forall_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) (s : Finset K) :
    ∃ S' : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧ S'.Finite ∧
      IsPrincipalIdealRing ↥(S'.integer K) ∧
      ∀ x ∈ s, ∀ hx : x ≠ 0, Units.mk0 x hx ∈ S'.unit K := by
  classical
  have : Finite {x // x ∈ s ∧ x ≠ 0} := Finite.of_injective (fun x ↦ (⟨x.1, x.2.1⟩ : s))
    fun a b h ↦ Subtype.ext (by simpa using h)
  choose T hT using fun x : {x // x ∈ s ∧ x ≠ 0} ↦ exists_finset_mem_unit (Units.mk0 _ x.2.2)
  set S₀ := S ∪ ⋃ x, (T x : Set (HeightOneSpectrum (𝓞 K))) with hS₀
  have hS₀fin : S₀.Finite := hS.union (Set.finite_iUnion fun x ↦ (T x).finite_toSet)
  obtain ⟨S', hS₀S', hS'fin, hPID⟩ := exists_finite_superset_isPrincipalIdealRing S₀ hS₀fin
  refine ⟨S', Set.subset_union_left.trans hS₀S', hS'fin, hPID, fun x hx hx0 ↦ ?_⟩
  refine mem_unit_of_subset (fun v hv ↦ hS₀S' ?_) (hT ⟨x, hx, hx0⟩)
  exact Set.mem_union_right _ (Set.mem_iUnion_of_mem _ hv)

/-- **The `S`-units modulo squares are finite**: there are finitely many constants `e` such that
every `S`-unit is one of them times a square. -/
theorem exists_finset_forall_eq_mul_sq {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ E : Finset K, ∀ v ∈ S.unit K, ∃ e ∈ E, ∃ h : K, (v : K) = e * h ^ 2 := by
  classical
  have := S.unit_fg hS
  set H := (powMonoidHom (α := ↥(S.unit K)) 2).range
  have : H.FiniteIndex := Subgroup.finiteIndex_range_powMonoidHom_of_fg _ two_ne_zero
  have hfin := Set.finite_range fun q : ↥(S.unit K) ⧸ H ↦ (((q.out : ↥(S.unit K)) : Kˣ) : K)
  refine ⟨hfin.toFinset, fun v hv ↦ ?_⟩
  obtain ⟨⟨h, hh⟩, hgh⟩ := QuotientGroup.mk_out_eq_mul H ⟨v, hv⟩
  obtain ⟨w, rfl⟩ := hh
  refine ⟨_, hfin.mem_toFinset.mpr ⟨QuotientGroup.mk ⟨v, hv⟩, rfl⟩,
    (((w⁻¹ : ↥(S.unit K)) : Kˣ) : K), ?_⟩
  beta_reduce
  rw [hgh]
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_pow,
    Units.val_pow_eq_pow_val, InvMemClass.coe_inv, Units.val_inv_eq_inv_val, inv_pow]
  rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), mul_one]

/-- A Bézout identity for `z` against a product of elements that differ from it by units. -/
private theorem exists_mul_add_mul_prod_eq_one {S : Set (HeightOneSpectrum (𝓞 K))} {z : K}
    {s : Multiset K}
    (hs : ∀ w ∈ s, w ∈ S.integer K ∧ ∃ v ∈ S.unit K, (v : K) = w - z) :
    ∃ p ∈ S.integer K, ∃ q ∈ S.integer K, p * z + q * s.prod = 1 := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, zero_mem _, 1, one_mem _, by simp⟩
  | cons w s ih =>
    obtain ⟨p, hp, q, hq, hpq⟩ := ih fun w' hw' ↦ hs w' (Multiset.mem_cons_of_mem hw')
    obtain ⟨hw, v, hv, hvw⟩ := hs w (Multiset.mem_cons_self _ _)
    have hvi : ((v⁻¹ : Kˣ) : K) ∈ S.integer K := Set.mem_integer_of_mem_unit (inv_mem hv)
    have hv0 : (v : K) ≠ 0 := v.ne_zero
    have hsp : s.prod ∈ S.integer K :=
      Subalgebra.multiset_prod_mem _ fun w' hw' ↦ (hs w' (Multiset.mem_cons_of_mem hw')).1
    refine ⟨p - q * s.prod * ((v⁻¹ : Kˣ) : K), sub_mem hp (mul_mem (mul_mem hq hsp) hvi),
      q * ((v⁻¹ : Kˣ) : K), mul_mem hq hvi, ?_⟩
    rw [Multiset.prod_cons, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination (v : K) * hpq - q * s.prod * hvw

/-- **A coprime factor of a square is a square up to a unit.** Over a principal ring of
`S`-integers, if `z ^ m * ∏ w = u c ^ 2` with `m` odd, `u` an `S`-unit, `z`, `c` and every `w`
`S`-integers and every `w - z` an `S`-unit, then `z` is an `S`-unit times a square in `K`. -/
theorem exists_eq_mul_sq_of_pow_mul_prod_eq {S : Set (HeightOneSpectrum (𝓞 K))}
    [IsPrincipalIdealRing ↥(S.integer K)] {z c : K} {s : Multiset K} {m : ℕ} (hm : Odd m)
    (hz : z ∈ S.integer K) (hs : ∀ w ∈ s, w ∈ S.integer K ∧ ∃ v ∈ S.unit K, (v : K) = w - z)
    (hc : c ∈ S.integer K) {u : Kˣ} (hu : u ∈ S.unit K) (h : z ^ m * s.prod = u * c ^ 2) :
    ∃ v ∈ S.unit K, ∃ γ : K, z = v * γ ^ 2 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_add_mul_prod_eq_one hs
  have hsp : s.prod ∈ S.integer K := Subalgebra.multiset_prod_mem _ fun w hw ↦ (hs w hw).1
  let U : (↥(S.integer K))ˣ := S.unitEquivUnitsInteger K ⟨u⁻¹, inv_mem hu⟩
  have hU : ((U : ↥(S.integer K)) : K) = (u : K)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  have hcop : IsCoprime ((U : ↥(S.integer K)) * (⟨z, hz⟩ : ↥(S.integer K)) ^ m)
      ⟨s.prod, hsp⟩ := by
    have h1 : IsCoprime (⟨z, hz⟩ : ↥(S.integer K)) ⟨s.prod, hsp⟩ :=
      ⟨⟨p, hp⟩, ⟨q, hq⟩, Subtype.ext (by simpa using hpq)⟩
    exact (isCoprime_mul_unit_left_left U.isUnit _ _).mpr h1.pow_left
  have hprod : (U : ↥(S.integer K)) * (⟨z, hz⟩ : ↥(S.integer K)) ^ m * ⟨s.prod, hsp⟩ =
      ⟨c, hc⟩ ^ 2 := by
    refine Subtype.ext ?_
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hU]
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
  obtain ⟨d, W, hW⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  have hWK := congrArg (fun r : ↥(S.integer K) ↦ (r : K)) hW
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hU] at hWK
  obtain ⟨k, rfl⟩ := hm
  by_cases hz0 : z = 0
  · exact ⟨1, one_mem _, 0, by simp [hz0]⟩
  refine ⟨u * (S.unitEquivUnitsInteger K).symm W, mul_mem hu ((S.unitEquivUnitsInteger K).symm W).2,
    d / z ^ k, ?_⟩
  have key : (u : K) * ((W : ↥(S.integer K)) : K) * (d : K) ^ 2 = z ^ (2 * k + 1) := by
    rw [mul_assoc, mul_comm _ ((d : K) ^ 2), hWK, ← mul_assoc, mul_inv_cancel₀ u.ne_zero,
      one_mul]
  simp only [Units.val_mul, Set.unitEquivUnitsInteger_symm_apply_coe, Units.val_mk0]
  rw [div_pow, ← pow_mul, mul_div_assoc', key, eq_div_iff (pow_ne_zero _ hz0)]
  ring

/-- **An element whose square is an `S`-integer is an `S`-integer.** -/
theorem mem_integer_of_sq_mem {S : Set (HeightOneSpectrum (𝓞 K))} {x : K}
    (hx : x ^ 2 ∈ S.integer K) : x ∈ S.integer K :=
  (Set.mem_integer_iff_finitePlace _ x).mpr fun v hv ↦ by
    have := (Set.mem_integer_iff_finitePlace _ _).mp hx v hv
    rwa [map_pow, pow_le_one_iff_of_nonneg (apply_nonneg _ _) two_ne_zero] at this

/-- **An integral factor of a unit with an integral cofactor is a unit.** -/
theorem exists_mem_unit_of_mul_eq {S : Set (HeightOneSpectrum (𝓞 K))} {a b : K}
    (ha : a ∈ S.integer K) (hb : b ∈ S.integer K) {w : Kˣ} (hw : w ∈ S.unit K)
    (h : a * b = w) : ∃ u ∈ S.unit K, (u : K) = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact w.ne_zero (by rw [← h, zero_mul])
  refine ⟨Units.mk0 a ha0, (Set.mk0_mem_unit_iff_finitePlace _ ha0).mpr fun v hv ↦ ?_, rfl⟩
  have ha' := (Set.mem_integer_iff_finitePlace _ _).mp ha v hv
  have hb' := (Set.mem_integer_iff_finitePlace _ _).mp hb v hv
  have hw' := (Set.mem_unit_iff_finitePlace _ _).mp hw v hv
  rw [← h, map_mul] at hw'
  nlinarith [apply_nonneg (FinitePlace.mk v) a, apply_nonneg (FinitePlace.mk v) b]

end NumberField
