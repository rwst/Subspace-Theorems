/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SimultaneousSubspaces

-- Used only inside proofs.
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.RationalPlaces
import DiophantineApproximation.SAdicHeight

/-!
# The Subspace Theorem at the primes of the base

**Layer 7.4, the Subspace Theorem step** (Adamczewski–Bugeaud–Luca 2004; Adamczewski–Bugeaud
2007, §4). The transcendence criterion for stammering sequences applies the Subspace Theorem over
`ℚ` in three variables, at `∞` and at the primes dividing the base `b`:

```text
at ∞:           X 0,   X 1,   ξ X 0 - ξ X 1 - X 2
at l ∣ b:       X 0,   X 1,   X 2
```

at the integer points `(b ^ (r + s), b ^ r, p)`. This file feeds that system to Layer 6.3.

## Main results

* `Rat.mulHeight_intCast_le_iSup_mul_prod`: the height of an integer point is at most the product
  of its sup norms at `∞` and at any finite set of primes.
* `Rat.linearIndependent_proj`: the coordinate forms are linearly independent.
* `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le`: **the Subspace Theorem over `ℚ` at
  `∞` and a finite set of primes**, with a full system of algebraic forms at `∞` and the
  coordinate forms at the primes, the hypothesis on the bare product of the values.
* `Real.exists_finset_submodule_of_repetition`: the step for the system above.

## Implementation notes

⚠ **The finite places are what 7.3 did not need, and they cost one inequality.** Layer 7.3's
`Rat.exists_finset_submodule_of_prod_le` is the case `S = ∅` of the statement proved here. With
primes in `S` the central quantity of the Subspace Theorem divides by the local sup norms at those
primes too, and the height of the point has to be bounded by the sup norms at `∞` and at `S`
together; for an integer point every local sup norm away from `S` is at most `1`, and that is
`Rat.mulHeight_intCast_le_iSup_mul_prod`. The absolute values of the number field above the
primes of `S` are chosen once, by `NumberField.exists_liesOver_finitePlace`, and only their values
on `ℚ` are ever used, because the forms at the primes are the coordinates.

⚠ **The gain is at the primes, and the Subspace Theorem sees it only because they are there.** At
`∞` alone the product of the three forms at `(b ^ (r + s), b ^ r, p)` is about
`b ^ (2 r + s) · b ^ (r + s) · b ^ (- r - w s)`, which is small only for `w > 2 + 2 r / s`; the
factor `b ^ (-(2 r + s))` from the `l`-adic sizes of the first two coordinates is what brings the
threshold down to `w > 1`.

This is part of Layer 7.4 of the `DiophantineApproximation` roadmap.
-/

public section

open Module Finset Height NumberField

namespace Rat

variable {ι : Type*}

/-- **The height of an integer point is carried by `∞` and any set of primes.** Away from `S`
every local sup norm of an integer point is at most `1`. -/
theorem mulHeight_intCast_le_iSup_mul_prod [Finite ι] (S : Finset Nat.Primes) {x : ι → ℤ}
    (hx : (fun i ↦ (x i : ℚ)) ≠ 0) :
    mulHeight (fun i ↦ (x i : ℚ))
      ≤ (⨆ i, Rat.infinitePlace ((x i : ℚ))) * ∏ l ∈ S, ⨆ i, Rat.finitePlace l ((x i : ℚ)) := by
  classical
  have harch : (∏ u : InfinitePlace ℚ, (⨆ i, u ((x i : ℚ))) ^ u.mult)
      = ⨆ i, Rat.infinitePlace ((x i : ℚ)) := by
    rw [Fintype.prod_unique]
    have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
    rw [hd, NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one]
  set M : FinitePlace ℚ → ℝ := fun v ↦ ⨆ i, v ((x i : ℚ)) with hM
  set G : FinitePlace ℚ → ℝ := fun v ↦ if v ∈ S.image Rat.finitePlace then M v else 1 with hG
  have hM0 : ∀ v, 0 ≤ M v := fun v ↦ Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _
  have hGsupp : Function.mulSupport G ⊆ ((S.image Rat.finitePlace : Finset _) : Set _) := by
    intro v hv
    by_contra hvS
    exact hv (by simp only [hG]; rw [ite_eq_right (by simpa using hvS)])
  have hMG : M ≤ G := fun v ↦ by
    simp only [hG]
    split_ifs
    · exact le_rfl
    · exact Real.iSup_le (fun i ↦ v.apply_intCast_le_one (x i)) zero_le_one
  have hfin : ∏ᶠ v, M v ≤ ∏ l ∈ S, ⨆ i, Rat.finitePlace l ((x i : ℚ)) := by
    calc ∏ᶠ v, M v ≤ ∏ᶠ v, G v :=
          finprod_le_finprod₀ (NumberField.FinitePlace.hasFiniteMulSupport_iSup hx) hM0
            ((Finset.finite_toSet _).subset hGsupp) hMG
      _ = ∏ v ∈ S.image Rat.finitePlace, G v :=
          finprod_eq_finsetProd_of_mulSupport_subset G hGsupp
      _ = ∏ v ∈ S.image Rat.finitePlace, M v :=
          Finset.prod_congr rfl fun v hv ↦ by simp only [hG]; rw [ite_eq_left hv]
      _ = ∏ l ∈ S, ⨆ i, Rat.finitePlace l ((x i : ℚ)) :=
          Finset.prod_image fun l _ l' _ h ↦ Rat.finitePlace_injective h
  rw [NumberField.mulHeight_eq hx, harch]
  exact mul_le_mul_of_nonneg_left hfin (Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _)

/-- The coordinate forms are linearly independent. -/
theorem linearIndependent_proj [Finite ι] {F : Type*} [Field F] :
    LinearIndependent F fun i : ι ↦ (LinearMap.proj i : Dual F (ι → F)) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h : (∑ i, g i • (LinearMap.proj i : Dual F (ι → F))) (Pi.single k 1) = 0 := by
    rw [hg]; simp
  simpa [LinearMap.sum_apply, Pi.single_apply] using h

variable {F : Type*} [Field F] [NumberField F]

/-- **The Subspace Theorem over `ℚ` at `∞` and a finite set of primes**, for a full system of
linearly independent forms at `∞` with coefficients in a number field and the coordinate forms at
the primes of `S`. If the product of the values of the forms at `∞` and of the `l`-adic sizes of
the coordinates, `l ∈ S`, is at most the sup norm of an integer point to the power `-ε`, the point
lies in one of finitely many proper rational subspaces. With `S = ∅` this is
`Rat.exists_finset_submodule_of_prod_le`. -/
theorem exists_finset_submodule_of_prod_mul_prod_padicNorm_le [Fintype ι] [Nontrivial ι]
    (W : AbsoluteValue F ℝ) (hW : W.LiesOver Rat.infinitePlace.1)
    (L : ι → Dual F (ι → F)) (hL : LinearIndependent F L) (S : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ))))
            * ∏ l ∈ S, ∏ i, ((padicNorm (l : ℕ) ((x i : ℤ) : ℚ) : ℚ) : ℝ)
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hex : ∀ l : Nat.Primes, ∃ w : AbsoluteValue F ℝ, w.LiesOver (Rat.finitePlace l).1 :=
    fun l ↦ NumberField.exists_liesOver_finitePlace (Rat.finitePlace l)
  choose wf hwf using hex
  set w : AbsoluteValue ℚ ℝ → AbsoluteValue F ℝ := fun u ↦
    if h : ∃ l : Nat.Primes, (Rat.finitePlace l).1 = u then wf h.choose else W with hwdef
  set Lf : AbsoluteValue ℚ ℝ → ι → Dual F (ι → F) := fun u ↦
    if u = Rat.infinitePlace.1 then L else fun i ↦ LinearMap.proj i with hLfdef
  have hnofin : ¬ ∃ l : Nat.Primes, (Rat.finitePlace l).1 = Rat.infinitePlace.1 := by
    rintro ⟨l, hl⟩
    rw [Rat.finitePlace_val] at hl
    exact Rat.infinitePlace_val_ne_padic l hl.symm
  have hwinf : w Rat.infinitePlace.1 = W := by simp only [hwdef]; rw [dite_eq_right hnofin]
  have hwfin : ∀ l, w (Rat.finitePlace l).1 = wf l := fun l ↦ by
    have h : ∃ l' : Nat.Primes, (Rat.finitePlace l').1 = (Rat.finitePlace l).1 := ⟨l, rfl⟩
    simp only [hwdef]
    rw [dite_eq_left h]
    exact congrArg wf (Rat.finitePlace_injective (Subtype.ext h.choose_spec))
  have hLinf : Lf Rat.infinitePlace.1 = L := by simp [hLfdef]
  have hLfin : ∀ l, Lf (Rat.finitePlace l).1 = fun i ↦ LinearMap.proj i := fun l ↦ by
    simp only [hLfdef]
    refine ite_eq_right fun h ↦ ?_
    rw [Rat.finitePlace_val] at h
    exact Rat.infinitePlace_val_ne_padic l h.symm
  obtain ⟨T, hTproper, hTmem⟩ := NumberField.exists_finset_submodule_of_approxProd_le_extension
    (K := ℚ) (F := F) {Rat.infinitePlace} (S.image Rat.finitePlace) w
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hwinf]; exact hW)
    (fun v hv ↦ by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hv
      rw [hwfin]; exact hwf l)
    Lf (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hLinf]; exact hL)
    (fun v hv ↦ by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hv
      rw [hLfin]; exact linearIndependent_proj)
    hε
  refine ⟨T, hTproper, fun x hx hle ↦ hTmem _ hx ?_⟩
  set n := Fintype.card ι with hn
  set Minf : ℝ := ⨆ i, Rat.infinitePlace ((x i : ℚ)) with hMinf
  set Mf : Nat.Primes → ℝ := fun l ↦ ⨆ i, Rat.finitePlace l ((x i : ℚ)) with hMf
  set A : ℝ := ∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ))) with hA
  set B : Nat.Primes → ℝ := fun l ↦ ∏ i, ((padicNorm (l : ℕ) ((x i : ℤ) : ℚ) : ℚ) : ℝ) with hB
  set H : ℝ := mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) with hHdef
  have hMeq : Minf = ⨆ i, |((x i : ℤ) : ℝ)| := by
    simp only [hMinf, Rat.infinitePlace_apply, Rat.cast_abs, Rat.cast_intCast]
  have hHpos : 0 < H := mulHeight_pos _
  have hH : H ≤ Minf * ∏ l ∈ S, Mf l := mulHeight_intCast_le_iSup_mul_prod S hx
  have hH' : H ≤ Minf := mulHeight_intCast_le_iSup Rat.infinitePlace hx
  have hfinval : ∀ l : Nat.Primes, (∏ i, w (Rat.finitePlace l).1
        (Lf (Rat.finitePlace l).1 i fun k ↦ algebraMap ℚ F ((x k : ℚ)))
          / ⨆ j, Rat.finitePlace l ((x j : ℚ))) = B l / Mf l ^ n := fun l ↦ by
    have : (wf l).LiesOver (Rat.finitePlace l).1 := hwf l
    rw [hwfin, hLfin, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [LinearMap.proj_apply,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := (Rat.finitePlace l).1) (wf l),
      ← NumberField.FinitePlace.coe_apply, Rat.finitePlace_apply]
  have happrox : approxProd {Rat.infinitePlace} (S.image Rat.finitePlace) w Lf
      (fun i ↦ ((x i : ℤ) : ℚ)) = (A * ∏ l ∈ S, B l) / (Minf * ∏ l ∈ S, Mf l) ^ n := by
    rw [approxProd, Finset.prod_singleton, hwinf, hLinf,
      NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
      Finset.prod_image fun l _ l' _ h ↦ Rat.finitePlace_injective h]
    simp only [hfinval]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_div_distrib,
      Finset.prod_pow, mul_pow, div_mul_div_comm]
  have hAB : A * ∏ l ∈ S, B l ≤ H ^ (-ε) := by
    refine le_trans ?_ (Real.rpow_le_rpow_of_nonpos hHpos hH' (by linarith))
    rw [hMeq]
    exact hle
  rw [happrox, show (-(n : ℝ) - ε) = -ε - n by ring, Real.rpow_sub hHpos, Real.rpow_natCast]
  exact div_le_div₀ (Real.rpow_nonneg hHpos.le _) hAB (pow_pos hHpos n)
    (pow_le_pow_left₀ hHpos.le hH n)

end Rat

namespace Real

open IntermediateField in
/-- **The Subspace Theorem step for a repetition**: the system `X 0`, `X 1`,
`ξ X 0 - ξ X 1 - X 2` at `∞` for a real algebraic `ξ`, and the coordinate forms at the primes of
`S`. The integer points `(b ^ (r + s), b ^ r, p)` of the transcendence criterion are points of
this system. -/
theorem exists_finset_submodule_of_repetition {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (S : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : Fin 3 → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        |((x 0 : ℤ) : ℝ)| * |((x 1 : ℤ) : ℝ)| * |ξ * (x 0 : ℝ) - ξ * (x 1 : ℝ) - (x 2 : ℝ)|
            * ∏ l ∈ S, ∏ i, ((padicNorm (l : ℕ) ((x i : ℤ) : ℚ) : ℚ) : ℝ)
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hint : IsIntegral ℚ ξ := hξ.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
  have hnf : NumberField ℚ⟮ξ⟯ := {}
  set W : AbsoluteValue ℚ⟮ξ⟯ ℝ := AbsoluteValue.abs.comp (algebraMap ℚ⟮ξ⟯ ℝ).injective
    with hWdef
  have hWapply : ∀ z : ℚ⟮ξ⟯, W z = |(algebraMap ℚ⟮ξ⟯ ℝ) z| := fun z ↦ rfl
  have hW : W.LiesOver Rat.infinitePlace.1 := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def]
    simp only [AbsoluteValue.comp_apply]
    rw [hWapply, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
    simp
  set a : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hadef
  have ha : (algebraMap ℚ⟮ξ⟯ ℝ) a = ξ := rfl
  have hacoe : ((a : ℚ⟮ξ⟯) : ℝ) = ξ := rfl
  set c : Fin 3 → Fin 3 → ℚ⟮ξ⟯ := ![![1, 0, 0], ![0, 1, 0], ![a, -a, -1]] with hcdef
  have hc : LinearIndependent ℚ⟮ξ⟯ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : g 2 = 0 := by simpa [hcdef, Fin.sum_univ_three] using congrFun hg 2
    intro i
    fin_cases i
    · simpa [hcdef, Fin.sum_univ_three, h2] using congrFun hg 0
    · simpa [hcdef, Fin.sum_univ_three, h2] using congrFun hg 1
    · exact h2
  obtain ⟨T, hT, hmem⟩ := Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le W hW
    (fun i ↦ Module.Dual.sumForm (c i)) (Module.Dual.linearIndependent_sumForm hc) S hε
  refine ⟨T, hT, fun x hx hle ↦ hmem x hx (le_trans (le_of_eq ?_) hle)⟩
  have hcast : ∀ q : ℚ, (algebraMap ℚ⟮ξ⟯ ℝ) (algebraMap ℚ ℚ⟮ξ⟯ q) = q := fun q ↦ by
    rw [← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ]; simp
  congr 1
  rw [Fin.prod_univ_three]
  simp only [Module.Dual.sumForm_apply, Fin.sum_univ_three, hcdef, hWapply, map_add, map_mul,
    hcast]
  simp [ha, hacoe, sub_eq_add_neg]

end Real

/-! ### Acceptance criteria -/

/-- **Conformance: with no primes this is Layer 7.3's step**,
`Rat.exists_finset_submodule_of_prod_le`: the product over the empty set of primes is `1`. -/
example {F : Type*} [Field F] [NumberField F] {ι : Type*} [Fintype ι] [Nontrivial ι]
    (W : AbsoluteValue F ℝ) (hW : W.LiesOver Rat.infinitePlace.1)
    (L : ι → Dual F (ι → F)) (hL : LinearIndependent F L) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ))))
            ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  obtain ⟨T, hT, h⟩ := Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le W hW L hL ∅ hε
  exact ⟨T, hT, fun x hx hle ↦ h x hx (by rwa [Finset.prod_empty, mul_one])⟩

