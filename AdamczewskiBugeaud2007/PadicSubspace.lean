/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RepetitionSubspaces
public import Mathlib.NumberTheory.Padics.PadicNumbers

-- Used only inside proofs.
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.PlacesOverInfinite
import DiophantineApproximation.RationalPlaces
import DiophantineApproximation.SubspaceAlgebraic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The Subspace Theorem at a prime

**The Subspace Theorem step of Adamczewski–Bugeaud 2007, §6.** The `p`-adic transcendence
criterion (Theorem 6) applies Schlickewei's `p`-adic Subspace Theorem over `ℚ` in three variables,
with the coordinate forms at `∞` and, at `p`, the system

```text
at p:           X 0,   X 1,   α X 0 - α X 1 - X 2
```

for an algebraic `α ∈ ℚ_p`, at the integer points `(p ^ s, 1, P)`. This file feeds that system to
Layer 6.3 of `DiophantineApproximation`, whose forms may have coefficients in any number field `F`
measured by an absolute value of `F` over the place in question; here `F = ℚ(α) ⊆ ℚ_p` and the
absolute value is the norm of `ℚ_p`.

## Main results

* `Rat.exists_finset_submodule_of_prod_abs_mul_prod_le`: **the Subspace Theorem over `ℚ` at `∞`
  and one prime**, with the coordinate forms at `∞` and a full system of algebraic forms at the
  prime, the hypothesis on the bare product of the values.
* `Padic.exists_finset_submodule_of_repetition`: the step for the system above.

## Implementation notes

⚠ **The roles of `∞` and the prime are swapped from the real case**
(`Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le`, Layer 7.4). There the interesting
forms live at `∞` and the coordinates at the primes of the base; here the interesting form lives
at `p`, where the digits converge, and `∞` only carries the size of the point. The height
estimate is the same: for an integer point, `H(x) ≤ |x|_∞ |x|_p`, and `|x|_p ≤ 1` lets the
hypothesis be stated with `|x|_∞` alone.

⚠ **`F` is a subfield of `ℚ_p`, not an abstract number field with a chosen place.** `ℚ⟮α⟯` is an
`IntermediateField ℚ ℚ_[p]`, so the norm of `ℚ_p` restricts to it, and that absolute value lies
over `padicNorm p` because `ℚ_p`'s norm does on `ℚ` (`Padic.eq_padicNorm`).

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §6; H. P. Schlickewei, *The `p`-adic
Thue–Siegel–Roth–Schmidt theorem*, Arch. Math. (Basel) **29** (1977), 267–270.
-/

public section

open Module Finset Height NumberField

namespace Rat

variable {ι : Type*} {F : Type*} [Field F] [NumberField F]

/-- **The Subspace Theorem over `ℚ` at `∞` and one prime `l`**, for the coordinate forms at `∞`
and a full system of linearly independent forms at `l` with coefficients in a number field `F`,
measured by an absolute value `W` of `F` over `l`. If the product of the sizes of the coordinates
of an integer point and of the values of the forms at `l` is at most its sup norm to the power
`-ε`, the point lies in one of finitely many proper rational subspaces. -/
theorem exists_finset_submodule_of_prod_abs_mul_prod_le [Fintype ι] [Nontrivial ι]
    (l : Nat.Primes) (W : AbsoluteValue F ℝ) (hW : W.LiesOver (Rat.finitePlace l).1)
    (L : ι → Dual F (ι → F)) (hL : LinearIndependent F L) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, |((x i : ℤ) : ℝ)|) * ∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ)))
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  obtain ⟨Winf, hWinf⟩ := NumberField.exists_liesOver_infinitePlace (F := F) Rat.infinitePlace
  set w : AbsoluteValue ℚ ℝ → AbsoluteValue F ℝ := fun u ↦
    if u = Rat.infinitePlace.1 then Winf.1 else W with hwdef
  set Lf : AbsoluteValue ℚ ℝ → ι → Dual F (ι → F) := fun u ↦
    if u = Rat.infinitePlace.1 then fun i ↦ LinearMap.proj i else L with hLfdef
  have hne : (Rat.finitePlace l).1 ≠ Rat.infinitePlace.1 := by
    rw [Rat.finitePlace_val]
    exact (Rat.infinitePlace_val_ne_padic l).symm
  have hwinf : w Rat.infinitePlace.1 = Winf.1 := by simp [hwdef]
  have hwfin : w (Rat.finitePlace l).1 = W := by
    simp only [hwdef]
    exact ite_eq_right_iff.mpr fun h ↦ absurd h hne
  have hLinf : Lf Rat.infinitePlace.1 = fun i ↦ LinearMap.proj i := by simp [hLfdef]
  have hLfin : Lf (Rat.finitePlace l).1 = L := by
    simp only [hLfdef]
    exact ite_eq_right_iff.mpr fun h ↦ absurd h hne
  obtain ⟨T, hTproper, hTmem⟩ := NumberField.exists_finset_submodule_of_approxProd_le_extension
    (K := ℚ) (F := F) {Rat.infinitePlace} {Rat.finitePlace l} w
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hwinf]; exact hWinf)
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hwfin]; exact hW)
    Lf (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hLinf]; exact linearIndependent_proj)
    (fun v hv ↦ by rw [Finset.mem_singleton.mp hv, hLfin]; exact hL)
    hε
  refine ⟨T, hTproper, fun x hx hle ↦ hTmem _ hx ?_⟩
  set n := Fintype.card ι with hn
  set Minf : ℝ := ⨆ i, Rat.infinitePlace ((x i : ℚ)) with hMinf
  set Mp : ℝ := ⨆ i, Rat.finitePlace l ((x i : ℚ)) with hMp
  set A : ℝ := ∏ i, |((x i : ℤ) : ℝ)| with hA
  set B : ℝ := ∏ i, W (L i fun k ↦ algebraMap ℚ F ((x k : ℚ))) with hB
  set H : ℝ := mulHeight (fun i ↦ ((x i : ℤ) : ℚ)) with hHdef
  have hMeq : Minf = ⨆ i, |((x i : ℤ) : ℝ)| := by
    simp only [hMinf, Rat.infinitePlace_apply, Rat.cast_abs, Rat.cast_intCast]
  have hHpos : 0 < H := mulHeight_pos _
  have hH : H ≤ Minf * Mp := by
    have h := mulHeight_intCast_le_iSup_mul_prod {l} hx
    rwa [Finset.prod_singleton] at h
  have hH' : H ≤ Minf := mulHeight_intCast_le_iSup Rat.infinitePlace hx
  have hinfval : (∏ i, w Rat.infinitePlace.1
        (Lf Rat.infinitePlace.1 i fun k ↦ algebraMap ℚ F ((x k : ℚ)))
          / ⨆ j, Rat.infinitePlace ((x j : ℚ))) = A / Minf ^ n := by
    have : (Winf.1).LiesOver Rat.infinitePlace.1 := hWinf
    rw [hwinf, hLinf, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [LinearMap.proj_apply,
      AbsoluteValue.apply_algebraMap_of_liesOver (v := Rat.infinitePlace.1) Winf.1,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply, Rat.cast_abs,
      Rat.cast_intCast]
  have hfinval : (∏ i, w (Rat.finitePlace l).1
        (Lf (Rat.finitePlace l).1 i fun k ↦ algebraMap ℚ F ((x k : ℚ)))
          / ⨆ j, Rat.finitePlace l ((x j : ℚ))) = B / Mp ^ n := by
    rw [hwfin, hLfin, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have happrox : approxProd {Rat.infinitePlace} {Rat.finitePlace l} w Lf
      (fun i ↦ ((x i : ℤ) : ℚ)) = (A * B) / (Minf * Mp) ^ n := by
    rw [approxProd, Finset.prod_singleton, Finset.prod_singleton,
      NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one, hinfval,
      hfinval, mul_pow, div_mul_div_comm]
  have hAB : A * B ≤ H ^ (-ε) := by
    refine le_trans ?_ (Real.rpow_le_rpow_of_nonpos hHpos hH' (by linarith))
    rw [hMeq]
    exact hle
  rw [happrox, show (-(n : ℝ) - ε) = -ε - n by ring, Real.rpow_sub hHpos, Real.rpow_natCast]
  exact div_le_div₀ (Real.rpow_nonneg hHpos.le _) hAB (pow_pos hHpos n)
    (pow_le_pow_left₀ hHpos.le hH n)

end Rat

namespace Padic

variable {p : ℕ} [Fact p.Prime]

open IntermediateField in
/-- **The Subspace Theorem step for a `p`-adic repetition**: the coordinate forms at `∞`, and
`X 0`, `X 1`, `α X 0 - α X 1 - X 2` at `p` for an algebraic `α ∈ ℚ_p`. The integer points
`(p ^ s, 1, P)` of the `p`-adic transcendence criterion are points of this system. -/
theorem exists_finset_submodule_of_repetition {α : ℚ_[p]} (hα : IsAlgebraic ℚ α) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : Fin 3 → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, |((x i : ℤ) : ℝ)|) * (‖((x 0 : ℤ) : ℚ_[p])‖ * ‖((x 1 : ℤ) : ℚ_[p])‖
            * ‖α * (x 0 : ℚ_[p]) - α * (x 1 : ℚ_[p]) - (x 2 : ℚ_[p])‖)
          ≤ (⨆ i, |((x i : ℤ) : ℝ)|) ^ (-ε) →
        ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V := by
  classical
  have hint : IsIntegral ℚ α := hα.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hint
  have hnf : NumberField ℚ⟮α⟯ := {}
  set W : AbsoluteValue ℚ⟮α⟯ ℝ :=
    (NormedField.toAbsoluteValue ℚ_[p]).comp (algebraMap ℚ⟮α⟯ ℚ_[p]).injective with hWdef
  have hWapply : ∀ z : ℚ⟮α⟯, W z = ‖(algebraMap ℚ⟮α⟯ ℚ_[p]) z‖ := fun z ↦ rfl
  have hcast : ∀ q : ℚ, (algebraMap ℚ⟮α⟯ ℚ_[p]) (algebraMap ℚ ℚ⟮α⟯ q) = q := fun q ↦ by
    rw [← IsScalarTower.algebraMap_apply ℚ ℚ⟮α⟯ ℚ_[p]]
    simp
  set l : Nat.Primes := ⟨p, Fact.out⟩ with hl
  have hW : W.LiesOver (Rat.finitePlace l).1 := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def, Rat.finitePlace_val, Rat.AbsoluteValue.padic_eq_padicNorm]
    change W (algebraMap ℚ ℚ⟮α⟯ q) = _
    rw [hWapply, hcast, eq_padicNorm]
  set a : ℚ⟮α⟯ := ⟨α, mem_adjoin_simple_self ℚ α⟩ with hadef
  have ha : (algebraMap ℚ⟮α⟯ ℚ_[p]) a = α := rfl
  have hacoe : ((a : ℚ⟮α⟯) : ℚ_[p]) = α := rfl
  set c : Fin 3 → Fin 3 → ℚ⟮α⟯ := ![![1, 0, 0], ![0, 1, 0], ![a, -a, -1]] with hcdef
  have hc : LinearIndependent ℚ⟮α⟯ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : g 2 = 0 := by simpa [hcdef, Fin.sum_univ_three] using congrFun hg 2
    intro i
    fin_cases i
    · simpa [hcdef, Fin.sum_univ_three, h2] using congrFun hg 0
    · simpa [hcdef, Fin.sum_univ_three, h2] using congrFun hg 1
    · exact h2
  obtain ⟨T, hT, hmem⟩ := Rat.exists_finset_submodule_of_prod_abs_mul_prod_le l W hW
    (fun i ↦ Module.Dual.sumForm (c i)) (Module.Dual.linearIndependent_sumForm hc) hε
  refine ⟨T, hT, fun x hx hle ↦ hmem x hx (le_trans (le_of_eq ?_) hle)⟩
  congr 1
  rw [Fin.prod_univ_three]
  simp only [Module.Dual.sumForm_apply, Fin.sum_univ_three, hcdef, hWapply, map_add, map_mul,
    hcast]
  simp [ha, hacoe, sub_eq_add_neg]

end Padic
