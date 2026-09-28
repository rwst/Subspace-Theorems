/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproxProd
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

-- Used only inside proofs.
import DiophantineApproximation.LinearFormSubspaces
import DiophantineApproximation.PlacesOverFinite
import DiophantineApproximation.PlacesOverInfinite
import DiophantineApproximation.RepetitionSubspaces
import DiophantineApproximation.SimultaneousSubspaces
import DiophantineApproximation.SubspaceAlgebraic
import DiophantineApproximation.UnitNormalization
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The Subspace Theorem over `ℚ(β)`

**The Subspace Theorem step of Theorem 5 of Adamczewski–Bugeaud 2007, §4**, for a real algebraic
integer `β` whose conjugates other than `β` lie in the closed unit disc (a Pisot or a Salem number).
Over the number field `K = ℚ(β) ⊆ ℝ`, the Subspace Theorem is applied in three variables with the
places `S` = the infinite places of `K` together with the finite places where `|β|_v < 1`, and
the forms

```text
at the place β ↪ ℝ:     X 0,   X 1,   α X 0 - α X 1 - X 2
elsewhere in S:         X 0,   X 1,   X 2
```

for a real algebraic `α`, at the points `(β ^ m, β ^ r, y)` with `y` an algebraic integer of `K`.
The forms have their coefficients in the number field `F = K(α) ⊆ ℝ`, measured by the absolute
value of `ℝ`.

## Main results

* `Real.adjoinPlace`: the real place of `ℚ(β)` given by its inclusion into `ℝ`.
* `Real.apply_gen_le_one`: at every other infinite place, `|β|_v ≤ 1`.
* `Real.ringHom_eq_of_apply_gen_eq`, `Real.apply_gen_mem_aroots`: a complex embedding of `ℚ(β)`
  sends `β` to a conjugate, and to `β` itself only if it is the inclusion.
* `Real.exists_finset_submodule_of_pow_pow`: **the Subspace Theorem step**, with the hypothesis on
  the bare product of the values at the infinite places.

## Implementation notes

⚠ **The finite places carry the gain and drop out of the statement.** `β` is a unit away from the
finite places of `S`, and the first two coordinates `β ^ m`, `β ^ r` have product `1` over `S` by
the product formula. So the product of the forms over `S` is the product of the third ones, and at
the finite places those are at most `1` because `y` is integral. For the same reason the height
of the point is at most the product of its sup norms at the infinite places. What is left is a
condition on the value `|α β ^ m - α β ^ r - y|` at the real place and on the sizes `|y|_v` of the
third coordinate at the other infinite places.

⚠ **The paper's normalization by `1 / d` is Mathlib's `mult`.** The product formula and the
height are both taken with the weights `mult v ∈ {1, 2}` of the infinite places, so no `d`-th root
appears.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Annals of Mathematics **165** (2007), 547–565, §4.
-/

@[expose] public section

open IntermediateField NumberField Module Finset Height Polynomial

namespace Real

/-- **The real place of `ℚ(β)`**, given by its inclusion into `ℝ`. -/
noncomputable def adjoinPlace (β : ℝ) : InfinitePlace ℚ⟮β⟯ :=
  InfinitePlace.mk (Complex.ofRealHom.comp (algebraMap ℚ⟮β⟯ ℝ))

theorem adjoinPlace_apply (β : ℝ) (y : ℚ⟮β⟯) : adjoinPlace β y = |algebraMap ℚ⟮β⟯ ℝ y| := by
  simp [adjoinPlace, InfinitePlace.apply]

theorem isReal_adjoinPlace (β : ℝ) : (adjoinPlace β).IsReal :=
  InfinitePlace.isReal_mk_iff.mpr <| ComplexEmbedding.isReal_iff.mpr <| RingHom.ext fun y ↦ by
    simp [ComplexEmbedding.conjugate_coe_eq]

/-- **A complex embedding of `ℚ(β)` is determined by the image of `β`**: one sending `β` to `β` is
the inclusion. -/
theorem ringHom_eq_of_apply_gen_eq {β : ℝ} {φ : ℚ⟮β⟯ →+* ℂ}
    (h : φ (AdjoinSimple.gen ℚ β) = (β : ℂ)) :
    φ = Complex.ofRealHom.comp (algebraMap ℚ⟮β⟯ ℝ) := by
  have hb : algebraMap ℚ⟮β⟯ ℝ (AdjoinSimple.gen ℚ β) = β := AdjoinSimple.algebraMap_gen ℚ β
  have he : φ.toRatAlgHom = (Complex.ofRealHom.comp (algebraMap ℚ⟮β⟯ ℝ)).toRatAlgHom := by
    refine adjoin_algHom_ext ℚ fun x hx ↦ ?_
    have hx' := (Set.mem_singleton_iff.mp hx).symm
    subst hx'
    change φ (AdjoinSimple.gen ℚ β) = Complex.ofRealHom (algebraMap ℚ⟮β⟯ ℝ (AdjoinSimple.gen ℚ β))
    rw [h, hb]
    rfl
  exact RingHom.ext fun y ↦ congrArg (fun f : ℚ⟮β⟯ →ₐ[ℚ] ℂ ↦ f y) he

/-- **The image of `β` under a complex embedding of `ℚ(β)` is a conjugate of `β`.** -/
theorem apply_gen_mem_aroots {β : ℝ} (hint : IsIntegral ℚ β) (φ : ℚ⟮β⟯ →+* ℂ) :
    φ (AdjoinSimple.gen ℚ β) ∈ (minpoly ℚ β).aroots ℂ := by
  rw [mem_aroots]
  refine ⟨minpoly.ne_zero hint, ?_⟩
  have h0 : aeval (AdjoinSimple.gen ℚ β) (minpoly ℚ β) = 0 := by
    apply (algebraMap ℚ⟮β⟯ ℝ).injective
    rw [← aeval_algebraMap_apply, AdjoinSimple.algebraMap_gen, minpoly.aeval, map_zero]
  have := Polynomial.aeval_algHom_apply φ.toRatAlgHom (AdjoinSimple.gen ℚ β) (minpoly ℚ β)
  rw [h0, map_zero] at this
  exact this

/-- **The conjugates of `β` other than `β` itself.** If they all lie in the closed unit disc, then
`|β|_v ≤ 1` at every infinite place `v` of `ℚ(β)` other than the real place given by the
inclusion. -/
theorem apply_gen_le_one {β : ℝ} (hint : IsIntegral ℚ β)
    (hconj : ∀ z ∈ (minpoly ℚ β).aroots ℂ, z ≠ (β : ℂ) → ‖z‖ ≤ 1) {v : InfinitePlace ℚ⟮β⟯}
    (hv : v ≠ adjoinPlace β) : v (AdjoinSimple.gen ℚ β) ≤ 1 := by
  rw [← v.norm_embedding_eq]
  by_cases h : v.embedding (AdjoinSimple.gen ℚ β) = (β : ℂ)
  · refine absurd ?_ hv
    rw [← v.mk_embedding, ringHom_eq_of_apply_gen_eq h, adjoinPlace]
  · exact hconj _ (apply_gen_mem_aroots hint _) h

end Real

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place is at most `1` on the algebraic integers. -/
theorem apply_le_one_of_isIntegral (v : FinitePlace K) {y : K} (hy : IsIntegral ℤ y) :
    v y ≤ 1 := by
  have h := FinitePlace.norm_le_one (K := K) (v := v.maximalIdeal) (⟨y, hy⟩ : 𝓞 K)
  rwa [FinitePlace.norm_embedding_eq] at h

/-- A finite place is not an infinite place: it is at most `1` at `2`. -/
theorem val_ne_val (v : FinitePlace K) (u : InfinitePlace K) : v.1 ≠ u.1 := by
  intro h
  have h1 : v ((2 : ℤ) : K) ≤ 1 := apply_intCast_le_one v 2
  have h2 : u ((2 : ℤ) : K) = 2 := by
    rw [← u.norm_embedding_eq, map_intCast]
    simp
  rw [FinitePlace.coe_apply, h, ← InfinitePlace.coe_apply, h2] at h1
  norm_num at h1

end NumberField.FinitePlace

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

omit [NumberField F] in
open scoped Classical in
/-- **The central quantity of the Subspace Theorem at a point whose forms split off an `S`-unit.**
If at every place of `S` the product of the forms at `x` is `|z|_v` times a factor `g v`, where
`z` is a unit away from `S`, then by the product formula the central quantity is the product of
the factors divided by `H(x) ^ #ι`. -/
theorem approxProd_eq_of_prod_eq {ι : Type*} [Fintype ι] {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    {x : ι → K} (hx : x ≠ 0) {z : K} (hz : z ≠ 0) (hzS : ∀ v : FinitePlace K, v ∉ Sfin → v z = 1)
    {g : InfinitePlace K → ℝ} {gF : FinitePlace K → ℝ}
    (hI : ∀ v : InfinitePlace K,
      ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) = v z * g v)
    (hF : ∀ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) = v z * gF v)
    (hsup : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ j, v (x j) = 1) :
    approxProd univ Sfin w L x
      = ((∏ v, g v ^ v.mult) * ∏ v ∈ Sfin, gF v) / mulHeight x ^ Fintype.card ι := by
  set n := Fintype.card ι with hn
  have hPQ : (∏ v : InfinitePlace K, v z ^ v.mult) * ∏ v ∈ Sfin, v z = 1 := by
    have h := NumberField.prod_abs_eq_one (K := K) hz
    rwa [finprod_eq_prod_of_mulSupport_subset (s := Sfin) _ fun v hv ↦ by
      by_contra hvS
      exact hv (hzS v hvS)] at h
  have eI : ∀ v : InfinitePlace K,
      (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult
        = v z ^ v.mult * g v ^ v.mult / ((⨆ j, v (x j)) ^ v.mult) ^ n := by
    intro v
    rw [prod_div_distrib, prod_const, card_univ, hI v, div_pow, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm n]
  have eF : ∀ v ∈ Sfin, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      = v z * gF v / (⨆ j, v (x j)) ^ n := by
    intro v hv
    rw [prod_div_distrib, prod_const, card_univ, hF v hv]
  rw [mulHeight_eq_prod_of_forall_iSup_eq_one hx hsup, approxProd, prod_congr rfl fun v _ ↦ eI v,
    prod_congr rfl eF, prod_div_distrib, prod_div_distrib, prod_mul_distrib, prod_mul_distrib,
    prod_pow, prod_pow, div_mul_div_comm, mul_mul_mul_comm, hPQ, one_mul, mul_pow]

open scoped Classical in
open FinitePlace in
/-- **The Subspace Theorem step for a repetition in base `b`**, over a number field `K` with a
real place `v₀`. Let `b ≠ 0` be an algebraic integer of `K`, `ℓ` a linear form over a finite
extension `F` with `ℓ (e 2) ≠ 0`, `W` an absolute value of `F` over `v₀`, and `ε > 0`. The points
`(b ^ m, b ^ r, y)` with `y` an algebraic integer, for which `|ℓ (x)|_W` times the sizes
`|y|_v ^ mult v` at the other infinite places is at most the product of the sup norms at the
infinite places to the power `-ε`, lie in finitely many proper subspaces. The places are the
infinite places together with the finite places where `|b|_v < 1`, with the forms `X 0, X 1, ℓ`
at `v₀` and the coordinates elsewhere. -/
theorem exists_finset_submodule_of_pow_pow {v0 : InfinitePlace K} (hv0 : v0.IsReal)
    {W : AbsoluteValue F ℝ} (hW : W.LiesOver v0.1) {ℓ : Dual F (Fin 3 → F)}
    (hℓ : ℓ (Pi.single 2 1) ≠ 0) {b : K} (hb : IsIntegral ℤ b) (hb0 : b ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (Fin 3 → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ (m r : ℕ) (y : K), IsIntegral ℤ y →
        W (ℓ fun j ↦ algebraMap K F (![b ^ m, b ^ r, y] j))
            * ∏ v ∈ univ.erase v0, v y ^ v.mult
          ≤ (∏ v : InfinitePlace K, (⨆ j, v (![b ^ m, b ^ r, y] j)) ^ v.mult) ^ (-ε) →
        ∃ V ∈ T, ![b ^ m, b ^ r, y] ∈ V := by
  have hbfin : ∀ v : FinitePlace K, v b ≤ 1 := fun v ↦ apply_le_one_of_isIntegral v hb
  set c : Fin 3 → Dual F (Fin 3 → F) := ![LinearMap.proj 0, LinearMap.proj 1, ℓ] with hcdef
  have hc : LinearIndependent F c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := fun t ↦ LinearMap.congr_fun hg t
    have h2 : g 2 = 0 := by simpa [hcdef, Fin.sum_univ_three, hℓ] using e (Pi.single 2 1)
    have h0 : g 0 = 0 := by simpa [hcdef, Fin.sum_univ_three, h2] using e (Pi.single 0 1)
    have h1 : g 1 = 0 := by simpa [hcdef, Fin.sum_univ_three, h2] using e (Pi.single 1 1)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  -- absolute values of `F` over the other places
  have hext : ∀ u : AbsoluteValue K ℝ, ∃ W' : AbsoluteValue F ℝ,
      ((∃ v : InfinitePlace K, v.1 = u) ∨ (∃ v : FinitePlace K, v.1 = u)) → W'.LiesOver u := by
    intro u
    by_cases hi : ∃ v : InfinitePlace K, v.1 = u
    · obtain ⟨v, rfl⟩ := hi
      obtain ⟨W', hW'⟩ := exists_liesOver_infinitePlace (F := F) v
      exact ⟨W'.1, fun _ ↦ hW'⟩
    · by_cases hf : ∃ v : FinitePlace K, v.1 = u
      · obtain ⟨v, rfl⟩ := hf
        obtain ⟨W', hW'⟩ := exists_liesOver_finitePlace (F := F) v
        exact ⟨W', fun _ ↦ hW'⟩
      · exact ⟨W, fun h ↦ (h.elim hi hf).elim⟩
  choose Wc hWc using hext
  set w : AbsoluteValue K ℝ → AbsoluteValue F ℝ := fun u ↦ if u = v0.1 then W else Wc u
    with hwdef
  set L : AbsoluteValue K ℝ → Fin 3 → Dual F (Fin 3 → F) := fun u ↦
    if u = v0.1 then c else fun i ↦ LinearMap.proj i with hLdef
  have hw0 : w v0.1 = W := by simp [hwdef]
  have hL0 : L v0.1 = c := by simp [hLdef]
  have hwne : ∀ u, u ≠ v0.1 → w u = Wc u := fun u hu ↦ by simp [hwdef, hu]
  have hLne : ∀ u, u ≠ v0.1 → L u = fun i ↦ LinearMap.proj i := fun u hu ↦ by simp [hLdef, hu]
  have hwI : ∀ v ∈ (univ : Finset (InfinitePlace K)), (w v.1).LiesOver v.1 := by
    intro v _
    by_cases h : v.1 = v0.1
    · rw [h, hw0]; exact hW
    · rw [hwne _ h]; exact hWc _ (Or.inl ⟨v, rfl⟩)
  have hfne : ∀ v : FinitePlace K, v.1 ≠ v0.1 := fun v ↦ val_ne_val v v0
  -- the finite places where `b` is not a unit
  have hsupp : (Function.mulSupport fun v : FinitePlace K ↦ v b).Finite :=
    FinitePlace.hasFiniteMulSupport hb0
  set Sfin : Finset (FinitePlace K) := hsupp.toFinset with hSfindef
  have hSfin : ∀ v : FinitePlace K, v ∉ Sfin → v b = 1 := fun v hv ↦ by
    rw [hSfindef, Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
    exact hv
  have hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1 := fun v _ ↦ by
    rw [hwne _ (hfne v)]; exact hWc _ (Or.inr ⟨v, rfl⟩)
  have hLI : ∀ v ∈ (univ : Finset (InfinitePlace K)), LinearIndependent F (L v.1) := by
    intro v _
    by_cases h : v.1 = v0.1
    · rw [h, hL0]; exact hc
    · rw [hLne _ h]; exact Rat.linearIndependent_proj
  have hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1) := fun v _ ↦ by
    rw [hLne _ (hfne v)]; exact Rat.linearIndependent_proj
  obtain ⟨T, hTp, hTmem⟩ := exists_finset_submodule_of_approxProd_le_extension
    univ Sfin w hwI hwF L hLI hLF hε
  refine ⟨T, hTp, fun m r y hy hle ↦ ?_⟩
  set x : Fin 3 → K := ![b ^ m, b ^ r, y] with hxdef
  have hx0 : x ≠ 0 := fun h ↦ pow_ne_zero m hb0 (by simpa [hxdef] using congrFun h 0)
  refine hTmem x hx0 ?_
  have hyfin : ∀ v : FinitePlace K, v y ≤ 1 := fun v ↦ apply_le_one_of_isIntegral v hy
  have hproj : ∀ u : AbsoluteValue K ℝ, u ≠ v0.1 → (Wc u).LiesOver u →
      ∏ i, w u (L u i fun j ↦ algebraMap K F (x j)) = u (b ^ (m + r)) * u y := by
    intro u hu hlo
    rw [hwne u hu, hLne u hu, Fin.prod_univ_three, LinearMap.proj_apply, LinearMap.proj_apply,
      LinearMap.proj_apply, AbsoluteValue.apply_algebraMap_of_liesOver (v := u),
      AbsoluteValue.apply_algebraMap_of_liesOver (v := u),
      AbsoluteValue.apply_algebraMap_of_liesOver (v := u)]
    change u (b ^ m) * u (b ^ r) * u y = _
    rw [pow_add, map_mul]
  set ℓx : ℝ := W (ℓ fun j ↦ algebraMap K F (x j)) with hℓx
  set g : InfinitePlace K → ℝ := fun v ↦ if v = v0 then ℓx else v y with hgdef
  have hI : ∀ v : InfinitePlace K,
      ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) = v (b ^ (m + r)) * g v := by
    intro v
    by_cases hv : v = v0
    · rw [hv, hw0, hL0, Fin.prod_univ_three]
      change W (algebraMap K F (b ^ m)) * W (algebraMap K F (b ^ r)) * ℓx = _
      rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := v0.1),
        AbsoluteValue.apply_algebraMap_of_liesOver (v := v0.1), pow_add, map_mul]
      simp only [hgdef, ↓reduceIte]
      rfl
    · have h1 : v.1 ≠ v0.1 := fun h ↦ hv (Subtype.ext h)
      rw [hproj v.1 h1 (hWc _ (Or.inl ⟨v, rfl⟩))]
      simp only [hgdef, hv, ↓reduceIte]
      rfl
  have hsupfin : ∀ v : FinitePlace K, (⨆ j, v (x j)) ≤ 1 := fun v ↦ ciSup_le fun j ↦ by
    fin_cases j
    · simpa [hxdef] using pow_le_one₀ (apply_nonneg v b) (hbfin v)
    · simpa [hxdef] using pow_le_one₀ (apply_nonneg v b) (hbfin v)
    · simpa [hxdef] using hyfin v
  have hsup : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ j, v (x j) = 1 := fun v hv ↦
    le_antisymm (hsupfin v) (le_ciSup_of_le (Finite.bddAbove_range _) 0 (by
      simp [hxdef, hSfin v hv]))
  have hA := approxProd_eq_of_prod_eq (g := g) (gF := fun v ↦ v y) hx0
    (pow_ne_zero (m + r) hb0) (fun v hv ↦ by rw [map_pow, hSfin v hv, one_pow]) hI
    (fun v _ ↦ hproj v.1 (hfne v) (hWc _ (Or.inr ⟨v, rfl⟩))) hsup
  have hHpos : 0 < mulHeight x := mulHeight_pos x
  have hHle : mulHeight x ≤ ∏ v : InfinitePlace K, (⨆ j, v (x j)) ^ v.mult := by
    rw [mulHeight_eq_prod_of_forall_iSup_eq_one hx0 hsup]
    exact mul_le_of_le_one_right (prod_nonneg fun v _ ↦ pow_nonneg
      (Real.iSup_nonneg fun j ↦ v.1.nonneg _) _)
      (prod_le_one₀ (fun v _ ↦ Real.iSup_nonneg fun j ↦ v.1.nonneg _) fun v _ ↦ hsupfin v)
  have hg : (∏ v : InfinitePlace K, g v ^ v.mult) * ∏ v ∈ Sfin, v y
      ≤ ℓx * ∏ v ∈ univ.erase v0, v y ^ v.mult := by
    rw [← mul_prod_erase univ (fun v ↦ g v ^ v.mult) (mem_univ v0)]
    have he : ∏ v ∈ univ.erase v0, g v ^ v.mult = ∏ v ∈ univ.erase v0, v y ^ v.mult :=
      prod_congr rfl fun v hv ↦ by simp [hgdef, (mem_erase.mp hv).1]
    rw [he, hv0.mult_eq_one, pow_one]
    simp only [hgdef, ↓reduceIte]
    exact mul_le_of_le_one_right (mul_nonneg (W.nonneg _) (prod_nonneg fun v _ ↦
      pow_nonneg (v.1.nonneg _) _)) (prod_le_one₀ (fun v _ ↦ v.1.nonneg _) fun v _ ↦ hyfin v)
  rw [hA, Fintype.card_fin, show (-((3 : ℕ) : ℝ) - ε) = -ε - (3 : ℕ) by ring,
    Real.rpow_sub hHpos, Real.rpow_natCast]
  refine div_le_div_of_nonneg_right ?_ (pow_nonneg hHpos.le 3)
  exact (hg.trans hle).trans (Real.rpow_le_rpow_of_nonpos hHpos hHle (by linarith))

end NumberField

namespace Real

open scoped Classical in
/-- **The Subspace Theorem step for a repetition in base `β`** (Adamczewski–Bugeaud 2007, §4).
Let `β ≠ 0` be a real algebraic integer, `α` a real algebraic number and `ε > 0`. The points
`(β ^ m, β ^ r, y)` of `ℚ(β) ^ 3`, with `y` an algebraic integer, for which
`|α β ^ m - α β ^ r - y|` times the sizes `|y|_v ^ mult v` at the infinite places `v` other than
the real place is at most the product of the sup norms at the infinite places to the power `-ε`,
lie in finitely many proper subspaces. -/
theorem exists_finset_submodule_of_pow_pow {β : ℝ} [NumberField ℚ⟮β⟯] (hβ : β ≠ 0)
    (hint : IsIntegral ℤ β) {α : ℝ} (hα : IsAlgebraic ℚ α) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ⟮β⟯ (Fin 3 → ℚ⟮β⟯)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ (m r : ℕ) (y : ℚ⟮β⟯), IsIntegral ℤ y →
        |α * β ^ m - α * β ^ r - algebraMap ℚ⟮β⟯ ℝ y|
            * ∏ v ∈ univ.erase (adjoinPlace β), v y ^ v.mult
          ≤ (∏ v : InfinitePlace ℚ⟮β⟯,
              (⨆ j, v (![AdjoinSimple.gen ℚ β ^ m, AdjoinSimple.gen ℚ β ^ r, y] j)) ^ v.mult)
            ^ (-ε) →
        ∃ V ∈ T, ![AdjoinSimple.gen ℚ β ^ m, AdjoinSimple.gen ℚ β ^ r, y] ∈ V := by
  set K := ℚ⟮β⟯ with hKdef
  set b : K := AdjoinSimple.gen ℚ β with hbdef
  have hb : algebraMap K ℝ b = β := AdjoinSimple.algebraMap_gen ℚ β
  have hbint : IsIntegral ℤ b :=
    (isIntegral_algHom_iff (algebraMap K ℝ).toIntAlgHom (algebraMap K ℝ).injective).mp
      (by rw [RingHom.toIntAlgHom_apply, hb]; exact hint)
  have hb0 : b ≠ 0 := fun h ↦ hβ (by rw [← hb, h, map_zero])
  have hαK : IsIntegral K α := hα.isIntegral.tower_top
  set F := K⟮α⟯ with hFdef
  have : FiniteDimensional K F := adjoin.finiteDimensional hαK
  have : NumberField F := NumberField.of_module_finite K F
  set W : AbsoluteValue F ℝ :=
    (NormedField.toAbsoluteValue ℝ).comp (algebraMap F ℝ).injective with hWdef
  have hWapp : ∀ z : F, W z = |algebraMap F ℝ z| := fun z ↦ rfl
  have hKF : ∀ y : K, algebraMap F ℝ (algebraMap K F y) = algebraMap K ℝ y := fun y ↦
    (IsScalarTower.algebraMap_apply K F ℝ y).symm
  have hW : W.LiesOver (adjoinPlace β).1 := ⟨AbsoluteValue.ext fun y ↦ by
    change W (algebraMap K F y) = adjoinPlace β y
    rw [hWapp, hKF, adjoinPlace_apply]⟩
  set aF : F := AdjoinSimple.gen K α with haFdef
  have haF : algebraMap F ℝ aF = α := AdjoinSimple.algebraMap_gen K α
  set ℓ : Dual F (Fin 3 → F) := Module.Dual.sumForm ![aF, -aF, -1] with hℓdef
  have hℓ : ℓ (Pi.single 2 1) ≠ 0 := by simp [hℓdef, Fin.sum_univ_three]
  obtain ⟨T, hT, hmem⟩ := NumberField.exists_finset_submodule_of_pow_pow
    (isReal_adjoinPlace β) hW hℓ hbint hb0 hε
  refine ⟨T, hT, fun m r y hy hle ↦ hmem m r y hy (le_trans (le_of_eq ?_) hle)⟩
  congr 1
  rw [hWapp]
  congr 1
  have hb' : ((b : K) : ℝ) = β := hb
  have ha' : ((aF : F) : ℝ) = α := haF
  simp [hℓdef, Fin.sum_univ_three, hb', ha']
  ring

end Real
