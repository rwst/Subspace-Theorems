/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormDavenport
public import QuantitativeSubspace.TwistedSubspaceHeight

/-!
# Inequalities in an exterior power

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §11 ((11.10)–(11.21), Lemmas 11.4, 11.5) and (6.10).

EF13 pass from a system `(L, c)` on `Ωⁿ` to its `(n-k)`-th exterior power: the forms
`L̂_I^{(v)} = L_{i_1}^{(v)} ∧ ⋯ ∧ L_{i_{n-k}}^{(v)}` and exponents `ĉ_{I,v} = Σ_{i ∈ I} c_{iv}`,
indexed by the `(n-k)`-element subsets `I` (11.10), and the points
`ĥ_J = h_{j_1} ∧ ⋯ ∧ h_{j_{n-k}}` built from the vectors `h_j` of Davenport's lemma
(`FormSystem.exists_davenport`, EF13 Lemma 11.3). Here the forms of `L̂^{(v)}` are the rows of the
compound matrix `Matrix.compound`, and `ĥ_J` is the Plücker vector `plucker`.

* Off `v₀`, Davenport's bounds (11.6) for the `h_j` give the local bounds (11.14), (11.17) for the
  `ĥ_J` with respect to `L̂` and the weights `â_I = ∏_{i ∈ I} a_i`: Hadamard's inequality at the
  infinite places (the factor `(n-k)! / n^{n-k} ≤ 1`) and the ultrametric inequality at the finite
  ones.
* Above `v₀`, where the forms are the coordinates, Davenport's bounds (11.7)
  `|h_{j, π(i)}| ≤ B min(λ_i, λ_j)` give `|ĥ_J(I)| ≤ B^{n-k} min(ν_{π̂⁻¹(I)}, ν_J)` with
  `ν_J = ∏_{j ∈ J} λ_j` (11.12). For `J ≠ I_N = {k, …, n-1}` this is at most
  `B^{n-k} topBound λ π I`, which is `ν_{π̂⁻¹(I)}` except that `ν_{I_N}` is replaced by
  `ν_{I_N} λ_{k-1}/λ_k` (11.15). Its product over `I` is `(λ_0 ⋯ λ_{n-1})^{C(n-1, n-k-1)}
  λ_{k-1}/λ_k`, the identity behind (11.21).
* Lemma 11.4 (11.18)–(11.20): the sums, bounds and global sums of the `ĉ_{I,v}` off `v₀`.
* Lemma 11.5: the entries of `(L̂^{(v)})⁻¹ = (L^{(v)⁻¹})^{∧(n-k)}` are minors of `L^{(v)⁻¹}`, whose
  entries are quotients `d / det L^{(v)}` with `d` an `n × n` determinant of forms of the system
  once the coordinate forms belong to it. The product of the local bounds is
  `p!^{[K:ℚ]} (H_L / Δ_L)^p`, and with (7.4) at most `p! H_L^{p C(r, n)}` absolutely. EF13 have
  `H_L^{R^n}`, using the complementary-minor identity instead.

The inequalities (11.21), (11.22) themselves need EF13 Lemmas 9.3, 9.4 and the constant `C_2` of
Theorem 8.1, and Lemma 11.6 needs Lemma 10.3; they belong to the proof of Theorem 8.1 (Q4.1).

## Main definitions

* `NumberField.FormSystem.exteriorPower L p`: the system `L̂` of (11.10).
* `NumberField.FormWeight.exteriorPower a p`, `NumberField.FormExponent.exteriorPower c p`: the
  weights `â` and the exponents `ĉ` of (11.10); `FormExponent.weight_exteriorPower`.
* `NumberField.topSet k`: EF13's `I_N`; `NumberField.topBound λ π I`: the bound of (11.15).

## Main results

* `NumberField.FormSystem.archFactor_exteriorPower_plucker_le`,
  `NumberField.FormSystem.finFactor_exteriorPower_plucker_le`: (11.14), (11.17) off `v₀`.
* `NumberField.FinitePlace.apply_plucker_le_topBound`: (11.14), (11.17) above `v₀`.
* `NumberField.prod_topBound`, `NumberField.sum_logb_topBound`: the identity behind (11.21).
* `NumberField.FormExponent.sum_exteriorPower_arch`, `abs_exteriorPower_arch_le`,
  `sum_iSup_abs_exteriorPower_le` (and the finite-place versions): Lemma 11.4 (11.18)–(11.20).
* `NumberField.FormSystem.apply_inv_exteriorPower_arch_le`, `apply_inv_exteriorPower_fin_le`,
  `prod_invBound`, `prod_invBound_rpow_le`: Lemma 11.5.
* `Finset.prod_powersetCard_prod`: `∏_s ∏_{i ∈ s} f i = ∏_i f i ^ C(n-1, p-1)`.
* `Matrix.abv_det_le_of_col`, `NumberField.FinitePlace.apply_det_le_of_col`: determinant bounds.
-/

@[expose] public section

open Finset Module Matrix
open exteriorPower (plucker plucker_apply)

namespace Finset

variable {ι : Type*} [Fintype ι]

/-- Each element of `ι` lies in `C(#ι - 1, p - 1)` of the `p`-element subsets. -/
theorem card_filter_mem_powersetCard [DecidableEq ι] {p : ℕ} (hp : 1 ≤ p) (i : ι) :
    #{s ∈ powersetCard p (univ : Finset ι) | i ∈ s} = (Fintype.card ι - 1).choose (p - 1) := by
  have h := card_filter_powersetCard_subset {i} univ p (by simp) (by simpa using hp)
  simp only [singleton_subset_iff, card_singleton, card_univ] at h
  exact h

/-- **The product over the `p`-element subsets of the products over their elements**:
`∏_s ∏_{i ∈ s} f i = ∏_i f i ^ C(#ι - 1, p - 1)`. -/
@[to_additive /-- **The sum over the `p`-element subsets of the sums over their elements**:
`Σ_s Σ_{i ∈ s} f i = C(#ι - 1, p - 1) • Σ_i f i`. -/]
theorem prod_powersetCard_prod {M : Type*} [CommMonoid M] {p : ℕ} (hp : 1 ≤ p) (f : ι → M) :
    ∏ s ∈ powersetCard p (univ : Finset ι), ∏ i ∈ s, f i =
      ∏ i, f i ^ (Fintype.card ι - 1).choose (p - 1) := by
  classical
  calc ∏ s ∈ powersetCard p (univ : Finset ι), ∏ i ∈ s, f i
      = ∏ s ∈ powersetCard p (univ : Finset ι), ∏ i, if i ∈ s then f i else 1 :=
        prod_congr rfl fun s _ ↦ by rw [prod_ite_mem, univ_inter]
    _ = ∏ i, ∏ s ∈ powersetCard p (univ : Finset ι), if i ∈ s then f i else 1 := prod_comm
    _ = ∏ i, f i ^ (Fintype.card ι - 1).choose (p - 1) := by
        refine prod_congr rfl fun i _ ↦ ?_
        rw [prod_ite, prod_const_one, mul_one, prod_const, card_filter_mem_powersetCard hp]

/-- **EF13 (11.19)**: if `Σ_i c_i = 0` and `c_i ≤ M` for all `i`, then the sum of the `c_i` over a
nonempty proper subset is at most `(#ι - 1) M` in absolute value. -/
theorem abs_sum_le_of_sum_eq_zero {c : ι → ℝ} (h0 : ∑ i, c i = 0) {M : ℝ} (hM : ∀ i, c i ≤ M)
    {s : Finset ι} (hs : s.Nonempty) (hs' : s ≠ univ) :
    |∑ i ∈ s, c i| ≤ (Fintype.card ι - 1 : ℕ) * M := by
  classical
  obtain ⟨i₀, -⟩ := id hs
  have hM0 : 0 ≤ M := by
    by_contra h
    have : ∑ i, c i < 0 :=
      sum_neg (fun i _ ↦ (hM i).trans_lt (not_le.1 h)) ⟨i₀, mem_univ _⟩
    linarith
  have hsc : sᶜ.Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]
    exact hs'
  have hcard : #s + #sᶜ = Fintype.card ι := card_add_card_compl s
  have h1 : #s ≤ Fintype.card ι - 1 := by have := hsc.card_pos; omega
  have h2 : #sᶜ ≤ Fintype.card ι - 1 := by have := hs.card_pos; omega
  have hsum : ∑ i ∈ s, c i + ∑ i ∈ sᶜ, c i = 0 := by rw [sum_add_sum_compl, h0]
  have hle (t : Finset ι) (ht : #t ≤ Fintype.card ι - 1) :
      ∑ i ∈ t, c i ≤ (Fintype.card ι - 1 : ℕ) * M :=
    (sum_le_sum fun i _ ↦ hM i).trans <| by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hM0
  rw [abs_le]
  constructor
  · linarith [hle sᶜ h2]
  · exact hle s h1

end Finset

namespace Set.powersetCard

variable {ι : Type*} [LinearOrder ι] {p : ℕ}

/-- The product over the enumeration of a `p`-element subset is the product over its elements. -/
@[to_additive /-- The sum over the enumeration of a `p`-element subset is the sum over its
elements. -/]
theorem prod_ofFinEmbEquiv_symm {M : Type*} [CommMonoid M] (s : Set.powersetCard ι p)
    (f : ι → M) : ∏ q, f (ofFinEmbEquiv.symm s q) = ∏ i ∈ s.val, f i := by
  rw [ofFinEmbEquiv_symm_apply]
  conv_rhs => rw [← map_orderEmbOfFin_univ s.val s.prop, prod_map]
  rfl

omit [LinearOrder ι] in
variable [Fintype ι] in
/-- The product over the `p`-element subsets as a product over a finset. -/
@[to_additive /-- The sum over the `p`-element subsets as a sum over a finset. -/]
theorem prod_eq_prod_powersetCard {M : Type*} [CommMonoid M] (f : Finset ι → M) :
    ∏ s : Set.powersetCard ι p, f s.val =
      ∏ s ∈ Finset.powersetCard p (Finset.univ : Finset ι), f s := by
  rw [← prod_subtype (Finset.powersetCard p Finset.univ) (p := fun s ↦ s ∈ Set.powersetCard ι p)
    (fun s ↦ by simp) f]

end Set.powersetCard

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]

/-- A determinant is at most the sum over the permutations of the products of the absolute values
of the entries. -/
theorem abv_det_le_sum (f : AbsoluteValue R ℝ) (M : Matrix n n R) :
    f M.det ≤ ∑ σ : Equiv.Perm n, ∏ i, f (M (σ i) i) := by
  rw [det_apply]
  refine (f.sum_le _ _).trans (sum_le_sum fun σ _ ↦ ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, Units.smul_def]

/-- **Hadamard-type bound**: if the entries of the `j`-th column are at most `b j`, then the
determinant is at most `#n ! ∏_j b j`. -/
theorem abv_det_le_of_col (f : AbsoluteValue R ℝ) (M : Matrix n n R) {b : n → ℝ}
    (hb : ∀ i j, f (M i j) ≤ b j) : f M.det ≤ (Fintype.card n).factorial * ∏ j, b j := by
  refine (abv_det_le_sum f M).trans ?_
  calc ∑ σ : Equiv.Perm n, ∏ i, f (M (σ i) i) ≤ ∑ _σ : Equiv.Perm n, ∏ j, b j :=
        sum_le_sum fun σ _ ↦ prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ hb _ _
    _ = (Fintype.card n).factorial * ∏ j, b j := by
        rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

end Matrix

namespace NumberField.FinitePlace

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The ultrametric bound for a determinant**: if every product along a permutation is at most
`B`, so is the determinant. -/
theorem apply_det_le (w : FinitePlace E) (M : Matrix n n E) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ σ : Equiv.Perm n, ∏ i, w (M (σ i) i) ≤ B) : w M.det ≤ B := by
  rw [det_apply]
  refine apply_sum_le w _ hB fun σ _ ↦ ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;>
    simpa [hσ, Units.smul_def, map_prod] using h σ

/-- If the entries of the `j`-th column are at most `b j`, then the determinant is at most
`∏_j b j`. -/
theorem apply_det_le_of_col (w : FinitePlace E) (M : Matrix n n E) {b : n → ℝ}
    (hb : ∀ i j, w (M i j) ≤ b j) : w M.det ≤ ∏ j, b j :=
  apply_det_le w M (prod_nonneg fun j _ ↦ (apply_nonneg _ _).trans (hb j j)) fun _ ↦
    prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun _ _ ↦ hb _ _

end NumberField.FinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

namespace FinitePlace

variable {E : Type*} [Field E] [NumberField E]

/-- **EF13 (11.14) above `v₀`**: if `|x_{r,i}|_w ≤ (D min(μ_i, ν_r))^m`, then the Plücker
coordinates of `x_0 ∧ ⋯ ∧ x_{p-1}` are at most `(D^p min(∏_{i ∈ s} μ_i, ∏_r ν_r))^m`. -/
theorem apply_plucker_le (w : FinitePlace E) {p : ℕ} {x : Fin p → ι → E} {D : ℝ} (hD : 0 ≤ D)
    {μ : ι → ℝ} {ν : Fin p → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ r, 0 ≤ ν r) (m : ℕ)
    (h : ∀ r i, w (x r i) ≤ (D * min (μ i) (ν r)) ^ m) (s : Set.powersetCard ι p) :
    w (plucker p x s) ≤ (D ^ p * min (∏ i ∈ s.val, μ i) (∏ r, ν r)) ^ m := by
  have hmin : 0 ≤ min (∏ i ∈ s.val, μ i) (∏ r, ν r) :=
    le_min (prod_nonneg fun i _ ↦ hμ i) (prod_nonneg fun r _ ↦ hν r)
  rw [plucker_apply]
  refine apply_det_le w _ (by positivity) fun σ ↦ ?_
  set e := Set.powersetCard.ofFinEmbEquiv.symm s
  calc ∏ q, w (Matrix.of (fun r q ↦ x r (e q)) (σ q) q)
      ≤ ∏ q, (D * min (μ (e q)) (ν (σ q))) ^ m :=
        prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun q _ ↦ h _ _
    _ = (D ^ p * ∏ q, min (μ (e q)) (ν (σ q))) ^ m := by
        rw [prod_pow, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    _ ≤ (D ^ p * min (∏ i ∈ s.val, μ i) (∏ r, ν r)) ^ m := by
        gcongr
        · exact mul_nonneg (pow_nonneg hD _) (prod_nonneg fun q _ ↦ le_min (hμ _) (hν _))
        refine le_min ?_ ?_
        · rw [← Set.powersetCard.prod_ofFinEmbEquiv_symm s μ]
          exact prod_le_prod₀ (fun q _ ↦ le_min (hμ _) (hν _)) fun q _ ↦ min_le_left _ _
        · rw [← Equiv.prod_comp σ ν]
          exact prod_le_prod₀ (fun q _ ↦ le_min (hμ _) (hν _)) fun q _ ↦ min_le_right _ _

end FinitePlace

namespace FormWeight

/-- **The weights of the exterior power**: `â_{s,v} = ∏_{i ∈ s} a_{iv}` for a `p`-element subset
`s`, the weights matching EF13's `ĉ` of (11.10). -/
noncomputable def exteriorPower (a : FormWeight K ι) (p : ℕ) :
    FormWeight K (Set.powersetCard ι p) where
  arch v s := ∏ i ∈ s.val, a.arch v i
  arch_pos v _ := prod_pos fun i _ ↦ a.arch_pos v i
  fin v s := ∏ i ∈ s.val, a.fin v i
  fin_pos v _ := prod_pos fun i _ ↦ a.fin_pos v i
  finite_setOf_fin_ne_one := a.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv <| by
    funext s
    simp [h]

end FormWeight

namespace FormExponent

/-- **EF13 (11.10)**: the exponents `ĉ_{s,v} = Σ_{i ∈ s} c_{iv}` of the exterior power, for
`p`-element subsets `s`. -/
noncomputable def exteriorPower (c : FormExponent K ι) (p : ℕ) :
    FormExponent K (Set.powersetCard ι p) where
  arch v s := ∑ i ∈ s.val, c.arch v i
  fin v s := ∑ i ∈ s.val, c.fin v i
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext s
    simp [h]

omit [Fintype ι] [LinearOrder ι] in
/-- The weights `Q ^ ĉ` of the exterior power are the weights `â` built from `Q ^ c`. -/
theorem weight_exteriorPower (c : FormExponent K ι) (p : ℕ) {Q : ℝ} (hQ : 0 < Q) :
    (c.exteriorPower p).weight hQ = (c.weight hQ).exteriorPower p := by
  have harch : ((c.exteriorPower p).weight hQ).arch = ((c.weight hQ).exteriorPower p).arch := by
    funext v s
    change Q ^ ((∑ i ∈ s.val, c.arch v i) * _ / _) = ∏ i ∈ s.val, Q ^ (c.arch v i * _ / _)
    rw [sum_mul, sum_div, Real.rpow_sum_of_pos hQ]
  have hfin : ((c.exteriorPower p).weight hQ).fin = ((c.weight hQ).exteriorPower p).fin := by
    funext v s
    change Q ^ ((∑ i ∈ s.val, c.fin v i) * _) = ∏ i ∈ s.val, Q ^ (c.fin v i * _)
    rw [sum_mul, Real.rpow_sum_of_pos hQ]
  generalize (c.exteriorPower p).weight hQ = b at harch hfin
  cases b
  cases harch
  cases hfin
  rfl

end FormExponent

namespace FormSystem

variable (L : FormSystem K ι) (a : FormWeight K ι)

/-- **EF13 (11.10)**: the exterior power `L̂` of a system of forms, whose forms at `v` are the
`L_{i_1}^{(v)} ∧ ⋯ ∧ L_{i_p}^{(v)}`, i.e. the rows of the `p`-th compound matrix of `L^{(v)}`. -/
noncomputable def exteriorPower (p : ℕ) : FormSystem K (Set.powersetCard ι p) where
  arch v := (L.arch v).compound p
  arch_det_ne_zero v := det_compound_ne_zero p (L.arch_det_ne_zero v)
  fin v := (L.fin v).compound p
  fin_det_ne_zero v := det_compound_ne_zero p (L.fin_det_ne_zero v)
  finite_range_fin := (L.finite_range_fin.image fun M ↦ M.compound p).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨L.fin v, ⟨v, rfl⟩, rfl⟩

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField K] [NumberField E] in
/-- **EF13 (6.10)**: `(L_{i_1} ∧ ⋯ ∧ L_{i_p})(x_1 ∧ ⋯ ∧ x_p) = det(L_{i_k}(x_l))`, in matrix form:
the compound matrix acts on Plücker coordinates as the matrix acts on vectors. -/
theorem compound_map_mulVec_plucker (M : Matrix ι ι K) {p : ℕ} (x : Fin p → ι → E) :
    (M.compound p).map (algebraMap K E) *ᵥ plucker p x =
      plucker p fun r ↦ M.map (algebraMap K E) *ᵥ x r := by
  rw [← compound_map, compound_mulVec_plucker]

omit [NumberField E] in
/-- **EF13 (11.14), infinite places**: if every `x_r` has local factor at most `1/n` at an
infinite place `w`, then `x_0 ∧ ⋯ ∧ x_{p-1}` has local factor at most `1` for `L̂` and `â`. -/
theorem archFactor_exteriorPower_plucker_le {p : ℕ} (hp : p ≤ Fintype.card ι)
    (w : InfinitePlace E) {x : Fin p → ι → E}
    (hx : ∀ r, L.archFactor a w (x r) ≤ (Fintype.card ι : ℝ)⁻¹) :
    (L.exteriorPower p).archFactor (a.exteriorPower p) w (plucker p x) ≤ 1 := by
  set v := w.comap (algebraMap K E)
  set n := Fintype.card ι
  have hn : (p.factorial : ℝ) * ((n : ℝ)⁻¹) ^ p ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp0.trans_le hp
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hn0 _)]
    exact_mod_cast (Nat.factorial_le_pow p).trans (Nat.pow_le_pow_left hp p)
  have hy (r : Fin p) (i : ι) :
      w (((L.arch v).map (algebraMap K E) *ᵥ x r) i) ≤ a.arch v i * (n : ℝ)⁻¹ := by
    have h1 : w (((L.arch v).map (algebraMap K E) *ᵥ x r) i) / a.arch v i ≤ (n : ℝ)⁻¹ :=
      (le_ciSup (Finite.bddAbove_range _) i).trans (hx r)
    rwa [div_le_iff₀ (a.arch_pos v i), mul_comm] at h1
  have : Nonempty (Set.powersetCard ι p) := Set.powersetCard.nonempty_iff.2 hp
  refine ciSup_le fun s ↦ ?_
  have hpos : 0 < ∏ i ∈ s.val, a.arch v i := prod_pos fun i _ ↦ a.arch_pos v i
  change w ((((L.arch v).compound p).map (algebraMap K E) *ᵥ plucker p x) s) /
    ∏ i ∈ s.val, a.arch v i ≤ 1
  rw [compound_map_mulVec_plucker, plucker_apply, div_le_one hpos]
  calc w (Matrix.of fun r q ↦ ((L.arch v).map (algebraMap K E) *ᵥ x r)
        (Set.powersetCard.ofFinEmbEquiv.symm s q)).det
      ≤ (Fintype.card (Fin p)).factorial *
          ∏ q, a.arch v (Set.powersetCard.ofFinEmbEquiv.symm s q) * (n : ℝ)⁻¹ :=
        abv_det_le_of_col w.1 _ fun r q ↦ hy r _
    _ = p.factorial * ((n : ℝ)⁻¹) ^ p * ∏ i ∈ s.val, a.arch v i := by
        rw [Fintype.card_fin, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
          Set.powersetCard.prod_ofFinEmbEquiv_symm]
        ring
    _ ≤ ∏ i ∈ s.val, a.arch v i := mul_le_of_le_one_left hpos.le hn

/-- **EF13 (11.14), finite places**: if every `x_r` has local factor at most `1` at a finite
place `w`, then so has `x_0 ∧ ⋯ ∧ x_{p-1}` for `L̂` and `â`. -/
theorem finFactor_exteriorPower_plucker_le {p : ℕ} (w : FinitePlace E) {x : Fin p → ι → E}
    (hx : ∀ r, L.finFactor a w (x r) ≤ 1) :
    (L.exteriorPower p).finFactor (a.exteriorPower p) w (plucker p x) ≤ 1 := by
  set v := w.under K
  set e := w.localDegree K
  have hy (r : Fin p) (i : ι) :
      w (((L.fin v).map (algebraMap K E) *ᵥ x r) i) ≤ a.fin v i ^ e := by
    have h1 : w (((L.fin v).map (algebraMap K E) *ᵥ x r) i) / a.fin v i ^ e ≤ 1 :=
      (le_ciSup (Finite.bddAbove_range _) i).trans (hx r)
    rwa [div_le_one (pow_pos (a.fin_pos v i) _)] at h1
  rcases isEmpty_or_nonempty (Set.powersetCard ι p) with hs | hs
  · simp [finFactor]
  refine ciSup_le fun s ↦ ?_
  have hpos : 0 < (∏ i ∈ s.val, a.fin v i) ^ e := pow_pos (prod_pos fun i _ ↦ a.fin_pos v i) _
  change w ((((L.fin v).compound p).map (algebraMap K E) *ᵥ plucker p x) s) /
    (∏ i ∈ s.val, a.fin v i) ^ e ≤ 1
  rw [compound_map_mulVec_plucker, plucker_apply, div_le_one hpos, ← prod_pow,
    ← Set.powersetCard.prod_ofFinEmbEquiv_symm]
  exact FinitePlace.apply_det_le_of_col w _ fun r q ↦ hy r _

end FormSystem

/-! ### The exponents above `v₀` (EF13 (11.12), (11.15)–(11.17), (11.21)) -/

section TopExponents

variable {n : ℕ} (k : Fin n)

/-- The top `(n - k)`-element subset `{k, …, n - 1}` of `Fin n`, EF13's `I_N`. -/
def topSet : Set.powersetCard (Fin n) (n - k) :=
  ⟨univ.filter fun i : Fin n ↦ (k : ℕ) ≤ i, by
    have : (univ.filter fun i : Fin n ↦ (k : ℕ) ≤ i) = Ici k := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_Ici]
      exact Iff.rfl
    simp only [Set.powersetCard.mem_iff]
    rw [this, Fin.card_Ici]⟩

theorem mem_topSet {i : Fin n} : i ∈ (topSet k).val ↔ (k : ℕ) ≤ i := by
  simp [topSet]

variable {k} {lam : Fin n → ℝ}

/-- **The products `ν_J = ∏_{j ∈ J} λ_j` off the top subset** (EF13 (11.12)): for increasing
`λ > 0` and `0 < k`, every `(n - k)`-element subset `J ≠ I_N` has
`ν_J ≤ ν_{I_N} λ_{k-1} / λ_k = ν_{I_{N-1}}`. -/
theorem prod_le_prod_topSet_mul (hk : 0 < (k : ℕ)) (hpos : ∀ i, 0 < lam i) (hmono : Monotone lam)
    {J : Set.powersetCard (Fin n) (n - k)} (hJ : J ≠ topSet k) :
    ∏ j ∈ J.val, lam j ≤
      (∏ i ∈ (topSet k).val, lam i) * (lam ⟨k - 1, by omega⟩ / lam k) := by
  set T := (topSet k).val
  set k' : Fin n := ⟨k - 1, by omega⟩
  set P := ∏ i ∈ J.val ∩ T, lam i
  have hP : 0 ≤ P := prod_nonneg fun i _ ↦ (hpos i).le
  have hJeq : ∏ j ∈ J.val, lam j = (∏ j ∈ J.val \ T, lam j) * P := by
    rw [← sdiff_inter_self_left J.val T, prod_sdiff inter_subset_left]
  have hTeq : ∏ j ∈ T, lam j = (∏ j ∈ T \ J.val, lam j) * P := by
    rw [← sdiff_inter_self_right T J.val, prod_sdiff inter_subset_right]
  have hcard : #(J.val \ T) = #(T \ J.val) := by
    have h1 := card_sdiff_add_card_inter J.val T
    have h2 := card_sdiff_add_card_inter T J.val
    rw [inter_comm] at h2
    have h3 : #J.val = #T := by rw [J.prop, (topSet k).prop]
    omega
  set d := #(J.val \ T)
  have hd : 1 ≤ d := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 ↦ hJ ?_
    rw [Set.powersetCard.eq_iff_subset]
    exact sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 h0)
  have hA : ∏ j ∈ J.val \ T, lam j ≤ lam k' ^ d := by
    rw [← prod_const]
    refine prod_le_prod₀ (fun i _ ↦ (hpos i).le) fun i hi ↦ hmono ?_
    have : ¬ (k : ℕ) ≤ i := fun h ↦ (mem_sdiff.1 hi).2 ((mem_topSet k).2 h)
    change (i : ℕ) ≤ k - 1
    omega
  have hB : lam k ^ d ≤ ∏ j ∈ T \ J.val, lam j := by
    rw [hcard, ← prod_const]
    exact prod_le_prod₀ (fun _ _ ↦ (hpos k).le) fun i hi ↦
      hmono ((mem_topSet k).1 (mem_sdiff.1 hi).1)
  have hkk : lam k' ≤ lam k := hmono (by change k - 1 ≤ (k : ℕ); omega)
  have hk0 := hpos k
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  calc ∏ j ∈ J.val, lam j ≤ lam k' ^ d * P := by
        rw [hJeq]
        exact mul_le_mul_of_nonneg_right hA hP
    _ = lam k' ^ e * lam k' * P := by rw [he, pow_succ]
    _ ≤ lam k ^ e * lam k' * P :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hpos _).le hkk e) (hpos _).le) hP
    _ = lam k ^ d * P * (lam k' / lam k) := by
        rw [he, pow_succ]
        field_simp
    _ ≤ (∏ j ∈ T \ J.val, lam j) * P * (lam k' / lam k) := by
        gcongr
        exact div_nonneg (hpos _).le hk0.le
    _ = (∏ i ∈ T, lam i) * (lam k' / lam k) := by rw [hTeq]

variable (lam) (π : Equiv.Perm (Fin n))

/-- **EF13 (11.15)**: `ν_{π̂⁻¹(I)} = ∏_{i ∈ I} λ_{π⁻¹ i}`, replaced by
`ν_{N-1} = ν_{I_N} λ_{k-1}/λ_k` when `π̂⁻¹(I) = I_N`. With `D = 3^{n³}`,
`Q^{ĉ_{I,v₀}(Q)} = D · topBound λ π I`. -/
noncomputable def topBound (I : Set.powersetCard (Fin n) (n - k)) : ℝ :=
  if ∀ i ∈ I.val, (k : ℕ) ≤ π.symm i then
    (∏ i ∈ I.val, lam (π.symm i)) * (lam ⟨k - 1, by omega⟩ / lam k)
  else ∏ i ∈ I.val, lam (π.symm i)

variable {lam π}

/-- `π̂⁻¹(I) = I_N` exactly for `I = π̂(I_N)`. -/
theorem forall_le_symm_iff (I : Set.powersetCard (Fin n) (n - k)) :
    (∀ i ∈ I.val, (k : ℕ) ≤ π.symm i) ↔
      I = Set.powersetCard.map (n - k) π.toEmbedding (topSet k) := by
  constructor
  · intro h
    rw [Set.powersetCard.eq_iff_subset]
    intro i hi
    simp only [Set.powersetCard.val_map, mem_map, Equiv.coe_toEmbedding]
    exact ⟨π.symm i, (mem_topSet k).2 (h i hi), by simp⟩
  · rintro rfl i hi
    simp only [Set.powersetCard.val_map, mem_map, Equiv.coe_toEmbedding] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    simpa using (mem_topSet k).1 ht

omit [Fintype ι] in
theorem topBound_pos (hpos : ∀ i, 0 < lam i) (I : Set.powersetCard (Fin n) (n - k)) :
    0 < topBound lam π I := by
  unfold topBound
  split_ifs
  · exact mul_pos (prod_pos fun i _ ↦ hpos _) (div_pos (hpos _) (hpos _))
  · exact prod_pos fun i _ ↦ hpos _

omit [Fintype ι] in
/-- **EF13 (11.17) above `v₀`, the combinatorial core**: for `J ≠ I_N`,
`min(ν_{π̂⁻¹(I)}, ν_J) ≤ topBound λ π k I`. -/
theorem min_le_topBound (hk : 0 < (k : ℕ)) (hpos : ∀ i, 0 < lam i) (hmono : Monotone lam)
    (I : Set.powersetCard (Fin n) (n - k)) {J : Set.powersetCard (Fin n) (n - k)}
    (hJ : J ≠ topSet k) :
    min (∏ i ∈ I.val, lam (π.symm i)) (∏ j ∈ J.val, lam j) ≤ topBound lam π I := by
  unfold topBound
  split_ifs with h
  · refine (min_le_right _ _).trans ((prod_le_prod_topSet_mul hk hpos hmono hJ).trans_eq ?_)
    rw [(forall_le_symm_iff I).1 h]
    simp [prod_map]
  · exact min_le_left _ _

omit [Fintype ι] in
/-- **EF13 (11.21), the product**: `∏_I topBound λ π k I = (λ_0 ⋯ λ_{n-1})^{C(n-1, n-k-1)}
λ_{k-1} / λ_k`, since `I ↦ π̂⁻¹(I)` permutes the subsets and exactly one is replaced. -/
theorem prod_topBound (hk : 0 < (k : ℕ)) :
    ∏ I : Set.powersetCard (Fin n) (n - k), topBound lam π I =
      (∏ i, lam i) ^ ((n - 1).choose (n - k - 1)) * (lam ⟨k - 1, by omega⟩ / lam k) := by
  set I₀ := Set.powersetCard.map (n - k) π.toEmbedding (topSet k)
  set r := lam ⟨k - 1, by omega⟩ / lam k
  have h1 (I : Set.powersetCard (Fin n) (n - k)) :
      topBound lam π I = (∏ i ∈ I.val, lam (π.symm i)) * if I = I₀ then r else 1 := by
    unfold topBound
    split_ifs with h2 h3 h3
    · rfl
    · exact absurd ((forall_le_symm_iff I).1 h2) h3
    · exact absurd ((forall_le_symm_iff I).2 h3) h2
    · rw [mul_one]
  rw [prod_congr rfl fun I _ ↦ h1 I, prod_mul_distrib, prod_ite_eq' univ I₀ fun _ ↦ r,
    ite_eq_left (mem_univ _),
    Set.powersetCard.prod_eq_prod_powersetCard (f := fun s ↦ ∏ i ∈ s, lam (π.symm i)),
    prod_powersetCard_prod (by omega), Fintype.card_fin, prod_pow,
    Equiv.prod_comp π.symm lam]

omit [Fintype ι] in
/-- **EF13 (11.21)**: with `Q^{ĉ_{I,v₀}} = D · topBound λ π k I`, the sum of the `ĉ_{I,v₀}` is the
logarithm to base `Q` of `D^N (λ_0 ⋯ λ_{n-1})^{C(n-1, n-k-1)} λ_{k-1}/λ_k`, `N = C(n, n-k)`. -/
theorem sum_logb_topBound (hk : 0 < (k : ℕ)) (hpos : ∀ i, 0 < lam i) {D : ℝ} (hD : 0 < D)
    (Q : ℝ) :
    ∑ I : Set.powersetCard (Fin n) (n - k), Real.logb Q (D * topBound lam π I) =
      Real.logb Q (D ^ n.choose (n - k) *
        ((∏ i, lam i) ^ ((n - 1).choose (n - k - 1)) * (lam ⟨k - 1, by omega⟩ / lam k))) := by
  have hD' : ∏ _I : Set.powersetCard (Fin n) (n - k), D = D ^ n.choose (n - k) := by
    rw [Set.powersetCard.prod_eq_prod_powersetCard (f := fun _ ↦ D), prod_const,
      card_powersetCard, card_univ, Fintype.card_fin]
  rw [← hD', ← prod_topBound hk, ← prod_mul_distrib,
    Real.logb_prod _ _ fun I _ ↦ (mul_pos hD (topBound_pos hpos I)).ne']

omit [Fintype ι] in
/-- **EF13 (11.14), (11.17) above `v₀`**: if Davenport's lemma gives
`|h_{j, π(i)}|_w ≤ (B min(λ_i, λ_j))^m` (EF13 (11.7)), then for every `(n-k)`-element subset
`J ≠ I_N`, the Plücker coordinates of `ĥ_J = h_{j_1} ∧ ⋯ ∧ h_{j_{n-k}}` satisfy
`|ĥ_J(I)|_w ≤ (B^{n-k} · topBound λ π k I)^m`. -/
theorem FinitePlace.apply_plucker_le_topBound {E : Type*} [Field E] [NumberField E]
    (w : FinitePlace E) (hk : 0 < (k : ℕ)) (hpos : ∀ i, 0 < lam i) (hmono : Monotone lam)
    {h : Fin n → Fin n → E} {B : ℝ} (hB : 0 ≤ B) (m : ℕ)
    (hb : ∀ i j, w (h j (π i)) ≤ (B * min (lam i) (lam j)) ^ m)
    {J : Set.powersetCard (Fin n) (n - k)} (hJ : J ≠ topSet k)
    (I : Set.powersetCard (Fin n) (n - k)) :
    w (plucker (n - k) (fun r ↦ h (Set.powersetCard.ofFinEmbEquiv.symm J r)) I) ≤
      (B ^ (n - k) * topBound lam π I) ^ m := by
  have h' (r : Fin (n - k)) (i : Fin n) :
      w (h (Set.powersetCard.ofFinEmbEquiv.symm J r) i) ≤
        (B * min (lam (π.symm i)) (lam (Set.powersetCard.ofFinEmbEquiv.symm J r))) ^ m := by
    simpa using hb (π.symm i) (Set.powersetCard.ofFinEmbEquiv.symm J r)
  refine (FinitePlace.apply_plucker_le w hB (fun i ↦ (hpos _).le) (fun r ↦ (hpos _).le) m h'
    I).trans ?_
  rw [Set.powersetCard.prod_ofFinEmbEquiv_symm J lam]
  gcongr
  · exact mul_nonneg (pow_nonneg hB _) (le_min (prod_nonneg fun i _ ↦ (hpos _).le)
      (prod_nonneg fun i _ ↦ (hpos _).le))
  · exact min_le_topBound hk hpos hmono I hJ

end TopExponents

/-! ### The exponents `ĉ` off `v₀` (EF13 Lemma 11.4, (11.18)–(11.20)) -/

namespace FormExponent

variable (c : FormExponent K ι) {p : ℕ}

omit [LinearOrder ι] in
/-- **EF13 (11.18)**, infinite places: `Σ_s ĉ_{s,v} = C(n-1, p-1) Σ_i c_{iv}`. -/
theorem sum_exteriorPower_arch (hp : 1 ≤ p) (v : InfinitePlace K) :
    ∑ s, (c.exteriorPower p).arch v s =
      (Fintype.card ι - 1).choose (p - 1) * ∑ i, c.arch v i := by
  change ∑ s : Set.powersetCard ι p, ∑ i ∈ s.val, c.arch v i = _
  rw [Set.powersetCard.sum_eq_sum_powersetCard (f := fun s ↦ ∑ i ∈ s, c.arch v i),
    sum_powersetCard_sum hp]
  simp only [nsmul_eq_mul, ← mul_sum]

omit [LinearOrder ι] in
/-- **EF13 (11.18)**, finite places. -/
theorem sum_exteriorPower_fin (hp : 1 ≤ p) (v : FinitePlace K) :
    ∑ s, (c.exteriorPower p).fin v s =
      (Fintype.card ι - 1).choose (p - 1) * ∑ i, c.fin v i := by
  change ∑ s : Set.powersetCard ι p, ∑ i ∈ s.val, c.fin v i = _
  rw [Set.powersetCard.sum_eq_sum_powersetCard (f := fun s ↦ ∑ i ∈ s, c.fin v i),
    sum_powersetCard_sum hp]
  simp only [nsmul_eq_mul, ← mul_sum]

omit [LinearOrder ι] in
/-- A `p`-element subset with `1 ≤ p < #ι` is nonempty and proper. -/
theorem _root_.Set.powersetCard.nonempty_ne_univ (hp : 1 ≤ p) (hpn : p < Fintype.card ι)
    (s : Set.powersetCard ι p) : s.val.Nonempty ∧ s.val ≠ univ := by
  have hs := Set.powersetCard.card_eq s
  refine ⟨card_pos.1 (by omega), fun h ↦ ?_⟩
  rw [h, card_univ] at hs
  omega

omit [LinearOrder ι] in
/-- **EF13 (11.19)**, infinite places: if `Σ_i c_{iv} = 0`, then
`|ĉ_{s,v}| ≤ (n - 1) max_i c_{iv}`. -/
theorem abs_exteriorPower_arch_le (hp : 1 ≤ p) (hpn : p < Fintype.card ι) {v : InfinitePlace K}
    (h0 : ∑ i, c.arch v i = 0) (s : Set.powersetCard ι p) :
    |(c.exteriorPower p).arch v s| ≤ (Fintype.card ι - 1 : ℕ) * ⨆ i, c.arch v i :=
  abs_sum_le_of_sum_eq_zero h0 (fun i ↦ le_ciSup (Finite.bddAbove_range _) i)
    (Set.powersetCard.nonempty_ne_univ hp hpn s).1
    (Set.powersetCard.nonempty_ne_univ hp hpn s).2

omit [LinearOrder ι] in
/-- **EF13 (11.19)**, finite places. -/
theorem abs_exteriorPower_fin_le (hp : 1 ≤ p) (hpn : p < Fintype.card ι) {v : FinitePlace K}
    (h0 : ∑ i, c.fin v i = 0) (s : Set.powersetCard ι p) :
    |(c.exteriorPower p).fin v s| ≤ (Fintype.card ι - 1 : ℕ) * ⨆ i, c.fin v i :=
  abs_sum_le_of_sum_eq_zero h0 (fun i ↦ le_ciSup (Finite.bddAbove_range _) i)
    (Set.powersetCard.nonempty_ne_univ hp hpn s).1
    (Set.powersetCard.nonempty_ne_univ hp hpn s).2

omit [LinearOrder ι] in
/-- **EF13 (11.20)**: if `Σ_i c_{iv} = 0` at every place, then
`Σ_v max_s |ĉ_{s,v}| ≤ (n - 1) Σ_v max_i c_{iv}`. -/
theorem sum_iSup_abs_exteriorPower_le (hp : 1 ≤ p) (hpn : p < Fintype.card ι)
    (h0a : ∀ v, ∑ i, c.arch v i = 0) (h0f : ∀ v, ∑ i, c.fin v i = 0) :
    (∑ v, ⨆ s, |(c.exteriorPower p).arch v s|) + ∑ᶠ v, ⨆ s, |(c.exteriorPower p).fin v s| ≤
      (Fintype.card ι - 1 : ℕ) * ((∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i) := by
  have : Nonempty (Set.powersetCard ι p) := Set.powersetCard.nonempty_iff.2 hpn.le
  have hfin (v : FinitePlace K) (hv : c.fin v = 0) :
      (⨆ s, |(c.exteriorPower p).fin v s|) = 0 ∧ (⨆ i, c.fin v i) = 0 := by
    have : (c.exteriorPower p).fin v = 0 := by
      funext s
      simp [exteriorPower, hv]
    simp [this, hv]
  have hsupp1 : (Function.support fun v ↦ ⨆ s, |(c.exteriorPower p).fin v s|).Finite :=
    c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv (hfin v h).1
  have hsupp2 : (Function.support fun v ↦ ⨆ i, c.fin v i).Finite :=
    c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv (hfin v h).2
  rw [mul_add, mul_sum, mul_finsum' _ _ hsupp2]
  gcongr with v
  · exact ciSup_le fun s ↦ c.abs_exteriorPower_arch_le hp hpn (h0a v) s
  · refine finsum_le_finsum hsupp1 ?_ fun v ↦ ciSup_le fun s ↦
      c.abs_exteriorPower_fin_le hp hpn (h0f v) s
    exact hsupp2.subset fun v hv h ↦ hv (by simp [h])

end FormExponent

/-! ### The inverses of the exterior powers (EF13 Lemma 11.5) -/

theorem _root_.Matrix.inv_compound {F : Type*} [Field F] {κ : Type*} [Fintype κ] [LinearOrder κ]
    (p : ℕ) {M : Matrix κ κ F} (h : M.det ≠ 0) : (M.compound p)⁻¹ = M⁻¹.compound p :=
  inv_eq_right_inv (by rw [← compound_mul, mul_nonsing_inv _ h.isUnit, compound_one])

namespace FormSystem

variable (L : FormSystem K ι)

/-- If the forms at `v₀` are the coordinates (EF13 (8.8)), the coordinate forms are among the
forms of the system. -/
theorem one_mem_forms {v₀ : FinitePlace K} (hL : L.fin v₀ = 1) (i : ι) :
    (1 : Matrix ι ι K) i ∈ L.forms := by
  rw [← hL]
  exact L.fin_mem_forms v₀ i

variable {L}

/-- The entries of `B⁻¹`, for `B` with rows among the forms, are at most `max_d |d| / |det B|`
over `d ∈ detSet`, when the coordinate forms belong to the system. -/
theorem apply_inv_le (f : AbsoluteValue K ℝ) (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms)
    {B : Matrix ι ι K} (hB : ∀ i, B i ∈ L.forms) (i j : ι) :
    f (B⁻¹ i j) ≤ (⨆ e : L.detSet, f e) / f B.det := by
  simpa using L.apply_mul_inv_le f hB h1 i j

/-- **EF13 Lemma 11.5, local form at an infinite place**: the entries of the inverse of the
matrix of `L̂^{(v)}` are at most `p! (max_d |d|_v / |det L^{(v)}|_v)^p`. -/
theorem apply_inv_exteriorPower_arch_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms)
    (v : InfinitePlace K) (p : ℕ) (s t : Set.powersetCard ι p) :
    v (((L.exteriorPower p).arch v)⁻¹ s t) ≤
      p.factorial * ((⨆ e : L.detSet, v e) / v (L.arch v).det) ^ p := by
  change v (((L.arch v).compound p)⁻¹ s t) ≤ _
  rw [inv_compound p (L.arch_det_ne_zero v), compound_apply, plucker_apply]
  refine (abv_det_le_of_col v.1 _ (b := fun _ ↦ (⨆ e : L.detSet, v e) / v (L.arch v).det)
    fun r q ↦ apply_inv_le v.1 h1 (L.arch_mem_forms v) _ _).trans_eq ?_
  simp [prod_const, div_pow]

/-- **EF13 Lemma 11.5, local form at a finite place**: the entries of the inverse of the matrix
of `L̂^{(v)}` are at most `(max_d |d|_v / |det L^{(v)}|_v)^p`. -/
theorem apply_inv_exteriorPower_fin_le (h1 : ∀ i, (1 : Matrix ι ι K) i ∈ L.forms)
    (v : FinitePlace K) (p : ℕ) (s t : Set.powersetCard ι p) :
    v (((L.exteriorPower p).fin v)⁻¹ s t) ≤ ((⨆ e : L.detSet, v e) / v (L.fin v).det) ^ p := by
  change v (((L.fin v).compound p)⁻¹ s t) ≤ _
  rw [inv_compound p (L.fin_det_ne_zero v), compound_apply, plucker_apply]
  refine (FinitePlace.apply_det_le_of_col v _
    (b := fun _ ↦ (⨆ e : L.detSet, v e) / v (L.fin v).det)
    fun r q ↦ apply_inv_le v.1 h1 (L.fin_mem_forms v) _ _).trans_eq ?_
  simp [prod_const, div_pow]

variable (L)

/-- **EF13 Lemma 11.5, product form**, relative to `K`: the product over the places of the local
bounds is `p!^{[K:ℚ]} (H_L / Δ_L)^p`. -/
theorem prod_invBound (p : ℕ) :
    (∏ v : InfinitePlace K,
        (p.factorial * ((⨆ e : L.detSet, v e) / v (L.arch v).det) ^ p) ^ v.mult) *
      ∏ᶠ v : FinitePlace K, ((⨆ e : L.detSet, v e) / v (L.fin v).det) ^ p =
      (p.factorial : ℝ) ^ finrank ℚ K * (L.mulFormHeight / L.mulDet) ^ p := by
  have hM := L.hasFiniteMulSupport_iSup_detSet
  have hD := L.hasFiniteMulSupport_det_fin
  have hMD : (fun v : FinitePlace K ↦
      (⨆ e : L.detSet, v e) / v (L.fin v).det).HasFiniteMulSupport :=
    (hM.union hD).subset (Function.mulSupport_div _ _)
  rw [← finprod_pow hMD, finprod_div_distrib hM hD, mulFormHeight, mulDet]
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq,
    div_pow, prod_div_distrib, ← pow_mul]
  have hpow (f : InfinitePlace K → ℝ) : ∏ v, f v ^ (p * v.mult) = (∏ v, f v ^ v.mult) ^ p := by
    rw [← prod_pow]
    exact prod_congr rfl fun v _ ↦ by ring
  rw [hpow, hpow]
  ring

/-- **EF13 Lemma 11.5**, absolute form: the product over the places of the bounds for the entries
of the inverses of the matrices of `L̂` is, after the `[K:ℚ]`-th root, at most
`p! · H_L^{p C(r, n)}`, `r` the number of distinct forms (through EF13 (7.4)). EF13 bound it by
`H_L^{R^n}` through Jacobi's complementary-minor identity; we bound the minors of `L^{(v)⁻¹}`
directly, which costs the factor `p!`. -/
theorem prod_invBound_rpow_le (p : ℕ) :
    ((∏ v : InfinitePlace K,
        (p.factorial * ((⨆ e : L.detSet, v e) / v (L.arch v).det) ^ p) ^ v.mult) *
      ∏ᶠ v : FinitePlace K, ((⨆ e : L.detSet, v e) / v (L.fin v).det) ^ p) ^
        ((finrank ℚ K : ℝ))⁻¹ ≤
      p.factorial * L.absFormHeight ^ ((p : ℝ) * L.forms.card.choose (Fintype.card ι)) := by
  set d := finrank ℚ K
  have hd : d ≠ 0 := finrank_pos.ne'
  set C : ℝ := (L.forms.card.choose (Fintype.card ι) : ℝ)
  have hH1 : 1 ≤ L.mulFormHeight := L.one_le_mulFormHeight
  have hD0 := L.mulDet_pos
  have hA1 : 1 ≤ L.absFormHeight := Real.one_le_rpow hH1 (by positivity)
  have hA0 : 0 < L.absFormHeight := zero_lt_one.trans_le hA1
  have hX : 0 ≤ L.mulFormHeight / L.mulDet := div_nonneg (zero_le_one.trans hH1) hD0.le
  have key : ((p.factorial : ℝ) ^ d * (L.mulFormHeight / L.mulDet) ^ p) ^ ((d : ℝ))⁻¹ =
      p.factorial * (L.absFormHeight / L.absDet) ^ p := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast (by positivity) hd]
    congr 1
    rw [← Real.rpow_natCast (L.mulFormHeight / L.mulDet) p, ← Real.rpow_mul hX,
      mul_comm (p : ℝ), Real.rpow_mul hX, Real.rpow_natCast,
      Real.div_rpow (zero_le_one.trans hH1) hD0.le]
    rfl
  rw [prod_invBound, key]
  gcongr
  calc (L.absFormHeight / L.absDet) ^ p ≤ (L.absFormHeight ^ C) ^ p := by
        refine pow_le_pow_left₀ (div_nonneg hA0.le L.absDet_pos.le) ?_ p
        calc L.absFormHeight / L.absDet ≤ L.absFormHeight / L.absFormHeight ^ (1 - C) :=
              div_le_div_of_nonneg_left hA0.le (Real.rpow_pos_of_pos hA0 _)
                L.absFormHeight_rpow_le_absDet
          _ = L.absFormHeight ^ C := by
              rw [div_eq_iff (Real.rpow_pos_of_pos hA0 _).ne', ← Real.rpow_add hA0]
              norm_num
    _ = L.absFormHeight ^ ((p : ℝ) * C) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le, mul_comm]

end FormSystem

end NumberField
