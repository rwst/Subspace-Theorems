/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.AdaptedBasis
public import ArithmeticHeights.SuccessiveMinima

/-!
# A lattice basis from the successive minima

The vectors realizing the successive minima of a lattice `L` in a symmetric convex body `B` are
`ℝ`-linearly independent, but they need not be a `ℤ`-basis of `L`. This file produces a basis that
is almost as short: its `i`-th member lies in `max 1 ((i + 1) / 2) · λ i` times the body, where
`λ i` is the `i`-th minimum and the indices start at `0`.

## Main results

* `ZLattice.exists_basis_gauge_le`: the general form, and the one the proof gives. For *any*
  `ℝ`-independent family `a 0, …, a (n - 1)` of lattice vectors there is a `ℤ`-basis `b` of `L`
  with `gauge B (b j) ≤ max (gauge B (a j)) ((∑_{i ≤ j} gauge B (a i)) / 2)`.
* `ZLattice.exists_basis_mem_smul_successiveMinimum`: the minima form, Cassels' Chapter V,
  Lemma 8, as Bugeaud–Győry cite it. Against Minkowski's second theorem this loses exactly
  `∏_{i < n} max 1 ((i + 1) / 2) = n! / 2 ^ (n - 1)`.
* `gauge_smul_of_symmetric`: the gauge of a symmetric body is absolutely homogeneous.

## Implementation notes

The induction is along the flag `ZLattice.flagPart L a j` of `ArithmeticHeights/AdaptedBasis.lean`,
one coordinate at a time, and the only thing added to the construction there is *which* vector is
appended at each step. Across the step `flagPart L a j ≤ flagPart L a (j + 1)` the appended vector
`y` is determined modulo `flagPart L a j` — that is `ZLattice.extending_congr` — and `a j` itself
is `c • y` plus something of `flagPart L a j`, for a nonzero integer `c`.

⚠ **The two cases of the step are not "short" and "long"; they are `|c| = 1` and `|c| ≥ 2`, and
the bound is a maximum because of it.** If `|c| = 1` then `c • a j` is itself an admissible
choice, and it costs `gauge B (a j)` exactly. If `|c| ≥ 2` then `y` has `a j`-coordinate `c⁻¹`, of
absolute value at most `1/2`, and rounding its remaining coordinates into `[-1/2, 1/2]` — which
changes `y` by an element of `flagPart L a j` and so is admissible — costs at most
`(∑_{i ≤ j} gauge B (a i)) / 2`. Neither bound implies the other, and the first case is the one
that makes `max 1 (·)` rather than `(·)` appear in the minima form: at `j = 0` the sum bound is
`λ 0 / 2`, which is *better* than `λ 0`, but it is unavailable when `|c| = 1`.

⚠ **No measure, no closedness, and no boundedness enter the general form.** The body is used only
through its gauge, which is subadditive and absolutely homogeneous for any symmetric convex set
with `0` in its interior. Closedness is bought back in the minima form, and only there, because
turning `gauge B x ≤ t` into `x ∈ t • B` is exactly what it pays for
(`gauge_le_iff_mem_smul`); boundedness likewise, because it is what makes the minima positive.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
Lemma 8, p. 135.

Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. 74 (1996),
where this is the lemma that turns Minkowski's second theorem into a bound on a fundamental system
of units, at the cost of `n! / 2 ^ (n - 1)`.

This is Layer 4.6 of the `ArithmeticHeights` roadmap.
-/

public section

open Metric Module Set Submodule

open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}

/-! ### The gauge of a symmetric body -/

/-- The gauge of a symmetric body is *absolutely* homogeneous, not merely positively homogeneous.
Mathlib's `gauge_smul` asks for a balanced body over an `RCLike` field; over `ℝ` symmetry is all
that is needed, and symmetry is the hypothesis the geometry of numbers carries anyway. -/
theorem gauge_smul_of_symmetric (hB₁ : ∀ x ∈ B, -x ∈ B) (r : ℝ) (x : E) :
    gauge B (r • x) = |r| * gauge B x := by
  rcases le_or_gt 0 r with hr | hr
  · rw [gauge_smul_of_nonneg hr, abs_of_nonneg hr, smul_eq_mul]
  · rw [← gauge_neg hB₁ (r • x), ← neg_smul, gauge_smul_of_nonneg (neg_nonneg.2 hr.le),
      abs_of_neg hr, smul_eq_mul]

namespace ZLattice

/-! ### A basis from an independent family -/

/-- **A basis from any independent family.** For `ℝ`-linearly independent lattice vectors
`a 0, …, a (n - 1)` spanning `E` there is a `ℤ`-basis `b` of `L` with
`gauge B (b j) ≤ max (gauge B (a j)) ((∑_{i ≤ j} gauge B (a i)) / 2)` for every `j`.

This is the form the proof gives, and `ZLattice.exists_basis_mem_smul_successiveMinimum` is its
corollary for the family realizing the successive minima. No measure, no closedness and no
boundedness of the body enter; see the implementation notes of this file. -/
theorem exists_basis_gauge_le [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    {n : ℕ} (hn : n = finrank ℝ E) {a : Fin n → E} (haL : ∀ i, a i ∈ L)
    (ha : LinearIndependent ℝ a) :
    ∃ b : Basis (Fin n) ℤ L, ∀ j : Fin n,
      gauge B ((b j : L) : E) ≤
        max (gauge B (a j)) ((∑ i ∈ Finset.Iic j, gauge B (a i)) / 2) := by
  classical
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  have habs : Absorbent ℝ B := absorbent_nhds_zero h₀
  set A : ℕ → E := fun m ↦ if h : m < n then a ⟨m, h⟩ else 0 with hAdef
  have hA : ∀ (m : ℕ) (h : m < n), A m = a ⟨m, h⟩ := fun m h ↦ by simp [hAdef, h]
  set S : ℕ → ℝ := fun m ↦ ∑ i ∈ Finset.range m, gauge B (A i) with hSdef
  have hS : ∀ m : ℕ, S m = ∑ i ∈ Finset.range m, gauge B (A i) := fun _ ↦ rfl
  have hAmem : ∀ {m k : ℕ}, m < k → k ≤ n → A m ∈ flagPart L a k := by
    intro m k hmk hkn
    have hmn : m < n := lt_of_lt_of_le hmk hkn
    rw [hA m hmn]
    exact mem_flagPart_of_lt L a haL (i := ⟨m, hmn⟩) hmk
  have key : ∀ j, j ≤ n → ∃ b : Basis (Fin j) ℤ (flagPart L a j), ∀ k : Fin j,
      gauge B ((b k : flagPart L a j) : E) ≤
        max (gauge B (A (k : ℕ))) (S ((k : ℕ) + 1) / 2) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : flagPart L a 0 = ⊥ := flagPart_zero L a
      have : Subsingleton (flagPart L a 0) := by rw [h0]; infer_instance
      exact ⟨Basis.empty _, fun k ↦ k.elim0⟩
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      have hj' : j ≤ n := le_of_lt hjn
      obtain ⟨b, hb⟩ := ih hj'
      have hdisc : DiscreteTopology (flagPart L a (j + 1)) :=
        discreteTopology_of_le (flagPart_le L a (j + 1))
      have hmono : flagPart L a j ≤ flagPart L a (j + 1) := flagPart_mono L a (Nat.le_succ j)
      obtain ⟨y, hyN, hli, hsp⟩ := exists_extending hmono
        (fun c hc z hz hcz ↦ flagPart_saturated L a hc (flagPart_le L a (j + 1) hz) hcz)
        (by rw [finrank_flagPart L a ha haL hj, finrank_flagPart L a ha haL hj'])
      obtain ⟨c, hc⟩ :=
        hsp (a ⟨j, hjn⟩) (mem_flagPart_of_lt L a haL (i := ⟨j, hjn⟩) (Nat.lt_succ_self j))
      have hnotmem : a ⟨j, hjn⟩ ∉ span ℝ (a '' {i : Fin n | (i : ℕ) < j}) :=
        ha.notMem_span_image (by simp)
      have hc₀ne : -c ≠ 0 := by
        intro h
        have hc0 : c = 0 := by omega
        refine hnotmem ?_
        have hmem := ((mem_flagPart L a j).1 hc).2
        rwa [hc0, zero_smul, add_zero] at hmem
      have hnew : ∃ y₂ : E, y₂ - y ∈ flagPart L a j ∧
          gauge B y₂ ≤ max (gauge B (A j)) (S (j + 1) / 2) := by
        by_cases hunit : -c = 1 ∨ -c = -1
        · have hcval : c = -1 ∨ c = 1 := by omega
          refine ⟨(-c) • a ⟨j, hjn⟩, ?_, ?_⟩
          · have hcc : (-c) * c = -1 := by rcases hcval with h | h <;> rw [h] <;> ring
            have hstep : (-c) • a ⟨j, hjn⟩ - y = (-c) • (a ⟨j, hjn⟩ + c • y) := by
              rw [smul_add, smul_smul, hcc, neg_one_zsmul]
              abel
            rw [hstep]
            exact Submodule.smul_mem _ _ hc
          · have habs1 : |((-c : ℤ) : ℝ)| = 1 := by
              rcases hunit with h | h <;> rw [h] <;> norm_num
            have hg : gauge B ((-c) • a ⟨j, hjn⟩) = gauge B (a ⟨j, hjn⟩) := by
              rw [← Int.cast_smul_eq_zsmul ℝ, gauge_smul_of_symmetric hB₁, habs1, one_mul]
            rw [hg, hA j hjn]
            exact le_max_left _ _
        · push Not at hunit
          have h2 : (2 : ℤ) ≤ |(-c)| := by
            rcases abs_cases (-c) with ⟨he, hs⟩ | ⟨he, hs⟩ <;> rw [he] <;> omega
          have hcR : ((-c : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc₀ne
          have hfun : (fun i : Fin j ↦ A (i : ℕ)) = a ∘ Fin.castLE hj' := by
            funext i
            rw [hA (i : ℕ) (lt_of_lt_of_le i.isLt hj')]
            rfl
          have hrange : a '' {i : Fin n | (i : ℕ) < j}
              = Set.range (fun i : Fin j ↦ A (i : ℕ)) := by
            rw [hfun, Set.range_comp, Fin.range_castLE hj']
          have hwspan : a ⟨j, hjn⟩ + c • y ∈ span ℝ (Set.range (fun i : Fin j ↦ A (i : ℕ))) := by
            rw [← hrange]
            exact ((mem_flagPart L a j).1 hc).2
          obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hwspan
          set t : Fin j → ℝ := fun i ↦ -(((-c : ℤ) : ℝ)⁻¹ * s i) with htdef
          have ht : ∀ i, t i = -(((-c : ℤ) : ℝ)⁻¹ * s i) := fun _ ↦ rfl
          have hyexp : y = ((-c : ℤ) : ℝ)⁻¹ • a ⟨j, hjn⟩ + ∑ i : Fin j, t i • A (i : ℕ) := by
            have h1 : ((-c : ℤ) : ℝ) • y = a ⟨j, hjn⟩ - ∑ i : Fin j, s i • A (i : ℕ) := by
              rw [hs, Int.cast_smul_eq_zsmul, neg_smul]
              abel
            have hy2 : y = ((-c : ℤ) : ℝ)⁻¹ • (((-c : ℤ) : ℝ) • y) := by
              rw [smul_smul, inv_mul_cancel₀ hcR, one_smul]
            have hsum : ∑ i : Fin j, t i • A (i : ℕ)
                = -∑ i : Fin j, ((-c : ℤ) : ℝ)⁻¹ • (s i • A (i : ℕ)) := by
              rw [← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [ht i, smul_smul, neg_smul]
            rw [hsum]
            conv_lhs => rw [hy2, h1]
            rw [smul_sub, Finset.smul_sum]
            abel
          refine ⟨y - ∑ i : Fin j, (round (t i) : ℤ) • A (i : ℕ), ?_, ?_⟩
          · have hsub : y - ∑ i : Fin j, (round (t i) : ℤ) • A (i : ℕ) - y
                = -∑ i : Fin j, (round (t i) : ℤ) • A (i : ℕ) := by abel
            rw [hsub]
            exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ ↦
              Submodule.smul_mem _ _ (hAmem i.isLt hj'))
          · have hsplit : ∑ i : Fin j, (t i - (round (t i) : ℝ)) • A (i : ℕ)
                = (∑ i : Fin j, t i • A (i : ℕ))
                  - ∑ i : Fin j, (round (t i) : ℤ) • A (i : ℕ) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [sub_smul, Int.cast_smul_eq_zsmul]
            have hy₂exp : y - ∑ i : Fin j, (round (t i) : ℤ) • A (i : ℕ)
                = ((-c : ℤ) : ℝ)⁻¹ • a ⟨j, hjn⟩
                  + ∑ i : Fin j, (t i - (round (t i) : ℝ)) • A (i : ℕ) := by
              rw [hsplit]
              conv_lhs => rw [hyexp]
              abel
            have habs2 : (2 : ℝ) ≤ |((-c : ℤ) : ℝ)| := by
              rw [← Int.cast_abs]
              exact_mod_cast h2
            have hκ : |(((-c : ℤ) : ℝ))⁻¹| ≤ 1 / 2 := by
              rw [abs_inv, one_div]
              exact inv_anti₀ (by norm_num) habs2
            have hfirst : gauge B (((-c : ℤ) : ℝ)⁻¹ • a ⟨j, hjn⟩) ≤ 1 / 2 * gauge B (A j) := by
              rw [gauge_smul_of_symmetric hB₁, hA j hjn]
              exact mul_le_mul_of_nonneg_right hκ (gauge_nonneg _)
            have hSj : S j = ∑ i : Fin j, gauge B (A (i : ℕ)) := by
              rw [hS]
              exact (Fin.sum_univ_eq_sum_range (fun m ↦ gauge B (A m)) j).symm
            have hsumbound : ∑ i : Fin j, gauge B ((t i - (round (t i) : ℝ)) • A (i : ℕ))
                ≤ 1 / 2 * S j := by
              rw [hSj, Finset.mul_sum]
              refine Finset.sum_le_sum fun i _ ↦ ?_
              rw [gauge_smul_of_symmetric hB₁]
              exact mul_le_mul_of_nonneg_right (abs_sub_round (t i)) (gauge_nonneg _)
            have hSsucc : S (j + 1) = S j + gauge B (A j) := by
              rw [hS, hS, Finset.sum_range_succ]
            rw [hy₂exp]
            refine le_trans (gauge_add_le hB₀ habs _ _) ?_
            refine le_trans (add_le_add hfirst
              (le_trans (gauge_sum_le hB₀ habs _ _) hsumbound)) ?_
            rw [hSsucc]
            have hmax := le_max_right (gauge B (A j)) ((S j + gauge B (A j)) / 2)
            linarith
      obtain ⟨y₂, hy₂sub, hy₂gauge⟩ := hnew
      have hy₂mem : y₂ ∈ flagPart L a (j + 1) := by
        have heq : y₂ = y + (y₂ - y) := by abel
        rw [heq]
        exact Submodule.add_mem _ hyN (hmono hy₂sub)
      obtain ⟨hli₂, hsp₂⟩ := extending_congr hy₂sub hli hsp
      refine ⟨Basis.mkFinSnocOfLE b hmono y₂ hy₂mem hli₂ hsp₂, fun k ↦ ?_⟩
      refine Fin.lastCases ?_ (fun k' ↦ ?_) k
      · have hlast : ((Basis.mkFinSnocOfLE b hmono y₂ hy₂mem hli₂ hsp₂ (Fin.last j) :
            flagPart L a (j + 1)) : E) = y₂ := by simp
        rw [hlast]
        simpa using hy₂gauge
      · have hcast : ((Basis.mkFinSnocOfLE b hmono y₂ hy₂mem hli₂ hsp₂ (Fin.castSucc k') :
            flagPart L a (j + 1)) : E) = ((b k' : flagPart L a j) : E) := by simp
        rw [hcast]
        simpa using hb k'
  obtain ⟨b, hb⟩ := key n le_rfl
  have hLn : flagPart L a n = L := flagPart_eq_self L a hn ha
  refine ⟨b.map (LinearEquiv.ofEq _ _ hLn), fun j ↦ ?_⟩
  have hcoe : (((b.map (LinearEquiv.ofEq _ _ hLn)) j : L) : E)
      = ((b j : flagPart L a n) : E) := by simp
  rw [hcoe]
  refine (hb j).trans ?_
  have h1 : A (j : ℕ) = a j := by rw [hA (j : ℕ) j.isLt]
  have h2 : S ((j : ℕ) + 1) = ∑ i ∈ Finset.Iic j, gauge B (a i) := by
    rw [hS, Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Fin.valEmbedding_apply, hA (i : ℕ) i.isLt]
  rw [h1, h2]

/-! ### A basis from the minima -/

/-- **A basis from the successive minima** (Cassels, Chapter V, Lemma 8, p. 135). The independent
vectors realizing the minima need not be a `ℤ`-basis of `L`, and Layer 4.4 does not make them one;
but some basis has its `i`-th member (indices from `0`) in `max 1 ((i + 1) / 2) · λ i` times the
body. Against Minkowski's second theorem this loses exactly
`∏_{i < n} max 1 ((i + 1) / 2) = n! / 2 ^ (n - 1)`.

`IsClosed B` is what turns the gauge bound of `ZLattice.exists_basis_gauge_le` into membership in
a dilation, and `Bornology.IsBounded B` is what makes the minima positive; neither is used in the
general form. -/
theorem exists_basis_mem_smul_successiveMinimum [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hB₄ : IsClosed B) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, ∀ i : Fin (finrank ℝ E),
      ((b i : L) : E) ∈ (max 1 ((((i : ℕ) : ℝ) + 1) / 2) * successiveMinimum L B i) • B := by
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  obtain ⟨b, hb⟩ := exists_basis_gauge_le L hB₀ hB₁ hB₂ rfl (fun i ↦ hvL i) hvind
  refine ⟨b, fun i ↦ ?_⟩
  have hpos : 0 < successiveMinimum L B i := successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ i.isLt
  have hone : (1 : ℝ) ≤ max 1 ((((i : ℕ) : ℝ) + 1) / 2) := le_max_left _ _
  rw [← gauge_le_iff_mem_smul hB₀ hB₄ (hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂) (by positivity)]
  refine (hb i).trans ?_
  have hsum : ∑ k ∈ Finset.Iic i, gauge B (v k)
      ≤ (((i : ℕ) : ℝ) + 1) * successiveMinimum L B i := by
    calc ∑ k ∈ Finset.Iic i, gauge B (v k)
        = ∑ k ∈ Finset.Iic i, successiveMinimum L B (k : ℕ) :=
          Finset.sum_congr rfl fun k _ ↦ hvg k
      _ ≤ ∑ _k ∈ Finset.Iic i, successiveMinimum L B (i : ℕ) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hki : k ≤ i := Finset.mem_Iic.1 hk
          exact successiveMinimum_le_of_le (Fin.val_fin_le.2 hki) i.isLt hB₀ hB₁ hB₂
      _ = (((i : ℕ) : ℝ) + 1) * successiveMinimum L B i := by
          rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
          push_cast
          ring
  refine max_le ?_ ?_
  · rw [hvg i]
    nlinarith [hpos.le]
  · have hhalf : (((i : ℕ) : ℝ) + 1) / 2 ≤ max 1 ((((i : ℕ) : ℝ) + 1) / 2) := le_max_right _ _
    nlinarith [hpos.le]

end ZLattice
