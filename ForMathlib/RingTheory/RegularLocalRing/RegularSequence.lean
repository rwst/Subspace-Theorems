/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.RegularLocalRing.Defs

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square

/-!
# Regular sequences in regular local rings

A regular local ring `R` of dimension `d` is a domain, and its maximal ideal contains an
`R`-regular sequence of length `d` (a regular system of parameters); so `R` is Cohen–Macaulay.
On a finite module over a Noetherian local ring, a regular element of the maximal ideal lowers the
length of the regular sequences in the maximal ideal by at most one (by the Rees theorem).

## Main statements

* `IsLocalRing.exists_isRegular_quotSMulTop`: if `M` has a regular sequence of length `n + 1` in
  the maximal ideal and `x` in the maximal ideal is `M`-regular, then `M / x M` has one of
  length `n`.
* `IsRegularLocalRing.quotient`: `R / (x)` is regular local, of dimension one less, for `x` in
  the maximal ideal but not in its square.
* `IsRegularLocalRing.isDomain`: a regular local ring is a domain.
* `IsRegularLocalRing.exists_isRegular`: the maximal ideal contains an `R`-regular sequence of
  length `dim R`.

## References

* H. Matsumura, *Commutative ring theory*, Thms. 14.3 and 17.4.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Pointwise

universe u v

/-- `(R / I) / x (R / I) = R / (I + (x))`, as `R`-modules. -/
noncomputable def Ideal.quotSMulTopQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R) (x : R) :
    QuotSMulTop x (R ⧸ I) ≃ₗ[R] R ⧸ (I ⊔ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [show (Ideal.span {x} : Submodule R R) = x • ⊤ by
        rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top],
      Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).trans
    (Submodule.quotientQuotientEquivQuotientSup (I : Submodule R R) (Ideal.span {x}))

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The dimension of `R / Q` is the coheight of `Q` in the prime spectrum. -/
theorem ringKrullDim_quotient_eq_coheight (Q : Ideal R) [Q.IsPrime] :
    ringKrullDim (R ⧸ Q) = Order.coheight (⟨Q, ‹_›⟩ : PrimeSpectrum R) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  congr 2

/-- `ht Q + dim R / Q ≤ dim R` for a prime `Q`. -/
theorem height_add_ringKrullDim_quotient_le (Q : Ideal R) [Q.IsPrime] :
    (Q.height : WithBot ℕ∞) + ringKrullDim (R ⧸ Q) ≤ ringKrullDim R := by
  set p : PrimeSpectrum R := ⟨Q, ‹_›⟩
  have hp : Q.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  rw [ringKrullDim_quotient_eq_coheight, hp, ← WithBot.coe_add, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a ↦ Order.height a + Order.coheight a) p)

/-- The dimension of `R / Q` drops along a strict inclusion of primes. -/
theorem ringKrullDim_quotient_add_one_le_of_lt {Q Q' : Ideal R} [Q.IsPrime] [Q'.IsPrime]
    (h : Q < Q') : ringKrullDim (R ⧸ Q') + 1 ≤ ringKrullDim (R ⧸ Q) := by
  rw [ringKrullDim_quotient_eq_coheight, ringKrullDim_quotient_eq_coheight]
  exact_mod_cast Order.coheight_add_one_le (α := PrimeSpectrum R) (a := ⟨Q', ‹_›⟩) (b := ⟨Q, ‹_›⟩) h

end Ideal

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Nakayama: the maximal ideal does not fill a nonzero finite module. -/
theorem maximalIdeal_smul_top_lt_top {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
  lt_top_iff_ne_top.mpr (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (le_of_eq_of_le (jacobson_eq_maximalIdeal _ bot_ne_top).symm
      (Ideal.jacobson_mono bot_le))).symm

/-- **The depth drops by at most one.** If `M` has a regular sequence of length `n + 1` in the
maximal ideal and `x` in the maximal ideal is `M`-regular, then `M / x M` has a regular sequence
of length `n` in the maximal ideal. By the Rees theorem, from the long exact `Ext` sequence of
`0 → M → M → M / x M → 0`. -/
theorem exists_isRegular_quotSMulTop [IsNoetherianRing R] [Small.{v} R] (M : ModuleCat.{v} R)
    [Module.Finite R M] {n : ℕ} {rs : List R} (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsRegular M rs) {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular (QuotSMulTop x M) rs' := by
  have : Nontrivial M := hrs.nontrivial
  have h1 := ((ModuleCat.exists_isRegular_tfae (maximalIdeal R) (n + 1) M
    maximalIdeal_smul_top_lt_top).out 2 4).mpr (by exact ⟨rs, hlen, hmem, hrs⟩)
  have : Nontrivial (QuotSMulTop x M) := by
    rw [Submodule.Quotient.nontrivial_iff, ← lt_top_iff_ne_top]
    exact lt_of_le_of_lt (Submodule.smul_mono_left (Ideal.span_singleton_le_iff_mem _ |>.mpr hx)
      |>.trans_eq' (Submodule.ideal_span_singleton_smul x ⊤)) maximalIdeal_smul_top_lt_top
  refine ((ModuleCat.exists_isRegular_tfae (maximalIdeal R) n (ModuleCat.of R (QuotSMulTop x M))
    maximalIdeal_smul_top_lt_top).out 2 4).mp fun i hi ↦ ?_
  have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h1 i (by omega))
  have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h1 (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    ((Ext.covariant_sequence_exact₃' _ hreg.smulShortComplex_shortExact) i (i + 1) rfl)
    (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)

/-- The ring-quotient form of `exists_isRegular_quotSMulTop`: if `R / I` has a regular sequence
of length `n + 1` in the maximal ideal and `x` in the maximal ideal is `R / I`-regular, then
`R / (I + (x))` has one of length `n`. -/
theorem exists_isRegular_quotient_sup [IsNoetherianRing R] (I : Ideal R) {n : ℕ} {rs : List R}
    (hlen : rs.length = n + 1) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsRegular (R ⧸ I) rs)
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular (R ⧸ I) x) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular (R ⧸ (I ⊔ Ideal.span {x})) rs' := by
  obtain ⟨rs', hlen', hmem', hrs'⟩ :=
    exists_isRegular_quotSMulTop (ModuleCat.of R (R ⧸ I)) hlen hmem hrs hx hreg
  exact ⟨rs', hlen', hmem', (Ideal.quotSMulTopQuotientEquiv I x).isRegular_congr rs' |>.mp hrs'⟩

/-- **Associated primes and depth** (Matsumura, Thm. 17.2): if `M` has a regular sequence of
length `r` in the maximal ideal, then `dim R / Q ≥ r` for every associated prime `Q` of `M`. -/
theorem length_le_ringKrullDim_quotient_of_mem_associatedPrimes [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsRegular M rs) {Q : Ideal R}
    (hQ : Q ∈ associatedPrimes R M) : (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Q) := by
  induction rs generalizing M Q with
  | nil =>
    have := hQ.isPrime
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  | cons y ys ih =>
    obtain ⟨hy, hys⟩ := (isRegular_cons_iff M y ys).mp hrs
    have hym : y ∈ maximalIdeal R := hmem y List.mem_cons_self
    obtain ⟨hQp, x, hx⟩ := (isAssociatedPrime_iff).mp hQ
    have := hQp
    set N := Submodule.torsionBySet R M Q
    have hxN : x ∈ N := by
      refine (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨q, hq⟩ ↦ ?_
      rw [hx] at hq
      simpa using Submodule.mem_colon_singleton.mp hq
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hQp.ne_top
      rw [hx, eq_top_iff]
      intro r _
      simp [Submodule.mem_colon_singleton]
    -- Some element of `N` is not in `y M`, by Nakayama.
    obtain ⟨v, hvN, hvy⟩ : ∃ v ∈ N, v ∉ y • (⊤ : Submodule R M) := by
      by_contra! H
      have hNy : N ≤ maximalIdeal R • N := by
        intro v hv
        obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (H v hv)
        have hw : w ∈ N := by
          refine (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨q, hq⟩ ↦ hy ?_
          have := (Submodule.mem_torsionBySet_iff _ _).mp hv ⟨q, hq⟩
          simp only at this ⊢
          rw [smul_comm, this, smul_zero]
        exact Submodule.smul_mem_smul hym hw
      have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) N
        (IsNoetherian.noetherian N) hNy (maximalIdeal_le_jacobson _)
      exact hx0 ((Submodule.mem_bot R).mp (this ▸ hxN))
    set v' : QuotSMulTop y M := Submodule.Quotient.mk v
    have hv' : v' ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨Q', hQ', hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R v' hv'
    have := hQ'.isPrime
    have hQQ' : Q < Q' := by
      refine lt_of_le_of_ne (fun q hq ↦ hle ?_) fun h ↦ ?_
      · rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
          (Submodule.mem_torsionBySet_iff _ _).mp hvN ⟨q, hq⟩, Submodule.Quotient.mk_zero]
      · have hyQ : y ∈ Q := h ▸ hle (by
          rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
        have := (Submodule.mem_torsionBySet_iff _ _).mp hxN ⟨y, hyQ⟩
        exact hx0 (hy (by simpa using this))
    have h1 := ih (fun r hr ↦ hmem r (List.mem_cons_of_mem _ hr)) hys hQ'
    have h2 := Ideal.ringKrullDim_quotient_add_one_le_of_lt hQQ'
    calc ((y :: ys).length : WithBot ℕ∞) = (ys.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Q') + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ Q) := h2

/-- **Unmixedness from depth** (Matsumura, Thm. 17.4): if `dim R = t`, `ht I = k` and `R / I` has
a regular sequence of length `t - k` in the maximal ideal, then every associated prime of `R / I`
has height `k`. -/
theorem height_eq_of_mem_associatedPrimes [IsNoetherianRing R] {I : Ideal R} {k t : ℕ}
    (hdim : ringKrullDim R = t) (hI : I.height = k) {rs : List R} (hlen : rs.length + k = t)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsRegular (R ⧸ I) rs) {Q : Ideal R}
    (hQ : Q ∈ associatedPrimes R (R ⧸ I)) : Q.height = k := by
  have := hQ.isPrime
  have hIQ : I ≤ Q := by
    simpa [Submodule.annihilator_top, Ideal.annihilator_quotient] using hQ.annihilator_le
  have h1 : (k : ℕ∞) ≤ Q.height := hI ▸ Ideal.height_mono hIQ
  have h2 := length_le_ringKrullDim_quotient_of_mem_associatedPrimes hmem hrs hQ
  have h3 := Ideal.height_add_ringKrullDim_quotient_le Q
  rw [hdim] at h3
  have h4 : (Q.height : WithBot ℕ∞) + rs.length ≤ t :=
    (by gcongr : (Q.height : WithBot ℕ∞) + rs.length ≤ Q.height + ringKrullDim (R ⧸ Q)).trans h3
  refine le_antisymm ?_ h1
  have hfin : Q.height ≠ ⊤ := by
    rintro h
    rw [h] at h4
    norm_cast at h4
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hq] at h4 ⊢
  norm_cast at h4 ⊢
  omega

/-- An element of the maximal ideal outside its square is part of a minimal system of
generators: the maximal ideal is generated by `x` and fewer than `spanFinrank 𝔪` other
elements. -/
theorem exists_span_insert_eq_maximalIdeal [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ s : Set R, s.Finite ∧ s.ncard + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert x s) = maximalIdeal R := by
  set V := CotangentSpace R
  set v : V := (maximalIdeal R).toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]; exact hx2
  set U := Submodule.span (ResidueField R) {v}
  set W := V ⧸ U
  have hW : Module.finrank (ResidueField R) W + 1 = Module.finrank (ResidueField R) V := by
    rw [← Submodule.finrank_quotient_add_finrank U, finrank_span_singleton hv]
  set b := Module.finBasis (ResidueField R) W
  have hmk : ∀ w : W, ∃ y : maximalIdeal R, U.mkQ ((maximalIdeal R).toCotangent y) = w :=
    fun w ↦ by
      obtain ⟨u, rfl⟩ := U.mkQ_surjective w
      obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ u
      exact ⟨y, rfl⟩
  choose y hy using hmk
  set t : Set (maximalIdeal R) := insert ⟨x, hx⟩ (Set.range (y ∘ b))
  have ht : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' t) = ⊤ := by
    set S := Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' t)
    have hvS : U ≤ S :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨_, Set.mem_insert _ _, rfl⟩)
    have hmap : S.map U.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨_, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩, hy (b i)⟩
    have := Submodule.comap_map_mkQ U S
    rw [hmap, Submodule.comap_top, sup_eq_right.mpr hvS] at this
    exact this.symm
  have hspan := (CotangentSpace.span_image_eq_top_iff).mp ht
  refine ⟨Set.range (fun i ↦ (y (b i) : R)), Set.finite_range _, ?_, ?_⟩
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hW]
    gcongr
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
  · have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_top, Submodule.range_subtype, ← Submodule.span_image] at this
    refine Eq.trans ?_ this
    simp only [t, Set.image_insert_eq, Submodule.coe_subtype]
    congr 2
    ext; simp

end IsLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The quotient by an element of the maximal ideal outside its square is local. -/
theorem isLocalRing_quotient {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) :=
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hx))
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- **Cutting a regular local ring by a minimal generator** (Matsumura, Thm. 14.2): for `x` in
the maximal ideal but not in its square, `R / (x)` is regular local, its maximal ideal needs one
generator less, and its dimension is one less. -/
theorem quotient {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    letI := isLocalRing_quotient hx
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient hx
  set f := Ideal.Quotient.mk (Ideal.span {x})
  obtain ⟨s, hs, hcard, hspan⟩ := exists_span_insert_eq_maximalIdeal hx hx2
  have hm : maximalIdeal (R ⧸ Ideal.span {x}) = Ideal.span (f '' s) := by
    rw [← map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective, ← hspan, Ideal.map_span,
      Set.image_insert_eq, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x),
      Ideal.span_insert_zero]
  have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ s.ncard := by
    rw [hm]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _)).trans
      (Set.ncard_image_le hs)
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span {x}) ?_).trans ?_
    · exact ringJacobson_eq_maximalIdeal R ▸ (Ideal.span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span {x})
  have h4 := (isRegularLocalRing_iff R).mp ‹_›
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ringKrullDim (R ⧸ Ideal.span {x}) = k := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.span {x})
    generalize ringKrullDim (R ⧸ Ideal.span {x}) = d at h0 h3
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe d => induction d using ENat.recTopCoe with
      | top => exact absurd h3 (by exact_mod_cast (ENat.natCast_lt_top _).not_ge)
      | coe k => exact ⟨k, rfl⟩
  rw [hk] at h2 h3 ⊢
  rw [← h4] at h2 ⊢
  norm_cast at h2 h3 ⊢
  refine ⟨(isRegularLocalRing_iff _).mpr ?_, by omega, by omega⟩
  rw [hk]
  norm_cast
  omega

/-- In a regular local ring of positive dimension there is an element of the maximal ideal
outside its square and outside every minimal prime (prime avoidance). -/
theorem exists_mem_maximalIdeal_notMem {n : ℕ} (hn : (maximalIdeal R).spanFinrank = n + 1) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ P ∈ minimalPrimes R, x ∉ P := by
  classical
  have h4 := (isRegularLocalRing_iff R).mp ‹_›
  have hdim : ringKrullDim R ≠ 0 := by
    rw [← h4, hn]; exact_mod_cast Nat.succ_ne_zero n
  have hsq := maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim
  have hP : ∀ P ∈ minimalPrimes R, ¬ maximalIdeal R ≤ P := by
    intro P hP hle
    have := hP.1.1
    have hPm : P = maximalIdeal R := le_antisymm (le_maximalIdeal this.ne_top) hle
    have h0 := Ideal.height_eq_zero_iff.mpr hP
    rw [hPm] at h0
    apply hdim
    rw [← maximalIdeal_height_eq_ringKrullDim, h0]
    rfl
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  set f : Option (Ideal R) → Ideal R := fun o ↦ o.elim (maximalIdeal R ^ 2) id
  set s : Finset (Option (Ideal R)) := insert none (hfin.toFinset.image some)
  have hprime : ∀ i ∈ s, i ≠ none → i ≠ none → (f i).IsPrime := by
    intro i hi hne _
    obtain ⟨P, hP, rfl⟩ : ∃ P ∈ hfin.toFinset, some P = i := by
      simpa [s, hne] using hi
    exact (hfin.mem_toFinset.mp hP).1.1
  by_contra! H
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ i ∈ (s : Set (Option (Ideal R))), (f i : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hx2
    · obtain ⟨P, hP, hxP⟩ := H x hx hx2
      exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hP)))) hxP
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime none none hprime).mp hsub
  cases i with
  | none => exact hsq.not_ge hle
  | some P =>
    have hPs : P ∈ hfin.toFinset := by simpa [s] using hi
    exact hP P (hfin.mem_toFinset.mp hPs) hle

/-- **A regular local ring is a domain** (Matsumura, Thm. 14.3). By induction on the dimension:
for `x` in the maximal ideal, outside its square and outside the minimal primes, `R / (x)` is a
domain, so a minimal prime `P ⊆ (x)` satisfies `P = x P`, and `P = 0` by Nakayama. -/
theorem isDomain : IsDomain R := by
  suffices ∀ n : ℕ, ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R from this _ R rfl
  intro n
  induction n with
  | zero =>
    intro R _ _ hn
    exact (isField_iff_maximalIdeal_eq.mpr ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp hn)).isDomain
  | succ n ih =>
    intro R _ _ hn
    obtain ⟨x, hx, hx2, hxP⟩ := exists_mem_maximalIdeal_notMem hn
    have := isLocalRing_quotient hx
    obtain ⟨hreg, hrank, -⟩ := quotient hx hx2
    have : (Ideal.span {x}).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp (ih _ (by omega))
    obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Ideal.span {x})
    have := hP.1.1
    have hPbot : P = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) P
        (IsNoetherian.noetherian P) (fun y hy ↦ ?_) (maximalIdeal_le_jacobson _)
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hPx hy)
      have ha : a ∈ P := (this.mem_or_mem hy).resolve_right (hxP P hP)
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx ha
    have : (⊥ : Ideal R).IsPrime := hPbot ▸ this
    exact IsDomain.of_bot_isPrime R

/-- **A regular system of parameters is a regular sequence** (Matsumura, Thm. 14.3, 17.8): the
maximal ideal of a regular local ring `R` contains an `R`-regular sequence of length
`spanFinrank 𝔪 = dim R`. -/
theorem exists_isRegular : ∃ rs : List R, rs.length = (maximalIdeal R).spanFinrank ∧
    (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular R rs := by
  suffices ∀ n : ℕ, ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → ∃ rs : List R, rs.length = n ∧
        (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular R rs from this _ R rfl
  intro n
  induction n with
  | zero => exact fun R _ _ _ ↦ ⟨[], rfl, by simp, IsRegular.nil R R⟩
  | succ n ih =>
    intro R _ _ hn
    obtain ⟨x, hx, hx2, -⟩ := exists_mem_maximalIdeal_notMem hn
    have := isLocalRing_quotient hx
    obtain ⟨hreg, hrank, -⟩ := quotient hx hx2
    obtain ⟨rs', hlen, hmem, hrs'⟩ := ih (R ⧸ Ideal.span {x}) (by omega)
    have := isDomain (R := R)
    have hx0 : x ≠ 0 := by
      rintro rfl; exact hx2 (zero_mem _)
    set g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    have hg : ∀ r, Ideal.Quotient.mk (Ideal.span {x}) (g r) = r :=
      Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    have hspan : (Ideal.span {x} : Submodule R R) = x • (⊤ : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    set e : (R ⧸ Ideal.span {x}) ≃+ QuotSMulTop x R :=
      (Submodule.quotEquivOfEq _ _ hspan).toAddEquiv
    refine ⟨x :: rs'.map g, by simp [hlen], ?_, IsRegular.cons (IsSMulRegular.of_ne_zero hx0) ?_⟩
    · simp only [List.mem_cons, List.mem_map, forall_eq_or_imp]
      refine ⟨hx, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      by_contra h
      have hu := (IsLocalRing.notMem_maximalIdeal.mp h).map (Ideal.Quotient.mk (Ideal.span {x}))
      rw [hg] at hu
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp (hmem r hr)) hu
    · refine (e.isRegular_congr ?_).mp hrs'
      refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ y ↦ ?_)
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      have : r • Ideal.Quotient.mk (Ideal.span {x}) z = g r • Ideal.Quotient.mk _ z := by
        rw [smul_eq_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hg]
      rw [this]
      exact (Submodule.quotEquivOfEq _ _ hspan).map_smul (g r) (Ideal.Quotient.mk _ z)

end IsRegularLocalRing
