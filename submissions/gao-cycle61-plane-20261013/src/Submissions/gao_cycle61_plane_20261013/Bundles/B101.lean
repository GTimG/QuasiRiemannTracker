/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B100

/- BEGIN ORIGINAL Cycle61.Density.ExceptionalLift; sha256 f152728adfeb35f39aa5b19881c1a5de5beffa337e5bab9c7985c7eb9676321b -/
section
                                   

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ConcretePrimeRowBridge
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- A uniform sixth-power lift for predicates of the free core. This pays
all multiples of finitely many exceptional cores, including principal rows. -/
theorem raw_core_density_uniform :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : FreeRow → Prop) (C ρ : ℝ), 0 ≤ C → 2/7 ≤ ρ →
      (∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ P u) → (F.card : ℝ) ≤ C*Y^ρ) →
      ∀ H : ℝ, 0 < H → ∀ R : Finset NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ P (sixthFrequencyEquiv.symm h).1) →
        (R.card : ℝ) ≤ C*D*H^ρ := by
  let w : NZIdeal → ℝ := fun B => (B.val.absNorm : ℝ)^(-6*(2/7 : ℝ))
  have hw := ideal_sixth_power_summable (2/7) (by norm_num)
  have hw0 : ∀ B, 0 ≤ w B := fun B => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D : ℝ := (∑' B : NZIdeal, w B)+1
  have hsum : 0 ≤ ∑' B : NZIdeal, w B := tsum_nonneg hw0
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro P C ρ hC hρ hfree H hH R hR
  have hBpos (B : NZIdeal) : 0 < (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hBone (B : NZIdeal) : 1 ≤ (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hfiber (B : NZIdeal) : ((sixthFreeFiber R B).card : ℝ) ≤
      C*(H/(B.val.absNorm : ℝ)^6)^ρ := by
    let Y : ℝ := H/(B.val.absNorm : ℝ)^6
    have hmem (u : FreeRow) (hu : u ∈ sixthFreeFiber R B) : rowNorm u ≤ Y ∧ P u := by
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
      obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
      have he : p = (u,B) := Prod.ext hpu hpB
      subst p
      have hr := hR _ ((mem_sixthPairs R (u,B)).mp hp)
      rw [raw_sixth_norm] at hr
      exact ⟨(le_div_iff₀ (pow_pos (hBpos B) 6)).mpr hr.1,
        by simpa only [Equiv.symm_apply_apply] using hr.2⟩
    by_cases hY : 1 ≤ Y
    · exact hfree Y hY (sixthFreeFiber R B) hmem
    · have he : sixthFreeFiber R B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hY ((rowNorm_ge_one u).trans (hmem u hu).1)
      rw [he, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hc : (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
      C*(H/(B.val.absNorm : ℝ)^6)^ρ := by
    rw [raw_sixth_cardinality R, Nat.cast_sum]
    exact Finset.sum_le_sum (fun B _ => hfiber B)
  simp_rw [sixth_window_power H _ ρ hH (hBpos _)] at hc
  calc
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
        C*(H^ρ*(B.val.absNorm : ℝ)^(-6*ρ)) := hc
    _ ≤ ∑ B ∈ (sixthPairs R).image Prod.snd, C*(H^ρ*w B) := by
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH.le _)
      exact Real.rpow_le_rpow_of_exponent_le (hBone B) (by linarith)
    _ = (C*H^ρ)*∑ B ∈ (sixthPairs R).image Prod.snd, w B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ ≤ (C*H^ρ)*∑' B : NZIdeal, w B := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum _ (fun B _ => hw0 B)) (by positivity)
    _ ≤ C*D*H^ρ := by
      have ht : (∑' B : NZIdeal, w B) ≤ D := by dsimp [D]; linarith
      calc
        _ ≤ (C*H^ρ)*D := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by ring

#print axioms raw_core_density_uniform
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.ExceptionalLift -/

/- BEGIN ORIGINAL Cycle61.Density.ActualZeros; sha256 c26e36011da9e2e6ec22a854fd802b1b8908e16da48dbdd3c6cf0aff9dbd20d6 -/
section
                                      

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical

def actualZeroRow {Label : Type*} (data : Label → RowData) (a T : ℝ)
    (u : NonzeroElement) : Prop :=
  ∃ j s, LFunction ((data j).character u) s = 0 ∧
    (s ≠ 1 ∨ ((data j).character u).residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

def orientedActualZeroRow {Label : Type*} (data : Label → RowData)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroElement) : Prop :=
  ∃ j s, let χ := if reverse j then ((data j).character u).inverse else (data j).character u
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem actual_zero_regular_bin {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (a T : ℝ) (ha : 33/40 ≤ a)
    (u : FreeRow) (hu : ¬D.exceptionalCore u)
    (hz : actualZeroRow D.data a T ⟨u.val, u.property.1⟩) :
    rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩ := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  have hn := D.regular_nonprincipal u hu
  have hmax := zero_re_le_maximum (fun j => (D.data j).character ⟨u.val, u.property.1⟩)
    hn T j (by linarith) ht hz
  have hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta := by
    have hh := HeckeZeroSupremum.zero_re_le_beta ((D.data j).character ⟨u.val, u.property.1⟩)
      (by linarith) hpole hz
    linarith
  exact ⟨hn, hs.trans hmax, (zeroMaximum_le_beta _ hn hβlo T).trans incumbent_beta_upper⟩

/-- Actual zeros of any orientation lie over either a counted nonprincipal
core or one of the fixed exceptional cores. Conjugation applies to the
whole character, including its Euler holes. -/
theorem oriented_zero_core_predicate {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (reverse : Label → Bool) (a T : ℝ)
    (ha : 33/40 ≤ a) (u : NonzeroFrequency)
    (hz : orientedActualZeroRow D.data reverse a T u) :
    let core := (sixthFrequencyEquiv.symm u).1
    rawZeroBin D.data a (7/8) T ⟨core.val, core.property.1⟩ ∨ D.exceptionalCore core := by
  let p := sixthFrequencyEquiv.symm u
  have hpu : sixthFrequencyEquiv p = u := sixthFrequencyEquiv.apply_symm_apply u
  change rawZeroBin D.data a (7/8) T ⟨p.1.val, p.1.property.1⟩ ∨ D.exceptionalCore p.1
  by_cases hex : D.exceptionalCore p.1
  · exact Or.inr hex
  · have hn := D.regular_nonprincipal p.1 hex
    obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
    have hraw : ((D.data j).character u).residue ≠ 1 := by
      have hh := amplified_nonprincipal (D.data j) ⟨p.1.val, p.1.property.1⟩ p.2 (hn j)
      change ((D.data j).character (sixthFrequencyEquiv p)).residue ≠ 1 at hh
      rw [hpu] at hh
      exact hh
    have hz' : actualZeroRow D.data a T u := by
      cases hr : reverse j
      · exact ⟨j, s, by simpa only [hr, Bool.false_eq_true, ite_false] using hz,
          Or.inr hraw, hs, ht⟩
      · have hi : LFunction ((D.data j).character u) (starRingEnd ℂ s) = 0 := by
          simpa only [hr, ite_true, LFunction_inverse_conj _ hraw, map_eq_zero] using hz
        exact ⟨j, starRingEnd ℂ s, hi, Or.inr hraw,
          by simpa only [Complex.conj_re] using hs, by simpa using ht⟩
    obtain ⟨j', s', hz', hpole', hs', ht'⟩ := hz'
    have hzero : LFunction ((D.data j').character ⟨p.1.val, p.1.property.1⟩) s' = 0 := by
      apply (sixthFrequency_positive_zeros (D.data j') p (hn j') (show 0 < s'.re by linarith)).mp
      rw [hpu]
      exact hz'
    exact Or.inl (actual_zero_regular_bin D a T ha p.1 hex
      ⟨j', s', hzero, Or.inr (hn j'), hs', ht'⟩)

theorem fixed_dictionary_eventual_with_exceptions {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧
        (rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u)) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ := fixed_dictionary_eventual_free_density D loss hloss
  let E : Finset FreeRow := D.exceptional_cores_finite.toFinset
  refine ⟨J, C+(E.card : ℝ), by positivity, ?_⟩
  filter_upwards [hf, eventually_ge_atTop (1 : ℝ)] with Y hf hY
  intro a T ha ha' hT rows hrows
  let good : FreeRow → Prop := fun u => rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩
  let kept := rows.filter good
  let removed := rows.filter (fun u => ¬good u)
  have hk := hf a T ha ha' hT kept (fun u hu =>
    ⟨(hrows u (Finset.mem_filter.mp hu).1).1, (Finset.mem_filter.mp hu).2⟩)
  have hsub : removed ⊆ E := by
    intro u hu
    have hr := hrows u (Finset.mem_filter.mp hu).1
    exact (Set.Finite.mem_toFinset _).mpr (hr.2.resolve_left (Finset.mem_filter.mp hu).2)
  have hc : (removed.card : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hpart : (rows.card : ℝ) = (kept.card : ℝ)+(removed.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows) (p := good)).symm
  have hρ : 0 ≤ unmarkedDensity (2*a-1)+loss := by
    linarith [unmarkedDensity_ge_two_sevenths (show 2*a-1 ≤ 3/4 by linarith)]
  have hweight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
  have hpower : 1 ≤ Y^(unmarkedDensity (2*a-1)+loss) := Real.one_le_rpow hY hρ
  have he : (E.card : ℝ) ≤ (E.card : ℝ)*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
    have he0 : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ (E.card : ℝ)*(1+T)^J := le_mul_of_one_le_right he0 hweight
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpower
  rw [hpart]
  calc
    _ ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss)+
        (E.card : ℝ)*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := add_le_add hk (hc.trans he)
    _ = _ := by ring

/-- Actual D+ for every member of the fixed natural dictionary, in either
whole-character orientation. Finite inducing cores and all their infinitely
many raw sixth-power multiples are paid by the same uniform convolution. -/
theorem fixed_dictionary_actual_raw_zero_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ orientedActualZeroRow D.data reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ := fixed_dictionary_eventual_with_exceptions D loss hloss
  let P : DensityParameter → FreeRow → Prop := fun p u =>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : DensityParameter → ℝ := fun p => unmarkedDensity (2*p.val.1-1)+loss
  let weight : DensityParameter → ℝ := fun p => (1+p.val.2)^J
  have hρ (p : DensityParameter) : 2/7 ≤ exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths (show 2*p.val.1-1 ≤ 3/4 by linarith [p.property.2.1])]
  have hw (p : DensityParameter) : 1 ≤ weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : DensityParameter, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D₀, hD₀, hraw⟩ := raw_core_density_uniform
  refine ⟨J, C'*D₀, mul_pos hC' hD₀, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  let p : DensityParameter := ⟨(a,T), ha, ha', hT⟩
  have hb := hraw (P p) (C'*weight p) (exponent p) (by have := hw p; positivity) (hρ p)
    (fun Y hY F hF => hfree Y hY p F hF) H hH rows
    (fun u hu => ⟨(hrows u hu).1, oriented_zero_core_predicate D reverse a T ha u (hrows u hu).2⟩)
  convert hb using 1
  dsimp [p, weight, exponent]
  ring

#print axioms fixed_dictionary_actual_raw_zero_density
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.ActualZeros -/

/- BEGIN ORIGINAL Cycle61.Density.NaturalEndpoint; sha256 90f31bfe50124f37390f66ee80d080043298dfe26a2f9a0ef0c25a275e789526 -/
section
                                  

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
open Set
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open CenteredMomentNaturalRowSource HeckeFiniteDeletion
local notation "O" => HeckeFamily.O

/-- Every fixed inducing-character list has an admissible fixed ideal list. -/
def FixedUnmarkedDictionary.ofBases {Label : Type*} (base : Label → Character) :
    FixedUnmarkedDictionary Label where
  base := base
  fixedIdeal := fun j => Ideal.span {(72 : O)} ⊓ (base j).modulus
  nonzero := fun j => Ideal.inf_ne_bot_of_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0)) (base j).modulus_ne_bot
  proper := by
    intro j h
    have h72 : (Ideal.span {(72 : O)} : Ideal O) ≤ Ideal.span {(2 : O)} :=
      Ideal.span_singleton_le_span_singleton.mpr ⟨36, by norm_num⟩
    exact CanonicalQuadraticSieve.twoIdeal_maximal.isPrime.ne_top
      (top_le_iff.mp (h ▸ (inf_le_left.trans h72)))
  divides72 := fun _ => inf_le_left
  dividesBase := fun _ => inf_le_right

def naturalRawFamily {Label : Type*} (base : Label → Character) (u : NonzeroElement) :
    Label → Character := fun j => (naturalRow (base j) u.val u.property).character

theorem natural_raw_coefficients (η : Character) (u : NonzeroElement) (I : Ideal O) :
    idealCoeff (naturalRow η u.val u.property).character I =
      idealCoeff ((momentData η).character u) I := by
  rw [NaturalRow.ideal]
  have hc := HeckeRowClosure.idealCoeff_eq_row η ((momentData η).character u)
    (momentData η).m (momentData η).f u.val ((momentData η).character_spec u) I
  simp only [momentData, one_pow, mul_one] at hc
  have hm : CenteredMomentSecondHeightFamily.fixedBadMask = rowMaskElement := by
    unfold CenteredMomentSecondHeightFamily.fixedBadMask rowMaskElement
    ring
  rw [hm]
  exact hc.symm

theorem positive_zeros_eq_of_coefficients (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    (LFunction χ s = 0 ↔ LFunction ψ s = 0) ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) := by
  have hm := coefficient_equality_mask χ ψ hcoeff
  refine ⟨?_, ?_⟩
  · rw [LFunction_eq_of_mask_nonpole χ ψ hm hs hpole, mul_eq_zero]
    exact or_iff_left (factors_ne_zero χ.modulus ψ hs)
  · rcases hpole with h | h
    · exact Or.inl h
    · exact Or.inr (fun hp => h ((principal_iff_of_mask χ ψ hm).mpr hp))

def naturalActualZeroRow {Label : Type*} (base : Label → Character)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroElement) : Prop :=
  ∃ j s, let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem natural_zero_to_literal_dictionary {Label : Type*}
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ)
    (ha : 33/40 ≤ a) (u : NonzeroElement)
    (hz : naturalActualZeroRow base reverse a T u) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases base).data reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  let ψ := if reverse j then ((momentData (base j)).character u).inverse else (momentData (base j)).character u
  have hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I := by
    intro I
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false, naturalRawFamily] using natural_raw_coefficients (base j) u I
    · dsimp [χ, ψ]
      simp only [hr, ite_true]
      rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj]
      dsimp only [naturalRawFamily]
      rw [natural_raw_coefficients]
  have hh := positive_zeros_eq_of_coefficients χ ψ hc (show 0 < s.re by linarith) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- Lemma 2.1, directly for the bounded-conductor natural characters with
coefficients `c_η(I) s_{m₀⁶u}(I)`, including every raw integer row and either
whole-character orientation. The dictionary is fixed before the scale. -/
theorem fixed_natural_dictionary_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ naturalActualZeroRow base reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_dictionary_actual_raw_zero_density
    (FixedUnmarkedDictionary.ofBases base) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, natural_zero_to_literal_dictionary base reverse a T ha u (hrows u hu).2⟩)

#print axioms fixed_natural_dictionary_raw_density

theorem fixed_natural_dictionary_free_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ Y : ℝ, 1 ≤ Y → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧
        naturalActualZeroRow base reverse a T ⟨u.val, u.property.1⟩) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_natural_dictionary_raw_density base loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT Y hY rows hrows
  let embedRow : FreeRow → NonzeroFrequency := fun u => ⟨u.val, u.property.1⟩
  have hinj : Function.Injective embedRow := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : NonzeroFrequency => z.val) h
  have hcard : (rows.image embedRow).card = rows.card := Finset.card_image_of_injective rows hinj
  have hr : ∀ u ∈ rows.image embedRow, rawFrequencyNorm u ≤ Y ∧ naturalActualZeroRow base reverse a T u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have hh := hb reverse a T ha ha' hT Y (zero_lt_one.trans_le hY) (rows.image embedRow) hr
  simpa only [hcard] using hh

#print axioms fixed_natural_dictionary_free_density
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.NaturalEndpoint -/

/- BEGIN ORIGINAL Cycle61.Density.NaturalMaskTransport; sha256 7a3c2708469535e292e7d02d695c0d412881a06a3796e7f558c8e0ce4423d78f -/
section
                                      

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeFiniteDeletion ProbePhysical
local notation "O" => HeckeFamily.O

theorem inverse_coefficient_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    ∀ I : Ideal O, idealCoeff χ.inverse I =
      if IsCoprime I χ.inverse.modulus then idealCoeff ψ.inverse I else 0 := by
  intro I
  rw [show χ.inverse.modulus = χ.modulus from rfl]
  rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj, hmask]
  by_cases h : IsCoprime I χ.modulus <;> simp only [h, ite_true, ite_false, map_zero]

theorem positive_zeros_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    (LFunction χ s = 0 ↔ LFunction ψ s = 0) ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) := by
  refine ⟨?_, ?_⟩
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero]
    exact or_iff_left (factors_ne_zero χ.modulus ψ hs)
  · rcases hpole with h | h
    · exact Or.inl h
    · exact Or.inr (fun hp => h ((principal_iff_of_mask χ ψ hmask).mpr hp))

def maskedActualZeroRow {Label : Type*}
    (family : Label → NonzeroFrequency → Character)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroFrequency) : Prop :=
  ∃ j s, let χ := if reverse j then (family j u).inverse else family j u
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem masked_zero_to_natural {Label : Type*}
    (base : Label → Character) (family : Label → NonzeroFrequency → Character)
    (hmask : ∀ j u I, idealCoeff (family j u) I =
      if IsCoprime I (family j u).modulus then idealCoeff (naturalRawFamily base u j) I else 0)
    (reverse : Label → Bool) (a T : ℝ) (ha : 0 < a) (u : NonzeroFrequency)
    (hz : maskedActualZeroRow family reverse a T u) :
    naturalActualZeroRow base reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (family j u).inverse else family j u
  let ψ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  have hm : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false] using hmask j u
    · simpa only [χ, ψ, hr, ite_true] using inverse_coefficient_mask _ _ (hmask j u)
  have hh := positive_zeros_eq_of_mask_nonpole χ ψ hm (ha.trans_le hs) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- Moving finite Euler punctures are transported to the fixed natural dictionary.
The representatives may have arbitrarily large moduli. -/
theorem fixed_natural_dictionary_masked_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ family : Label → NonzeroFrequency → Character,
      (∀ j u I, idealCoeff (family j u) I =
        if IsCoprime I (family j u).modulus then idealCoeff (naturalRawFamily base u j) I else 0) →
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ maskedActualZeroRow family reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_natural_dictionary_raw_density base loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro family hmask reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, masked_zero_to_natural base family hmask reverse a T
      (by linarith) u (hrows u hu).2⟩)

#print axioms fixed_natural_dictionary_masked_raw_density
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.NaturalMaskTransport -/
