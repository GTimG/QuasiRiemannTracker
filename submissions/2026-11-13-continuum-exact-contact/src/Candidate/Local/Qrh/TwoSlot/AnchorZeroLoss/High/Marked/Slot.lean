/- Modified by Joseph Bebel (2026-11-12): actual source adapters for the
smaller-tolerance HIGH contract; original notices follow. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Pattern of `Interface.Bridge.physical_eq_conj_directSlot`; uses Hailey Collet's
`naturalSlot_eq_direct`, `naturalSlot_annular_filter` (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Twist

/-!
# High.Marked.Slot

The coefficient dictionary between a core slot at a fixed height and a canonical ray-twisted
direct slot (`Contract.canonicalSlots`), and the normalisation of the profile.

* `coeff_eq`: on the canonical pool (norms above the fixed masks) the core coefficient
  `excluded η mask · rowHom(fbm⁶) · relChar(η₀, θ) · annular(c·W')` is
  `c · relChar(data.η, θ') · data.η · annular(W')`.
* `node_slot_eq`: the slot identity.
* `canon_beta_norm_le`: `‖β‖ ≤ 1` on the canonical pool when `‖W'‖ ≤ 1`.
* `normalized_profile`: every smooth profile supported in `[1,2]` is `c·W'` with `c ≥ 1`,
  `W'` smooth, supported in `[1,2]`, `‖W'‖ ≤ 1`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface
local notation "O" => HeckeFamily.O
local instance markedSlotQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
local instance markedSlotPID : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- Smooth profiles supported in `[1,2]` are bounded: normalisation `W = c·W'`, `‖W'‖ ≤ 1`. -/
theorem normalized_profile (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) :
    ∃ c : ℝ, 1 ≤ c ∧ ∃ W' : ℝ → ℂ, ContDiff ℝ ∞ W' ∧ Function.support W' ⊆ Set.Icc (1:ℝ) 2 ∧
      (∀ y, ‖W' y‖ ≤ 1) ∧ ∀ y, W y = (c : ℂ) * W' y := by
  have hcs : HasCompactSupport W := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra h
    exact hx (hWs h)
  obtain ⟨B, hB⟩ := hW.continuous.bounded_above_of_compact_support hcs
  refine ⟨max 1 B, le_max_left _ _, fun y => ((max 1 B : ℝ) : ℂ)⁻¹ * W y,
    contDiff_const.mul hW, ?_, ?_, ?_⟩
  · intro y hy
    apply hWs
    intro h0
    apply hy
    simp [h0]
  · intro y
    have hc : (0:ℝ) < max 1 B := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [inv_mul_le_iff₀ hc, mul_one]
    exact (hB y).trans (le_max_right _ _)
  · intro y
    have hc : ((max 1 B : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- On the identity class the ray character `θ ∈ Characters rayM H` is trivial. -/
theorem rayChar_identity (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (θ : RayQuotient.Characters rayM H)
    {P : Ideal O} (hcl : P ∈ RayQuotient.identityClass rayM H) :
    idealCoeff (HeckeRayQuotient.character rayM H hH θ) P = 1 := by
  obtain ⟨hP0, a, ha, u, hua, huH⟩ := hcl
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hP0
    rw [← ha, Ideal.span_singleton_eq_bot]
  rw [HeckeRayQuotient.idealCoeff_character, ← ha]
  change IdealCharacter.ofResidue rayM (θ : MulChar (O⧸rayM) ℂ) _ (Ideal.span {a}) = 1
  rw [IdealCharacter.ofResidue_span _ _ _ ha0, ← hua]
  exact (RayOrthogonality.mem_characters_iff H _).mp θ.property u huH

section Coeff
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The canonical coefficient of the twist (the `β` of `canonicalSlots W' σ` with `θ' = ξ`). -/
def canonBeta (η η₀ : Character) (data : RowData) (W' : ℝ → ℂ) (D σ τ : ℝ) :
    Ideal O → ℂ := fun I =>
  idealCoeff (relativeCharacter (twistMod rayM η η₀)
      (RayOrthogonality.globalUnits (twistMod rayM η η₀)) le_rfl data.η (twistTheta rayM η η₀)) I *
    idealCoeff data.η I * HeckePrimeAnnular.annularWeight W' D σ τ I

theorem annular_smul (Wj W' : ℝ → ℂ) (c : ℂ) (hc : ∀ y, Wj y = c * W' y) (D σ τ : ℝ)
    (I : Ideal O) :
    HeckePrimeAnnular.annularWeight Wj D σ τ I = c * HeckePrimeAnnular.annularWeight W' D σ τ I := by
  unfold HeckePrimeAnnular.annularWeight
  rw [hc]; ring

include hH in
/-- **Coefficient identity** on the canonical pool. -/
theorem coeff_eq (η η₀ : Character) (data : RowData) (θ : RayQuotient.Characters rayM H)
    (Wj W' : ℝ → ℂ) (c : ℂ) (hc : ∀ y, Wj y = c * W' y) {D : ℝ} (hD : 0 < D) (σ τ : ℝ)
    (hT : ((twistMod rayM η η₀).absNorm : ℝ) < D)
    (hmask : ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) < D)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < D)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) < D)
    (P : Ideal O) (hP : P ∈ Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) D) :
    idealCoeff (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀)) P *
      CanonicalRowCompletion.idealRowHom (CenteredMomentSecondHeightFamily.fixedBadMask^6) P *
      (idealCoeff (relativeCharacter rayM H hH η₀ θ) P *
        HeckePrimeAnnular.annularWeight Wj D σ τ P) =
    c * canonBeta rayM η η₀ data W' D σ τ P := by
  simp only [Contract.canonicalPool, primePool, Finset.mem_filter] at hP
  obtain ⟨⟨_, hpr, hcl'⟩, hr⟩ := hP
  have hND : D ≤ (P.absNorm : ℝ) := by
    have := (le_div_iff₀ hD).mp hr.1; linarith
  have hcopT := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hpr
    (twistChar rayM η η₀).modulus_ne_bot (lt_of_lt_of_le hT hND)
  have hcl : P ∈ RayQuotient.identityClass rayM H :=
    (identityClass_twist_iff rayM H hH η η₀ hpr.ne_zero hcopT).mpr hcl'
  have hmask0 := Record12518109Natural.wholeAnchorMask_ne_zero rayM H hH η₀
  have hcopM := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hpr hmask0
    (lt_of_lt_of_le hmask hND)
  have hfbm0 : Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
  have hcopF := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hpr hfbm0
    (lt_of_lt_of_le hfbm hND)
  have hη0 := Qrh.MarkedAnchor.Interface.Bridge.eta_ne_zero data P hpr (lt_of_lt_of_le hdel hND)
  have : P.IsMaximal := (Ideal.isPrime_of_prime hpr).isMaximal hpr.ne_zero
  have hlam : ActualEisensteinCubic.lambda ∉ P := by
    intro hl
    have hm : CenteredMomentSecondHeightFamily.fixedBadMask ∈ P := by
      unfold CenteredMomentSecondHeightFamily.fixedBadMask
      exact P.mul_mem_right _ hl
    have hle : Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} ≤ P :=
      (Ideal.span_singleton_le_iff_mem P).mpr hm
    have htop : P ⊔ Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp hcopF
    rw [sup_eq_left.mpr hle] at htop
    exact (Ideal.isPrime_of_prime hpr).ne_top htop
  have hrow : CanonicalRowCompletion.idealRowHom
      (CenteredMomentSecondHeightFamily.fixedBadMask^6) P = 1 := by
    rw [CanonicalRowCompletion.idealRowHom_prime_sixth_mask _ P hlam, if_pos hcopF]
  have hex : idealCoeff (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀)) P =
      idealCoeff η P := by
    rw [excluded_ideal _ _ hmask0, if_pos hcopM]
  rw [hex, hrow, relativeCharacter_ideal rayM H hH η₀ θ P, rayChar_identity rayM H hH θ hcl,
    annular_smul Wj W' c hc]
  unfold canonBeta
  rw [relativeCharacter_ideal (twistMod rayM η η₀)
      (RayOrthogonality.globalUnits (twistMod rayM η η₀)) le_rfl data.η (twistTheta rayM η η₀) P,
    twistTheta_coeff, twist_coeff rayM H hH η η₀ P hcl,
    HeckeDetectorRelativePrime.idealCoeff_inverse data.η P]
  have hd : (idealCoeff data.η P)⁻¹ * idealCoeff data.η P = 1 := inv_mul_cancel₀ hη0
  linear_combination (-(c * idealCoeff η P * idealCoeff η₀.inverse P *
    HeckePrimeAnnular.annularWeight W' D σ τ P)) * hd

include hH in
/-- **Slot identity**: a core slot at a fixed height is a canonical ray-twisted direct slot. -/
theorem node_slot_eq (η η₀ : Character) (data : RowData) (θ : RayQuotient.Characters rayM H)
    (Wj W' : ℝ → ℂ) (hWjs : Function.support Wj ⊆ Set.Icc (1:ℝ) 2) (c : ℂ)
    (hc : ∀ y, Wj y = c * W' y) {D : ℝ} (hD : 0 < D) (σ τ : ℝ)
    (hT : ((twistMod rayM η η₀).absNorm : ℝ) < D)
    (hmask : ((Record12518109Natural.wholeAnchorMask rayM H hH η₀).absNorm : ℝ) < D)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < D)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) < D)
    (u : O) (hu : u ≠ 0) :
    naturalSlot (naturalRow (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
        u hu).character (primePool rayM H 2 D)
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
        HeckePrimeAnnular.annularWeight Wj D σ τ I) D =
    c * Contract.directSlot u
      (Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) D)
      (canonBeta rayM η η₀ data W' D σ τ) D := by
  have hfil : naturalSlot (naturalRow (excluded η
        (Record12518109Natural.wholeAnchorMask rayM H hH η₀)) u hu).character
      (primePool rayM H 2 D)
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
        HeckePrimeAnnular.annularWeight Wj D σ τ I) D =
      naturalSlot (naturalRow (excluded η
        (Record12518109Natural.wholeAnchorMask rayM H hH η₀)) u hu).character
      (Cycle61MarkedPlain.annularPool (primePool rayM H 2 D) D)
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I *
        HeckePrimeAnnular.annularWeight Wj D σ τ I) D :=
    (Cycle61MarkedPlain.naturalSlot_annular_filter _ _
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ θ) I) Wj hWjs D σ τ).symm
  rw [hfil, Record12518109GainDeletion.naturalSlot_eq_direct, pool_eq rayM H hH η η₀ hD hT]
  unfold Record12518109GainDeletion.directPrimeSlot Contract.directSlot
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  beta_reduce
  rw [coeff_eq rayM H hH η η₀ data θ Wj W' c hc hD σ τ hT hmask hfbm hdel I hI]
  ring

/-- `‖β‖ ≤ 1` on the canonical pool. -/
theorem canon_beta_norm_le (η η₀ : Character) (data : RowData) (W' : ℝ → ℂ)
    (hW'b : ∀ y, ‖W' y‖ ≤ 1) (D σ τ : ℝ) (hσ : 0 ≤ σ) (P : Ideal O)
    (hP : P ∈ Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) D) :
    ‖canonBeta rayM η η₀ data W' D σ τ P‖ ≤ 1 := by
  have hx : ((P.absNorm : ℝ)/D) ∈ Icc (1:ℝ) 2 := (Finset.mem_filter.mp hP).2
  have hxpos : 0 < (P.absNorm : ℝ)/D := lt_of_lt_of_le one_pos hx.1
  simp only [canonBeta, HeckePrimeAnnular.annularWeight, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have h1 := relativeCharacter_norm (twistMod rayM η η₀)
    (RayOrthogonality.globalUnits (twistMod rayM η η₀)) le_rfl data.η (twistTheta rayM η η₀) P
  have h2 := idealCoeff_norm_le_one data.η P
  have h3 := hW'b ((P.absNorm : ℝ)/D)
  have h4 : ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift σ τ).re) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hx.1
    simp only [Complex.neg_re, HeckeDyadic.shift_re]
    linarith
  have h5 : 0 ≤ ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift σ τ).re) :=
    Real.rpow_nonneg hxpos.le _
  have h12 : ‖idealCoeff (relativeCharacter (twistMod rayM η η₀)
      (RayOrthogonality.globalUnits (twistMod rayM η η₀)) le_rfl data.η (twistTheta rayM η η₀)) P‖ *
      ‖idealCoeff data.η P‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have h34 : ‖W' ((P.absNorm : ℝ)/D)‖ *
      ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift σ τ).re) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h3 h4 h5 zero_le_one
  simpa only [one_mul] using
    mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) h5) zero_le_one

end Coeff

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
