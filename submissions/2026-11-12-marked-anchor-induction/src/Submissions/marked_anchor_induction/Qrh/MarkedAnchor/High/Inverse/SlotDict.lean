/- Copyright (c) 2026 Sil. Apache-2.0.
Pattern of `High.Marked.Slot.coeff_eq` / `Interface.Bridge.eta_ne_zero`; uses Hailey Collet's
`naturalSlot_annular_filter`, `naturalRow_sixth_ideal`, `maximum_eq_of_excluded_coefficients`,
`clean_core_coefficients`, `relativeRayBase` (Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Dictionary
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Slot
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafCoreSlot

/-!
# High.Inverse.SlotDict — the canonical inverse slots as raw natural slots

For inverse row data `data`, fixed ray data `(rayM, G, hH)` and the common twist `tw`:

* `twistEta data tw := dataBase data · (rayChar tw)⁻¹`, the base twist of the core slots;
* `ray_coeff_eq` — on `canonicalPool rayM G.pool D` (`D` above the deleted modulus and
  `N(fixedBadMask)`): `rayCoeff · rowHom(w) = (naturalRow (dataBase data) w)(P) ·
  relChar_{G.pool}(twistEta, 1)(P) · annular(P)`;
* **`directSlot_eq_natural`** — the canonical slot `directSlot w (canonicalPool …) (rayCoeff …)` is
  the raw natural slot of `naturalRow (dataBase data) w` on `primePool rayM G.pool 2 D` with
  coefficient `relChar(twistEta, 1)·annular` (the `ns` form of `High.core_class_batch`, with
  `naturalSlot_excluded_one`);
* `polynomial_congr`, `polynomial_data_natural` — the inverse factor only sees coefficients;
* `rawFam` — the whole-source natural family of the raw row `w`; `rawFam_maximum_eq_core` /
  `rawFam_nonprincipal`: for `w = c·B⁶` its zero maxima are those of `coreFamily … (dataBase data)
  η₀ c` (so the core-family zero bins give the guards of `inverse_row_pointwise` and of
  `core_slot_bound` for the raw row);
* `raw_conductor_bound` — linear conductor bound for the raw family and its relative twists.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section
open scoped Classical BigOperators
open Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance slotDictQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The data base does not vanish at primes above the deleted modulus. -/
theorem dataBase_ne_zero (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) <
      (P.absNorm : ℝ)) :
    idealCoeff (dataBase data) P ≠ 0 := by
  have hc := ProbeRaySlots.prime_coprime_of_norm_gt
    (DetectorDictionaryInverseRawInitialGates.deletedBase data) ⟨P, hP⟩ hN
  have h1 := HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime
    (DetectorDictionaryInverseRawInitialGates.deletedBase data) P hP.ne_zero hc
  have h2 : idealCoeff (DetectorDictionaryInverseRawInitialGates.deletedBase data) P =
      if (∀ Q ∈ DetectorDictionaryInverseRawInitialGates.excluded data, IsCoprime P Q) then
        idealCoeff (InverseInitialDetectorSource.baseCharacter data) P else 0 :=
    HeckeFamily.idealCoeff_excludePrimes _ _ _ P
  rw [h2] at h1
  split_ifs at h1 with hcop
  · rw [InverseInitialDetectorSource.baseCharacter_coeff] at h1
    have he : InverseInitialRawDictionary.fixedBase data.η data.m data.f P =
        idealCoeff data.η P * CanonicalRowCompletion.idealRowHom (data.m^6*data.f^4) P := rfl
    rw [he] at h1
    rw [dataBase_coeff, mul_one]
    exact h1
  · exact absurd rfl h1

/-- The pool inclusion of the global units. -/
theorem hHpool {rayM : Ideal O} (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) :
    RayOrthogonality.globalUnits rayM ≤ G.pool := le_trans hH G.twist_le

section Ray
variable (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)

/-- The base twist of the core slots: `dataBase data · (rayChar tw)⁻¹`. -/
def twistEta (data : RowData) (tw : RayQuotient.Characters rayM G.twist) : Character :=
  (dataBase data).product (HeckeRayQuotient.character rayM G.twist hH tw).inverse

omit [NeZero rayM] in
/-- The trivial ray character is `1` on the identity class. -/
theorem rayChar_one_identity (H : Subgroup (O⧸rayM)ˣ) [NeZero rayM]
    (hH' : RayOrthogonality.globalUnits rayM ≤ H) {P : Ideal O}
    (hcl : P ∈ RayQuotient.identityClass rayM H) :
    idealCoeff (HeckeRayQuotient.character rayM H hH' 1) P = 1 := by
  have hch : HeckeRayQuotient.character rayM H hH' 1 = HeckeRayFamily.character rayM 1 := by
    rw [HeckeRayQuotient.character, map_one]
  rw [hch]
  exact HeckePrimeRow.identityClass_principal_coeff rayM H hH' hcl

/-- `rowHom(fixedBadMask⁶)` is `1` at primes above `N(fixedBadMask)`. -/
theorem rowHom_fbm_one (P : Ideal O) (hP : Prime P)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) <
      (P.absNorm : ℝ)) :
    CanonicalRowCompletion.idealRowHom (CenteredMomentSecondHeightFamily.fixedBadMask^6) P = 1 := by
  have hfbm0 : Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
  have hcopF := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hP hfbm0 hfbm
  have : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
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
    exact (Ideal.isPrime_of_prime hP).ne_top htop
  rw [CanonicalRowCompletion.idealRowHom_prime_sixth_mask _ P hlam]
  simp [hcopF]

/-- **Coefficient identity** on the canonical pool. -/
theorem ray_coeff_eq (W : ℝ → ℂ) (σ : ℝ) (data : RowData)
    (tw : RayQuotient.Characters rayM G.twist) {D : ℝ} (hD : 0 < D) (v : ℝ)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) < D)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < D)
    (w : O) (hw : w ≠ 0) (P : Ideal O) (hP : P ∈ canonicalPool rayM G.pool D) :
    rayCoeff rayM G hH W σ data tw D v P * CanonicalRowCompletion.idealRowHom w P =
      idealCoeff (naturalRow (dataBase data) w hw).character P *
        (idealCoeff (relativeCharacter rayM G.pool (hHpool G hH) (twistEta rayM G hH data tw) 1) P *
          HeckePrimeAnnular.annularWeight W D σ v P) := by
  simp only [canonicalPool, primePool, Finset.mem_filter] at hP
  obtain ⟨⟨_, hpr, hcl⟩, hr⟩ := hP
  have hND : D ≤ (P.absNorm : ℝ) := by
    have := (le_div_iff₀ hD).mp hr.1; linarith
  have hη0 := Interface.Bridge.eta_ne_zero data P hpr (lt_of_lt_of_le hdel hND)
  have hb0 := dataBase_ne_zero data P hpr (lt_of_lt_of_le hdel hND)
  have hrow := rowHom_fbm_one P hpr (lt_of_lt_of_le hfbm hND)
  unfold rayCoeff twistEta
  rw [(naturalRow _ _ _).ideal, CanonicalRowCompletion.idealRowHom_argument_mul, hrow,
    relativeCharacter_ideal, relativeCharacter_ideal,
    rayChar_one_identity rayM G.pool (hHpool G hH) hcl,
    HeckeDetectorRelativePrime.idealCoeff_inverse, HeckeDetectorRelativePrime.idealCoeff_inverse,
    idealCoeff_product, HeckeDetectorRelativePrime.idealCoeff_inverse, mul_inv, inv_inv]
  field_simp

/-- **Slot identity**: the canonical inverse slot is the raw natural slot of the data base. -/
theorem directSlot_eq_natural (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (σ : ℝ)
    (data : RowData) (tw : RayQuotient.Characters rayM G.twist) {D : ℝ} (hD : 0 < D) (v : ℝ)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) < D)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < D)
    (w : O) (hw : w ≠ 0) :
    directSlot w (canonicalPool rayM G.pool D) (rayCoeff rayM G hH W σ data tw D v) D =
      naturalSlot (naturalRow (dataBase data) w hw).character (primePool rayM G.pool 2 D)
        (fun I => idealCoeff (relativeCharacter rayM G.pool (hHpool G hH)
            (twistEta rayM G hH data tw) 1) I *
          HeckePrimeAnnular.annularWeight W D σ v I) D := by
  rw [← Cycle61MarkedPlain.naturalSlot_annular_filter _ _
    (fun I => idealCoeff (relativeCharacter rayM G.pool (hHpool G hH)
      (twistEta rayM G hH data tw) 1) I) W hWs D σ v]
  unfold directSlot naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  exact ray_coeff_eq rayM G hH W σ data tw hD v hdel hfbm w hw I hI

end Ray

/-- The natural slot only sees coefficients: `excluded χ 1` is `χ`. -/
theorem naturalSlot_excluded_one (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O → ℂ)
    (D : ℝ) : naturalSlot (excluded χ 1) pool β D = naturalSlot χ pool β D := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  rw [excluded_ideal _ _ one_ne_zero]
  simp only [isCoprime_one_right, ↓reduceIte]

/-- The dyadic polynomial only sees coefficients. -/
theorem polynomial_congr {χ ψ : Character} (h : ∀ I, idealCoeff χ I = idealCoeff ψ I)
    (inv : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) :
    polynomial χ inv W D σ ω = polynomial ψ inv W D σ ω := by
  unfold polynomial summand coefficient
  simp only [h]

/-- The inverse factor of an inverse row is that of the natural row of the data base. -/
theorem polynomial_data_natural (data : RowData) (w : NonzeroElement) (inv : Bool)
    (W : ℝ → ℂ) (D σ ω : ℝ) :
    polynomial (data.character w) inv W D σ ω =
      polynomial (naturalRow (dataBase data) w.val w.property).character inv W D σ ω :=
  polynomial_congr (data_character_natural data w) inv W D σ ω

section Raw
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The whole-source natural family of the raw row `w` (base `dataBase data`). -/
def rawFam (data : RowData) (η₀ : Character) (w : O) (hw : w ≠ 0)
    (j : Cycle61Moment.WholeSourceIndex rayM H) : Character :=
  (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j) w hw).character

theorem rawFam_inl (data : RowData) (η₀ : Character) (w : O) (hw : w ≠ 0) :
    rawFam rayM H hH data η₀ w hw (Sum.inl ()) = (naturalRow (dataBase data) w hw).character :=
  rfl

/-- Raw row coefficients are the core row coefficients with the primes of `B` removed. -/
theorem rawFam_coeff (data : RowData) (η₀ : Character) (c : FreeRow) (B : NZIdeal)
    (j : Cycle61Moment.WholeSourceIndex rayM H) (I : Ideal O) :
    idealCoeff (rawFam rayM H hH data η₀ (ProbePhysical.sixthFrequencyEquiv (c, B)).val
        (ProbePhysical.sixthFrequencyEquiv (c, B)).property j) I =
      idealCoeff (excluded (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
        c.val c.property.1).character (B.val * 1)) I := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hh := Record12518109GainDeletion.naturalRow_sixth_masked_ideal
    (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j) c.val c.property.1)
    (ConcretePrimeRowBridge.idealGenerator B.val) hg
    (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
      (ProbePhysical.sixthFrequencyEquiv (c, B)).val (ProbePhysical.sixthFrequencyEquiv (c, B)).property)
    1 one_ne_zero I
  rw [ConcretePrimeRowBridge.span_idealGenerator, excluded_ideal _ _ one_ne_zero] at hh
  simp only [isCoprime_one_right, ↓reduceIte] at hh
  exact hh

/-- Nonprincipality of the raw family from that of the core family. -/
theorem rawFam_nonprincipal (data : RowData) (η₀ : Character) (c : FreeRow) (B : NZIdeal)
    (hnclean : ∀ j, (coreFamily rayM H hH (dataBase data) η₀ c j).residue ≠ 1) :
    ∀ j, (rawFam rayM H hH data η₀ (ProbePhysical.sixthFrequencyEquiv (c, B)).val
      (ProbePhysical.sixthFrequencyEquiv (c, B)).property j).residue ≠ 1 := by
  intro j hp
  have hcore : (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
      c.val c.property.1).character.residue ≠ 1 :=
    Record12518109GainWholeGeometry.nonprincipal_of_excluded_coefficients _ _ _
      (Record12518109GainWholeGeometry.clean_core_coefficients rayM H hH (dataBase data) η₀ c j)
      (hnclean j)
  apply hcore
  have h1 := (HeckeFiniteDeletion.principal_iff_of_mask _ _
    (LocalMoment.coefficient_equality_mask _ _ (rawFam_coeff rayM H hH data η₀ c B j))).mp hp
  exact (HeckeFiniteDeletion.principal_iff_of_mask _ _
    (fun I => HeckeFamily.excludePrimes_mask _ _
      (CenteredMomentNaturalRowSource.support_prime _) I)).mp h1

/-- **Zero transfer, raw family**: for `w = c·B⁶` the raw whole-source family has the zero maxima
of the clean core family. -/
theorem rawFam_maximum_eq_core (data : RowData) (η₀ : Character) (c : FreeRow) (B : NZIdeal)
    (hnclean : ∀ j, (coreFamily rayM H hH (dataBase data) η₀ c j).residue ≠ 1)
    (hn : ∀ j, (rawFam rayM H hH data η₀ (ProbePhysical.sixthFrequencyEquiv (c, B)).val
      (ProbePhysical.sixthFrequencyEquiv (c, B)).property j).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum (rawFam rayM H hH data η₀
        (ProbePhysical.sixthFrequencyEquiv (c, B)).val (ProbePhysical.sixthFrequencyEquiv (c, B)).property)
        hn T =
      HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH (dataBase data) η₀ c) hnclean T := by
  have hcore : ∀ j, (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
      c.val c.property.1).character.residue ≠ 1 := fun j =>
    Record12518109GainWholeGeometry.nonprincipal_of_excluded_coefficients _ _ _
      (Record12518109GainWholeGeometry.clean_core_coefficients rayM H hH (dataBase data) η₀ c j)
      (hnclean j)
  have h1 := Record12518109GainWholeGeometry.maximum_eq_of_excluded_coefficients
    (rawFam rayM H hH data η₀ (ProbePhysical.sixthFrequencyEquiv (c, B)).val
      (ProbePhysical.sixthFrequencyEquiv (c, B)).property)
    (fun j => (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
      c.val c.property.1).character) (fun _ => B.val * 1) hn hcore
    (rawFam_coeff rayM H hH data η₀ c B) T
  have h2 := Record12518109GainWholeGeometry.maximum_eq_of_excluded_coefficients
    (coreFamily rayM H hH (dataBase data) η₀ c)
    (fun j => (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
      c.val c.property.1).character)
    (fun _ => Record12518109Natural.wholeAnchorMask rayM H hH η₀) hnclean hcore
    (Record12518109GainWholeGeometry.clean_core_coefficients rayM H hH (dataBase data) η₀ c) T
  exact h1.trans h2.symm

/-- **Raw conductors**: linear in the row norm, for the raw family and its relative twists. -/
theorem raw_conductor_bound (data : RowData) (η₀ : Character) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (w : O) (hw : w ≠ 0),
      (∀ j, ((rawFam rayM H hH data η₀ w hw j).modulus.absNorm : ℝ) ≤
        K * ((Ideal.span {w}).absNorm : ℝ)) ∧
      (∀ θ θ', ((HeckePrimeRay.twistedFamily rayM H hH
        (Record12518109GainWholeGeometry.relativeRayBase rayM H hH (dataBase data) η₀ w hw θ)
          θ').modulus.absNorm : ℝ) ≤ K * ((Ideal.span {w}).absNorm : ℝ)) := by
  let A : Cycle61Moment.WholeSourceIndex rayM H → ℝ := fun j =>
    ((Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j).modulus.absNorm : ℝ) *
      (fixedConductorFactor : ℝ)
  let A0 : ℝ := ((dataBase data).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)
  let Bc : ℝ := (rayM.absNorm : ℝ) * (η₀.modulus.absNorm : ℝ)
  let K : ℝ := 1 + ∑ j, A j + A0 * Bc * (rayM.absNorm : ℝ)
  have hA : ∀ j, 0 ≤ A j := fun j => by positivity
  have hA0 : 0 ≤ A0 := by positivity
  have hBc : 0 ≤ Bc := by positivity
  have hsum : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ => hA j
  have hext : 0 ≤ A0 * Bc * (rayM.absNorm : ℝ) := by positivity
  refine ⟨K, by linarith, ?_⟩
  intro w hw
  have hn : (0:ℝ) ≤ ((Ideal.span {w}).absNorm : ℝ) := Nat.cast_nonneg _
  constructor
  · intro j
    have hF : ((rawFam rayM H hH data η₀ w hw j).modulus.absNorm : ℝ) ≤
        A j * ((Ideal.span {w}).absNorm : ℝ) := by
      dsimp only [A, rawFam]
      exact_mod_cast (naturalRow (Cycle61Moment.wholeSourceBase rayM H hH η₀ (dataBase data) j)
        w hw).natural_modulus_bound
    have hAj : A j ≤ K := by
      have := Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ j)
      linarith
    exact hF.trans (mul_le_mul_of_nonneg_right hAj hn)
  · intro θ θ'
    have hF : ((naturalRow (dataBase data) w hw).character.modulus.absNorm : ℝ) ≤
        A0 * ((Ideal.span {w}).absNorm : ℝ) := by
      dsimp only [A0]
      exact_mod_cast (naturalRow (dataBase data) w hw).natural_modulus_bound
    have hν : (((relativeCharacter rayM H hH η₀ θ).inverse.inverse).modulus.absNorm : ℝ) ≤ Bc := by
      change ((relativeCharacter rayM H hH η₀ θ).modulus.absNorm : ℝ) ≤
        (rayM.absNorm : ℝ) * (η₀.modulus.absNorm : ℝ)
      exact_mod_cast relativeCharacter_modulus rayM H hH η₀ θ
    have hp : (((naturalRow (dataBase data) w hw).character.product
        (relativeCharacter rayM H hH η₀ θ).inverse.inverse).modulus.absNorm : ℝ) ≤
        ((naturalRow (dataBase data) w hw).character.modulus.absNorm : ℝ) *
        (((relativeCharacter rayM H hH η₀ θ).inverse.inverse).modulus.absNorm : ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound (naturalRow (dataBase data) w hw).character
        (relativeCharacter rayM H hH η₀ θ).inverse.inverse
    have ht : ((HeckePrimeRay.twistedFamily rayM H hH
        (Record12518109GainWholeGeometry.relativeRayBase rayM H hH (dataBase data) η₀ w hw θ)
          θ').modulus.absNorm : ℝ) ≤
        ((Record12518109GainWholeGeometry.relativeRayBase rayM H hH (dataBase data) η₀ w hw
          θ).modulus.absNorm : ℝ) * (rayM.absNorm : ℝ) := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound rayM H hH
        (Record12518109GainWholeGeometry.relativeRayBase rayM H hH (dataBase data) η₀ w hw θ) θ'
    have hprod := hp.trans (mul_le_mul hF hν (Nat.cast_nonneg _) (mul_nonneg hA0 hn))
    have he := ht.trans (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _))
    have hK : A0 * Bc * (rayM.absNorm : ℝ) ≤ K := by
      show _ ≤ 1 + ∑ j, A j + A0 * Bc * (rayM.absNorm : ℝ)
      linarith
    exact he.trans (by
      have := mul_le_mul_of_nonneg_right hK hn
      calc A0 * ((Ideal.span {w}).absNorm : ℝ) * Bc * (rayM.absNorm : ℝ) =
          A0 * Bc * (rayM.absNorm : ℝ) * ((Ideal.span {w}).absNorm : ℝ) := by ring
        _ ≤ _ := this)

end Raw

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.directSlot_eq_natural
#print axioms Qrh.MarkedAnchor.High.Inverse.rawFam_maximum_eq_core
#print axioms Qrh.MarkedAnchor.High.Inverse.raw_conductor_bound
