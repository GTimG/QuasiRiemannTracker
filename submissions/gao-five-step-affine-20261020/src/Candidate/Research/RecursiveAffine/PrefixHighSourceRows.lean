import Candidate.Research.RecursiveAffine.PrefixHighPhysicalWitness
import Candidate.Research.RecursiveAffine.HighRecordAtJunction
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducerRows

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider
variable {Base : Type} {base : HeckeFamily.Character → Base → HeckeFamily.Character}
open Cycle63MarkedPlain Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
attribute [local instance] geometryAffineHighPaymentSumDecidable

/- The facts of a joint label of a HIGH row at the child multiplier `v` that make it a label of a class of the count
form with the coordinates `x`: its row norm, supports, caps, and missing radical. -/
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger]

theorem affine_high_universal_row_package {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ qh : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ) (hqh : Cycle63.Arithmetic.q0≤qh) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(hT : 2<Z^τ)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 →
      |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(P : PrefixHighPresentation (base η₀) s.η R)(B Tz : ℝ),((Ideal.span {P.mult}).absNorm:ℝ)≤Z^(B-130) →
      3*Z^τ*Z^τ≤Tz → Mrow≤1 →
      ∀(reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)(χ₀ : RayCharacter)
        (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
          (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
            else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
        (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
          (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
            else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)),
      ∃W : ∀r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask,
          DepthTwoHighWitness M (extendFixedDictionary (base η₀)) η₀
            (nonzeroJointSourceRow (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
              (internalQ Q η₀) fixedBadMask r)),
        ∀r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask,
          (1+qh)/2≤bufferValue e (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ
            bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _)
            (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r) →
          let sel := affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂
            χ₀ (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
            (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r
          let δ := 2*bufferValue e sel-1
          let x := affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r
          bufferValue e sel≤7/8 ∧ bufferValue e sel≤(W r).zeroMax M H hH Tz ∧
          Cycle153HighProvider.HighRowFacts Z B (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r) x (Real.logb Z ((Ideal.span {P.mult}).absNorm:ℝ)) ∧
          Cycle153HighProvider.highExponentValue δ x≤
            (1-unmarkedDensity δ)*(frequencyLoss Z 32 (μ/64)+μ/8)+unmarkedDensity δ*(μ/8)+μ/8-
              (Mrow*(1-unmarkedDensity δ)-δ*Real.logb Z (CenteredMomentAmplificationChildInput.volume s)-
                amp*(5-6*unmarkedDensity δ)) := by
  let F₀ : NaturalRow η₀ 1 := naturalRow η₀ 1 one_ne_zero
  filter_upwards [eventually_actual_main_high_literal_admission (α:=ι) M H hH (9/4) (9/4) (μ/8) (μ/64) (1/4) τ e 28
      bΦ 20 (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by norm_num) hτ he
      (by norm_num) hbΦ η₀,
    eventual_geometry_joint_support η₀ 1 F₀ 1 one_ne_zero (9/4) (μ/8) (Fintype.card ι) (by norm_num)
      (by positivity),
    eventual_geometry_literal_high_frequency η₀ 1 F₀ 1 one_ne_zero (9/4) (μ/8) (Fintype.card ι) (by norm_num)
      (by positivity),
    eventually_geometry_zero_heights e τ hτ] with Z hlit hjoint hfreq hzero
  refine ⟨hlit.1,?_⟩
  intro hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega P B Tz hvcap hTz
    hMrow1 reflected second bin t χ₀ hP hPN
  have hK : 0<Z^Mrow := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  obtain ⟨keep,hcanonical⟩ := actual_main_high_canonical_family_admission M H hH
    (fun j => affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j) (fun _ => χ₀)
    (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Z 28 bΦ hZ hbΦ
    second hP hPN η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi
  have hrowdata (r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
      fixedBadMask) :
      ∃Wr : DepthTwoHighWitness M (extendFixedDictionary (base η₀)) η₀
          (nonzeroJointSourceRow (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r)),
        bufferValue e (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂
            χ₀ (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
            (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r)≤7/8 ∧
        bufferValue e (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂
            χ₀ (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
            (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r)≤Wr.zeroMax M H hH Tz := by
    have hzb := (hcanonical r).2.2.2
    have hbuf := hzero.2.2 (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁
      hz₂ χ₀ (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
      (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r)
    clear hlit hjoint hfreq
    have hT3 : ((3*(affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
        (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
        (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN r).1.val : ℕ) : ℝ)*Z^τ≤Tz := by
      have hZτ : 0≤Z^τ := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hbuf hZτ]
    cases second
    · obtain ⟨Wr,hWr⟩ := prefixHighPhysicalWitness_exists M H hH η₀ P reflected false R seed (Z^Mrow) Z (μ/64) hK bin
        r.val.1.val.1.1.val
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
        (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r rfl rfl
        (actual_geometry_child_puncture_ne_zero reflected s R seed hR (Z^Mrow) Z (μ/64) hK bin _)
        (dvd_mul_right _ _) r.val.2.1 _ _ _ _ _ rfl rfl rfl e (Z^τ) Tz _ hzb hT3
      exact ⟨Wr,hzb.2.2.2.1,hWr⟩
    · obtain ⟨Wr,hWr⟩ := prefixHighPhysicalWitness_exists M H hH η₀ P reflected true R seed (Z^Mrow) Z (μ/64) hK bin
        r.val.1.val.1.1.val
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
        (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r rfl rfl
        (actual_geometry_child_puncture_ne_zero reflected s R seed hR (Z^Mrow) Z (μ/64) hK bin _)
        (dvd_mul_right _ _) r.val.2.2.1⁻¹ _ _ _ _ _ rfl rfl rfl e (Z^τ) Tz _ hzb hT3
      exact ⟨Wr,hzb.2.2.2.1,hWr⟩
  choose W hW using hrowdata
  refine ⟨W,?_⟩
  intro r hsel
  intro sel δ x
  have hB130 : 130≤B := by
    by_contra hlt
    have h1 : (1:ℝ)≤((Ideal.span {P.mult}).absNorm:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr P.hv))
    have h2 : Z^(B-130)<1 := Real.rpow_lt_one_of_one_lt_of_neg hZ (by linarith)
    linarith
  obtain ⟨h78,hzeroW⟩ := hW r
  obtain ⟨h1,h2,h3,h4,-⟩ := hlit.2 hZ reflected second s R seed Mrow amp (μ/8) t hend hseed hR hRcap hz₁ hz₂
    hsource hvol hamp0 (by positivity) hMrow hA hamp homega bin χ₀ (internalQ Q η₀) hQ72 fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right hβlo hβhi
    r.val.1
  have hsrc : sourceRadius s≤Z^(4:ℝ) := hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hZB : ∀a : ℝ,a≤4→Z^a≤Z^B := fun a ha => Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨h78,hzeroW,?_,?_⟩
  · have hC : Supported (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.1 :=
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val.1).hC
    have hD' : Supported (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.2 :=
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val.1).hD
    have hsame : primeSupport (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.1 =
        primeSupport (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.2 :=
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val.1).sameSupport
    have hvpos : (0:ℝ)<((Ideal.span {P.mult}).absNorm:ℝ) := by
      have := norm_ge_one (Ideal.span {P.mult}) (Ideal.span_singleton_eq_bot.not.mpr P.hv)
      linarith
    have hfreq1 := hfreq.2 reflected second s R seed Mrow (μ/64) hK bin r.val.1.val.1.1.val
      (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
      (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r rfl amp (μ/8) (μ/8)
      (by linarith) rfl
    dsimp only at hfreq1
    rw [child_coordinate_two] at hfreq1
    have hfreq2 : rawFrequencyNorm (nonzeroJointSourceRow (affineHighUniversalKey η₀ 1 F₀ 1 one_ne_zero second
        reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r))≤
        Z^(affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
          (internalQ Q η₀) fixedBadMask r 2) := by
      rw [affineHighUniversalCoordinates, compensated_child_coordinate_two]
      exact hfreq1
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have hchg := Cycle153HighProvider.rawFrequencyNorm_unit_change (left := !reflected) (v := P.mult)
        (unit := fun l => (firstDictionaryUnit (!reflected) η₀ 1 F₀ 1 l : O)) (unit' := P.unit (!reflected))
        (affineHighUniversalKey η₀ 1 F₀ 1 one_ne_zero second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
          (internalQ Q η₀) fixedBadMask r)
        (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
          fixedBadMask r)
        ((affineHighUniversalKey_val s.η 1 P.selfRow 1 one_ne_zero second reflected s R seed Z Mrow amp μ t
          hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r).trans
          (affineHighUniversalKey_val η₀ 1 F₀ 1 one_ne_zero second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r).symm)
        (Units.isUnit _) (Units.isUnit _)
      rw [hchg]
      have hZ0 : 0<Z := zero_lt_one.trans hZ
      calc ((Ideal.span {P.mult}).absNorm:ℝ)*rawFrequencyNorm (nonzeroJointSourceRow (affineHighUniversalKey η₀ 1 F₀ 1
            one_ne_zero second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
            fixedBadMask r))
          ≤ ((Ideal.span {P.mult}).absNorm:ℝ)*Z^(affineHighUniversalCoordinates second reflected s R seed Z Mrow
            amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r 2) :=
            mul_le_mul_of_nonneg_left hfreq2 (Nat.cast_nonneg _)
        _ = Z^(affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r 2+Real.logb Z ((Ideal.span {P.mult}).absNorm:ℝ)) := by
            rw [Real.rpow_add hZ0,Real.rpow_logb hZ0 hZ.ne' hvpos]
            ring
    · cases second <;> exact ⟨hC,hD'.1,
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask
          r.val.1).hC,(affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
          fixedBadMask r.val.1).hD.1⟩
    · cases second <;> exact ⟨hsame,(affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
        (internalQ Q η₀) fixedBadMask r.val.1).sameSupport⟩
    · have hexp : Mrow+6*3+μ/8≤130 := by linarith [(abs_le.mp hMrow).2]
      have hj := (hjoint hZ reflected s R seed (Z^Mrow) (μ/64) amp (μ/8) Mrow 3 hK hseed hz₁ hz₂ hsource le_rfl
        (by positivity) (by linarith) hamp0 (by positivity) bin r.val.1.val.1.1.val
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
        (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r rfl rfl)
      have hj' : ((Ideal.span {jointSourceRow (!reflected) 1 (fun l => (firstDictionaryUnit (!reflected) η₀ 1 F₀ 1 l : O))
          (secondEncodedRow (fun j => (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask j).block)
            (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r)}*
          firstSourceMissing (!reflected) (secondEncodedRow (fun j => (affineHighOrdinary reflected s R seed Z Mrow amp
            μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask j).block)
            (fun j => geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val) r).1).absNorm : ℝ)≤
          Z^(130:ℝ) := hj.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
      have key : ∀L0 : JointSourceLabel,
          ((Ideal.span {jointSourceRow (!reflected) 1 (fun l => (firstDictionaryUnit (!reflected) η₀ 1 F₀ 1 l : O))
            L0}*firstSourceMissing (!reflected) L0.1).absNorm : ℝ)≤Z^(130:ℝ) →
          ((Ideal.span {jointSourceRow (!reflected) P.mult (P.unit (!reflected))
            (if second then reflectedJointLabel L0 else L0)}*
            firstSourceMissing (!reflected) (if second then reflectedJointLabel L0 else L0).1).absNorm : ℝ)≤Z^B := by
        intro L0 hL0
        have hc := joint_cap_transfer (left := !reflected) (v := P.mult)
          (unit := fun l => (firstDictionaryUnit (!reflected) η₀ 1 F₀ 1 l : O)) (unit' := P.unit (!reflected)) L0
          (Units.isUnit _) (Units.isUnit _) Z (B-130) 130 hZ.le hvcap hL0
        rw [show (B-130)+(130:ℝ) = B by ring] at hc
        cases second
        · exact hc
        · simp only [↓reduceIte]
          rw [joint_cap_reflected]
          exact hc
      have hval := affineHighUniversalKey_val s.η 1 P.selfRow 1 one_ne_zero second reflected s R seed Z
        Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r
      have hval' : (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
          fixedBadMask r).val = _ := hval
      rw [hval']
      exact key _ hj'
    · cases second <;> exact ⟨h1.trans (hZB 4 le_rfl),h2.trans (hZB 4 le_rfl),h3.trans (hZB 4 le_rfl),
        h4.trans (hZB 4 le_rfl)⟩
    · have hm := actual_geometry_compensated_high_missing s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask
          r.val.1) reflected (!reflected) second
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask
          r.val.1).inactive Mrow (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData)) amp (μ/8)
        (μ/8) (μ/8) hZ
      cases second <;> exact hm.le
  · have hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4 := by
      constructor
      · change Cycle63.Arithmetic.q0≤2*bufferValue e sel-1
        linarith [hqh]
      · change 2*bufferValue e sel-1≤3/4
        linarith
    have hpay := actual_geometry_compensated_allocation_payment_reserve s R seed (Z^Mrow) Z (μ/64) hK bin
      r.val.1.val.1.1.val
      (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r.val.1)
      reflected (!reflected) second
      (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask
        r.val.1).inactive Mrow (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData)) amp (μ/8) (μ/8)
      (μ/8) δ hZ hδ rfl
    dsimp only at hpay
    have hC : Supported (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.1 :=
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val.1).hC
    have hD' : Supported (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.2 :=
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val.1).hD
    have hc : 0≤Real.logb Z ((if reflected then
        (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.2
        else (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val).1.1).absNorm:ℝ) := by
      apply Real.logb_nonneg hZ
      cases reflected
      · exact norm_ge_one _ hC.1
      · exact norm_ge_one _ hD'.1
    have hb₂ : 0≤Real.logb Z ((if second then
        (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask
          r.val.1).D
        else (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀)
          fixedBadMask r.val.1).C).absNorm:ℝ) := by
      apply Real.logb_nonneg hZ
      cases second
      · exact norm_ge_one _ (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
          (internalQ Q η₀) fixedBadMask r.val.1).hC.1
      · exact norm_ge_one _ (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
          (internalQ Q η₀) fixedBadMask r.val.1).hD.1
    have hγ := mul_nonneg (Cycle63.Physical.commonRate_nonneg hδ) (add_nonneg hc hb₂)
    have hvol : CenteredMomentAmplificationChildInput.volume s =
        CenteredMomentExceptionalAmplitudePair.volume s.toData := rfl
    rw [hvol]
    refine hpay.trans ?_
    linarith only [hγ]

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
