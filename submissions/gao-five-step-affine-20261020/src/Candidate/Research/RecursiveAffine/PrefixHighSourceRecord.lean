/- The count-form record of the HIGH part of the second step at the configuration of the largest transport. Released
under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrefixHighSourceRows
import Candidate.Research.RecursiveAffine.PrefixHighSourceCore

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

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

set_option linter.constructorNameAsVariable false in
variable [Cycle63.AffineLedger] in
include M H hH in
/-- At a presented parent of the second step, the HIGH rows of all nonzero second-stage blocks of the parent at one
configuration have a count-form record whose value is the transport form shifted by `shift`, with at most the buffer bins
times the fourth power of the exponent bins of the box classes, and which pays the reserve of the parent whenever the loss
covers the frequency loss and the shift of the class exponents. -/
theorem depth_two_high_config_record {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ qh : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ)
    (hqh : Cycle63.Arithmetic.q0≤qh) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(hT : 2<Z^τ)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 →
      |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(P : PrefixHighPresentation (base η₀) s.η R)(B Tz shift extra : ℝ),((Ideal.span {P.mult}).absNorm:ℝ)≤Z^(B-130) →
      3*Z^τ*Z^τ≤Tz → Mrow≤1 → ∀(reflected : Bool),
      ∀(second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)(χ₀ : RayCharacter)
            (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
            (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤
                Z^(28:ℝ)),
      ∃Hb : SecondStepHighCount M H hH (extendFixedDictionary (base η₀)) η₀ Z B Tz (!reflected) P.mult (P.unit (!reflected)),
        (∀length ampP loss : ℝ,Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length → amp≤ampP →
          (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
          Hb.Pays qh Mrow length ampP loss) ∧
        (Fintype.card Hb.Class:ℝ)≤Cycle153HighProvider.depthTwoHighClassBound e μ ∧
        Hb.value=Z^shift*
          affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second s R
              seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
              (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP
              hPN qh extra := by
  filter_upwards [affine_high_universal_box (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ hμ hμ1 he hτ hbΦ,
    affine_high_universal_row_package (base:=base) (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ qh hμ hμ1 he hτ hbΦ hqh]
    with Z hbox hrows
  refine ⟨hbox.1,?_⟩
  intro hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega P B Tz shift
    extra hvcap hTz hMrow1 reflected second bin t χ₀ hP hPN
  have hbx := (hbox.2 hZ s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega
    reflected second bin t χ₀).2.2
  obtain ⟨W,hW⟩ := hrows.2 hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp
    homega P B Tz hvcap hTz hMrow1 reflected second bin t χ₀ hP hPN
  obtain ⟨Hb,hpay,hcard,hval⟩ := Cycle153HighProvider.high_record_of_facts M H hH Tz hZ
    (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
      (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN)
    (affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      (internalQ Q η₀) fixedBadMask)
    (prefixHighRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
    (affineHighUniversalKey η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero second reflected s R seed Z Mrow amp
      μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
    (fun r => (affineHighUniversalKey_val s.η 1 P.selfRow 1 one_ne_zero second reflected s R seed Z Mrow
      amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r).trans
      (affineHighUniversalKey_val η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero second reflected s R seed Z
        Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r).symm)
    W μ qh Mrow (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) amp shift extra hμ (by have hq0:=Cycle63.Arithmetic.q0_bounds; linarith [hqh,hq0.1])
    (fun l j => hbx l j) hW
  exact ⟨Hb,hpay,hcard,hval⟩


set_option linter.constructorNameAsVariable false in
variable [Cycle63.AffineLedger] in
include M H hH in
/-- At a presented parent of the second step, the HIGH rows of all nonzero second-stage blocks of the parent are
bounded in transport form, at every configuration `(second, bin, χ₀, t)`, by the count form of one record of the
configuration of the largest transport; the record has at most the buffer bins times the fourth power of the exponent
bins of the box classes, and it pays the reserve of the parent whenever the loss covers the frequency loss and the
shift of the class exponents. -/
theorem depth_two_high_record {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ qh : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ)
    (hqh : Cycle63.Arithmetic.q0≤qh) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(hT : 2<Z^τ)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 →
      |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(P : PrefixHighPresentation (base η₀) s.η R)(B Tz shift extra : ℝ),((Ideal.span {P.mult}).absNorm:ℝ)≤Z^(B-130) →
      3*Z^τ*Z^τ≤Tz → Mrow≤1 → ∀(reflected : Bool),
      ∃Hb : SecondStepHighCount M H hH (extendFixedDictionary (base η₀)) η₀ Z B Tz (!reflected) P.mult (P.unit (!reflected)),
        (∀length ampP loss : ℝ,Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length → amp≤ampP →
          (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
          Hb.Pays qh Mrow length ampP loss) ∧
        (Fintype.card Hb.Class:ℝ)≤Cycle153HighProvider.depthTwoHighClassBound e μ ∧
        ∀(second : Bool)(bin : ℤ×(Fin 5→ℤ)),bin∈commonGeometryBins s R seed (Z^Mrow) Z (μ/64) →
          ∀(t : ℝ)(χ₀ : RayCharacter)
            (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
            (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤
                Z^(28:ℝ)),
            affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second s R
              seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
              (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP
              hPN qh extra≤Z^(-shift)*Hb.value := by
  filter_upwards [affine_high_universal_box (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ hμ hμ1 he hτ hbΦ,
    depth_two_high_config_record (base:=base) (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ qh hμ hμ1 he hτ hbΦ hqh]
    with Z hbox hcfg
  refine ⟨hbox.1,?_⟩
  intro hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega P B Tz shift
    extra hvcap hTz hMrow1 reflected
  have hb := fun (second : Bool) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ) (χ₀ : RayCharacter) =>
    hbox.2 hZ s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega reflected second
      bin t χ₀
  let Idx := Bool×{bin : ℤ×(Fin 5→ℤ) // bin∈commonGeometryBins s R seed (Z^Mrow) Z (μ/64)}×RayCharacter
  let Tr : Idx→ℝ→ℝ := fun c t =>
    affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected c.1 s R seed Z
      Mrow amp μ t hZ c.2.1.val hz₁ hz₂ c.2.2 (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi
      (hb c.1 c.2.1.val t c.2.2).1 (hb c.1 c.2.1.val t c.2.2).2.1 qh extra
  have hmax : ∀c : Idx,∃t₀ : ℝ,∀t : ℝ,Tr c t≤Tr c t₀ := fun c =>
    affine_high_transport_max M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero c.1 reflected s R seed Z Mrow
      amp μ hZ c.2.1.val hz₁ hz₂ c.2.2 (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi
      (fun t => (hb c.1 c.2.1.val t c.2.2).1) (fun t => (hb c.1 c.2.1.val t c.2.2).2.1) qh extra (148+μ/8) hμ
      (fun t => (hb c.1 c.2.1.val t c.2.2).2.2)
  choose t₀ ht₀ using hmax
  by_cases hne : Nonempty Idx
  · obtain ⟨c,-,hc⟩ := Finset.exists_max_image (Finset.univ : Finset Idx) (fun c => Tr c (t₀ c))
      (Finset.univ_nonempty_iff.mpr hne)
    have hbc := hb c.1 c.2.1.val (t₀ c) c.2.2
    obtain ⟨Hb,hpay,hcard,hval⟩ := hcfg.2 hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0
      hMrow hA hamp homega P B Tz shift extra hvcap hTz hMrow1 reflected c.1 c.2.1.val (t₀ c) c.2.2 hbc.1 hbc.2.1
    have hvalue : Hb.value=Z^shift*Tr c (t₀ c) := hval
    refine ⟨Hb,hpay,hcard,?_⟩
    intro second bin hbin t χ₀ hP hPN
    have h1 : affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second
        s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
        (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN
        qh extra=Tr (second,⟨bin,hbin⟩,χ₀) t := rfl
    rw [h1]
    calc Tr (second,⟨bin,hbin⟩,χ₀) t≤Tr (second,⟨bin,hbin⟩,χ₀) (t₀ (second,⟨bin,hbin⟩,χ₀)) :=
          ht₀ (second,⟨bin,hbin⟩,χ₀) t
      _≤Tr c (t₀ c) := hc _ (Finset.mem_univ _)
      _=Z^(-shift)*Hb.value := by
          rw [hvalue,← mul_assoc,← Real.rpow_add (zero_lt_one.trans hZ),neg_add_cancel,Real.rpow_zero,one_mul]
  · refine ⟨SecondStepHighCount.empty M H hH (extendFixedDictionary (base η₀)) η₀ Z B Tz (!reflected) P.mult
      (P.unit (!reflected)),?_,?_,?_⟩
    · intro length ampP loss _ _ _ σ
      exact σ.elim
    · change ((Fintype.card Empty : ℕ) : ℝ)≤_
      rw [Fintype.card_eq_zero, Nat.cast_zero]
      unfold Cycle153HighProvider.depthTwoHighClassBound
      positivity
    · intro second bin hbin t χ₀ hP hPN
      exact absurd ⟨(second,⟨bin,hbin⟩,χ₀)⟩ hne

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
