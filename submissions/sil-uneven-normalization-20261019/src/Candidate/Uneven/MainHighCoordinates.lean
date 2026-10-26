/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainHighAdmission
import Candidate.Uneven.MainPointwise
import Candidate.Target830.High.Channels
import Candidate.Cycle63.Physical.InitialMass.GeometryUniformScalar
import Candidate.Cycle63.Physical.InitialMass.SecondHighBox
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open CenteredMomentFirstPhysicalSource CenteredMomentExceptionalAmplitudePair CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentCommonHeightEnvelope
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open Target830
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
theorem actual_geometry_compensated_high_gates
     (P : Sil.Uneven.MainSource.Plane)
     (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv B b δ : ℝ)(hZ : 1<Z)(hB : 0 ≤ B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B)
    (hsecond : (d₂.C.absNorm:ℝ) ≤ Z^B ∧ (d₂.D.absNorm:ℝ) ≤ Z^B)
    (hDbox : |D| ≤ B)(hAbox : |A| ≤ B)(habox : |a| ≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve| ≤ B)(hε : |ε| ≤ B)
    (hb : b∈Set.Icc Sil.Uneven.MainSource.widthLo Sil.Uneven.MainSource.widthHi)
    (hδ : P.q ≤ δ ∧ δ ≤ 3/4)(hD : 0 ≤ D)
    (hA : A ≤ D*Sil.Uneven.MainSource.total P b)(ha : a ≤ D*Sil.Uneven.MainSource.amp P b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=unevenGeometrySide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    ((firstSourceMissing (!reflected) l).absNorm:ℝ)=Z^(x 1) ∧
      (∀k,-(38*B+|εv|) ≤ x k ∧ x k ≤ 38*B+|εv|) ∧
      highExponentValue δ x ≤ 
        (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
          D*Sil.Uneven.MainSource.highBase P b δ-Sil.Uneven.MainSource.gamma δ*
            (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
             Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)) := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val
  have hf : (l.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.1.2.absNorm:ℝ) ≤ Z^B := ⟨(hn 0).2,(hn 1).2⟩
  have hbox:=actual_high_coordinate_box reflected (!reflected) second l hC hD' d₂.C d₂.D
    d₂.hC d₂.hD d₂.sameSupport U Z D A a ξ reserve ε B hZ hB hf hsecond hDbox hAbox habox hω hε
  have hside : |side| ≤ 6*B := by
    apply uneven_geometry_side_box reflected A B _ hB hAbox
    · intro k
      exact ⟨Real.logb_nonneg hZ (hn k).1,
        (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (hn k).1)).mpr (hn k).2⟩
    · exact Target830.Source.actual_surplus_nonneg s R seed K Z ξ hZ j.1.val
  refine ⟨?_,?_,?_⟩
  · simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
      ite_false,add_zero] using
      actual_child_high_missing reflected (!reflected) second l hC hD' d₂.C d₂.D U
        Z D A a ξ reserve ε εv hZ
  · have hh:=compensated_high_coordinate_box _ side (32*B+|εv|) (6*B)
      (child_high_coordinate_box _ (32*B) εv hbox) hside
    intro k
    simpa only [show 32*B+|εv|+6*B=38*B+|εv| by ring] using hh k
  · have hd : 31/50 ≤ δ := (Sil.Uneven.MainSource.parameter_gates P).1.trans hδ.1
    have hh:=actual_geometry_uneven_high_payment s R seed K Z ξ hK bin j d₂
      reflected second U D A a reserve ε εv δ hZ hd hδ.2
    dsimp only at hh
    rw [←uneven_geometry_side_label s R seed K Z ξ hK hZ bin j reflected A] at hh
    have hr:=Target830.Source.Valuation.rho_extended_range
      (show (405/662:ℝ) ≤ δ by linarith) hδ.2
    have hc : 0 ≤ 5-6*rho δ := by linarith [hr.2]
    have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ δ by linarith)
    have haa:=mul_le_mul_of_nonneg_right ha hc
    have hg:=(Sil.Uneven.MainSource.gamma_bounds hd hδ.2).2.1
    have hb2 : 0 ≤ Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ) := by
      apply Real.logb_nonneg hZ
      cases second
      · exact norm_ge_one d₂.C d₂.hC.1
      · exact norm_ge_one d₂.D d₂.hD.1
    have hgg:=mul_le_mul_of_nonneg_right hg hb2
    change highExponentValue δ x ≤
      (1-rho δ)*(frequencyLoss Z 32 ξ+reserve)+rho δ*ε+εv-
        D*(1-rho δ-δ*Sil.Uneven.MainSource.total P b-Sil.Uneven.MainSource.amp P b*(5-6*rho δ))-
        Sil.Uneven.MainSource.gamma δ*(labelC reflected l Z+Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ))
    change highExponentValue δ x ≤
      (1-rho δ)*(frequencyLoss Z 32 ξ+reserve)+rho δ*ε+εv-
        (D*(1-rho δ)-δ*A-a*(5-6*rho δ))-
        Sil.Uneven.MainSource.gamma δ*labelC reflected l Z-δ*Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ) at hh
    nlinarith only [hh,hAA,haa,hgg]

end OAI.SevenEighths.MainHigh
