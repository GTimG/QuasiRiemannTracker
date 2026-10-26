import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalLow.Chain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighProfiles.Control
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighResidualAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighSelected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

/-- Literal retained second rows supply the frequency coordinate, including
reflection. Fixed unit costs are absorbed before sources and labels move. -/
theorem eventual_geometry_literal_high_frequency
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (b εfreq : ℝ)(N : ℕ)(hb : 0<b)(hε : 0<εfreq) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{α DataLabel : Type}[Fintype α][DecidableEq α][Fintype DataLabel],
    ∀(reflected second : Bool)(s : Input α)(R seed : Ideal O)(D ξ : ℝ)(hK : 0<Z^D)
      (bin : ℤ×(Fin 5→ℤ))
      (column : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : secondLiveRows (fun l=>(datum l).block))
      (hfirst : first row.val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin column)
      (ampExponent reserveShift εvolume : ℝ),
    ξ≤εfreq →
    (datum row.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) (volume s) Z ξ (3*ampExponent) reserveShift b N
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin column)) Z ξ →
    let left:=!reflected
    let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
    let hf:=geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK
      bin column datum first row hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left u₀ unit hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let d₂:=datum row.val.1
    let x:=childHighCoordinates (actualHighCoordinates reflected left second
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin column) d₂.C d₂.D d₂.inactive
      Z D (Real.logb Z (volume s)) ampExponent ξ reserveShift εfreq) εvolume
    rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2) := by
  filter_upwards [eventual_actual_child_high_frequency u₀ b εfreq N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro α DataLabel _ _ _ reflected second s R seed D ξ hK bin column datum first row hfirst
    ampExponent reserveShift εvolume hξ hradius left unit hf key₀ key d₂ x
  have hC : Supported (first row.val.1).1.1 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).hC
  have hD : Supported (first row.val.1).1.2 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).hD
  have heq : primeSupport (first row.val.1).1.1=primeSupport (first row.val.1).1.2 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).sameSupport
  have hret:=actual_second_live_retained_weight (fun l=>(datum l).block) row.val row.property
  change retainedWeight d₂.radius (normValue
    ((commonFrequencyGenerator d₂.C d₂.D*nonunitFrequencyGenerator d₂.C d₂.D d₂.inactive)*
      row.val.2.2.2.val))≠0 at hret
  rw [hradius] at hret
  have hh:=hz.2 reflected left second (firstDictionaryUnit left η₀ u₀ F₀ R₀) key₀ hC hD heq
    (volume s) D ampExponent reserveShift ξ εvolume (volume_pos s) hξ (by
      simpa only [key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
        originalSecondBlock,hfirst] using hret)
  have hfreq : rawFrequencyNorm (nonzeroJointSourceRow key₀)≤Z^(x 2) := by
    simpa only [x,key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
      originalSecondBlock,hfirst,rawFrequencyNorm,nonzeroJointSourceRow,normValue] using hh.2
  cases second
  · exact hfreq
  · exact (reflected_joint_norm key₀).trans_le hfreq

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
