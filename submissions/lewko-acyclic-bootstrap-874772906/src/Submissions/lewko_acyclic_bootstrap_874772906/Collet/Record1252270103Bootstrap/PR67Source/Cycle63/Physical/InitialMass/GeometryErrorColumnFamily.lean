import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorColumn
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorActiveInput
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentCommonPairedSource Cycle63FinalError Cycle63FinalNatural
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentRestrictedEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment Cycle63FinalError
open CenteredMomentAmplificationErrorEnergy CenteredMomentSlotRatios
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstMixedRightTransport
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentCompleteCommon
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily RayFourExpansion
open CenteredMomentCommonRawScale CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildSourceCaps CenteredMomentLogDyadic
local instance errorColumnFamilyDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The entire nonexceptional frequency set supplies its own keep and
unit radial majorant; no row energy or majorization input is required. -/
theorem actual_error_complete_row_admission (s : Input α) (q : Chain s)
    (Z Mrow amp omega ξ b J : ℝ)
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α))
    (Bmask : ℝ) (hZ : 1<Z) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hP : q.R₂*q.E₂≠0) (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
    (z : O) (hz : z∈partRows false q.υ χ Q fixedBadMask g.C g.D g.U g.radius) :
    let st := retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    st.radial.keep z ∧ 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
  refine ⟨?_,?_⟩
  · have hne : nonexceptional q.υ χ Q fixedBadMask
        (commonFrequencyGenerator g.C g.D*nonunitFrequencyGenerator g.C g.D g.U) z := by
      exact (Finset.mem_filter.mp hz).2
    exact (actual_nonexceptional_keep g.family g.radius Z Bmask hZ χ Q (q.R₂*q.E₂) hP hPN
      fixedBadMask z fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hne
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact actual_partRows_majorized Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN
      q.υ χ fixedBadMask g.radius g.C g.D g.U z hz

/-- Exact restoration of the original extracted weight. -/
theorem error_column_paid_restore (p : O) (k : ℕ) (Z coefficient energy C envelope : ℝ)
    (hZ : 0<Z) (hc : 0≤ coefficient)
    (hpaid : localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy≤C*envelope) :
    coefficient*localErrorCost p (k-1)*energy≤
      C*(coefficient*Z^(errorRemoval p Z k-errorMoving p Z k)*envelope) := by
  have hinv : Z^(errorRemoval p Z k-errorMoving p Z k)*
      Z^(-errorRemoval p Z k+errorMoving p Z k)=1 := by
    rw [←Real.rpow_add hZ]
    simp only [show errorRemoval p Z k-errorMoving p Z k+
      (-errorRemoval p Z k+errorMoving p Z k)=0 by ring,Real.rpow_zero]
  calc
    _ = (coefficient*Z^(errorRemoval p Z k-errorMoving p Z k))*
        (localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy) := by
      linear_combination -(coefficient*localErrorCost p (k-1)*energy)*hinv
    _ ≤ (coefficient*Z^(errorRemoval p Z k-errorMoving p Z k))*(C*envelope) :=
      mul_le_mul_of_nonneg_left hpaid (mul_nonneg hc (Real.rpow_nonneg hZ.le _))
    _ = _ := by ring

/-- The literal extracted retained datum supplies both projector divisibilities. -/
theorem actual_geometry_error_seed_gates (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :
    let datum := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    datum.seed∣datum.C ∧ datum.seed∣datum.D := by
  have hg := actual_retained_block_gates (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) n
  exact ⟨hg.1,hg.2.1⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
