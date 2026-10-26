/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.NativeAffineContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentInductionEnergy
open Cycle63InitialSource Cycle63Moment Cycle153HighProvider Cycle153RegionalLow
open Cycle153ReachableGeometry

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable (C : SourceContext (α:=α) M H) (j : Fin 4)
variable (Zparent parentUnit u oldMask : ℝ)
variable (hparentUnit : 0<parentUnit) (hu : 0<u)
variable (hbase : Zparent=C.globalBase^parentUnit)
variable (st : NaturalState Zparent oldMask 2) (hwidth : st.width ≤ u)
variable (hmask : (st.puncture.absNorm:ℝ) ≤ (Zparent^u)^(20:ℝ))
variable (slots : Finset α) (p : Profiles (1/4) (9/4))
variable (X1 X2 : ℝ) (hX1 : 0<X1) (hX2 : 0<X2)

/-- Arithmetic data proved at the actual deleted daughter, before its
recursive energy is estimated. In particular all slots still refer to
the original dictionary and the position is the actual rounded one. -/
structure NativeChildGeometry where
  coordinates : Fin 14 → ℝ
  prefixRows : PrefixRows (j.val+1) coordinates
  physical_nonnegative : ∀ i : Fin 48,35 ≤ i.val → 0 ≤ Cycle153Geometry.Coordinates.rows i coordinates
  unit_eq : parentUnit*u=modelUnit j coordinates
  unit_floor : (1/50:ℝ) ≤ parentUnit*u
  unit_le_one : parentUnit*u ≤ 1
  length_eq : (parentUnit*u)*(length (Zparent^u) X1+length (Zparent^u) X2+
    ∑ i : slots,C.originalWeight i/(parentUnit*u))=modelLength j coordinates
  slots_eq : (∑ i : slots,C.originalWeight i)=modelSlots j coordinates
  plane : ℝ
  plane_eq : plane=modelPlane j coordinates/(parentUnit*u)
  position : Cycle153.RegionalPosition
  rounded : position=Cycle153.roundedPosition (1/C.gridDenominator) plane
    (length (Zparent^u) X1) (length (Zparent^u) X2)
    (∑ i : slots,C.originalWeight i/(parentUnit*u))
  facts : position.Facts (innerStage j.val)
  window : @Cycle63.AffineLedger.PlainWindow
    (Cycle153.regionalLedger (innerStage j.val) position facts)
    (length (Zparent^u) X1) (length (Zparent^u) X2)
    (∑ i : slots,C.originalWeight i/(parentUnit*u))
  overshoot : length (Zparent^u) X1+length (Zparent^u) X2+
    6*Cycle63.Optimization.slotPrice*(∑ i : slots,C.originalWeight i/(parentUnit*u)) ≤ 1+9/1000

variable (P : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) st.character st.puncture)
variable (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap j.val))
variable (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)
variable (t height : ℝ) (hheight : 0 ≤ height)
variable (hfreq : ∀ i : slots,|C.frequency i| ≤ height)
variable (geom : NativeChildGeometry C j Zparent parentUnit u slots X1 X2)
variable (hPhistory : Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
  modelMissing j geom.coordinates+modelReduction j geom.coordinates+
    ((j.val:ℝ)+1)/1000000000000000)

/-- Construct the actual reachable state using the native rebase/widen
operation. Its source presentation and root multiplier are the literal
ones of the retained daughter. There is no supplied energy estimate. -/
def nodeOfNativeContinuation : ReachableNode C j where
  coordinates := geom.coordinates
  prefixRows := geom.prefixRows
  physical_nonnegative := geom.physical_nonnegative
  unit := parentUnit*u
  unit_eq := geom.unit_eq
  unit_floor := geom.unit_floor
  unit_le_one := geom.unit_le_one
  localBase := Zparent^u
  localBase_eq := by
    rw [hbase,←Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]
  slots := slots
  state := nativeContinuationState st u hu hwidth hmask
  puncture_global_log := hPhistory
  fixedModulus := hfixed
  width_le_one := (nativeContinuationState_width st u hu hwidth hmask).le
  presentation := P
  presentation_global_norm := hPnorm
  profiles := p
  X1 := X1
  X2 := X2
  X1_pos := hX1
  X2_pos := hX2
  length_eq := geom.length_eq
  slots_eq := geom.slots_eq
  t := t
  height := height
  height_nonneg := hheight
  frequency_bound := hfreq
  plane := geom.plane
  plane_eq := geom.plane_eq
  position := geom.position
  rounded := geom.rounded
  positionFacts := geom.facts
  weight_mesh := by
    intro i
    have hunit : 0<parentUnit*u := lt_of_lt_of_le (by norm_num) geom.unit_floor
    apply (div_le_iff₀ hunit).mpr
    exact (C.originalWeight_mesh i).trans
      (by nlinarith only [geom.unit_floor,C.slotMesh_pos])
  window := geom.window
  overshoot := geom.overshoot

/-- Original coefficients and their exact relative scaling identify the
next affine input. No arbitrary input is asserted equal to the source. -/
theorem nodeOfNativeContinuation_input :
    let N := nodeOfNativeContinuation C j Zparent parentUnit u oldMask hu hbase st hwidth hmask
      slots p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight hfreq geom hPhistory
    letI := N.ledger
    N.input hH = nativeRegionalContinuationInput M H hH C.etaSeed
      (fun i : slots=>C.theta i) C.W C.W_smooth.continuous 1 2 (33/50) (33/50)
      (by norm_num) C.W_support (fun i : slots=>C.originalWeight i/parentUnit)
      (fun i : slots=>C.sigma i) (fun i : slots=>C.frequency i) (fun i=>C.sigma_fixed i)
      st u hu hwidth hmask p (by norm_num) t X1 X2 hX1 hX2 := by
  dsimp only [ReachableNode.input,nativeRegionalContinuationInput,nodeOfNativeContinuation]
  simp only [div_div]

/-- The induction hypothesis on the constructed node controls the
literal physical daughter energy. All original ray coefficients and
radial normalization are retained in this identity. -/
theorem nodeOfNativeContinuation_energy :
    let N := nodeOfNativeContinuation C j Zparent parentUnit u oldMask hu hbase st hwidth hmask
      slots p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight hfreq geom hPhistory
    N.sourceEnergy hH =
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : slots=>CenteredMomentPrimeSlot.primePool M H 2 (Zparent^(C.originalWeight i/parentUnit)))
        (fun (i : slots) I=>
          idealCoeff
            (relativeCharacter M H hH C.etaSeed (C.theta i)) I*
          HeckePrimeAnnular.annularWeight C.W (Zparent^(C.originalWeight i/parentUnit))
            (C.sigma i) (C.frequency i) I)
        (fun i : slots=>Zparent^(C.originalWeight i/parentUnit)) X1 X2
        st.radial.keep st.radial.profile st.radial.scale := by
  intro N
  letI := N.ledger
  have hin := nodeOfNativeContinuation_input hH C j Zparent parentUnit u oldMask hu hbase st hwidth hmask
    slots p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight hfreq geom hPhistory
  have henergy := nativeRegionalContinuationInput_energy M H hH C.etaSeed
    (fun i : slots=>C.theta i) C.W C.W_smooth.continuous 1 2 (33/50) (33/50)
    (by norm_num) C.W_support (fun i : slots=>C.originalWeight i/parentUnit)
    (fun i : slots=>C.sigma i) (fun i : slots=>C.frequency i) (fun i=>C.sigma_fixed i)
    st u hu hwidth hmask p (by norm_num) t X1 X2 hX1 hX2
  unfold ReachableNode.sourceEnergy
  rw [hin]
  exact henergy

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.nodeOfNativeContinuation_input
#print axioms OAI.SevenEighths.Cycle153Reachable.nodeOfNativeContinuation_energy
