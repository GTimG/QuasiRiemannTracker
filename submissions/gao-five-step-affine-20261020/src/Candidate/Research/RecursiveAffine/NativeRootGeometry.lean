/- Actual outer LOW source to the first reachable regional geometry. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootCoordinates
import Candidate.Research.RecursiveAffine.NativeRootStepRebase
import Candidate.Research.RecursiveAffine.PhysicalChildContinuation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle63Moment.LowBranch Cycle153RootStep Cycle153Geometry Cycle153RegionalLow
open Cycle153ContinuationUnit

noncomputable local instance rootGeometryLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- The actual root cell, same residual allocation and genuine native
continuation tests construct the first inner geometry. No next-ledger
fact, energy bound or count hypothesis is supplied. -/
def rootGeometryOfActualNativeContinuation
    (C : SourceContext (α:=α) M H)
    (s : Input α) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (bs omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi bs n)
    (hb : 1  ≤  bs) (hcard : Fintype.card α  ≤  n)
    (hs : s.upper  ≤  bs) (hlower : 1  ≤  s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion C.originalWeight  ≤  ∑i∈Rdel,C.originalWeight i)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i)  ≤  rootDetectorDeletion C.originalWeight+mesh)
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=(1:Ideal O)*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+
      (2*(n:ℝ)*Real.logb C.globalBase bs+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂))  ≤  1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)  ≤  positionMargin)
    (hwide :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      (397/1000:ℝ)  ≤  r.u)
    (hnotOld :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      r.u < length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
        length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑i : ↥(ch.indices L alloc \ Rdel),C.originalWeight i))
    (hnotReflect :
      let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
        C.originalWeight g second L alloc Rdel
      let x1:=length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 0)
      let x2:=length C.globalBase (rawDaughterScale (ch.final χ t) second L alloc 1)
      let z:=∑i : ↥(ch.indices L alloc \ Rdel),C.originalWeight i
      ¬(x1+x2+6*Cycle63.Optimization.slotPrice*z  ≤  r.u+19/5000 ∧
        (max 0 (r.u-x2+1/10000)+x1+6*Cycle63.Optimization.slotPrice*z+19/5000  ≤  r.u ∨
         max 0 (r.u-x1+1/10000)+x2+6*Cycle63.Optimization.slotPrice*z+19/5000  ≤  r.u))) :
    let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
      C.originalWeight g second L alloc Rdel
    NativeChildGeometry C (0:Fin 4) C.globalBase 1 r.u (ch.indices L alloc\Rdel)
      (rawDaughterScale (ch.final χ t) second L alloc 0)
      (rawDaughterScale (ch.final χ t) second L alloc 1) := by
  let r:=nativeRootStepValues s ch χ t C.globalBase n bs 1 omega xi reserve
    C.originalWeight g second L alloc Rdel
  let x:=rootCoordinates r.b r.rootSlack r.V r.Red r.ell
  let slots:=ch.indices L alloc\Rdel
  let X1:=rawDaughterScale (ch.final χ t) second L alloc 0
  let X2:=rawDaughterScale (ch.final χ t) second L alloc 1
  let z:=∑i : slots,C.originalWeight i
  have hu : 0 < r.u := lt_of_lt_of_le (by norm_num) hwide
  have hz : 0  ≤  z:=Finset.sum_nonneg (fun i _=>C.originalWeight_nonneg i)
  have facts:=actual_outer_native_root_step s ch χ t C.globalBase C.globalBase_gt_one n bs 1
    omega xi reserve mesh C.originalWeight g hb hcard hs hlower C.originalWeight_nonneg hscale
    hwindow second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR₂ hPuncture hfinite
  have hblo:=facts.1
  have hbhi:=facts.2.1
  have hslack:=facts.2.2.1
  have hslackMesh:=facts.2.2.2.1
  have hsum:=facts.2.2.2.2.1
  have hV:=facts.2.2.2.2.2.1
  have hRed:=facts.2.2.2.2.2.2.1
  have hell:=facts.2.2.2.2.2.2.2.1
  have hunit:=facts.2.2.2.2.2.2.2.2.1
  have hslot:=facts.2.2.2.2.2.2.2.2.2.1
  have hA:=facts.2.2.2.2.2.2.2.2.2.2.1
  have hpaid:=facts.2.2.2.2.2.2.2.2.2.2.2.1
  have hmask:=facts.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpad:=facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcap:=facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hxb : Coordinates.b x=rootSourceCell C.originalWeight:=rfl
  have hxs : Coordinates.rootSlack x=rootSourceSlack C.originalWeight:=rfl
  have hamp:=root_amp_model_alias C.originalWeight x hxb
  have hdel:=root_deletion_model_alias C.originalWeight x hxb
  have hlen:=root_length_model_alias C.originalWeight x hxb hxs
  have hU : r.u=modelUnit (0:Fin 4) x := by
    change r.u=1-6*Coordinates.a0 x-r.V
    rw [←hamp]
    exact hunit
  have hAmodel : r.childA=modelLength (0:Fin 4) x := by
    change r.childA=Coordinates.A0 x-Coordinates.d0 x-r.V-r.Red
    rw [←hlen.1,←hdel]
    exact hA
  have hSmodel : r.childSlots=modelSlots (0:Fin 4) x := by
    change r.childSlots=Coordinates.z0 x-Coordinates.d0 x-r.ell
    rw [←hlen.2,←hdel]
    exact hslot
  have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwindow.slots_ge,hwindow.slots_le⟩
  have ha0 : 0  ≤  rootSourceAmp C.originalWeight :=
    (Cycle63.AffineLedger.amp_pos (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).le
  have hu1 : r.u ≤ 1 := by
    have hunit' : r.u=1-6*r.amp-r.V:=hunit
    have ha0' : 0 ≤ r.amp:=ha0
    have hV' : 0 ≤ r.V:=hV
    linarith only [hunit',ha0',hV']
  have hrebase:=actual_root_child_length_rebase s ch χ t C.globalBase C.globalBase_gt_one
    n bs 1 omega xi reserve C.originalWeight g second L alloc Rdel hu
  have hzmodel : z=modelSlots (0:Fin 4) x:=hrebase.1.trans hSmodel
  have hplain : 0  ≤  modelLength (0:Fin 4) x-modelSlots (0:Fin 4) x := by
    rw [←hAmodel,←hSmodel]
    have h1:=Real.logb_nonneg C.globalBase_gt_one (le_max_left 1 X1)
    have h2:=Real.logb_nonneg C.globalBase_gt_one (le_max_left 1 X2)
    change 0  ≤  length C.globalBase X1 at h1
    change 0  ≤  length C.globalBase X2 at h2
    change 0  ≤  length C.globalBase X1+length C.globalBase X2+_
      -(∑i∈ch.indices L alloc\Rdel,C.originalWeight i)
    linarith only [h1,h2]
  have hkappa : Coordinates.kappa=Cycle63.Optimization.slotPrice := by
    norm_num [Coordinates.kappa,Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound]
  have hactive : 0 < modelLength (0:Fin 4) x+
      (6*Coordinates.kappa-1)*modelSlots (0:Fin 4) x-modelUnit (0:Fin 4) x := by
    rw [←hAmodel,←hzmodel,←hU,hkappa]
    have hs' : (∑i∈ch.indices L alloc\Rdel,C.originalWeight i)=z :=
      (Finset.sum_coe_sort _ _).symm
    change 0 < length C.globalBase X1+length C.globalBase X2+_
      +(6*Cycle63.Optimization.slotPrice-1)*z-r.u
    rw [hs']
    linarith only [hnotOld]
  have hraw:=rootCoordinates_raw r.b r.rootSlack r.V r.Red r.ell
    hblo hbhi hslack hslackMesh hV hRed hell
    (by linarith only [hpaid,hpad]) (by rw [←hamp];exact ha0)
    (by
      change Coordinates.mu ≤ modelUnit (0:Fin 4) x
      simpa only [Coordinates.mu] using hwide.trans_eq hU)
    hactive hplain (by
      change 0 ≤ modelSlots (0:Fin 4) x
      rw [←hzmodel];exact hz)
  have hphysical:=rootCoordinates_nonnegative r.b r.rootSlack r.V r.Red r.ell hslack hV hRed hell
  have hAroot : 1*(length C.globalBase X1+length C.globalBase X2+z)=modelLength (0:Fin 4) x := by
    have hs' : (∑i∈ch.indices L alloc\Rdel,C.originalWeight i)=z :=
      (Finset.sum_coe_sort _ _).symm
    simpa only [r,nativeRootStepValues,NativeRootStepValues.childA,hs',one_mul] using hAmodel
  have hroot : ∀i : Fin 48,i.val < 3→-(1/1000000000000000:ℝ)  ≤  Coordinates.rows i x := by
    intro i hi
    exact hraw i (Or.inl (by omega)) (by omega) (by omega)
  have hover:=actual_reflection_capacity_of_physical (0:Fin 4) x 1 r.u
    (length C.globalBase X1) (length C.globalBase X2) z (by norm_num) rfl
    (by simpa only [one_mul] using hU) hAroot (by simpa only [one_mul] using hzmodel) hroot hphysical
  rw [hkappa] at hover
  have hbalance:=actual_continuation_balance hz hwide hover hnotReflect
  have hx (X : ℝ) : r.u*length (C.globalBase^r.u) X=length C.globalBase X:=
    unit_mul_logb_rebase C.globalBase_gt_one hu
  have hbal : |(1*r.u)*length (C.globalBase^r.u) X1-(1*r.u)*length (C.globalBase^r.u) X2|  ≤
      6*Cycle63.Optimization.slotPrice*modelSlots (0:Fin 4) x+modelUnit (0:Fin 4) x/100 := by
    simpa only [one_mul,hx,←hzmodel,←hU] using hbalance
  exact childGeometryOfRawPhysical C 0 x C.globalBase 1 r.u slots X1 X2 hraw hphysical
    (by simpa only [one_mul] using hU) (by simpa only [one_mul] using hu1) hgrid
    (by simpa only [one_mul] using hrebase.2.trans hAmodel)
    hzmodel hbal (by simpa only [hkappa] using hactive)

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.rootGeometryOfActualNativeContinuation
