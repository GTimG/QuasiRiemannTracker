/- Preserve actual physical path data when a deeper child extends future coordinates. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceAttach
import Candidate.Research.RecursiveAffine.ActualTraceTerminal

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153Geometry

theorem prefixCoordinate_mono {j k : ℕ} (hjk : j≤k) {i : Fin 14}
    (hi : prefixCoordinate j i) : prefixCoordinate k i := by
  dsimp only [prefixCoordinate] at hi ⊢
  omega

theorem physical_step_models_preserved (j : Fin 4) (x y : Fin 14→ℝ)
    (h : ∀i,prefixCoordinate (j.val+2) i→y i=x i) :
    modelLength j y=modelLength j x ∧ modelUnit j y=modelUnit j x ∧
    pathDeletion j.val y=pathDeletion j.val x ∧ pathV j.val y=pathV j.val x ∧
    pathRed j.val y=pathRed j.val x ∧
    ![Coordinates.a1 y,Coordinates.a2 y,Coordinates.a3 y,Coordinates.a4 y] j=
      ![Coordinates.a1 x,Coordinates.a2 x,Coordinates.a3 x,Coordinates.a4 x] j := by
  fin_cases j
  · have h0:y (0:Fin 14)=x 0:=h 0 (by norm_num [prefixCoordinate])
    have h1:y (1:Fin 14)=x 1:=h 1 (by norm_num [prefixCoordinate])
    have h2:y (2:Fin 14)=x 2:=h 2 (by norm_num [prefixCoordinate])
    have h5:y (5:Fin 14)=x 5:=h 5 (by norm_num [prefixCoordinate])
    have h6:y (6:Fin 14)=x 6:=h 6 (by norm_num [prefixCoordinate])
    have h9:y (9:Fin 14)=x 9:=h 9 (by norm_num [prefixCoordinate])
    have h10:y (10:Fin 14)=x 10:=h 10 (by norm_num [prefixCoordinate])
    have h13:y (13:Fin 14)=x 13:=h 13 (by norm_num [prefixCoordinate])
    simp [modelLength, modelUnit, pathDeletion, pathV, pathRed, pathStage, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4, Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, h0, h1, h2, h5, h6, h9, h10, h13]
  · have h0:y (0:Fin 14)=x 0:=h 0 (by norm_num [prefixCoordinate])
    have h1:y (1:Fin 14)=x 1:=h 1 (by norm_num [prefixCoordinate])
    have h2:y (2:Fin 14)=x 2:=h 2 (by norm_num [prefixCoordinate])
    have h3:y (3:Fin 14)=x 3:=h 3 (by norm_num [prefixCoordinate])
    have h5:y (5:Fin 14)=x 5:=h 5 (by norm_num [prefixCoordinate])
    have h6:y (6:Fin 14)=x 6:=h 6 (by norm_num [prefixCoordinate])
    have h7:y (7:Fin 14)=x 7:=h 7 (by norm_num [prefixCoordinate])
    have h9:y (9:Fin 14)=x 9:=h 9 (by norm_num [prefixCoordinate])
    have h10:y (10:Fin 14)=x 10:=h 10 (by norm_num [prefixCoordinate])
    have h11:y (11:Fin 14)=x 11:=h 11 (by norm_num [prefixCoordinate])
    have h13:y (13:Fin 14)=x 13:=h 13 (by norm_num [prefixCoordinate])
    simp [modelLength, modelUnit, pathDeletion, pathV, pathRed, pathStage, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4, Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, h0, h1, h2, h3, h5, h6, h7, h9, h10, h11, h13]
  · have h0:y (0:Fin 14)=x 0:=h 0 (by norm_num [prefixCoordinate])
    have h1:y (1:Fin 14)=x 1:=h 1 (by norm_num [prefixCoordinate])
    have h2:y (2:Fin 14)=x 2:=h 2 (by norm_num [prefixCoordinate])
    have h3:y (3:Fin 14)=x 3:=h 3 (by norm_num [prefixCoordinate])
    have h4:y (4:Fin 14)=x 4:=h 4 (by norm_num [prefixCoordinate])
    have h5:y (5:Fin 14)=x 5:=h 5 (by norm_num [prefixCoordinate])
    have h6:y (6:Fin 14)=x 6:=h 6 (by norm_num [prefixCoordinate])
    have h7:y (7:Fin 14)=x 7:=h 7 (by norm_num [prefixCoordinate])
    have h8:y (8:Fin 14)=x 8:=h 8 (by norm_num [prefixCoordinate])
    have h9:y (9:Fin 14)=x 9:=h 9 (by norm_num [prefixCoordinate])
    have h10:y (10:Fin 14)=x 10:=h 10 (by norm_num [prefixCoordinate])
    have h11:y (11:Fin 14)=x 11:=h 11 (by norm_num [prefixCoordinate])
    have h12:y (12:Fin 14)=x 12:=h 12 (by norm_num [prefixCoordinate])
    have h13:y (13:Fin 14)=x 13:=h 13 (by norm_num [prefixCoordinate])
    simp [modelLength, modelUnit, pathDeletion, pathV, pathRed, pathStage, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4, Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · have h0:y (0:Fin 14)=x 0:=h 0 (by norm_num [prefixCoordinate])
    have h1:y (1:Fin 14)=x 1:=h 1 (by norm_num [prefixCoordinate])
    have h2:y (2:Fin 14)=x 2:=h 2 (by norm_num [prefixCoordinate])
    have h3:y (3:Fin 14)=x 3:=h 3 (by norm_num [prefixCoordinate])
    have h4:y (4:Fin 14)=x 4:=h 4 (by norm_num [prefixCoordinate])
    have h5:y (5:Fin 14)=x 5:=h 5 (by norm_num [prefixCoordinate])
    have h6:y (6:Fin 14)=x 6:=h 6 (by norm_num [prefixCoordinate])
    have h7:y (7:Fin 14)=x 7:=h 7 (by norm_num [prefixCoordinate])
    have h8:y (8:Fin 14)=x 8:=h 8 (by norm_num [prefixCoordinate])
    have h9:y (9:Fin 14)=x 9:=h 9 (by norm_num [prefixCoordinate])
    have h10:y (10:Fin 14)=x 10:=h 10 (by norm_num [prefixCoordinate])
    have h11:y (11:Fin 14)=x 11:=h 11 (by norm_num [prefixCoordinate])
    have h12:y (12:Fin 14)=x 12:=h 12 (by norm_num [prefixCoordinate])
    have h13:y (13:Fin 14)=x 13:=h 13 (by norm_num [prefixCoordinate])
    simp [modelLength, modelUnit, pathDeletion, pathV, pathRed, pathStage, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4, Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- The parent edge binds the immediate actual physical source. A child
IH may extend later coordinates; its prefix-preserved receipt transports
this SAME edge to that final path, without setting future coordinates equal. -/
def NativeTraceEdge.transportFinal {N : ReachableNode C j} {x : Fin 14→ℝ}
    {m A logPrefix : ℝ} (edge : NativeTraceEdge (hH:=hH) N x m A logPrefix)
    (y : Fin 14→ℝ) (hy : ∀i,prefixCoordinate (j.val+2) i→y i=x i) :
    NativeTraceEdge (hH:=hH) N y m A logPrefix := by
  have hm:=physical_step_models_preserved j x y hy
  refine {
    node:=edge.node
    fee:=edge.fee
    sourceGates:=edge.sourceGates
    fineSource:=edge.fineSource
    fineFee:=edge.fineFee
    fineScalePad:=edge.fineScalePad
    fineCapacityPad:=edge.fineCapacityPad
    fineAmplifierError:=edge.fineAmplifierError
    remainingFee:=edge.remainingFee
    V:=edge.V
    Red:=edge.Red
    residualF:=edge.residualF
    residualF_nonneg:=edge.residualF_nonneg
    capacityPad:=edge.capacityPad
    scalePad:=edge.scalePad
    amplifierError:=edge.amplifierError
    amplifierError_nonneg:=edge.amplifierError_nonneg
    root_scale:=edge.root_scale
    root_length:=edge.root_length
    relative_scale:=edge.relative_scale
    length_step:=edge.length_step
    capacity:=edge.capacity
    prefix_preserved:=fun i hi=>(hy i (prefixCoordinate_mono (by omega) hi)).trans (edge.prefix_preserved i hi)
    length_model:=?_
    unit_model:=?_
    junction_model:=edge.junction_model
    deletion_model:=edge.deletion_model.trans hm.2.2.1.symm
    missing_model:=edge.missing_model.trans hm.2.2.2.1.symm
    reduction_model:=edge.reduction_model.trans hm.2.2.2.2.1.symm
    amplifier_model:=?_ }
  · rw [pathStage_fin]
    exact edge.length_model.trans (by simpa only [pathStage_fin] using hm.1.symm)
  · rw [pathStage_fin]
    exact edge.unit_model.trans (by simpa only [pathStage_fin] using hm.2.1.symm)
  · rw [pathStage_fin]
    rw [hm.2.2.2.2.2]
    simpa only [pathStage_fin] using edge.amplifier_model

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NativeTraceEdge.transportFinal
