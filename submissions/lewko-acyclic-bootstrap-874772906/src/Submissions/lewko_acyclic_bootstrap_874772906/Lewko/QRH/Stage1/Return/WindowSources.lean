/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Both globally downward suppliers feed every admitted actual counting window. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.CountSource
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.CountWindows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage1Return
noncomputable section
open scoped Classical BigOperators ContDiff
open LewkoStage1Finite QRH.Record12518109Source QRH.Record12518109Existence
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly

def countingSource (b:CountBranch) : SourceFace :=
 broadFace (branchB b) (branchL b) (branchCap b)
def sourceSupplier (b:CountBranch) : SourceFace :=
 match b with
 | .P | .capP => physicalGlobal
 | _ => countGlobal

theorem supplier_restricts_counting (b:CountBranch) (hb:b≠.old) :
 (sourceSupplier b).Restricts (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (constructor <;>
  norm_num [sourceSupplier,countingSource,broadFace,countGlobal,physicalGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,physicalB,physicalLambda])

theorem all_counting_sources_common_mesh
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {ε:ℝ} (hε:0<ε) : ∃mesh:ℝ,0<mesh ∧
 UnitFaceSource countGlobal mesh ε ∧ UnitFaceSource physicalGlobal mesh ε ∧
 ∀b:CountBranch,b≠.old → UnitFaceSource (countingSource b) mesh ε := by
 obtain ⟨mesh,hm,hc,hp,_⟩ := selected_sources_common_mesh hC hP hε
 refine ⟨mesh,hm,hc,hp,?_⟩
 intro b hb
 apply unit_source_restrict (supplier_restricts_counting b hb)
 cases b <;> first | exact (hb rfl).elim | exact hc | exact hp

/-- The common source mesh precedes the actual moment data and source carrier.
The resulting detector energy retains all row labels and all independent heights. -/
theorem all_detector_inputs_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {ε:ℝ} (hε:0<ε) : ∃mesh:ℝ,0<mesh ∧
 ∀D:Cycle25.Weighted.MomentData,∀F:WeightedSourceData D,D.t=ε →
 (∀j,D.ell j≤mesh/200) →
 ∀w:ReturnCountWindow,QRH.Record12518109Count.WeightedAffineFineInput F (countingSource w.branch) := by
 obtain ⟨mesh,hm,_,_,hs⟩ := all_counting_sources_common_mesh hC hP hε
 refine ⟨mesh,hm,?_⟩
 intro D F ht hf w
 apply detector_affine_of_unit F (countingSource w.branch) (by rfl) mesh hm hf
 rw [ht]
 exact hs w.branch w.nonold
end
end QRH.LewkoStage1Return
#print axioms QRH.LewkoStage1Return.all_counting_sources_common_mesh
#print axioms QRH.LewkoStage1Return.all_detector_inputs_of_global_sources
