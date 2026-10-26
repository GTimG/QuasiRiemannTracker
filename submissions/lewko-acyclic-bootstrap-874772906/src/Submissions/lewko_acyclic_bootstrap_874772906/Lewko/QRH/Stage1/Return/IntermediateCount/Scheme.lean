/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The intermediate return uses its independent pre-C30 natural moment input. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.IntermediateCount.FinalWindows
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.CountScheme
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.SourceInlet
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage1Return.IntermediateCount
noncomputable section
open LewkoStage1Return.C30 QRH.Record12518109Source QRH.Record12518109Existence
noncomputable abbrev countScheme : CountScheme where
 naturalκ := naturalK/6
 natural_lo := by norm_num [naturalK]
 natural_hi := by norm_num [naturalK]
 windows := intermediateAdmittedWindows

def countGlobal : SourceFace := globalFace countCB countCL (54998999999/1000000000000)
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda (54998999999/1000000000000)
def physicalWindow : SourceFace := ⟨physicalB,physicalLambda,2/5,11/25,17/500,1/25⟩
def countingSource (b:CountBranch) : SourceFace := broadFace (branchB b) (branchL b) (branchCap b)
def sourceSupplier (b:CountBranch) : SourceFace :=
 match b with | .P | .capP => physicalGlobal | _ => countGlobal

theorem supplier_restricts_counting (b:CountBranch) (hb:b≠.old) :
 (sourceSupplier b).Restricts (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (constructor <;>
  norm_num [sourceSupplier,countingSource,broadFace,countGlobal,physicalGlobal,globalFace,
   branchB,branchL,branchCap,countCB,countCL,physicalB,physicalLambda])

theorem physical_restricts : physicalGlobal.Restricts physicalWindow := by
 constructor <;> norm_num [physicalGlobal,physicalWindow,globalFace,physicalB,physicalLambda]

theorem ReturnCountWindow.toAdmitted_face (w:ReturnCountWindow) :
 w.toAdmitted.face=countingSource w.branch := rfl

theorem windows_common_mesh
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {ε:ℝ} (hε:0<ε) : ∃mesh:ℝ,0<mesh ∧
 UnitFaceSource physicalWindow mesh ε ∧
 ∀w∈countScheme.windows,UnitFaceSource w.face mesh ε := by
 obtain ⟨cm,hcm,hc⟩ := hC ε hε
 obtain ⟨pm,hpm,hp⟩ := hP ε hε
 have hc' := hc.mono_mesh (min_le_left cm pm)
 have hp' := hp.mono_mesh (min_le_right cm pm)
 refine ⟨min cm pm,lt_min hcm hpm,unit_source_restrict physical_restricts hp',?_⟩
 intro w hw
 obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
 change UnitFaceSource (countingSource v.branch) _ ε
 apply unit_source_restrict (supplier_restricts_counting v.branch v.nonold)
 cases v.branch <;> first | exact (v.nonold rfl).elim | exact hc' | exact hp'
end
end QRH.LewkoStage1Return.IntermediateCount
#print axioms QRH.LewkoStage1Return.IntermediateCount.windows_common_mesh
