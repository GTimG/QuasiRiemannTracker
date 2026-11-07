/- Subhanjan Das; MIT for new source assembly; AI-assisted with OpenAI Codex.
Analytic rules: Hailey Collet through the admitted Mark Lewko dependency. -/
import Candidate.InputInterface
import Candidate.Geometry
import Candidate.GraphAssembly.ACount
import Candidate.GraphAssembly.APhysical
import Candidate.ReturnA.SourceInlet
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.SuppliersA
noncomputable section
open OAI.SevenEighths
open Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record12518109Existence
open Das.QRH.ReturnA

theorem global_suppliers
 (input:Das.QRH.TrackerRebuild.Inputs)
 (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
 UniformUnitFaceSource countGlobal ∧ UniformUnitFaceSource physicalGlobal := by
 have hcap : 6*(2*HeckeZeroSupremum.beta-1) ≤ (11243189691/2500000000:ℝ) := Das.QRH.TrackerRebuild.root_cap input
 have hn := input.natural_source (11243189691/2500000000:ℝ)
   (by norm_num) (by norm_num) hb hcap
 let S : Source → Prop := fun n => ParentGood n ∧ QRH.Record1252270103Graph.P n
 have step : ∀(n low:Source), (n.allowance=1/10^17 ∧ n.lowFee=1/10^12 ∧ n.highFee=1/10^10) →
   SourceValid n low (some low) → S low → S n := by
  intro n low ha hv hl
  refine ⟨parent_good_of_source_valid hv, ?_⟩
  exact input.nf_step n low (some low) hb
    (Das.QRH.TrackerRebuild.internal_cap input) hv hl.1 (Or.inr ha) hl.2
    (by intro h hh; cases hh; exact hl.2)
 have hc0 : S Das.QRH.GraphAssembly.ACount.root := by
  constructor
  · norm_num [ParentGood,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.ACount.root,Das.QRH.Graphs.ACount000.source000]
  · convert hn using 1 <;>
     norm_num [QRH.Record1252270103Graph.P,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.ACount.root,
       Das.QRH.Graphs.ACount000.source000,Das.QRH.TrackerRebuild.rootK]
 have hp0 : S Das.QRH.GraphAssembly.APhysical.root := by
  constructor
  · norm_num [ParentGood,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.APhysical.root,Das.QRH.Graphs.APhysical000.source000]
  · convert hn using 1 <;>
     norm_num [QRH.Record1252270103Graph.P,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.APhysical.root,
       Das.QRH.Graphs.APhysical000.source000,Das.QRH.TrackerRebuild.rootK]
 have hc := (Das.QRH.GraphAssembly.ACount.advance S step hc0).2
 have hp := (Das.QRH.GraphAssembly.APhysical.advance S step hp0).2
 constructor
 · change UniformUnitFaceSource _ at hc
   convert hc using 1 <;>
    norm_num [QRH.Record1252270103Graph.P,QRH.Record1252270103Source.GlobalSource,
      QRH.Record1252270103Source.globalFace,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.ACount.terminal,
      Das.QRH.Graphs.ACount168.source023,countGlobal,globalFace,DasStageAFinite.countCB,DasStageAFinite.countCL]
 · change UniformUnitFaceSource _ at hp
   convert hp using 1 <;>
    norm_num [QRH.Record1252270103Graph.P,QRH.Record1252270103Source.GlobalSource,
      QRH.Record1252270103Source.globalFace,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.APhysical.terminal,
      Das.QRH.Graphs.APhysical152.source073,physicalGlobal,globalFace,DasStageAFinite.physicalB,DasStageAFinite.physicalLambda]
end
end Das.QRH.SuppliersA
#print axioms Das.QRH.SuppliersA.global_suppliers
