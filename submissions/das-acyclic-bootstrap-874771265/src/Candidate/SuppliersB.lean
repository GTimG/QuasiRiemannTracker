/- Subhanjan Das; MIT for new source assembly; AI-assisted with OpenAI Codex.
Analytic rules: Hailey Collet through the admitted Mark Lewko dependency. -/
import Candidate.InputInterface
import Candidate.Geometry
import Candidate.GraphAssembly.BCount
import Candidate.GraphAssembly.BPhysical
import Candidate.ReturnB.SourceInlet
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.SuppliersB
noncomputable section
open OAI.SevenEighths
open Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record12518109Existence
open Das.QRH.ReturnB

theorem global_suppliers
 (input:Das.QRH.TrackerRebuild.Inputs)
 (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprior : HeckeZeroSupremum.beta ≤ Das.QRH.TrackerGeometry.thetaA) :
 UniformUnitFaceSource countGlobal ∧ UniformUnitFaceSource physicalGlobal := by
 have hcap : 6*(2*HeckeZeroSupremum.beta-1) ≤ (112431381/25000000:ℝ) := by
   have h := hprior
   norm_num [Das.QRH.TrackerGeometry.thetaA] at h
   linarith
 have hn := input.natural_source (112431381/25000000:ℝ)
   (by norm_num) (by norm_num) hb hcap
 let S : Source → Prop := fun n => ParentGood n ∧ QRH.Record1252270103Graph.P n
 have step : ∀(n low:Source), (n.allowance=1/10^17 ∧ n.lowFee=1/10^12 ∧ n.highFee=1/10^10) →
   SourceValid n low (some low) → S low → S n := by
  intro n low ha hv hl
  refine ⟨parent_good_of_source_valid hv, ?_⟩
  exact input.nf_step n low (some low) hb
    (Das.QRH.TrackerRebuild.internal_cap input) hv hl.1 (Or.inr ha) hl.2
    (by intro h hh; cases hh; exact hl.2)
 have hc0 : S Das.QRH.GraphAssembly.BCount.root := by
  constructor
  · norm_num [ParentGood,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BCount.root,Das.QRH.Graphs.BCount000.source000]
  · convert hn using 1 <;>
     norm_num [QRH.Record1252270103Graph.P,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BCount.root,
       Das.QRH.Graphs.BCount000.source000,Das.QRH.TrackerRebuild.rootK]
 have hp0 : S Das.QRH.GraphAssembly.BPhysical.root := by
  constructor
  · norm_num [ParentGood,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BPhysical.root,Das.QRH.Graphs.BPhysical000.source000]
  · convert hn using 1 <;>
     norm_num [QRH.Record1252270103Graph.P,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BPhysical.root,
       Das.QRH.Graphs.BPhysical000.source000,Das.QRH.TrackerRebuild.rootK]
 have hc := (Das.QRH.GraphAssembly.BCount.advance S step hc0).2
 have hp := (Das.QRH.GraphAssembly.BPhysical.advance S step hp0).2
 constructor
 · change UniformUnitFaceSource _ at hc
   convert hc using 1 <;>
    norm_num [QRH.Record1252270103Graph.P,QRH.Record1252270103Source.GlobalSource,
      QRH.Record1252270103Source.globalFace,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BCount.terminal,
      Das.QRH.Graphs.BCount168.source023,countGlobal,globalFace,DasStageBFinite.countCB,DasStageBFinite.countCL]
 · change UniformUnitFaceSource _ at hp
   convert hp using 1 <;>
    norm_num [QRH.Record1252270103Graph.P,QRH.Record1252270103Source.GlobalSource,
      QRH.Record1252270103Source.globalFace,Das.QRH.CoreBridge.toOriginal,Das.QRH.GraphAssembly.BPhysical.terminal,
      Das.QRH.Graphs.BPhysical152.source073,physicalGlobal,globalFace,DasStageBFinite.physicalB,DasStageBFinite.physicalLambda]
end
end Das.QRH.SuppliersB
#print axioms Das.QRH.SuppliersB.global_suppliers
