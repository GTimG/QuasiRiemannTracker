/- Exact interface for already formalized analytic inputs.
Subhanjan Das; MIT; AI-assisted with OpenAI Codex.
TrackerInput supplies every field from admitted Collet/Lewko theorems. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.GraphContract
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.TrackerRebuild
noncomputable section
open OAI.SevenEighths

def thetaInput : ℝ := 8747729897/10000000000
def rootK : ℝ := 11243189691/2500000000

structure Inputs : Prop where
 family_bound : HeckeZeroSupremum.beta ≤ thetaInput
 natural_source : ∀ K:ℝ, (21/5:ℝ)≤K → K≤9/2 →
  (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤K →
  QRH.Record1252270103Source.GlobalSource 1 K (11/200)
 nf_step : QRH.Record1252270103Graph.NFStep

theorem root_cost_identity : rootK=6*(2*thetaInput-1) := by
 norm_num [rootK,thetaInput]
theorem root_cap (input:Inputs) : 6*(2*HeckeZeroSupremum.beta-1)≤rootK := by
 rw [root_cost_identity]
 linarith [input.family_bound]
theorem internal_cap (input:Inputs) :
 6*(2*HeckeZeroSupremum.beta-1)≤QRH.Record1252270103Graph.finalK := by
 have hk : rootK≤QRH.Record1252270103Graph.finalK := by
  norm_num [rootK,QRH.Record1252270103Graph.finalK]
 exact (root_cap input).trans hk
end
end Das.QRH.TrackerRebuild
#print axioms Das.QRH.TrackerRebuild.root_cap
#print axioms Das.QRH.TrackerRebuild.internal_cap
