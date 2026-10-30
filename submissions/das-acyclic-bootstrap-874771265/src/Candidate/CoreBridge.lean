/- Definition-preserving bridge for the finite arithmetic layer.
Subhanjan Das; MIT; AI-assisted with OpenAI Codex.
The analytic NF rule and original Collet predicate are unchanged. -/
import Candidate.CoreSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.CoreBridge

def toOriginal (n : CoreSource.Source) : Record1252270103Finite.Source :=
 ⟨n.B,n.L,n.cap,n.q,n.allowance,n.lowFee,n.highFee⟩

theorem sound (n low : CoreSource.Source)
 (h : CoreSource.SourceValid n low (some low)) :
 Record1252270103Finite.SourceValid (toOriginal n) (toOriginal low) (some (toOriginal low)) := by
 rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
 refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,?_,?_⟩
 · intro v hv
   have he : toOriginal low=v := Option.mem_some_iff.mp hv
   subst v
   exact h12 low (by simp)
 · exact h13
end Das.QRH.CoreBridge
#print axioms Das.QRH.CoreBridge.sound
