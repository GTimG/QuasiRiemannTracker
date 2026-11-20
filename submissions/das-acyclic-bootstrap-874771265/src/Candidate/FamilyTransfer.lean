/- Subhanjan Das; MIT; AI-assisted with OpenAI Codex.
This is a scope-explicit corollary of the admitted Collet/OpenAI transfer. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Assembly.Continuation
set_option autoImplicit false
namespace Das.QRH.FamilyTransfer
noncomputable section
open OAI.SevenEighths

theorem dirichlet_of_family_beta {θ:ℝ} (hθ:0<θ)
 (hβ:HeckeZeroSupremum.beta≤θ) {q:ℕ} [NeZero q]
 (χ:DirichletCharacter ℂ q) (s:ℂ) (hs:θ<s.re)
 (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 := by
 apply Cycle25.dirichlet_of_hecke hθ _ χ s hs hpole
 intro η z hz hexc
 exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η (hβ.trans_lt hz) hexc
end
end Das.QRH.FamilyTransfer
#print axioms Das.QRH.FamilyTransfer.dirichlet_of_family_beta
