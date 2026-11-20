/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine native physical bank returns the exact original restored
family; no pointwise horizon or physical energy is assumed. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamilyReturn
import Candidate.C092.transport.ActualStageFrameBudgetDispatch
set_option autoImplicit false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate
open QRH.Cycle092.NativeStrip

/-- Direct supplier for the root's final family contract. All assumptions
are the original ordered geometry and the explicit early numerical schedule. -/
theorem actual_original_family_return (n y l mesh ε δ:ℝ)
    (hmesh:mesh ≤ 1/6)(hδ:0<δ)
    (hy0:sourceY0 ≤ y)(hy1:y ≤ sourceY)(hn:n ≤ sourceRatio*y)
    (hl:l ≤ sourceWidth n y)(hρ:δ ≤ (rho:ℝ)/10000)
    (hm0:0 < mesh)(hmδ:mesh ≤ δ)(hm1:mesh ≤ 1/100) :
    OriginalFamilyReturn n y l mesh ε δ hmesh hδ := by
  apply original_family_return_of_horizon n y l mesh ε δ hmesh hδ hy0 hy1 hn hl
  intro N
  exact retained_frame_prices_of_bank N n y l δ mesh (mesh/4) hδ hρ hm0 hmδ
    (by linarith) (by linarith) hy0 hy1 hn hl

#print axioms actual_original_family_return
end
end QRH.Cycle092.ActualStageFrameBudget
