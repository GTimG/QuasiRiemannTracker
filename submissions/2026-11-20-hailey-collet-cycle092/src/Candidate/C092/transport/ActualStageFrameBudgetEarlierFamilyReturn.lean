/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact physical restored-family return, with all finite bank parameters
chosen before the two positive Poisson fee arrays. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamily
import Candidate.C092.transport.ActualStageFrameBudgetReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.FP RepairedSourceSideSupply
open QRH.Cycle092.NativeStrip QRH.Cycle090
open QRH.Cycle092.FixedRayPair
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- The only supplier is the genuine uniform physical retained-bank
horizon. All original array specialization and geometric caps are internal. -/
theorem original_family_return_of_horizon
    (n y l mesh ε δ:ℝ)(hmesh:mesh ≤ 1/6)(hδ:0<δ)
    (hy0:sourceY0 ≤ y)(hy1:y ≤ sourceY)(hn:n ≤ sourceRatio*y)
    (hl:l ≤ sourceWidth n y)
    (horizon:∀N:ℕ,RetainedBankHorizon N n y l δ mesh (mesh/4) hδ) :
    OriginalFamilyReturn n y l mesh ε δ hmesh hδ := by
  intro Slot instF instD M instM Hr hHr W hW hWs bPhi hbPhi hPhi η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
  dsimp only
  intro hQM hQ0 hQt hQ72 hQbase bank hFee hAt Cz Ct hpositive
  let base:=η₀₁.product η₁.inverse
  let q:=stageQ Q₁ η₀₁ base η₁ η₂
  have hfamily:=earlier_centered_frames_of_bank (Slot:=Slot)
    n y l δ mesh (mesh/4) bPhi ε (ε/8) hδ hy0 hy1 hn hl hmesh M Hr hHr W hW hWs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ q hQM hQ0 hQt hQ72 hQbase
    (RestoredRootSource.slotBound W hW.continuous hWs) le_rfl bank hFee
    (horizon (Fintype.card Slot)) Cz Ct
  filter_upwards [hfamily,hAt] with Z hf ha
  exact fun hZ=>hf hZ ha

#print axioms original_family_return_of_horizon
end
end QRH.Cycle092.ActualStageFrameBudget
