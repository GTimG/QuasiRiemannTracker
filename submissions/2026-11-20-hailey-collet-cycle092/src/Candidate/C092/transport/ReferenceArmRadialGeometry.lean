/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original source-width, Poisson capacity and all-radius reference-arm
prices. The source certificate u,H,rho are imported, never replaced. -/
import Candidate.C092.transport.StrongPairRegularTerminalReserve
import Candidate.C092.transport.ReferenceShortP3Geometry
set_option autoImplicit false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.StrongPair

def widthCap : ℝ := 13319/100000
def shortCap : ℝ := 23/200+1/1000000
def longCap : ℝ := 18023/25000+1/1000000
def markedRadius : ℝ := 993/1000
def cutoffBuffer : ℝ := 1/10000

/-- The actual P.1 envelope throughout its original ordered source domain.
This cap is derived from its exact lower endpoint, not guessed numerically. -/
theorem actual_source_width_cap {n y : ℝ}
    (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY) (hn : y≤ n) :
    sourceWidth n y < widthCap := by
  have hg := sourceGain_antitone hy0 hy1
  have hc : sourceGain sourceY0=4370430517/2000000000000 := by
    norm_num [sourceGain,sourceY0,sourceY,sourceSeam,lowerGain,QRH.Cycle090.upperGain]
  rw [hc] at hg
  norm_num [sourceY0] at hy0
  dsimp [sourceWidth,widthCap]
  linarith

theorem genuine_short_capacity :
    4*(shortCap+widthCap)+cutoffBuffer/2 < markedRadius ∧
    0 < markedRadius ∧ markedRadius < 1 ∧ 0 < cutoffBuffer ∧ longCap < 1 := by
  norm_num [shortCap,widthCap,cutoffBuffer,markedRadius,longCap]

def radialPrice (V : ℝ) : ℝ :=
  if V≤4/5 then V+widthCap else (max V markedRadius+V)/2

/-- Tiny cores pay the genuine absolute whole-mark volume cost. Larger
cores put all marks on the short fourth and pay half of each radial fourth.
Both prices fit the original terminal source reserve at EVERY radius. -/
theorem all_radius_price {V fee : ℝ} (hV : 0≤ V)
    (hfee : fee≤(u:ℝ)/2) : radialPrice V+fee < terminalFramePrice V := by
  unfold radialPrice terminalFramePrice terminalReserve
  norm_num [u,rho,H,markedRadius,widthCap] at hfee ⊢
  simp only [max_def]
  split_ifs <;> linarith

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.actual_source_width_cap
#print axioms QRH.Cycle092.ReferenceArmRadial.genuine_short_capacity
#print axioms QRH.Cycle092.ReferenceArmRadial.all_radius_price
