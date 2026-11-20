/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Restriction of Joseph Bebel's AnchorContinuum.PositiveSource theorem (Apache-2.0).
   Use the coupled face before the earlier proof restricts it to 3/40. -/
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSource
import Candidate.C092.Intake.QRH.Constants

set_option autoImplicit false
namespace QRH.Cycle092.PhysicalInlet
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence OAI.SevenEighths
open QRH.Cycle090

def qFace (s : ℝ) : SourceFace := ⟨1-s,2+10*s,0,1/2,0,physicalCap⟩

theorem physical_source {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : UniformUnitFaceSource (qFace s) := by
  have hr : (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face s).Restricts (qFace s) := by
    constructor <;> dsimp [Qrh.TwoSlot.AnchorContinuum.PositiveSource.face,qFace,physicalCap] <;> linarith
  intro ε hε
  obtain ⟨mesh,hm,hsrc⟩ := Qrh.TwoSlot.AnchorContinuum.PositiveSource.source hs hsmax hβ ε hε
  exact ⟨mesh,hm,QRH.Record1252270103Return.unit_source_restrict hr hsrc⟩

theorem q_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource (qFace sourceCost) := by
  apply physical_source allowances_pos.1 _ hβ
  linarith [sourceCost_le_rowPad, rowPad_small]

theorem small_plain_shortening {s n₁ n₂ n z : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (h₁ : n₁ ≤ 0) (h₂ : n₂ ≤ n)
    (hcone : 2*n+(2+10*s)*z ≤ 1-s) (hz : z ≤ physicalCap) :
    n₁+n₂+(9/2)*z ≤ 1 := by
  unfold physicalCap at hz
  have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ (9/2:ℝ)-(2+10*s)/2 by linarith)
  nlinarith

end
end QRH.Cycle092.PhysicalInlet
#print axioms QRH.Cycle092.PhysicalInlet.physical_source
#print axioms QRH.Cycle092.PhysicalInlet.q_source
#print axioms QRH.Cycle092.PhysicalInlet.small_plain_shortening
