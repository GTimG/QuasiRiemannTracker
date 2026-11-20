/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original source guards for the native reference-arm fallback. -/
import Candidate.C092.transport.ReferenceArmRadialGeometry
set_option autoImplicit false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.ReferenceArmRadial

theorem original_source_caps {n y : ℝ} (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY)
    (hn0 : y≤ n) (hn1 : n≤ sourceRatio*y) :
    sourceWidth n y-(u:ℝ)≤ widthCap ∧ n≤1 ∧ y≤1 := by
  have hw := actual_source_width_cap hy0 hy1 hn0
  have hu : (0:ℝ)≤(u:ℝ) := by norm_num [u]
  constructor
  · linarith
  · norm_num [sourceY,sourceRatio] at hy1 hn1
    constructor <;> linarith

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.original_source_caps
