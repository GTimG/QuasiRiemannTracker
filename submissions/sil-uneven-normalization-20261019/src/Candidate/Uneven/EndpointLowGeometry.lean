/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
import Candidate.Uneven.EndpointProbeGeometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace UnevenEndpointPhysical.Assembly
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic
theorem marked_short_margin :
    y-2*x+ell < 0 := by
  rcases config with ⟨stage⟩
  cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell,x,y]
end
end UnevenEndpointPhysical.Assembly
/-! Exact low-probe geometry. All lengths refer to Cycle63, including the total ray length. -/
namespace UnevenEndpointPhysical.Assembly.LowGeometry
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic

theorem x_pos : 0 < x := by linarith [ell_pos, ell_lt_x]
theorem b_pos : 0 < y-x := by linarith [x_lt_y]
theorem signal_pos : 0 < signal theta := by
  rw [signal_at_boundary]
  linarith [x_pos, b_pos]
theorem scale_square : (2*x-y)+y=2*x := by ring
theorem gram_power (δ : ℝ) :
    x+(y-x)*(1/6)+y*δ = 2*signal theta+y*δ := by
  rw [signal_at_boundary]
  ring
theorem dilation_gap : 0 < 2*x-y-ell := by
  linarith only [marked_short_margin]
theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
end
end UnevenEndpointPhysical.Assembly.LowGeometry

