import ZetaZeroFree.Analytic.Final
import ZetaZeroFree.Analytic.Audit
set_option maxHeartbeats 0

namespace D3NegativeControl
theorem circular : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (29 / 33 : ℝ) :=
  ZetaZeroFree.Analytic.beta_le_twenty_nine_thirty_thirds
end D3NegativeControl

run_cmd ZetaZeroFree.AnalyticVerification.auditD3Independence #[``D3NegativeControl.circular]
