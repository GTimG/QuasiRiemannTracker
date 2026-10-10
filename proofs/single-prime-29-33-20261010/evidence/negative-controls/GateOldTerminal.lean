import ZetaZeroFree.Analytic.Audit
import ZetaZeroFree.Nonvanishing
namespace GateOldTerminal
theorem reused {s : ℂ} (hs : (29/33:ℝ)<s.re) (hp : s≠1) : riemannZeta s≠0 := ZetaZeroFree.riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re hs hp
end GateOldTerminal
