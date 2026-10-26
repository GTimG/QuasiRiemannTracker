import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.ReflectionRetainedLength
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.WidthRanges
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle25.Energy

open OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

lemma compact_mesh_le (M B L κ ε : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hε : 0 < ε) (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) :
    fineMesh M B L (3 / 4) ε ≤ fineMesh M B L κ ε := by
  have hcap := sourceCap_nonneg M B L hM hB (count M ε)
  have hr := (bounds M (finalSourceCap M B L ε) 0 ε hM hcap
    (by norm_num) hε).2.2.2.1
  unfold fineMesh mesh
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

end Cycle25.Energy

end Record1252270103Bootstrap.PR67
