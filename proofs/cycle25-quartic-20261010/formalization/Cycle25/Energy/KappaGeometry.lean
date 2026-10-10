import Cycle25.Energy.ReflectionRetainedLength
import OAI.NumberTheory.DirichletL.Energy.WidthRanges

namespace Cycle25.Energy

open OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

lemma comparison_denominator_pos (κ : ℝ) (hκ : 7 / 10 ≤ κ) :
    0 < 2 * (6 * κ - 1) := by linarith

lemma comparison_margin (κ : ℝ) (hκ : 7 / 10 ≤ κ) :
    1 / 16 ≤ (2 * κ - 1) / (2 * (6 * κ - 1)) := by
  apply (le_div_iff₀ (comparison_denominator_pos κ hκ)).mpr
  linarith

lemma compact_mesh_le (M B L κ ε : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hε : 0 < ε) (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) :
    fineMesh M B L (3 / 4) ε ≤ fineMesh M B L κ ε := by
  have hcap := sourceCap_nonneg M B L hM hB (count M ε)
  have hr := (bounds M (finalSourceCap M B L ε) 0 ε hM hcap
    (by norm_num) hε).2.2.2.1
  unfold fineMesh mesh
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

end Cycle25.Energy
