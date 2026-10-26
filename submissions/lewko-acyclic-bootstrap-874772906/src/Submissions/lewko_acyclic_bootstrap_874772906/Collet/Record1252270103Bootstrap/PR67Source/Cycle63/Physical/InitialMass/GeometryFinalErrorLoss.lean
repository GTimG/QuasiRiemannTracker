import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalLossParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The extracted projector uses actual slot cardinality, while its scalar
loss is paid by a common ambient rate. This does not alter Fourier data. -/
theorem geometry_final_error_raw_loss
    (μ omega mesh : ℝ) (n N : ℕ) (hμ : 0<μ) (hn : n≤N)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*n+
      (omega+μ/8)/6+Cycle63.Optimization.slotPrice*mesh+δ≤μ := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hd : δ≤μ/128:=hb.2.2.1
  have he:=(geometry_final_error_dictionary_budget μ N hμ).2 n hn
  have hk := Cycle63.Optimization.slotPrice_mem
  have hm1 := mul_le_mul_of_nonneg_left hmesh Cycle63.Optimization.slotPrice_pos.le
  have hm2 := mul_le_mul_of_nonneg_right hk.2 (show (0:ℝ) ≤ μ/8 by positivity)
  linarith only [hd,he,hω,hmesh,hμ,hm1,hm2]

/-- The physical error theorem has room for the actual projector error,
source-volume loss, four common losses, and its remaining error fee. -/
theorem geometry_final_error_physical_loss (μ error : ℝ)
    (hμ : 0<μ) (he : error≤μ) :
    error+μ/8+4*(μ/8)+μ/8≤64*μ := by
  linarith only [hμ,he]

variable [Cycle63.AffineLedger] in
/-- A strict saving remains after the complete scalar error ledger. -/
theorem geometry_final_error_exponent_saving (εaffine : ℝ) :
    -((Cycle63.AffineLedger.lowReserve/2):ℝ)+geometryLossUnit 1 εaffine≤-((Cycle63.AffineLedger.lowReserve/4):ℝ) := by
  have h:=(geometry_loss_unit_reserve 1 εaffine 1 le_rfl).2
  linarith only [h, Cycle63.AffineLedger.lowReserve_pos]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
