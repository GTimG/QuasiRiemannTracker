import OAI.NumberTheory.DirichletL.ParametersHighDataFine
import WeightedQRH.MomentDetectorPlainMomentParameters
import OAI.NumberTheory.DirichletL.ParametersHighData
namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

theorem weighted_fine_slot_widths (D:WeightedQRH.MomentData)(mesh:ℝ→ℝ)
    (hmesh:0<mesh D.t)(hfine:∀j,D.ell j ≤ mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ) ≤ d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d ≤ mesh D.t:=by
  have hd0:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith

end SevenEighths.Parameters

end

end OAI
