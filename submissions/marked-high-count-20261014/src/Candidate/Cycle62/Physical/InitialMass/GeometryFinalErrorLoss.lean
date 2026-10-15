/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryFinalLossParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section

/-- The extracted projector uses actual slot cardinality, while its scalar
loss is paid by a common ambient rate. This does not alter Fourier data. -/
theorem geometry_final_error_raw_loss
    (μ omega mesh : ℝ) (n N : ℕ) (hμ : 0<μ) (hn : n≤N)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*n+
      (omega+μ/8)/6+(3/4)*mesh+δ≤μ := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hd : δ≤μ/128:=hb.2.2.1
  have he:=(geometry_final_error_dictionary_budget μ N hμ).2 n hn
  linarith only [hd,he,hω,hmesh,hμ]

/-- The physical error theorem has room for the actual projector error,
source-volume loss, four common losses, and its remaining error fee. -/
theorem geometry_final_error_physical_loss (μ error : ℝ)
    (hμ : 0<μ) (he : error≤μ) :
    error+μ/8+4*(μ/8)+μ/8≤64*μ := by
  linarith only [hμ,he]

/-- Projector, allocation, shell, and finite ratio losses are paid together.
The error joint weight already contains its single prime average. -/
theorem geometry_final_error_paid_ledger (μ : ℝ) (N : ℕ) (hμ : 0<μ) :
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    (δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))+δ≤
      -(7/60000000:ℝ)+μ := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hd : 0<δ:=hb.1
  have hp:=hb.2.2.2.2.2.1
  change 130*δ+3*(3*((N:ℝ)+2))*δ+δ+8*δ≤μ at hp
  linarith only [hd,hp]

/-- A strict saving remains after the complete scalar error ledger. -/
theorem geometry_final_error_exponent_saving (εaffine : ℝ) :
    -(7/60000000:ℝ)+geometryLossUnit 1 εaffine≤-(7/120000000:ℝ) := by
  have h:=(geometry_loss_unit_reserve 1 εaffine 1 le_rfl).2
  linarith only [h]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_error_raw_loss
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_error_physical_loss
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_error_paid_ledger
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_final_error_exponent_saving
