import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The common mesh decreases with the mask exponent. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle25.Energy
noncomputable section
open OAI OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

/-- The range of the width schedule grows with the mask exponent. -/
theorem range_mono_mask (M L : ℝ) {B₁ B₂ : ℝ} (h : B₁ ≤ B₂) (n : ℕ) :
    range M B₁ L n ≤ range M B₂ L n := by
  induction n with
  | zero => simp only [range, le_refl]
  | succ n ih =>
    simp only [range, step]
    linarith

/-- The common mesh of a larger mask exponent is at most the common mesh of a smaller one. -/
theorem commonMesh_anti_mask (Mcap L ε : ℝ) (hM : 0 ≤ Mcap) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (h : B₁ ≤ B₂)
    (hε : 0 < ε) : commonMesh Mcap B₂ L ε ≤ commonMesh Mcap B₁ L ε := by
  have hcap : finalSourceCap Mcap B₁ L ε ≤ finalSourceCap Mcap B₂ L ε := by
    unfold finalSourceCap sourceCap
    have := range_mono_mask Mcap L h (count Mcap ε)
    linarith
  have hcap0 : 0 ≤ finalSourceCap Mcap B₁ L ε := sourceCap_nonneg Mcap B₁ L hM hB₁ _
  have hscale : scale Mcap (finalSourceCap Mcap B₁ L ε) ε ≤ scale Mcap (finalSourceCap Mcap B₂ L ε) ε := by
    unfold scale
    linarith
  have hpos : 0 < scale Mcap (finalSourceCap Mcap B₁ L ε) ε := by
    unfold scale
    have : (0 : ℝ) ≤ count Mcap ε := Nat.cast_nonneg _
    linarith
  unfold commonMesh fineMesh mesh reserve
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact min_le_min le_rfl (div_le_div_of_nonneg_left hε.le (by positivity) (by gcongr))

/-- The common mesh is at most the loss. -/
theorem commonMesh_le (Mcap Bmask L ε : ℝ) (hM : 0 ≤ Mcap) (hB : 0 ≤ Bmask) (hε : 0 < ε) :
    commonMesh Mcap Bmask L ε ≤ ε := by
  have hb := bounds Mcap (finalSourceCap Mcap Bmask L ε) (3 / 4) ε hM (sourceCap_nonneg Mcap Bmask L hM hB _)
    (by norm_num) hε
  unfold commonMesh fineMesh
  linarith [hb.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1]

end
end Cycle25.Energy

end Record1252270103Bootstrap.PR67
