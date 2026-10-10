import OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff
import QRH.Adaptive

/-! Actual supported witnesses at the optimized adaptive cutoff.
The general witness theorem and actual characters/zeros are imported unchanged. -/
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.QRHAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness

def cutoff (δ q : ℝ) : ℝ :=
  if δ≤5/6 then QRH.Certificate.witness δ (min (1/2) (max 0 (q/δ))) else 3/2

section
variable (δ q : ℝ)
include δ q

lemma cutoff_bounds (hδ : 0≤δ) : 1≤cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact QRH.Certificate.witness_range hδ hd (le_min (by norm_num) (le_max_left _ _))
      (min_le_left _ _)
  · norm_num

lemma cutoff_eq_balanced (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) : cutoff δ q=QRH.Certificate.witness δ (q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,ite_eq_left hd,max_eq_right hx,min_eq_right hx']

lemma cutoff_eq_high (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

end



end SevenEighths.QRHAdaptiveCutoff
end
end OAI
