import QRH.NumericFacts
import QRH.Detector.OptimizedCentralExponent
namespace OAI
noncomputable section
namespace SevenEighths.QRHProbeCentralExponent
lemma floor_source_margin (q ζ v : ℝ) (hq:q≤1/100) (hζ:0≤ζ) (hv:v≤QRH.h+ζ) :
    sourceExponent (51/100) v 1 q-QRH.C QRH.tightTheta≤-(1/200:ℝ)+2*ζ := by
  have he:=QRH.floor_saving
  have hell:=QRH.NumericFacts.ell_bounds.1.le
  have hq':=mul_le_mul_of_nonneg_right hq hell
  rw [manuscript_exponent_identity]
  norm_num only at *
  unfold QRH.exponent at he ⊢
  nlinarith
end SevenEighths.QRHProbeCentralExponent
end
end OAI
