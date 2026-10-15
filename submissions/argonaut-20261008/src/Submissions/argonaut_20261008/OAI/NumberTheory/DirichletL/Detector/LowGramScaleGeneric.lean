import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma source_gram_power_generic (Z lx ly δ : ℝ) (hZ : 0<Z) :
    Z^lx*(Z^(ly-lx))^(1/6:ℝ)*(Z^ly)^δ=
      Z^(lx+(ly-lx)/6+ly*δ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,
    ←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_gram_sqrt_power_generic (Z lx ly δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(lx+(ly-lx)/6+ly*δ))=
      Z^(lx/2+(ly-lx)/12+ly*δ/2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
