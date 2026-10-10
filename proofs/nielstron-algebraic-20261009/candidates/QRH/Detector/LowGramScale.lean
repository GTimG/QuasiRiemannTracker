import OAI.NumberTheory.DirichletL.Detector.LowGramScale
import QRH.Detector.LowReflectedLength

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual physical objects unchanged. Optimized scales and explicit reflected penalty. -/
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

section
variable (Z δ : ℝ) (hZ : 0<Z)
include Z δ hZ

lemma source_gram_power_optimized :
    Z^(QRH.lx:ℝ)*(Z^(QRH.b:ℝ))^(1/6:ℝ)*(Z^(QRH.ly:ℝ))^δ=
      Z^((2*QRH.C QRH.theta)+(QRH.ly)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  dsimp [QRH.C, QRH.h, QRH.lx, QRH.ly, QRH.M, QRH.ell]
  ring


lemma source_gram_sqrt_power_optimized :
    Real.sqrt (Z^((2*QRH.C QRH.theta)+(QRH.ly)*δ:ℝ))=Z^(QRH.C QRH.theta+((QRH.ly/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  dsimp [QRH.C, QRH.h, QRH.lx, QRH.ly, QRH.M, QRH.ell]
  ring

end

end SevenEighths.ProbePhysical
end

end OAI
