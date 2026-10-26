import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGramScale.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
namespace SevenEighths.Cycle63ProbeLow
open ProbePhysical

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(Cycle63.Arithmetic.x:ℝ)*(Z^((Cycle63.Arithmetic.y-Cycle63.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle63.Arithmetic.y:ℝ))^δ=
      Z^((2*Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+(Cycle63.Arithmetic.y)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  exact Cycle63.Assembly.LowGeometry.gram_power δ

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^((2*Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+(Cycle63.Arithmetic.y)*δ:ℝ))=Z^((Cycle63.Assembly.signal Cycle63.Arithmetic.theta)+((Cycle63.Arithmetic.y/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.Cycle63ProbeLow
end

end OAI

end Record1252270103Bootstrap.PR67
