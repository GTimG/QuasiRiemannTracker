import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGramScale

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Low_Detector_LowGramScale : Cycle63.AffineLedger := Cycle153.Root.rootLedger


set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGramScale.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
namespace SevenEighths.Cycle153EndpointProbeLow
open ProbePhysical

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(Cycle153Endpoint.Arithmetic.x:ℝ)*(Z^((Cycle153Endpoint.Arithmetic.y-Cycle153Endpoint.Arithmetic.x):ℝ))^(1/6:ℝ)*(Z^(Cycle153Endpoint.Arithmetic.y:ℝ))^δ=
      Z^((2*Cycle153Endpoint.Assembly.signal Cycle153Endpoint.Arithmetic.theta)+(Cycle153Endpoint.Arithmetic.y)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  exact Cycle153Endpoint.Assembly.LowGeometry.gram_power δ

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^((2*Cycle153Endpoint.Assembly.signal Cycle153Endpoint.Arithmetic.theta)+(Cycle153Endpoint.Arithmetic.y)*δ:ℝ))=Z^((Cycle153Endpoint.Assembly.signal Cycle153Endpoint.Arithmetic.theta)+((Cycle153Endpoint.Arithmetic.y/2))*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.Cycle153EndpointProbeLow
end

end OAI
