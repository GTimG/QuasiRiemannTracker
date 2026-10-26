import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Low.Detector.LowSlotScales
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.LowDetector.LowNominalGeometry

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Low_Detector_LowNominalGeometry : Cycle63.AffineLedger := Cycle153.Root.rootLedger

/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNominalGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle153EndpointProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤Cycle153Endpoint.Arithmetic.ell) (J : Finset (Fin K)) :
    0≤OAI.SevenEighths.WeightedProbeLow.lowUnselectedLength ell J ∧ OAI.SevenEighths.WeightedProbeLow.lowUnselectedLength ell J≤Cycle153Endpoint.Arithmetic.ell ∧
    0≤OAI.SevenEighths.WeightedProbeLow.lowSelectedLength ell J ∧ OAI.SevenEighths.WeightedProbeLow.lowSelectedLength ell J≤Cycle153Endpoint.Arithmetic.ell-OAI.SevenEighths.WeightedProbeLow.lowUnselectedLength ell J := by
  have hu : 0≤OAI.SevenEighths.WeightedProbeLow.lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤OAI.SevenEighths.WeightedProbeLow.lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := OAI.SevenEighths.WeightedProbeLow.lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(Cycle153Endpoint.Arithmetic.x:ℝ)/L) (Z^(Cycle153Endpoint.Arithmetic.y:ℝ)/L)=
      elementNorm C.generator*Z^((1-Cycle153Endpoint.Arithmetic.ell):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(Cycle153Endpoint.Arithmetic.x:ℝ)*Z^(Cycle153Endpoint.Arithmetic.y:ℝ)=Z^((1-Cycle153Endpoint.Arithmetic.ell):ℝ) := by rw [←Real.rpow_add hZ,Cycle153Endpoint.Arithmetic.x_add_y]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(Cycle153Endpoint.Arithmetic.x:ℝ)/L) (Z^(Cycle153Endpoint.Arithmetic.y:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^((1-Cycle153Endpoint.Arithmetic.ell)-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^((1-Cycle153Endpoint.Arithmetic.ell):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ (1-Cycle153Endpoint.Arithmetic.ell) (2*d)]
      ring

end SevenEighths.Cycle153EndpointProbeLow
end

end OAI
