import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing
import QRH.RobustReflectionGeometry

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
OAI/NumberTheory/DirichletL/Hecke/DetectorRowCountCrossing.lean. Original objects imported unchanged.
Extended theorem names and explicit κ/reserve changes; untrusted until kernel checked. -/
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma plain_capacity_bound_extended {m κ : ℝ} (hm : 1/3≤m) (hm' : m≤1/2) (hκ : 13/18≤κ) :
    0≤(1-2*m)/(6*κ) ∧ (1-2*m)/(6*κ)≤1/13 := by
  have hkp : 0<6*κ := by linarith
  constructor
  · exact div_nonneg (by linarith) hkp.le
  · apply (div_le_iff₀ hkp).mpr
    nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
