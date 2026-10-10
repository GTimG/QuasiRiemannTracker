import QRH.Geometry
import OAI.NumberTheory.DirichletL.Detector.CanonicalPhysicalRows
import OAI.NumberTheory.DirichletL.Detector.GaussianCommon

/-! The optimized physical probe uses the original Gauss sums, calibration,
actual characters and compensated tuple operation at the exact manuscript scales.
The row-triple identity below is an equality, not an asserted analytic bound. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.QRHOptimizedProbe
open ProbePhysical HeckeInverseAmplification CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def optimizedProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ → ℂ) (slots : Fin K → Finset O)
    (W : Fin K → ℝ → ℂ) (lengths : Fin K → ℝ) (Z : ℝ) : ℂ :=
  compensatedPhysicalProbe η C W0 W1 slots W (fun i => Z ^ lengths i)
    (Z ^ QRH.lx) (Z ^ QRH.ly) Z



section
variable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal) (hpS : ∀ P ∈ S, Prime P) (hbad : fixedBadPrimes ⊆ S) (hSne : S.Nonempty)
include K η S hS hpS hbad hSne





end

end SevenEighths.QRHOptimizedProbe
end
end OAI
