import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.Transport.LowNormalizer
set_option autoImplicit false
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped Classical BigOperators ContDiff
namespace OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def actualNormalizer {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) [NeZero (∏P∈S,P)]
    (slotEll : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell
      (slotMass T (residueWeights W Yp)) : ℂ)
end OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
