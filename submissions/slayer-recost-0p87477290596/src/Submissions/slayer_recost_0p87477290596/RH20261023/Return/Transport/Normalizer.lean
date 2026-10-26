/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.TransportGeometry
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.Transport.LowNormalizer
set_option autoImplicit false
noncomputable section
variable [QRH.RH20261023Return.Geometry.Parameters] [QRH.RH20261023Return.Geometry.Bounds]
open scoped Classical BigOperators ContDiff
namespace OAI.SevenEighths.RH20261023Return.TransportHighTransport
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def actualNormalizer {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) [NeZero (∏P∈S,P)]
    (slotEll : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z RH20261023Return.Transport.Arithmetic.ell
      (slotMass T (residueWeights W Yp)) : ℂ)

end OAI.SevenEighths.RH20261023Return.TransportHighTransport
