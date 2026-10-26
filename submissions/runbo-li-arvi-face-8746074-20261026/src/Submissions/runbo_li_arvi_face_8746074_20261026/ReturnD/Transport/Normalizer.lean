/- Repeated marks: fork of Collet's generic return module Transport.Normalizer (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.TransportGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Transport.LowNormalizer
set_option autoImplicit false
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
open scoped Classical BigOperators ContDiff
namespace OAI.SevenEighths.RepeatedMarksReturn.TransportHighTransport
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def actualNormalizer {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) [NeZero (∏P∈S,P)]
    (slotEll : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z RepeatedMarksReturn.Transport.Arithmetic.ell
      (slotMass T (residueWeights W Yp)) : ℂ)

end OAI.SevenEighths.RepeatedMarksReturn.TransportHighTransport
