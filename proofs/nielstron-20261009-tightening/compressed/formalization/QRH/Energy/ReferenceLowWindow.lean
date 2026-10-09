import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import QRH.PlainReflectionGeometry
import QRH.Energy.ReferenceLowBranchGeometry

/-!
Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Energy/ReferenceLowWindow.lean. Original objects and hypotheses retained; new theorem names
extend κ to 13/18 and adjust reflection reserves. Must be kernel checked before
integration. The original source is imported unchanged.
-/
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O



end SevenEighths.CenteredMomentEnergyReferenceLowWindow

end

end OAI
