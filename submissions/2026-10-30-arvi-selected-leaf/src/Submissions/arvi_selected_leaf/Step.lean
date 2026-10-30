/-
The selected-leaf native step.

Sil's generic cube-free step (`CubeFree.cubefree_step`) with the step data `e5Data`, its gates
`stepGates_of_e5`, and the generic root-chain provider (`contrary_raw_side_provider` with the
diagonal supply), exactly as for the native step. The only remaining input is the Seam A leaf at the
selected-leaf price, stated here as a hypothesis.
-/
import Submissions.arvi_selected_leaf.Gates
import Submissions.sil_density_split_20261026.CubeFree.Step
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths QRH.Record1252270103Source

variable {p n : Face} {a K : ℝ}

/-- The root-chain input of a selected-leaf step, from the generic provider. -/
theorem e5_inputs (h : E5Gates p n a K) : StepInputs (e5Data p n a K h) (stepGates_of_e5 h) 4 :=
  Assembly.step_inputs_of_provider _ _ 4 (fun _ hleaf =>
    Second.Provider.contrary_raw_side_provider (stepGates_of_e5 h) 4 le_rfl hleaf
      (Second.ProviderDiag.diag_supply _))

/-- The Seam A leaf of a selected-leaf step: the packed source at the selected-leaf price, from the
parent face. -/
def E5Leaf (p n : Face) (a K : ℝ) (h : E5Gates p n a K) : Prop :=
  GlobalSource p.B p.L p.c →
    PricedPackedSource (e5Data p n a K h).price (e5Data p n a K h).Hmin
      ((e5Data p n a K h).Hmax + 1) 4

/-- **The selected-leaf native step.** -/
theorem e5_step (h : E5Gates p n a K) (hleaf : E5Leaf p n a K h)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hp : GlobalSource p.B p.L p.c) :
    GlobalSource n.B n.L n.c :=
  cubefree_step (e5Data p n a K h) (stepGates_of_e5 h) 4 (e5_inputs h) hβ hp (hleaf hp)

end
end QRH.ArviSelectedLeaf
