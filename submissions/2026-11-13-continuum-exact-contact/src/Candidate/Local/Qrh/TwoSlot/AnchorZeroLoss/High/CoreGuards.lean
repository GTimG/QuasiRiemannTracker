/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafContract
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRootMaxima

/-!
# High.CoreGuards

The buffered zero guards of a raw HIGH row transfer to its core.

For a kept row `z = (sixthFrequencyEquiv (u, B)).val` of a natural state `st` (any puncture), the
zero maximum of its whole-source geometry family (`geometryRowMaximum`, which `RetainedZeroBin` /
`selectBin` use) equals the zero maximum of the clean core family `coreFamily … st.character η₀ u`
at every height (HC `source_root_maximum_eq_clean`, with `χ = excluded (naturalRow η z) st.puncture`
and `R = st.puncture`).
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification CenteredMomentEnergyState ProbePhysical
local notation "O" => HeckeFamily.O

variable (rayM : Ideal O) [NeZero rayM]
local instance coreGuardsQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **Raw row zero maximum = core zero maximum.** -/
theorem geometryRowMaximum_eq_core {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (u : FreeRow) (B : HeckeInverseAmplification.NonzeroIdeal) (hz : st.radial.keep (sixthFrequencyEquiv (u, B)).val)
    (hnclean : ∀ j, (coreFamily rayM H hH st.character η₀ u j).residue ≠ 1) (T : ℝ) :
    Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη
        (sixthFrequencyEquiv (u, B)).val hz T =
      HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH st.character η₀ u) hnclean T := by
  unfold Cycle61InitialMass.geometryRowMaximum
  exact OAI.SevenEighths.Record12518109GainWholeGeometry.source_root_maximum_eq_clean rayM H hH
    st.character η₀ _ u B st.puncture st.puncture_ne_zero (fun _ => rfl) _ hnclean T

end
end Qrh.TwoSlot.AnchorZeroLoss.High
