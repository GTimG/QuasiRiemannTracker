/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Assembly
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.AdmImage

/-!
# Inverse.Select.Stage — the inverse reduction at a stage (separated-oracle form)

Combines `Select/Assembly.selectionReductionExcess'_canonical` with the oracle chain
(`AdmImage.inverse_reduction_excess_canonical_stage'`). The driver uses the injective form
`Inj.inverse_reduction_excess_canonical_stage` instead.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Filter
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
open CanonicalCoefficientClass FirstPassCubeLabels SecondPassArithmetic
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => OAI.ActualEisensteinCubic.O

/-- **The inverse reduction at a stage**, conditional on the restoration and on the injective
oracle chain `OracleChainInj'` (with the separated oracle `OracleOn'`). -/
theorem inverse_reduction_canonical_conditional
    (hinj : OracleChainInj' canonicalFamily imageAdm')
    (hRB : RestoreChildBoundUniform canonicalFamily canonicalFamily)
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess canonicalFamily (childRect r s ((1-H)/6) κ)
      (((1-H)/6)/(1-6*((1-H)/6)-κ))) :
    UniformInverseRectSource canonicalFamily ⟨r, s⟩ :=
  inverse_reduction_excess_canonical_stage' hinj (selectionReductionExcess'_canonical hRB)
    H r s κ hH hH1 hr hs hκ hκ1 hdiag hchild

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_canonical_conditional
