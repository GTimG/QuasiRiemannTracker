/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
One arithmetic event before all moving root/common/supplier data.
Every field is numeric/support data; no energy field.
Modified by Sil (2026-10-26): Event is indexed by the step gates G; of the OuterFresh admission field uniform (replaced lane) only 1 < Z and the sector frequency loss at cutoffLoss G N eps are kept (fields one_lt, freq; eventually_event proves both); the numerical fixed-factor and pool caps are unchanged.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedRootCaps
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceCubicCharacter
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedInnerExceptionalLedger

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedCapEvent
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedOriginalTailCaps
open Qrh.MarkedAnchor.Ordinary.RootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def sigmaFixed : ℝ := (ReferenceCubicCharacter.conductorConstant:ℝ) * (Ideal.span {(12:O)}).absNorm
def outerFixed : ℝ := 4 * (Ideal.span {(12:O)}).absNorm *
  (Ideal.span {fixedBadMask}).absNorm^2 * (Ideal.span {(72:O)}).absNorm^2
def innerFixed : ℝ := 4 * (CenteredMomentSecondRadicalBudget.fixedFactor:ℝ) *
  (Ideal.span {fixedBadMask}).absNorm * (Ideal.span {(72:O)}).absNorm

def PoolBound (N : ℕ) (Z : ℝ) : Prop :=
  ∀ (κ : Type u) [Fintype κ], ∀ r : Source κ (1/4) (9/4), Fintype.card κ ≤ N →
    r.X₁ ≤ Z^(3:ℝ) → r.X₂ ≤ Z^(3:ℝ) → r.Y₁ ≤ Z^(3:ℝ) → r.Y₂ ≤ Z^(3:ℝ) →
    (∏ i,r.P i) ≤ Z → poolCap r ≤ Z^(8:ℝ)

/-- The arithmetic event at step gates `G`. Of FP's `uniform` field (the OuterFresh
admission event, replaced lane) only the two parts used by the root caps are kept:
`one_lt : 1 < Z` and the sector frequency loss `freq` at the cutoff loss. -/
structure Event {D : StepData} (G : StepGates D) (N : ℕ) (ε Z : ℝ) : Prop where
  dimension : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z
  presentation : fixedPresentationCost ≤ Z
  sigma : sigmaFixed ≤ Z
  outer : outerFixed ≤ Z
  inner : innerFixed ≤ Z
  one_lt : 1 < Z
  freq : CenteredMomentSectorLocalization.frequencyLoss Z 1 (cutoffLoss G N ε) ≤ cutoffLoss G N ε
  pool : PoolBound.{u} N Z

theorem eventually_event {D : StepData} (G : StepGates D) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, Event.{u} G N ε Z := by
  have hθ := (internal_losses_paid G N ε hε).1
  have hfour : ∀ᶠ Z : ℝ in atTop, (4:ℝ) ≤ Z^(cutoffLoss G N ε/2) :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0 < cutoffLoss G N ε/2))) _
  filter_upwards [eventually_source_caps N (9/4) 3 1 1 (by norm_num),
    eventually_ge_atTop ((9/4:ℝ)^2 * (2:ℝ)^N),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop sigmaFixed,
    eventually_ge_atTop outerFixed, eventually_ge_atTop innerFixed,
    eventually_gt_atTop (1:ℝ), hfour]
    with Z hp hd hf hs ho hi hu h4
  refine ⟨hd,hf,hs,ho,hi,hu,?_,?_⟩
  · have hl := Real.logb_le_logb_of_le hu (by norm_num : (0:ℝ) < 4) h4
    rw [Real.logb_rpow (zero_lt_one.trans hu) hu.ne'] at hl
    simp only [CenteredMomentSectorLocalization.frequencyLoss, mul_one]
    linarith
  intro κ instκ r hcard hx₁ hx₂ hy₁ hy₂ hprod
  have hh := (hp.2 κ (1/4) r hcard hx₁ hx₂ hy₁ hy₂ (by simpa only [Real.rpow_one] using hprod)).1
  simpa only [show (2*(3:ℝ)+1+1)=8 by norm_num] using hh

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedCapEvent
