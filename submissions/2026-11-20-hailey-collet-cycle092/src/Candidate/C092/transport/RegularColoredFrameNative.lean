/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The independently colored regular source on the actual native
GData/GSrc/GLabel/Fits interface, with its true V=r.V0*twist packed child.
The genuine colored physical-label hred is supplied by the proved chain.
-/
import Candidate.C092.transport.RegularColoredFrameHred
import Candidate.C092.transport.RegularColoredFrameClass
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedSteps
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceUniformApproximation
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.Cycle092.RegularColoredForward
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.NativeFiniteHoles Candidate.FourthPower.KernelNaturalSlots
open QRH.SilDensitySplit.CubeFree.FP QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.SilDensitySplit.CubeFree.Packet
open QRH.SilDensitySplit.CubeFree.Packet.Grouped

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows
open NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedCommonSource MixedOriginalSource MixedRestrictedDictionary MixedHeightEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyChildState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergySlotHeight
open CenteredMomentEnergyAllocatedChildren CenteredMomentLattice CenteredMomentTwist
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
open ProfileSeparation (commonPair scale pairWeight pairMajorant)
local notation "O" => HeckeFamily.O

local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameNative_14039407a9136e9a_001 (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The literal native fitting-label source with independent ordinary
characters inside each original tuple coefficient. -/
def frameRawEnergy (ω₁ ω₂ η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (h : Fits η r x) (v : ℝ) : ℝ :=
  frameLabelEnergy θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq r.t r.R₀
    (x.char r) ω₁ ω₂ (internalQ θ.Q θ.η₀) x.n θ.Cap θ.Lcap x.R x.G h.G_ne x.seed x.D
    x.holesH r.W₁ r.W₂ r.t₁ r.t₂ θ.b r.X₁ r.X₂ r.Y₁ r.Y₂ x.d ⟨h.d₁,h.d₂⟩ v

/-- The true original-sublattice pair child of a fitting native label.
The ordinary characters are independent; the original mark anchor is frozen. -/
def frameChildE (ω₁ ω₂ η : Character) (r : GSrc θ mesh Z) (v : ℝ) (j : DictIdx)
    (A : Finset (Fin θ.N)) (X₁ X₂ : ℝ) (V : O) (K : ℝ) : ℝ :=
  GroupedPair.pairEnergy ((anchors η j).product ω₁) ((anchors η j).product ω₂) pmask 1 1
    (fun y=>∏i∈A,CenteredMomentWholeSlotDeletion.normalizedSlot (anchors η j) pmask 1 y
      (primePool θ.rayM θ.Hray 2 (Z^(r.w i)))
      (slotBeta θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq i) (r.t+v) (Z^(r.w i)))
    (2*Real.pi*(r.t₁+v/(2*Real.pi))) (2*Real.pi*(r.t₂+v/(2*Real.pi))) r.W₁ r.W₂ X₁ X₂
    (packedKeep (anchors η j) (internalQ θ.Q θ.η₀) V) ballProfile
    (((Ideal.span {V}).absNorm:ℝ)*K)

theorem frame_label_reduction_native (θ : GData L) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cred : ℝ, 0 < Cred ∧ ∀ (mesh Z : ℝ), mesh ≤ 1 → ∀ (η ω₁ ω₂ : Character)
      (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η r x) (v : ℝ),
      frameRawEnergy ω₁ ω₂ η r x h v ≤ 0 ∨
      ∃ (A : Finset (Fin θ.N)) (X₁' X₂' : ℝ), 0 < X₁' ∧ 0 < X₂' ∧
        ((X₁' ≤ r.X₁ ∧ X₂' ≤ r.X₂) ∨ (X₁' ≤ r.Y₁ ∧ X₂' ≤ r.Y₂)) ∧
        frameRawEnergy ω₁ ω₂ η r x h v ≤ labelMass Cred Z ε δ r.w r.X₁ r.X₂ x.G x.D x.d *
          frameChildE ω₁ ω₂ η r v (x.anchor r) A X₁' X₂' (r.V₀ * x.twist) (dyadicScale (x.n 1)) := by
  obtain ⟨C, hC, hred⟩ := frame_label_reduction_single θ.rayM θ.Hray θ.hH (α := Fin θ.N) θ.Holes θ.W
    θ.a θ.b L 1 θ.Lcap θ.Cap θ.Bmask ε δ (33/50) (33/50) θ.hWs θ.hW θ.ha0 θ.hb1
    zero_le_one θ.hLcap θ.hCap θ.hBmask θ.hCapb θ.hLL hε hδ
  refine ⟨C, hC, ?_⟩
  intro mesh Z hmesh η ω₁ ω₂ r x hx v
  rcases hred Z r.hZ.le θ.η₀ r.χ r.w r.σ r.freq r.t r.R₀ r.hw (fun i => (r.hwm i).trans hmesh)
      (fun i => (r.hσ i).ge) (fun i => (r.hσ i).le) r.hR₀ (x.char r) (anchors η (x.anchor r)) ω₁ ω₂
      (internalQ θ.Q θ.η₀) x.n (r.V₀ * x.twist) (x.mask r) (mul_ne_zero r.hV₀ hx.twist_ne)
      hx.mask_ne hx.coef x.R x.G x.seed x.D hx.R_ne hx.G_ne hx.seed_dvd hx.D_sq hx.G_mask
      x.holesH hx.holes_sub hx.cap hx.holes_R₀ r.W₁ r.W₂ r.hs₁ r.hs₂ r.t₁ r.t₂ r.X₁ r.X₂
      r.Y₁ r.Y₂ r.hX₁ r.hX₂ r.hY₁ r.hY₂ r.hX₁L r.hX₂L r.hY₁L r.hY₂L r.hXY x.d
      ⟨hx.d₁, hx.d₂⟩ v with h0 | ⟨A, X₁', X₂', h1, h2, h3, h4⟩
  · exact Or.inl h0
  · refine Or.inr ⟨A, X₁', X₂', h1, h2, h3, ?_⟩
    exact h4


end
end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_label_reduction_native
