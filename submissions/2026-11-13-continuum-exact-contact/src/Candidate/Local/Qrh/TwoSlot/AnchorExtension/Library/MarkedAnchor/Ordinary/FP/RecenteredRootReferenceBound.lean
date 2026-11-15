/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The actual kept root reference (both original short-side orientations and the installed
reference rectangle at `Z^l_ref`) is bounded by the reference lane `ReferenceEnergyFine D`,
taken as the hypothesis `hlane`.

Modified by Sil (2026-10-26): threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceBound`. The native proof (homogeneous
two-orientation reference energy `uniform_profiled_reference_energy_either`, which needs
`P + 2S + 4ω < 1 + ω` and fails at the anchor corner) is replaced by the explicit reference lane
`ReferenceEnergyFine D` (`Reference/Statement.lean`), a hypothesis `hlane` of
`uniform_original_reference`; `bΦ η η₀ Q0` (with the gates of `Q0`) precede the constants, the
root has `s.η₀ = η₀`, slot widths `≤ laneMesh`, slot frequencies `≤ V`, and the weights are at
`Q` with `internalQ Q η₀ = Q0`; the bound carries `height 0 V`. The root reference is `Z^l_ref`;
the slot type lives in `Type` (the lane's universe).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceCaps
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Statement
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstReferenceOrientation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceBound
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower Qrh.MarkedAnchor.Ordinary.Reference
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCanonicalSource
open MixedFirstReferenceDispatch MixedFirstReferenceEnergy MixedFirstReferenceOrientation
open RestoredRootDictionary RestoredRootEnergy RestoredInitialSource NativeMaskedEnergy
open RecenteredRootSetup RecenteredRootRows RecenteredRootReferenceDictionary
open RecenteredRootReferenceEvent RecenteredRootReferenceCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
variable {D:Qrh.MarkedAnchor.Ordinary.StepData}(G:Qrh.MarkedAnchor.Ordinary.StepGates D)

/-- The slot-width mesh of the reference lane at loss `ε` (a choice; `1` if `ε ≤ 0`). -/
def laneMesh (hlane : ReferenceEnergyFine D) (ε : ℝ) : ℝ :=
  if h : 0 < ε then Classical.choose (hlane ε h) else 1

theorem laneMesh_pos (hlane : ReferenceEnergyFine D) {ε : ℝ} (hε : 0 < ε) :
    0 < laneMesh hlane ε := by
  rw [laneMesh, dif_pos hε]
  exact (Classical.choose_spec (hlane ε hε)).1

set_option maxHeartbeats 400000 in
/-- Both original short-side orientations and the newly installed reference rectangle, from
the reference lane `hlane` at the loss `omegaLoss G ε + ε/100`. The constants
follow `bΦ, η, η₀, Q0` and precede all restoration data, profiles, heights and rectangles.
A high root has `P ≥ Pref` (`RootParameters.high_ordinary`). -/
theorem uniform_original_reference (hlane : ReferenceEnergyFine D)
    (W:ℝ → ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (Lcap ε:ℝ)(hLcap:8 ≤ Lcap)(hε:0 < ε)
    (bΦ:ℝ)(hbΦ:2 ≤ bΦ)(η η₀:Character)(Q0:Id)[NeZero Q0]
    (hQt:Q0 ≠ ⊤)(hQ72:Q0 ≤ Ideal.span {(72:O)})(hQM:Q0 ≤ M)(hQη:Q0 ≤ η₀.modulus) :
    ∃J:ℕ,∃control:Finset (ℕ×ℕ),∃C:ℝ,0 < C ∧ ∀ᶠZ:ℝ in atTop,1 < Z ∧
    ∀s:Setup M H D α,s.Z=Z → s.W=W → s.Lcap=Lcap → s.η₀=η₀ →
    (∀i,s.w i ≤ laneMesh hlane (Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100)) →
    ∀V:ℝ,0 ≤ V → (∀i,|s.v i| ≤ V) →
    ∀hn₁:comparisonScale (9/4) < s.Y₁,∀hn₂:comparisonScale (9/4) < s.Y₂,
    D.s₀≤markedWidth M H s → Qrh.MarkedAnchor.Ordinary.RootParameters.NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s) →
    ∀X Y:ℝ,0 < X → 0 < Y → X*Y=s.Y₁*s.Y₂ →
      X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ →
      (X ≤ rootReference M H G s ε ∨ Y ≤ rootReference M H G s ε) →
    ∀Q:Id,internalQ Q η₀ = Q0 →
    ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Iic bΦ → (∀x,0 ≤ (Φ x).re) → ∀rows:Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤
      radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
        (MixedFirstProfileEnvelope.height 0 V s.t s.t)^J*
        Z^(1+Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100)) := by
  have homega := (Qrh.MarkedAnchor.Ordinary.RootParameters.omega_spec G ε hε).1
  have hε' : 0 < Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100 := by positivity
  have hm : laneMesh hlane (Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100) =
      Classical.choose (hlane _ hε') := by
    rw [laneMesh, dif_pos hε']
  obtain ⟨J,control,C,hC,hb⟩ := (Classical.choose_spec (hlane _ hε')).2 M H hH α W hW hWs Lcap
    hLcap bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  refine ⟨J,control,C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hsZ hsW hsLc hsη hw V hV hv hn₁ hn₂ hs₀ hhigh X Y hX hY hXY hXU hYU hshort Q hQ Φ hΦs hΦ rows
  have hP := Qrh.MarkedAnchor.Ordinary.RootParameters.high_ordinary G hε (actual_face M H s hs₀) hhigh
  have hshort' : X ≤ Z^D.lref ∨ Y ≤ Z^D.lref := by
    subst Z; exact hshort
  have hw' : ∀ i, s.w i ≤ Classical.choose (hlane _ hε') := fun i => by rw [← hm]; exact hw i
  have h := hZ.2 s hsZ hsW hsLc hsη hw' V hV hv hn₁ hn₂ hs₀ hP X Y hX hY hXY hXU hYU hshort'
    Q hQ Φ hΦs hΦ rows
  simpa only [add_assoc] using h

end
end Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceBound
