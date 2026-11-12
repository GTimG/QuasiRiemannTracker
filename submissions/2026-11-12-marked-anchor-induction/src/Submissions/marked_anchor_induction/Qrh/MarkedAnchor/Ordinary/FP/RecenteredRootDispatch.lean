/- Copyright (c) 2026 Sil. Apache-2.0.
Ingredients of the high-volume root dispatch: the reference cost `referenceCost` and the
literal rectangle form of the original initial energy (`original_energy_rectangle`). The
dispatch itself is `RecenteredRootFamilyDispatch.uniform_root_family_dispatch`.
Modified by Sil (2026-10-26): threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootDispatch`; `referenceCost` carries the slot-frequency
height `V` (`height 0 V`, the reference lane `ReferenceEnergyFine`); the single-type dispatch
`uniform_high_root_dispatch` (unused by the chain, which uses the family dispatch) is not forked;
the slot type lives in `Type`.
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootDispatch
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedFirstRebase MixedFirstPuncturedReference MixedFirstReferenceEnergy
open RestoredRootEnergy RestoredInitialSource RecenteredRootSource RecenteredRootSetup
open RecenteredRootRows RecenteredRootReferenceBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
variable {D:Qrh.MarkedAnchor.Ordinary.StepData}(G:Qrh.MarkedAnchor.Ordinary.StepGates D)

def referenceCost (s:Setup M H D α)(ε:ℝ)(J:ℕ)(control:Finset (ℕ×ℕ))(C V:ℝ)(Φ:𝓢(ℝ,ℂ)) : ℝ :=
  radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
    (MixedFirstProfileEnvelope.height 0 V s.t s.t)^J*
    s.Z^(1+Qrh.MarkedAnchor.Ordinary.RootParameters.omegaLoss G ε+ε/100))

theorem original_energy_rectangle (s:Setup M H D α)
    (hn₁:comparisonScale (9/4) < s.Y₁)(hn₂:comparisonScale (9/4) < s.Y₂)
    (η:Character)(Q:Id)(Φ:𝓢(ℝ,ℂ))(rows:Finset O) :
    (∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*‖s.literalRow hH (naturalCharacter η z)‖^2)=
      ∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) s.Y₁ s.Y₂‖^2 := by
  rw [s.initial_energy_source hH hn₁ hn₂ η Q Φ rows]
  apply Finset.sum_congr rfl
  intro z hz
  rw [weighted_row_uncentered (s.rootSource hH hn₁ hn₂) (by norm_num) rfl rfl (naturalCharacter η z)]
  rfl

end
end Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootDispatch
