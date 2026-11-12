/- Copyright (c) 2026 Sil. Apache-2.0.
The reference lane of the ordinary anchor step, in the form of the root reference statement.

`ReferenceEnergy D` is the conclusion of `RecenteredRootReferenceBound.uniform_original_reference`
of sil-density-split, with
* the root-dependent centered exponent replaced by the fixed reference width `D.lref`
  (the reference rectangle has ordinary widths `l_ref`, `P - l_ref`), and the
  short-original alternative (`X ≤ Z^l_ref` or `Y ≤ Z^l_ref`) in the same disjunction;
* the gate-dependent loss `omegaLoss G ε + ε/100` replaced by an arbitrary `ε > 0`;
* the centering condition `NeedsCentering G ε P S` (which depends on the chosen gates) replaced
  by its consequence `D.Pref ≤ P` (`RootParameters.high_ordinary`), so the statement depends
  on the step data `D` only.
`ReferenceLane D` adds the contrary hypothesis `51/100 ≤ β`. The root chain consumes the
source form `ReferenceEnergyFine D` (`Reference/Statement.lean`), which `ReferenceEnergy D`
implies (`fine_of_reference`) and which is proved in `Reference/Lane.lean`: the reference is
paid by the parent source `G(.99, 49/20, .14)`, directly or after reflection. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootRows
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Qrh.MarkedAnchor.Ordinary.FP
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstReferenceEnergy
open RestoredRootDictionary RestoredRootEnergy RestoredInitialSource
open RecenteredRootSetup RecenteredRootRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqReferenceLane {κ:Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotReferenceLane (M:Id) [NeZero M] : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- **The reference energy at the fixed reference width.**
For every ray datum, ambient slot type and window, and every loss `ε > 0`, there are
constants (fixed before the character, the height and `Z`) such that for every restored root
`s` of the step face with `s₀ ≤ S` and `P ≥ Pref`, every factorization `X·Y = Y₁Y₂` inside the
original enclosure with one side at most `Z^l_ref` has its rectangle energy bounded by the
reference normalization at `Z^(1+ε)`. -/
def ReferenceEnergy (D : StepData) : Prop :=
  ∀ (M : Id) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (α : Type) [Fintype α]
    (W : ℝ → ℂ) (_hW : ContDiff ℝ ∞ W) (_hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (Lcap ε : ℝ), 8 ≤ Lcap → 0 < ε →
  ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
  ∀ (η : Character) (bΦ : ℝ), 2 ≤ bΦ → ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ s : Setup M H D α, s.Z = Z → s.W = W → s.Lcap = Lcap →
  ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
  D.s₀ ≤ markedWidth M H s → D.Pref ≤ ordinaryExponent M H s →
  ∀ X Y : ℝ, 0 < X → 0 < Y → X*Y = s.Y₁*s.Y₂ →
    X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ →
    (X ≤ Z^D.lref ∨ Y ≤ Z^D.lref) →
  ∀ Q : Id, ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ → ℂ) ⊆ Iic bΦ → (∀ x, 0 ≤ (Φ x).re) →
  ∀ rows : Finset O,
    (∑ z ∈ rows, initialWeight η s.η₀ Q Φ Z z*
      ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤
    radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
      (MixedFirstProfileEnvelope.height 0 0 s.t s.t)^J*Z^(1+ε))

/-- **The reference lane**: the reference energy under the contrary hypothesis. -/
def ReferenceLane (D : StepData) : Prop :=
  (51/100:ℝ) ≤ HeckeZeroSupremum.beta → ReferenceEnergy D

end
end Qrh.MarkedAnchor.Ordinary
