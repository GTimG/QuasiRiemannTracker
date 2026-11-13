/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The reference lane in the form that the parent-source route can deliver.

`ReferenceEnergy D` (`Ordinary/FP/ReferenceLane.lean`) fixes `J, control, C` before the row
character `η`, the support bound `bΦ`, the base character `s.η₀` and the internal modulus `Q`,
allows arbitrary marked slot widths `s.w` and has no dependence on the slot frequencies `s.v`.
The reference is paid by the parent source `G(.99, 49/20, .14)` (`Reference.parent_source`), a
`GlobalSource`, whose degree, seminorm set and constant are chosen AFTER `bΦ, η, η₀, Q`, which
needs every slot width `≤ mesh(ε)`, and whose bound carries `(1+|t|+height)^degree` with
`height ≥ |v i|`. None of these can be absorbed (the profile `s.p`, the heights `s.t, s.v` and
`s.η₀`, `Q` are chosen after `Z`), so `ReferenceEnergy D` is not derivable from any
`GlobalSource` by this route.

`ReferenceEnergyFine D` is the statement with exactly the data the consumer
(`RepairedSourceSetupBound.uniform_setup_core`) already holds before its constants:
`ε` then a mesh (before every ambient datum), then `bΦ, η, η₀, Q₀` with `Q₀`'s gates
(`[NeZero Q₀]`, `Q₀ ≠ ⊤`, `Q₀ ≤ (72)`, `Q₀ ≤ M`, `Q₀ ≤ η₀.modulus`) before `∃ J control C`;
roots with `s.η₀ = η₀`, slot widths `≤ mesh`, slot frequencies `≤ V`, weights at any `Q` with
`internalQ Q η₀ = Q₀`; the bound has the height `1 + 2|t| + V` (`height 0 V t t`).
`fine_of_reference` shows it is implied by `ReferenceEnergy D` (it is a weakening). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.ReferenceLane

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Qrh.MarkedAnchor.Ordinary Qrh.MarkedAnchor.Ordinary.FP
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
local instance instDecEqReferenceStatement {κ:Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotReferenceStatement (M:Id) [NeZero M] : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- **The reference energy at the fixed reference width, in source form.**
Same rectangle, weights and conclusion as `ReferenceEnergy D`, with the quantifier order and
the fine-slot / slot-height data of a `GlobalSource` application (see the module doc). -/
def ReferenceEnergyFine (D : StepData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ (M : Id) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (α : Type) [Fintype α]
    (W : ℝ → ℂ) (_hW : ContDiff ℝ ∞ W) (_hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (Lcap : ℝ), 8 ≤ Lcap →
  ∀ (bΦ : ℝ), 2 ≤ bΦ → ∀ (η η₀ : Character) (Q₀ : Id) [NeZero Q₀],
    Q₀ ≠ ⊤ → Q₀ ≤ Ideal.span {(72:O)} → Q₀ ≤ M → Q₀ ≤ η₀.modulus →
  ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
  ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ s : Setup M H D α, s.Z = Z → s.W = W → s.Lcap = Lcap → s.η₀ = η₀ →
  (∀ i, s.w i ≤ mesh) → ∀ V : ℝ, 0 ≤ V → (∀ i, |s.v i| ≤ V) →
  ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
  D.s₀ ≤ markedWidth M H s → D.Pref ≤ ordinaryExponent M H s →
  ∀ X Y : ℝ, 0 < X → 0 < Y → X*Y = s.Y₁*s.Y₂ →
    X ≤ (s.rootSource hH hn₁ hn₂).U₁ → Y ≤ (s.rootSource hH hn₁ hn₂).U₂ →
    (X ≤ Z^D.lref ∨ Y ≤ Z^D.lref) →
  ∀ Q : Id, internalQ Q η₀ = Q₀ →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ → ℂ) ⊆ Iic bΦ → (∀ x, 0 ≤ (Φ x).re) →
  ∀ rows : Finset O,
    (∑ z ∈ rows, initialWeight η s.η₀ Q Φ Z z*
      ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y‖^2) ≤
    radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
      (MixedFirstProfileEnvelope.height 0 V s.t s.t)^J*Z^(1+ε))

/-- **The reference lane in source form**: under the contrary hypothesis. -/
def ReferenceLaneFine (D : StepData) : Prop :=
  (51/100:ℝ) ≤ HeckeZeroSupremum.beta → ReferenceEnergyFine D

/-- The source-form energy is a weakening of the stated one. -/
theorem fine_of_reference {D : StepData} (h : ReferenceEnergy D) : ReferenceEnergyFine D := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro M _ H hH α _ W hW hWs Lcap hLcap bΦ hbΦ η η₀ Q₀ _ _ _ _ _
  obtain ⟨J, control, C, hC, hev⟩ := h M H hH α W hW hWs Lcap ε hLcap hε
  refine ⟨J, control, C, hC, ?_⟩
  filter_upwards [hev η bΦ hbΦ] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro s hsZ hsW hsL _ _ V hV _ hn₁ hn₂ hs₀ hP X Y hX hY hXY hXU hYU hshort Q _ Φ hΦs hΦ rows
  refine (hZ.2 s hsZ hsW hsL hn₁ hn₂ hs₀ hP X Y hX hY hXY hXU hYU hshort Q Φ hΦs hΦ rows).trans ?_
  have hh0 : 0 ≤ MixedFirstProfileEnvelope.height 0 0 s.t s.t := by
    unfold MixedFirstProfileEnvelope.height; positivity
  have hh : MixedFirstProfileEnvelope.height 0 0 s.t s.t ≤ MixedFirstProfileEnvelope.height 0 V s.t s.t := by
    unfold MixedFirstProfileEnvelope.height; linarith
  have hZ0 : 0 ≤ Z^(1+ε) := Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _
  apply mul_le_mul_of_nonneg_left _ (radial_control_nonneg Φ)
  apply mul_le_mul_of_nonneg_right _ hZ0
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hh J) (by positivity)

end
end Qrh.MarkedAnchor.Ordinary.Reference
