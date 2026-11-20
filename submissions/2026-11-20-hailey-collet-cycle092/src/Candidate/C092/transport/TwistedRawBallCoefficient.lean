/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The actual independently colored allocated live coefficient. -/
import Candidate.C092.transport.RootColoredSeedActual
import Candidate.C092.transport.TwistedRawSourceClosure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedFirstLiveSource
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumBallDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

theorem live_source_colored_coefficient (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (D I : Id) :
    sourceColumn (liveSource s) ha ω₁ ω₂ D I =
      if D ∣ I then coloredColumn (liveBox (MixedPrincipalAllocations.tuplePools s) s.B s.hB)
        (MixedCommonRestriction.punctureProduct s.S s.H) ω₁ ω₂
        (liveProfile s.B s.G s.R s.ν s.Wslot s.P
          (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
          (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
          s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2) I else 0 := by
  rw [sourceColumn_seed]
  split_ifs
  · unfold sourceColumn coloredColumn finiteColumnCoefficient
    rw [live_source_box]
    apply Finset.sum_congr rfl
    intro v hv
    unfold MixedOriginalSecondZero.originalTuple coloredTuple liveProfile
    dsimp only [liveSource, MixedPrincipalPair.Source.prefixPair]
    ring
  · rfl

#print axioms live_source_colored_coefficient
end
end QRH.Cycle092.TwistedRawBall
