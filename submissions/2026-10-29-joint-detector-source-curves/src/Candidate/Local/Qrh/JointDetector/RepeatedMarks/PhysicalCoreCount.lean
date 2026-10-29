/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.RepeatedWeightedHigh
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.NaturalLiftAway
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Rate
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateContinuity
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.UnmarkedHigh
import Candidate.Local.Qrh.JointDetector.FineNaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeInverseAmplification ProbeHighRowFamily
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open HeckeDetectorWitnessRows
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentRetainedProfile
open LocalMoment HeckeDetectorZeros ProbePhysical ActualEisensteinCubic
open RefinedSupplier FineNaturalCount
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)


/-! The remaining actual core provider, stated on the literal physical
row/slot event. Its fixed exceptional set, degree and constant precede Z,
the row character, the natural root and every live profile/height. -/
def PhysicalCoreCount (νMin B L c : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss dmin : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 < dmin →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ extra : Finset FreeRow, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc dmin (2*b-1) → 0 ≤ T' → |t|+height ≤ T' →
  ∀ (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (cores : Finset FreeRow),
    Z^(Mmin/20) ≤ Y → Y ≤ bΦ*Z^st.rowWidth →
    (∀ u ∈ cores, rowNorm u ≤ Y ∧ u ∉ extra ∧
      ∃ hz : st.radial.keep (rowMap (u,root)),
        st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη (rowMap (u,root)) hz T' ∧
        Z^(δ*∑ k,w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) →
    (cores.card:ℝ) ≤ C*(1+T')^J*Y^(rawRepeatedCountRate B L c (2*b-1) δ+loss)

end
end Qrh.JointDetector.RepeatedMarks
