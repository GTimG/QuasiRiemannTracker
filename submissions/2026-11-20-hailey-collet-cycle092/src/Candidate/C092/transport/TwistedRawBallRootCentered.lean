/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The actual restored source centered before taking norms or enlarging its keep. -/
import Candidate.C092.transport.TwistedRawBallRootComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentLattice
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalAllocations MixedPrincipalPair MixedPrincipalWindow MixedLiveNormalization MixedInnerExceptionalBlock
open NativeMaskedEnergy RestoredRootDictionary
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
variable (hHr : RayOrthogonality.globalUnits M ≤ Hr)
variable {D : QRH.SilDensitySplit.CubeFree.StepData} {α : Type*} [Fintype α]
variable (s : RestoredRootEnergy.Setup M Hr D α)
variable (hn₁ : CenteredMomentUncenteredTerminal.comparisonScale (9/4) < s.Y₁)
variable (hn₂ : CenteredMomentUncenteredTerminal.comparisonScale (9/4) < s.Y₂)
variable (t₁ t₂ q : ℝ)
variable (hq : 0 < q)
variable (hY : (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂).Y₁ ≤ q)
variable (h₁ : q ≤ (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂).X₁)
variable (h₂ : q ≤ (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂).X₂)

def centeredPairRoot : Source (remainingSet s.r s.A) (1/4) (9/4) :=
  RecenteredRootSource.recenter (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂) q hq hY h₁ h₂

theorem centeredPairRoot_canonical :
    MixedFirstActualNonexceptional.Canonical M Hr hHr s.W 16 s.Lcap s.Z s.η₀
      (fun i : remainingSet s.r s.A=>s.θ i.val) (fun i=>s.w i.val) (fun _=>33/50)
      (fun i=>s.v i.val) s.t
      (fun _=>restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti)
      (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂) := by
  exact actualPairRoot_canonical M Hr hHr s hn₁ hn₂ t₁ t₂

theorem centeredPairRoot_original_enclosure :
    OriginalEnclosure (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂) := by
  exact actualPairRoot_original_enclosure M Hr hHr s hn₁ hn₂ t₁ t₂

theorem centeredPairRoot_masks :
    (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂).H=∅ ∧
    (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂).R=1 ∧
    (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂).d=(1,1) := ⟨rfl,rfl,rfl⟩

/-- This is the literal native canonical source, with the new reference
    still present before absolute values and the two ordinary heights separate. -/
theorem centeredPairRoot_signed (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0) :
    let r := actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂
    let c := centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂
    let β := fun i I=>r.ν i I*r.Wslot i (I.absNorm/r.P i)
    let V₁ := normPowerProfile r.W₁ (1/4) (9/4) (by norm_num) r.hs₁ (r.W₁.smooth ⊤) t₁
    let V₂ := normPowerProfile r.W₂ (1/4) (9/4) (by norm_num) r.hs₂ (r.W₂.smooth ⊤) t₂
    coloredWeightedRow c (by norm_num) ω₁ ω₂ χ =
      restoredRow χ ω₁ ω₂ r.S r.pool β r.P V₁ V₂ (9/4) r.X₁ r.X₂-
        restoredRow χ ω₁ ω₂ r.S r.pool β r.P V₁ V₂ (9/4) q (r.T/q) := by
  exact actual_source_signed_unpunctured
    (centeredPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂) (by norm_num) (by norm_num)
    (centeredPairRoot_original_enclosure M Hr hHr s hn₁ hn₂ t₁ t₂ q hq hY h₁ h₂)
    rfl rfl rfl χ ω₁ ω₂ hoff

#print axioms centeredPairRoot_canonical
#print axioms centeredPairRoot_original_enclosure
#print axioms centeredPairRoot_masks
#print axioms centeredPairRoot_signed
end
end QRH.Cycle092.TwistedRawBallRootProducer
