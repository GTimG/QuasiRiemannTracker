/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual canonical restored root with independently colored ordinary slots. -/
import Candidate.C092.transport.TwistedRawBallLive
import Candidate.C092.transport.RegularColoredForwardSource
import Submissions.sil_density_split_20261026.CubeFree.FP.RestoredRootEnergy
import Submissions.sil_density_split_20261026.CubeFree.FP.RecenteredRootSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedCanonicalSource
open NativeMaskedEnergy
open MixedInnerExceptionalBlock MixedLiveNormalization RestoredRootDictionary
open Candidate.FourthPower.KernelNaturalSlots Candidate.FourthPower.KernelAssignmentReindex
open Candidate.FourthPower.NativeFiniteHoles Candidate.FourthPower.RestorationCollisionEnergy
open KernelRowProfiles KernelRowExpansion
open KernelMarkedRows KernelRowPools KernelLabelledSlots
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

/-- A common domain can be chosen before both signed arms and restoration. -/
def restoredRowOn (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (S : Finset PrimeIdeal) (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (D : Finset (Id×Id)) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) : ℂ :=
  weightedSum (naturalCoefficients χ S pool β P)
    (fun slot=>RegularColoredForward.row χ ω₁ ω₂ D (sourceValue false S slot) W₁ W₂ X₁ X₂)

def restoredRow (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (S : Finset PrimeIdeal) (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  restoredRowOn χ ω₁ ω₂ S pool β P (supportedRectangle S b X₁ X₂) W₁ W₂ X₁ X₂

theorem restoredRow_character_congr (χ ψ : Character) (h : ∀I,idealCoeff χ I=idealCoeff ψ I)
    (ω₁ ω₂ : Id→*₀ℂ) (S : Finset PrimeIdeal) (pool : ι→Finset Id)
    (β : ι→Id→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b X₁ X₂ =
      restoredRow ψ ω₁ ω₂ S pool β P W₁ W₂ b X₁ X₂ := by
  unfold restoredRow restoredRowOn weightedSum naturalCoefficients slotTerm
    RegularColoredForward.row normalizedRow pairCharacter
  simp_rw [h]

/-- The canonical ordinary marked coefficient after moving the old first
    ordinary character to the bare common sextic anchor. Zeros are exact. -/
theorem relative_reanchor (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M ≤ Hr) (base η : Character)
    (θ : RayQuotient.Characters M Hr) (I : Id) :
    idealCoeff (relativeCharacter M Hr hHr (base.product η.inverse) θ) I =
      idealCoeff η I*idealCoeff (relativeCharacter M Hr hHr base θ) I := by
  simp only [relativeCharacter,idealCoeff_product,idealCoeff_inverse_conj,map_mul,Complex.conj_conj]
  ring

theorem slotCoefficient_reanchor (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M ≤ Hr) (base η : Character)
    (θ : ι→RayQuotient.Characters M Hr) (R₀ : ι→Finset Id) (t : ℝ) (i : ι) (I : Id) :
    slotCoefficient (fun j=>relativeCharacter M Hr hHr (base.product η.inverse) (θ j)) R₀ t i I =
      idealCoeff η I*slotCoefficient (fun j=>relativeCharacter M Hr hHr base (θ j)) R₀ t i I := by
  unfold slotCoefficient CenteredMomentCommonMaskEnergy.heightCoefficient Candidate.FourthPower.NativeFiniteHoles.holeCoefficient
  by_cases h : I∈R₀ i
  · simp only [h,ite_true,zero_mul,mul_zero]
  · simp only [h,ite_false,relative_reanchor]
    ring

/-- Original independent ordinary heights do not modify canonical mark data. -/
def withOrdinaryHeights {a b : ℝ} (s : Source ι a b) (t₁ t₂ : ℝ) : Source ι a b :=
  {s with t₁:=t₁,t₂:=t₂}

theorem withOrdinaryHeights_canonical {a b : ℝ}
    (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M ≤ Hr)
    (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (base : Character) (θ : ι→RayQuotient.Characters M Hr)
    (w σ freq : ι→ℝ) (t : ℝ) (R₀ : ι→Finset Id) (s : Source ι a b)
    (hc : MixedFirstActualNonexceptional.Canonical M Hr hHr W Cap Lcap Z base θ w σ freq t R₀ s)
    (t₁ t₂ : ℝ) :
    MixedFirstActualNonexceptional.Canonical M Hr hHr W Cap Lcap Z base θ w σ freq t R₀
      (withOrdinaryHeights s t₁ t₂) := hc

section Root
variable (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
variable (hHr : RayOrthogonality.globalUnits M ≤ Hr)
variable {D : QRH.SilDensitySplit.CubeFree.StepData} {α : Type*} [Fintype α]
variable (s : RestoredRootEnergy.Setup M Hr D α)
variable (hn₁ : CenteredMomentUncenteredTerminal.comparisonScale (9/4) < s.Y₁)
variable (hn₂ : CenteredMomentUncenteredTerminal.comparisonScale (9/4) < s.Y₂)

def actualPairRoot (t₁ t₂ : ℝ) : Source (remainingSet s.r s.A) (1/4) (9/4) :=
  withOrdinaryHeights (s.rootSource hHr hn₁ hn₂) t₁ t₂

theorem actualPairRoot_canonical (t₁ t₂ : ℝ) :
    MixedFirstActualNonexceptional.Canonical M Hr hHr s.W 16 s.Lcap s.Z s.η₀
      (fun i : remainingSet s.r s.A=>s.θ i.val) (fun i=>s.w i.val) (fun _=>33/50)
      (fun i=>s.v i.val) s.t
      (fun _=>restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti)
      (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂) := by
  exact RestoredRootSource.Data.source_canonical hHr (s.rootData hn₁ hn₂)

theorem actualPairRoot_original_enclosure (t₁ t₂ : ℝ) :
    OriginalEnclosure (actualPairRoot M Hr hHr s hn₁ hn₂ t₁ t₂) := by
  exact RestoredRootSource.Data.source_original_enclosure hHr (s.rootData hn₁ hn₂)

end Root

/-- The unpunctured restored family is exactly the common colored row used
    by canonical centralization, including all cube-free/injective gates. -/
theorem restoredRow_eq_punctured (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (S : Finset PrimeIdeal) (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b X₁ X₂ =
      RegularColoredForward.coloredPuncturedRow χ ω₁ ω₂ S ∅ pool β P W₁ W₂ b X₁ X₂ := by
  unfold restoredRow restoredRowOn RegularColoredForward.coloredPuncturedRow
  congr 1
  funext slot
  have he : KernelPunctureRows.augmented S ∅ (marked S slot)=marked S slot := by
    funext P
    simp only [KernelPunctureRows.augmented,Finset.notMem_empty,decide_false,Bool.or_false]
  rw [he]
  rfl

/-- Exact post-restoration signed row at any genuine root Source; no source
    projection is inferred from an unrestricted original ordinary product. -/
theorem actual_source_signed {a b : ℝ} (s : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (hH : s.H=∅) (hd : s.d=(1,1))
    (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0) :
    let χR := χ.excludePrimes (primeSupport s.R) (fun _ h=>IdealMobiusDivisorSum.support_prime h)
    let β := fun i I=>s.ν i I*s.Wslot i (I.absNorm/s.P i)
    let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
    let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
    normalization (s.X₁*s.X₂) s.P *
      (∑I∈sourceColumns s,sourceColumn s ha ω₁ ω₂ 1 I*idealCoeff χ I) =
      restoredRow χR ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.X₁ s.X₂-
        restoredRow χR ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.Y₁ s.Y₂ := by
  dsimp only
  rw [RegularColoredForward.sourceColumn_centered s ha hb cover χ ω₁ ω₂ hoff]
  unfold RegularColoredForward.coloredCenteredRow
  rw [hd]
  simp only [pairNorm,map_one,Nat.cast_one,mul_one,Real.sqrt_one,Complex.ofReal_one,inv_one,
    one_mul,div_one,hH,←restoredRow_eq_punctured]

theorem actual_source_signed_unpunctured {a b : ℝ} (s : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (hH : s.H=∅) (hd : s.d=(1,1)) (hR : s.R=1)
    (χ : Character) (ω₁ ω₂ : Id→*₀ℂ) (hoff : ∀I,¬Supported I→idealCoeff χ I=0) :
    let β := fun i I=>s.ν i I*s.Wslot i (I.absNorm/s.P i)
    let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
    let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
    normalization (s.X₁*s.X₂) s.P *
      (∑I∈sourceColumns s,sourceColumn s ha ω₁ ω₂ 1 I*idealCoeff χ I) =
      restoredRow χ ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.X₁ s.X₂-
        restoredRow χ ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.Y₁ s.Y₂ := by
  have hh := actual_source_signed s ha hb cover hH hd χ ω₁ ω₂ hoff
  dsimp only at hh ⊢
  have he : ∀I,idealCoeff (χ.excludePrimes (primeSupport s.R)
      (fun _ h=>IdealMobiusDivisorSum.support_prime h)) I=idealCoeff χ I := by
    intro I
    rw [hR]
    exact excluded_one_ideal χ I
  rw [restoredRow_character_congr _ χ he,restoredRow_character_congr _ χ he] at hh
  exact hh

#print axioms relative_reanchor
#print axioms slotCoefficient_reanchor
#print axioms actualPairRoot_canonical
#print axioms actualPairRoot_original_enclosure
#print axioms actual_source_signed
#print axioms actual_source_signed_unpunctured
end
end QRH.Cycle092.TwistedRawBallRootProducer
