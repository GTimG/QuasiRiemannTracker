/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Actual colored first raw side with corrected selected image multiplicity. -/
import Candidate.C092.transport.ColoredSelectionAverage
import Candidate.C092.transport.ColoredGaussSelectionRadius
import Candidate.C092.transport.TwistedRawBallAllocation
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteAssemblyAvg
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredSelectionAverage
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentChildRows
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance (priority := 2000) averageSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- Native corrected outer mass: the assignment sum has already been grouped by
    the actual dilation image. Its multiplicity M remains an explicit factor. -/
def outerAvg (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (ω₁ ω₂ : Id→*₀ℂ)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (τ : Character) (t : ℝ) (M : actualAllocations (tuplePools s) G→ℝ)
    (F : actualAllocations (tuplePools s) G→RayCharacter→ℝ) : ℝ :=
  (actualAllocations (tuplePools s) G).card *
    ∑ B : actualAllocations (tuplePools s) G,TwistedRawBall.allocationWeight s ω₁ ω₂ G B *
      (Atot (allocatedLiveSource s hb cover G B) (J B) τ t *
        ((2:ℝ)^(Fintype.card (J B))*M B) * ∑χ : RayCharacter,∑ζ : RayCharacter,F B ζ)

theorem raw_sum_le_average (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id→*₀ℂ) (opposite G : Id)
    (hOpp : Supported opposite) (hG : Supported G)
    (hOppG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀u∈Us,Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G)→Finset (liveIndices B.val))
    (W M : actualAllocations (tuplePools s) G→ℝ) (τ : Character) (t K : ℝ) (hK : 0<K)
    (hW : WidthBound s hb cover G J W) (hM : MultBound s hb cover G J K W M) :
    (∑u∈Us,TwistedRawBall.rawEnergy s ha ω₁ ω₂ opposite G hG u τ t K)/sourceVolume s ≤
      outerAvg s hb cover G ω₁ ω₂ J τ t M (fun B ζ =>
        ∑v∈Vset (allocatedLiveSource s hb cover G B) (fun _=>rfl) (J B) Us,
          RootColoredSeed.energy (restOf s hb cover G B (J B)) ha ω₁ ω₂ v
            (childCharacter τ ζ) t (16*K*W B^4))/sourceVolume s := by
  apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
  refine (TwistedRawBall.raw_sum_le_allocated s ha hb cover ω₁ ω₂ opposite G hOpp hG hOppG
    Us τ t K hK).trans ?_
  unfold outerAvg
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply summed_live_energy_avg_le ω₁ ω₂ (allocatedLiveSource s hb cover G B) (fun _=>rfl)
    (J B) ha Us _ hUs (fun u hu y hy => ColoredGaussSelection.vset_seed_image _ _ _ Us u hu y hy)
    τ t K (16*K*W B^4) hK (by have := (hW B).1;positivity) _ (M B) (hM B).1 (hM B).2
  intro y hy
  refine (selWidth_scale K hK y).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (selWidth_pos _ _ y hy).le ((hW B).2 y hy) 4) (by positivity)

#print axioms raw_sum_le_average
end
end QRH.Cycle092.ColoredSelectionAverage
