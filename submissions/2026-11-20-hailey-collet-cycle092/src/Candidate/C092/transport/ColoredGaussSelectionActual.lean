/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual allocation → whole-slot selection, with the original source-volume denominator. -/
import Candidate.C092.transport.ColoredGaussSelectionTransfer
import Candidate.C092.transport.RootColoredSeedActual
import Candidate.C092.transport.TwistedRawBallAllocation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussSelection
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentChildRows
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem vset_seed_image (s : Source ι a b) (hB1 : ∀k,s.B k=1) (J : Finset ι)
    (Us : Finset Id) (u : Id) (hu : u∈Us) (y : ↥J→Id) (hy : y∈selY s J) :
    seedRest u (∏j,y j) ∈ Vset s hB1 J Us := by
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨(u,y),Finset.mem_product.mpr ⟨hu,hy⟩,rfl⟩

def selectedTerms (s : Source ι a b) (hB1 : ∀k,s.B k=1) (J : Finset ι) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (Us : Finset Id) (τ : Character) (t : ℝ) (Kp : (↥J→Id)→ℝ) : ℝ :=
  Atot s J τ t * ∑y∈selY s J, ∑χ : RayCharacter, ∑ζ : RayCharacter,
    2^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card *
      ∑v∈Vset s hB1 J Us, RootColoredSeed.energy (restSource s hB1 J) ha ω₁ ω₂ v
        (childCharacter τ ζ) t (Kp y)

theorem selection_to_vset (s : Source ι a b) (hB1 : ∀k,s.B k=1) (J : Finset ι) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (Us : Finset Id) (hUs : ∀u∈Us,Squarefree u)
    (τ : Character) (t K : ℝ) (Kp : (↥J→Id)→ℝ) (hK : 0<K)
    (hKp : ∀y∈selY s J,0<Kp y)
    (hKK : ∀y∈selY s J,2*K*‖ConcreteTraceCRT.eisEmbedding
      (CompletedGauss.primaryGenerator (∏j,y j)^4)‖^2 ≤ Kp y) :
    ∑u∈Us,RootColoredSeed.energy s ha ω₁ ω₂ u τ t K ≤
      selectedTerms s hB1 J ha ω₁ ω₂ Us τ t Kp :=
  summed_live_energy_le ω₁ ω₂ s hB1 J ha Us _ hUs
    (fun u hu y hy => vset_seed_image s hB1 J Us u hu y hy) τ t K Kp hK hKp hKK

/-- Selection uses the actual colored allocated first side. The denominator
    remains the volume of the original source throughout allocation and selection. -/
theorem raw_sum_le_selected (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id→*₀ℂ) (C G : Id)
    (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀u∈Us,Squarefree u)
    (J : ∀B : actualAllocations (tuplePools s) G, Finset (liveIndices B.val))
    (τ : Character) (t K : ℝ)
    (Kp : ∀B : actualAllocations (tuplePools s) G,(↥(J B)→Id)→ℝ) (hK : 0<K)
    (hKp : ∀B y, y∈selY (allocatedLiveSource s hb cover G B) (J B) → 0<Kp B y)
    (hKK : ∀B y, y∈selY (allocatedLiveSource s hb cover G B) (J B) →
      2*K*‖ConcreteTraceCRT.eisEmbedding (CompletedGauss.primaryGenerator (∏j,y j)^4)‖^2 ≤ Kp B y) :
    (∑u∈Us,TwistedRawBall.rawEnergy s ha ω₁ ω₂ C G hG u τ t K) / sourceVolume s ≤
      ((actualAllocations (tuplePools s) G).card *
        ∑B : actualAllocations (tuplePools s) G,
          TwistedRawBall.allocationWeight s ω₁ ω₂ G B *
            selectedTerms (allocatedLiveSource s hb cover G B) (fun _=>rfl) (J B)
              ha ω₁ ω₂ Us τ t (Kp B)) / sourceVolume s := by
  apply div_le_div_of_nonneg_right _ (le_of_lt (sourceVolume_pos s))
  refine (TwistedRawBall.raw_sum_le_allocated s ha hb cover ω₁ ω₂ C G hC hG hCG Us τ t K hK).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact selection_to_vset (allocatedLiveSource s hb cover G B) (fun _=>rfl) (J B)
    ha ω₁ ω₂ Us hUs τ t K (Kp B) hK (hKp B) (hKK B)

#print axioms selection_to_vset
#print axioms raw_sum_le_selected
end
end QRH.Cycle092.ColoredGaussSelection
