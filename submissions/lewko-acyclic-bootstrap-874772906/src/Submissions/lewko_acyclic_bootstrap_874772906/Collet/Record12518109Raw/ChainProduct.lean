/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.GeometryProduct
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalLow.Chain
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentAllocatedRayDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentRetainedEnergy
open CenteredMomentEnergyReindex CenteredMomentSecondHeightFamily
open Cycle61FinalLow Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O

/-- Literal pointwise transport of all slots and the whole-product normalizer. -/
theorem retained_subset_map {ι α : Type*} (e : ι↪α) (T : Finset ι)
    (η : Character)(m A z : O)(W₁ W₂ : ℝ→ℂ)
    (pool : α→Finset (Ideal O))(coeff : α→Ideal O→ℂ)(P : α→ℝ)(t X₁ X₂ : ℝ) :
    retainedPositiveRow η m A z W₁ W₂
      (fun i:T=>pool (e i)) (fun i:T=>coeff (e i)) (fun i:T=>P (e i)) t X₁ X₂ =
    retainedPositiveRow η m A z W₁ W₂
      (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i) t X₁ X₂ := by
  unfold retainedPositiveRow
  exact positive_reindex (Finset.equivMap e T) η m A z _ _
    (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i) t _ _

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A two-stage common allocation and a residual allocation leave the exact
original relative-slot dictionary. This is a pointwise identity for the
physical retained product, with no energy or mask-compatibility premise. -/
theorem actual_chain_positive_row_original
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ)(W : ℝ→ℂ)(bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)(q : Chain s)
    (η : Character)(v : ℝ)(second : Bool)(L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2)))
    (z : O) :
    let src:=q.final η v
    let X₁:=Cycle61.Physical.sourcePlainScales src.toSource second 0/(selectedPlain L a 0).absNorm
    let X₂:=Cycle61.Physical.sourcePlainScales src.toSource second 1/(selectedPlain L a 1).absNorm
    Cycle61.Physical.sourcePositiveRow src.toSource second L a z =
      retainedPositiveRow η (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1 z s.W₁ s.W₂
        (fun i:q.indices L a=>primePool M H bslot (Z^(w i)))
        (fun (i:q.indices L a) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:q.indices L a=>Z^(w i)) v X₁ X₂ := by
  intro src X₁ X₂
  change retainedPositiveRow η (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1 z s.W₁ s.W₂
    (fun i:liveIndices L a=>s.slots (q.embedding i))
    (fun (i:liveIndices L a) I=>s.ν (q.embedding i) I*s.W (q.embedding i)
      ((I.absNorm:ℝ)/s.P (q.embedding i)))
    (fun i:liveIndices L a=>s.P (q.embedding i)) v X₁ X₂ = _
  have hp : (fun i:liveIndices L a=>s.slots (q.embedding i)) =
      fun i:liveIndices L a=>primePool M H bslot (Z^(w (q.embedding i))) := by
    funext i
    exact hm.pool (q.embedding i)
  have hP : (fun i:liveIndices L a=>s.P (q.embedding i)) =
      fun i:liveIndices L a=>Z^(w (q.embedding i)) := by
    funext i
    exact hm.scale (q.embedding i)
  have hc : (fun (i:liveIndices L a) I=>s.ν (q.embedding i) I*s.W (q.embedding i)
      ((I.absNorm:ℝ)/s.P (q.embedding i))) =
      fun (i:liveIndices L a) I=>idealCoeff (relativeCharacter M H hH η₀ (θ (q.embedding i))) I*
        HeckePrimeAnnular.annularWeight W (Z^(w (q.embedding i)))
          (σ (q.embedding i)) (freq (q.embedding i)) I := by
    funext i I
    rw [hm.character,hm.profile,hm.scale]
    rfl
  rw [hp,hc,hP]
  exact retained_subset_map q.embedding (liveIndices L a) η
    (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1 z s.W₁ s.W₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) v X₁ X₂

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.retained_subset_map
#print axioms OAI.SevenEighths.Record12518109Raw.actual_chain_positive_row_original
