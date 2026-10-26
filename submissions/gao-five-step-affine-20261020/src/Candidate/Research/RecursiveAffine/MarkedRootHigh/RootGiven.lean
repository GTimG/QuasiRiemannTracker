/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootAffine
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAtState
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainPayment
import Candidate.Cycle63.Arithmetic.Constants
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge Cycle63Moment
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional
open Cycle63InitialSource

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable [L : Cycle63.AffineLedger] [Cycle153.MarkedRootPrice.RootLedgerBinding L]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The literal affine high estimate supplies the exact selected branch
used by the main payment, with source admission already discharged. -/
theorem actual_root_high_given
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (ηseed : Character)(SH : Finset (ℕ×ℕ))(dh : ℕ)(KH target : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hspec : GeometryAffineMainHighSpec (α:=α) M H hH W hW hWs hβlo P
      g.μ g.δ target ηseed SH dh KH η₀ Q hQM hQ72 Z)
    (hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hwmarked : ∀i,w i≤ markedRawMesh*markedCoreMin)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i))
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    let amp:=(1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    GeometryAffineMainCanonicalHighBound M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4)
      reflected s 1 1 1 amp baseHeight key Ψ χ₀ hz₁ hz₂
      (KH*Z^(amp+target)*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*(1+|baseHeight|+height)^dh) dh := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro s hz₁ hz₂ amp second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
    firstIndex selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hwmarked hheight hfreq hT hβhi hwin
    reflected second key baseHeight firstIndex hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u hP hPN
  convert hb using 1 <;> (try simp only [Cycle153.MarkedRootPrice.RootLedgerBinding.q_eq])
  all_goals first | rfl | (simp only [Real.norm_eq_abs]; ring)

/-- The same actual root source provides the native HIGH interface simultaneously at every bin and height. -/
theorem actual_root_high_given_all
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (ηseed : Character)(SH : Finset (ℕ×ℕ))(dh : ℕ)(KH target : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hspec : GeometryAffineMainHighSpec (α:=α) M H hH W hW hWs hβlo P
      g.μ g.δ target ηseed SH dh KH η₀ Q hQM hQ72 Z)
    (hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hwmarked : ∀i,w i≤ markedRawMesh*markedCoreMin)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i))
    (Ψ : 𝓢(ℝ,ℂ)) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    let amp:=(1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    GeometryAffineHighGiven M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4)
      s p 1 1 1 amp Ψ hz₁ hz₂ SH dh height (KH*Z^(amp+target)) := by
  intro s hz₁ hz₂ amp reflected key _ firstHeight χ₀
  exact actual_root_high_given (α:=α) M H hH W hW hWs hβlo g P hPe hPτ
    ηseed SH dh KH target η₀ Q hQM hQ72 Z hspec hZ θ w σ freq hσ bΦ state hη p
    tplain X₁ X₂ hX₁ hX₂ height mesh hw hmesh hmeshcap hwm hwmarked hheight hfreq
    hT hβhi hwin reflected firstHeight key Ψ χ₀

end
end OAI.SevenEighths.Cycle153RootHigh

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_root_high_given

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_root_high_given_all
