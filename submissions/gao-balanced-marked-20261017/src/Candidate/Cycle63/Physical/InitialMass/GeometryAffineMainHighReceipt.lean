/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainPayment

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap
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
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The proved high cost uses precisely the canonical family required by
the retained main contraction. Only selector field equalities and scalar
norm notation are transported; no row, filter, or weight is changed. -/
theorem affine_main_high_receipt_of_selected_cost
    (W : ℝ→ℂ)(hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(P : HighSourceParameters)
    (hPe : P.e=g.e)(hPτ : P.τ=g.τ)(ηseed : Character)(Cs target : ℝ)
    (SH : Finset (ℕ×ℕ))(dh : ℕ)(KH : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)(hsη : s.η=ηseed)
    (height mesh : ℝ)(hw : ∀j,0≤w j)
    (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hwmarked : ∀j,w j≤ markedRawMesh*markedCoreMin)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)(hT : 2<Z^g.τ)
    (hzslot : (17/500:ℝ)≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤1/25)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
      Cycle63.Arithmetic.B)
    (hvolumeCell : Real.logb Z (volume s)≤Cycle63.Arithmetic.totalA
      (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑j,Real.logb Z (s.P j)))))
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hspec : GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hβlo P g.μ g.δ target
      (fun _ _ _ _ _=>True) ηseed Cs SH dh KH η₀ Q hQM hQ72 Z) :
    let amp:=(1:ℝ)*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    0≤amp → |amp|≤4 → |omega|≤4 →
    GeometryAffineMainCanonicalHighReceipt M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh target := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro amp omega hamp0 hamp homega second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex
    selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ
    hheight hfreq hT hβhi hzslot haff hvolumeCell
    reflected second key baseHeight firstIndex hamp0 hamp homega hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u trivial hP hPN
  convert hb using 1
  rfl

/-- The literal affine high estimate supplies the exact selected branch
used by the main payment, with source admission already discharged. -/
theorem actual_affine_main_high_receipt
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
    (hlo₁ : (41/100:ℝ)≤length Z X₁)(hlo₂ : (41/100:ℝ)≤length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B)
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    let amp:=(1:ℝ)*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    GeometryAffineMainCanonicalHighReceipt M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh target := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro s hz₁ hz₂ amp second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
    firstIndex selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hwmarked hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone
    reflected second key baseHeight firstIndex hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u hP hPN
  convert hb using 1
  rfl

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_main_high_receipt_of_selected_cost
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_main_high_receipt
