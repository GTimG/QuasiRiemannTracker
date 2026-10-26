/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePhysicalSelection
import Candidate.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
local instance affineMainNormalizedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The genuine physical selection receipt turns complete selected costs
into the original full-family normalized contract. Every selected first
allocation retains its complete second-block row sum. -/
theorem actual_affine_main_normalized_of_selected
    (Cs ε ξ K Z C : ℝ) (degree : ℕ) (hZ : 1<Z)
    (hK : 0≤K) (hC : 0≤C)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (amp reserve height : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hselected : ∀(second : Bool)(t₀ u : ℝ),
      let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
      let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key) (fun _=>logAnnulus)
      let ideal:=fun j : rows=>geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key j.val
      let mass:=fun j : rows=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z ξ ε hKfirst key j.val
      ∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key (column j).val,
          (column j).val.2.1.val)) →
      ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
        (∀j,frozenCoefficient (alloc j).val (ideal (column j)) 1 s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s 1 1 Z 1 amp ξ reserve
          (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
          ⟨column j,alloc j⟩)≤(C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) :
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) height
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=>geometryMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card α) hZ key 1 (Real.logb Z (volume s))
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
    SecondNormalizedBound W degree degree datum weight (fun _=>K*Z^ε*C) (fun _=>1) := by
  intro selected datum weight
  apply second_normalized_bound_of_full
  intro second t₀ u
  have hs := hselection hZ reflected s p caps amp reserve height key Ψ χ Q m W second t₀ u
    ((C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) hz₁ hz₂ (hselected second t₀ u)
  have hu : (1+‖u‖)^degree≤(1+‖u‖)^(2*degree) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  have hc : 0≤(K*Z^ε)*(C*(1+‖t₀‖)^degree) := by positivity
  have he := mul_le_mul_of_nonneg_left hu hc
  apply hs.trans
  convert he using 1 <;> ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_main_normalized_of_selected
