import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePhysicalSelection
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
variable {α : Type} [Fintype α] [DecidableEq α]
local instance affineMainNormalizedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

variable [Cycle63.AffineLedger] in
/-- The genuine physical selection receipt turns complete selected costs
into the original full-family normalized contract. Every selected first
allocation retains its complete second-block row sum. -/
theorem actual_affine_main_normalized_of_selected
    (Cs ε ξ K Z C : ℝ) (degree : ℕ) (hZ : 1<Z)
    (hK : 0≤K) (hC : 0≤C)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (R seed : Ideal O) (Mrow : ℝ) (hseed : Squarefree seed) (hMrow : 0≤Mrow)
    (amp reserve height : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hselected : ∀(second : Bool)(t₀ u : ℝ),
      let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hKfirst key) (fun _=>logAnnulus)
      let ideal:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hKfirst key j.val
      let mass:=fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hKfirst key j.val
      ∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hKfirst key (column j).val,
          (column j).val.2.1.val)) →
      ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
        (∀j,frozenCoefficient (alloc j).val (ideal (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve
          (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
          ⟨column j,alloc j⟩)≤(C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) :
    let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve (9/4) height
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve
      (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=>geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve
      (9/4) height (Fintype.card α) hZ key Mrow (Real.logb Z (volume s))
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
    SecondNormalizedBound W degree degree datum weight (fun _=>K*Z^ε*C) (fun _=>1) := by
  intro selected datum weight
  apply second_normalized_bound_of_full
  intro second t₀ u
  have hs := hselection hZ reflected s p caps R seed Mrow hseed hMrow amp reserve height key Ψ χ Q m W second t₀ u
    ((C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) hz₁ hz₂ (hselected second t₀ u)
  have hu : (1+‖u‖)^degree≤(1+‖u‖)^(2*degree) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  have hc : 0≤(K*Z^ε)*(C*(1+‖t₀‖)^degree) := by positivity
  have he := mul_le_mul_of_nonneg_left hu hc
  apply hs.trans
  convert he using 1 <;> ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
