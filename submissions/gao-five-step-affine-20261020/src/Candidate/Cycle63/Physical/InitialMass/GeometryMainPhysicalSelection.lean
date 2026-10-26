/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedCost
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local instance mainPhysicalSelectionSumDecidable {α : Type*} [DecidableEq α] :
    DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Physical phase-weight specialization. Its selected mass is exactly the
mass used by the genuine low, high and coarse analytic family bounds. -/
theorem actual_geometry_main_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (Cs b ε Amax Dmax B ξ slotlo plainlo : ℝ)
    (hCs : 1≤Cs) (hε : 0<ε) (hA : 0≤Amax) (hD : 0≤Dmax)
    (hB : 0≤B) (hξ : 0≤ξ) (hslot : 0<slotlo) (hplain : 0<plainlo) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow amp reserve t : ℝ),
      Fintype.card α≤N → (∀i,s.M i≤Cs) → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^Amax → (Z^Mrow)⁻¹≤Z^Dmax →
      slotlo≤ s.lower → (∀x,s.W₁ x≠0→plainlo≤x) → (∀x,s.W₂ x≠0→plainlo≤x) →
      ∀(key : ℤ×(Fin 5→ℤ))
        (Ψ : 𝓢(ℝ,ℂ))
        (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
      let mass := fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hK key j.val
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨column j,alloc j⟩)≤E) →
      let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
      let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mrow (Real.logb Z (volume s.toData))
          (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
      secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
        (K₀*Z^ε)*E := by
  obtain ⟨K₀,hK₀,hselection⟩ := actual_geometry_main_selected_cost (α:=α)
    N Cs b ε Amax Dmax B ξ slotlo plainlo hCs hε hA hD hB hξ hslot hplain
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hselection] with Z hsel
  intro hZ reflected s R seed Mrow amp reserve t hn hM hseed hz₁ hz₂
    hsource hcap hV hKi hlo hW₁ hW₂ key Ψ χ Q m W second t₀ u E hK rows C mass hselected datum w
  exact hsel hZ reflected s R seed Mrow amp reserve t Mrow (Real.logb Z (volume s.toData))
    hn hM hseed hz₁ hz₂ hsource hcap hV hKi hlo hW₁ hW₂ key
    (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) χ Q m W second t₀ u E hselected

end
end OAI.SevenEighths.Cycle63InitialMass
