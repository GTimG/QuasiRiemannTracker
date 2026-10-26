import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainPhysicalSelection
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 180000
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
open CenteredMomentFiniteProfileExceptional
local instance affinePhysicalSelectionSumDecidable {ι : Type*} [DecidableEq ι] :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Only the card field uses the ambient cap in the saved affine source record. -/
theorem geometry_affine_source_gates_actual_card {ι : Type*} [Fintype ι]
    (s : Input ι)(p : Profiles (1/4) (9/4))(N : ℕ)(Cs Z : ℝ)
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z) :
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z where
  card := le_rfl
  controls := caps.controls
  lower := caps.lower
  lo := caps.lo
  hi := caps.hi
  endpoints := caps.endpoints
  scales := caps.scales
  profile₁ := caps.profile₁
  profile₂ := caps.profile₂
  zero₁ := caps.zero₁
  zero₂ := caps.zero₂
  support₁ := caps.support₁
  support₂ := caps.support₂
  volume := caps.volume
  volumeLog := caps.volumeLog
  sourcePositive := caps.sourcePositive
  sourceCap := caps.sourceCap
  poolCap := caps.poolCap
  plain₁ := caps.plain₁
  plain₂ := caps.plain₂
  plain₃ := caps.plain₃
  plain₄ := caps.plain₄

variable [Cycle63.AffineLedger] in
/-- The supported allocation is selected before the complete second cost.
The original full-block filter and actual-cardinality Fourier cutoff remain literal. -/
def GeometryAffinePhysicalSelectionSpec {ι : Type} [Fintype ι] [DecidableEq ι]
    (Cs ε ξ K Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(reflected : Bool)(s : Input ι)(p : Profiles (1/4) (9/4)),
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
  ∀(R seed : Ideal O)(Mrow : ℝ),Squarefree seed → 0≤Mrow →
  ∀(amp reserve height : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
  ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
  let mass:=fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hK key j.val
  (∀{Label : Type}[Fintype Label](column : Label → rows),
    Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
      (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
    (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
    (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve
      (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
      ⟨column j,alloc j⟩)≤E) →
  let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve (9/4) height
    (Fintype.card ι) hZ key hz₁ hz₂
  let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m j.val
  let w:=fun j : selected=>geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key Mrow (Real.logb Z (volume s.toData))
    (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
  secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    (K*Z^ε)*E

variable [Cycle63.AffineLedger] in
/-- All constants and thresholds precede the live subset and source.
The caps record supplies every physical source gate of the selection theorem. -/
theorem uniform_actual_affine_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (Cs ε ξ : ℝ)(hCs : 1≤Cs)(hε : 0<ε)(hξ : 0≤ξ) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,∀T : Finset α,
      GeometryAffinePhysicalSelectionSpec (ι:=T) Cs ε ξ K Z := by
  have data (T : Finset α) := actual_geometry_main_physical_selection (α:=T)
    (Fintype.card T) Cs (9/4) ε 2 2 3 ξ 1 (1/4)
    hCs hε (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num) (by norm_num)
  choose K hK hpaid using data
  let total:=1+∑T : Finset α,K T
  have hn : ∀T : Finset α,0≤K T := fun T=>(hK T).le
  have ht : 0<total := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hn T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : K T≤total := by
    have hh:=Finset.single_le_sum (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=>hn T)
      (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total,ht,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpaid] with Z hz
  intro T
  unfold GeometryAffinePhysicalSelectionSpec
  intro hZ reflected s p caps R seed Mrow hseed hMrow amp reserve height key Ψ χ Q m W second t₀ u E hz₁ hz₂
    hKfirst rows C mass hselected selected datum w
  have hKi : (Z^Mrow)⁻¹≤Z^(2:ℝ) :=
    (inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hMrow)).trans (Real.one_le_rpow hZ.le (by norm_num))
  have hlo : (1:ℝ)≤ s.lower := le_of_eq caps.lower.symm
  have hbound := hz T hZ reflected s R seed Mrow amp reserve height caps.card caps.controls
    hseed hz₁ hz₂ caps.sourcePositive caps.sourceCap caps.volume hKi hlo
    caps.support₁ caps.support₂ key Ψ χ Q m W second t₀ u E hselected
  have hE : 0≤E := by
    have hh:=hselected (fun j : Fin 0=>Fin.elim0 j)
      (fun j k _=>Fin.elim0 j) (fun j=>Fin.elim0 j) (fun j=>Fin.elim0 j)
    simpa using hh
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hle T) (Real.rpow_nonneg (zero_lt_one.trans hZ).le ε)) hE

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
