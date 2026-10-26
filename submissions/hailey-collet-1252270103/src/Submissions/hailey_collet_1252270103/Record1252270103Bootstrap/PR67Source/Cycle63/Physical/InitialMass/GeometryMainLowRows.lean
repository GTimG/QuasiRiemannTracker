import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainCostPartition
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentFirstDiscardedEnergy LocalMoment
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The original, unrestricted block fixes its common allocation and row
witness once. No nonzero ordinary or low block is required. -/
theorem actual_geometry_main_low_choices
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      ∃_rwitness : secondLiveRows (fun _:Unit=>d.block),
        frozenCoefficient B₂.val (if second then d.D else d.C) d.R
          d.input.ν d.input.W d.input.P≠0 ∧ d.inactive∈inactiveSubsets d.C d.D := by
  intro d
  obtain ⟨B₂,hB₂⟩ := actual_geometry_main_live_common_allocation
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ j second
  obtain ⟨hr,hU⟩ := actual_geometry_main_original_admission
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ j
  obtain ⟨r,hr⟩ := hr
  exact ⟨B₂,⟨r,hr⟩,hB₂,hU⟩

/-- Reflection acts only on the row and selected ray; it never requests
closure of the original finite source row set under negation. -/
def mainLowSignedRow (second : Bool) (z : O) : O := if second then -z else z

theorem main_low_signed_row_injective (second : Bool) :
    Function.Injective (mainLowSignedRow second) := by
  cases second
  · exact Function.injective_id
  · exact neg_injective

/-- Complete signed physical rows on a fixed pair of rays. The predicate
may select one literal buffered bin; no row or label multiplicity is lost. -/
def mainLowSourceRows (second : Bool) (d : SecondInputDatum α)
    (low : O→Prop) : Finset O :=
  ((secondLiveColumnRows d.block).filter (fun z=>low (mainLowSignedRow second z.val))).image
    (fun z=>mainLowSignedRow second z.val)

theorem mem_main_low_source_rows (second : Bool) (d : SecondInputDatum α)
    (low : O→Prop) (z : O) :
    z∈mainLowSourceRows second d low ↔
      ∃x∈secondLiveColumnRows d.block,mainLowSignedRow second x.val=z ∧ low z := by
  simp only [mainLowSourceRows,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hl⟩,he⟩
    exact ⟨x,hx,he,he ▸ hl⟩
  · rintro ⟨x,hx,he,hl⟩
    exact ⟨x,⟨hx,he.symm ▸ hl⟩,he⟩

theorem main_low_source_sum (second : Bool) (d : SecondInputDatum α)
    (low : O→Prop) (f : O→ℝ) :
    (∑x∈secondLiveColumnRows d.block,
      if low (mainLowSignedRow second x.val) then f (mainLowSignedRow second x.val) else 0)=
      ∑z∈mainLowSourceRows second d low,f z := by
  rw [mainLowSourceRows,Finset.sum_image]
  · exact (Finset.sum_filter _ _).symm
  · intro x _ y _ h
    exact Subtype.ext ((main_low_signed_row_injective second) h)

/-- The ordinary physical filter provides both the natural keep gate and
unit weight domination by the actual radial profile. -/
theorem actual_main_low_source_admission
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (low : O→Prop) (z : O)
    (hz : z∈mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) low) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    st.radial.keep z ∧ low z ∧
      1≤(st.radial.profile (normValue z/st.radial.scale)).re := by
  obtain ⟨x,hx,he,hl⟩ := (mem_main_low_source_rows _ _ _ _).mp hz
  have ha := actual_main_ordinary_row_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN x.val x.property
  change _ ∧ _ ∧ _
  rw [←he]
  exact ⟨ha.1,he.symm ▸ hl,ha.2⟩

variable [Cycle63.AffineLedger] in
/-- A supported row in a strict low buffered bin satisfies the genuine
whole-family low predicate, at that bin's next height. -/
theorem actual_main_low_bin_admission
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p<((1+Cycle63.AffineLedger.q)/2))
    (hweight : 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) :
    ActualLow M H hH st η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e (3*(p.1.val+1:ℕ)*T) z := by
  apply hbin.2.2.2.2.2.2.2.2.1 hlow
  intro heq
  rw [heq] at hweight
  norm_num at hweight

section Costs
variable {Label : Type*} [Fintype Label]
/-- Low filtering commutes with the exact physical row disintegration.
Each first coefficient and original-block label stays inside its own sum. -/
theorem actual_main_low_physical_cost_reindex
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→SecondInputDatum α) (coefficient : Label→ℝ) (t u : ℝ)
    (low : Label→RayCharacter→RayCharacter→O→Prop) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
      if low r.1 r.2.1 r.2.2.1 (mainLowSignedRow second r.2.2.2.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u r D else 0)=
    ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
      ∑D∈(d l).block.divisors.filter Squarefree,
        (coefficient l*((d l).K/lowerFactor N a ap)*
          normalizer (d l).C (d l).D (d l).inactive)*
        ∑z∈mainLowSourceRows second (d l) (low l χ ψ),
          ‖normalizedColumn
            (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
              ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (by cases second; exact (d l).hC; exact (d l).hD)
            (d l).R (d l).seed D z‖^2 := by
  rw [actual_second_column_reindex]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro χ _
  apply Finset.sum_congr rfl; intro ψ _
  apply Finset.sum_congr rfl; intro D _
  rw [←main_low_source_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  cases second
  · simp only [mainNormalizedPhysicalCost,mainLowSignedRow]
    split_ifs <;> simp only [mul_zero]
  · simp only [mainNormalizedPhysicalCost,mainLowSignedRow,ite_true]
    split_ifs <;> simp only [mul_zero]
end Costs
end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
