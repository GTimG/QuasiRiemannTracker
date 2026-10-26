import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowRows
import Candidate.Target836.SourceProvider.LowPaidMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCostPartition

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
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
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

theorem actual_main_low_bin_admission
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p < ((1+Named.q)/2))
    (hweight : 1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) :
    ActualLow M H hH st η₀ hQM hQη (((1+Named.q)/2)) e (3*(p.1.val+1:ℕ)*T) z := by
  have hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 := by
    intro heq
    rw [heq] at hweight
    norm_num at hweight
  apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
  change geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) < (1+Named.q)/2+2*e
  linarith [hbin.2.2.2.2.2.2.2.1]

/-- Choose actual buffered bins on every complete signed ordinary row at
this fixed ray pair. Constants and allocations are not chosen per frequency. -/
theorem actual_main_low_buffered_rows
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    ∃select : rows→BufferIndex e,∀z : rows,
      st.radial.keep z.val ∧
      1 ≤ (st.radial.profile (normValue z.val/st.radial.scale)).re ∧
      (bufferValue e (select z) < ((1+Named.q)/2) →
        ActualLow M H hH st η₀ hQM hQη (((1+Named.q)/2)) e
          (3*((select z).1.val+1:ℕ)*T) z.val) := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (ha z).1 e T he hT hβlo hβhi
  let select : rows→BufferIndex e := fun z=>Classical.choose (hp z)
  refine ⟨select,?_⟩
  intro z
  refine ⟨(ha z).1,(ha z).2.2,?_⟩
  intro hl
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z.val (ha z).1 e T
    (select z) (Classical.choose_spec (hp z)) hl
  simpa only [normValue_eq_embedding] using (ha z).2.2

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_main_low_bin_admission
#print axioms Target874836.SourceProvider.Physical.actual_main_low_buffered_rows
