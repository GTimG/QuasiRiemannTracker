import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryNaturalDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryWidth

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentNaturalRowSource CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open Cycle61FinalNatural CenteredMomentEnergyState
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

/-- The natural state used by the high-density estimate is the literal
retained state of the physical row, with the appropriate signed puncture.
This connects its keep predicate, ball majorant and fixed dictionary at once. -/
theorem actual_geometry_natural_state {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter)(Bmask : ℝ)(Q : Ideal O)
    (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤Z^Bmask)
    (m : O)(hm : m≠0)(hml : ConcretePrimeRowBridge.goodLambda∣m)(hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η ψ Q m
      (d r.val.1).block.frequency (if second then -r.val.2.2.2.val else r.val.2.2.2.val)) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let hP : puncture≠0 := mul_ne_zero hR (by
      split <;> first | exact (d r.val.1).hD.1 | exact (d r.val.1).hC.1)
    let st := retainedState Z Bmask hZ ((d r.val.1).τ ψ) Q puncture hP hPN
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let holes := (d r.val.1).input.η.modulus*puncture
    st.fixedModulus=Q ∧
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture ∧
      holes≠0 ∧ ∃hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z puncture hP st holes
  have ha : st.radial.keep z ∧ st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 := by
    cases second
    · exact actual_second_live_state_admission d r Z Bmask hZ ψ Q puncture hP hPN m hm hml hm2 hkeep
    · exact actual_second_reflected_state_admission d r Z Bmask hZ ψ Q puncture hP hPN m hm hml hm2 hkeep
  have hd := actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin j d first r hparent hfirst hR ψ
  exact ⟨rfl,rfl,hd.1,ha.1,ha.2,hd.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_natural_state
