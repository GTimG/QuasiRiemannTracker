import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEncodedGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoPresented
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLabelDisintegration
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A final daughter of a first-level LOW child is presented by its child multiplier in the four-ray dictionary, at the
retained state of its second-stage row. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentEnergyState
open CenteredMomentAmplificationChildInput Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondCanonicalFrequency
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A final daughter of a first-level LOW child is presented by its child multiplier in the four-ray dictionary of
`η₀` at the height `Z^τT`: the multiplier `childMultiplier` of the prefix of the row, the first label of its column and
the arithmetic label of its second block, with the unit of the column's dictionary. This holds at the retained state
of its second-stage row widened to any width `W'`. The parent of the first step is presented by an excluded natural
row of the dictionary; the column character of the first transform is then a natural row of the dictionary off its
modulus, the second datum carries the family of the column character, and the puncture is the second puncture times
the selected second ideal, whose prime support is that of the own second ideal. -/
theorem depth_two_presented_low_child (τT : ℝ) (reflected second : Bool) (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0) (s : Input α) (hη : ParentPresentation s.η F₀ R₀)
    (R seed : Ideal O) (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    let d := geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    let src := geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    ∀ (B₂ : actualAllocations src.pools (if second then d.D else d.C))
      (r : secondLiveRows (fun _:Unit=>d.block))
      (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
      (hf₂ : frozenCoefficient B₂.val (if second then d.D else d.C) d.R src.ν src.W src.P≠0)
      (χ : RayCharacter) (Bmask : ℝ) (Q : Ideal O),
    let chain := geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let g := geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
      r hf₁ hf₂
    ∀ (hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤Z^Bmask) (W' : ℝ)
      (hW' : (retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (chain.R₂*chain.E₂) hP hPN g.datum.radius
        g.datum.C g.datum.D g.datum.inactive).width≤W'),
    DepthTwoPresented τT η₀ Z (LowBranch.widenState (retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀)
        (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive) W' hW')
      (childMultiplier (!reflected) u₀ (fun l => (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O))
        ⟨geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val,
          actualSecondArithmeticLabel _ _ _ _ _ _ _ n⟩) (Z^τT) := by
  intro d src B₂ r hf₁ hf₂ χ Bmask Q chain g hP hPN W' hW'
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let l := geometryFirstLabel s R seed (Z^Mrow) Z ξ hK bin q.1.val
  let w₁ := u₀*(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)*
    primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val*firstSourceNumerator (!reflected) l
  have hl : Supported l.1.1 := (geometryFirstSource s R seed (Z^Mrow) Z ξ hK bin q.1.val.1).hC
  have hw₁0 : w₁≠0 := by
    apply mul_ne_zero _ (first_source_numerator_ne_zero _ l hl)
    apply mul_ne_zero (mul_ne_zero hu₀ (Units.ne_zero _))
    exact Ideal.span_singleton_eq_bot.not.mp (subsetGenerator_supported _ _ hl l.2.val).1
  have hGV : commonFrequencyGenerator d.C d.D*nonunitFrequencyGenerator d.C d.D d.inactive≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero _ _ d.hC) (nonunitFrequencyGenerator_ne_zero _ _ d.hC _)
  unfold DepthTwoPresented
  refine ⟨⟨le_refl _,le_refl _⟩,(geometryDictionaryRay reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val,χ),d.input.η,w₁,
    d.C,d.D,d.hC,d.hD,d.inactive,d.τ,⟨naturalRow _ w₁ hw₁0,fun I=>?_⟩,d.sameSupport,d.family,rfl,
    mul_ne_zero hw₁0 hGV,rfl,?_⟩
  · exact actual_geometry_column_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed (Z^Mrow) Z ξ hK bin q.1.val
      (naturalRow _ w₁ hw₁0) I
  · intro I hI
    change IsCoprime I (d.R*(if second then d.D else d.C)) at hI
    cases second
    · exact hI.of_mul_right_right
    · exact isCoprime_of_primeSupport_eq d.hC.1 d.sameSupport hI.of_mul_right_right

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
