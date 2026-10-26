import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.FirstDictionaryIdentity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData

/-- The signed phase and the actual ray of a selected first column. -/
def geometryDictionaryRay {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : RayCharacter :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  if reflected then firstPhaseCharacter src.C src.D src.hC
    (fun p=>6-activeExponent src.C src.D p)*j.2.2.2⁻¹
  else firstPhaseCharacter src.C src.D src.hC (activeExponent src.C src.D)*j.2.2.1

/-- What the column dictionary uses of a parent character: its modulus and its coefficients are those of an excluded
natural row of the fixed dictionary. -/
def ParentPresentation (σ : Character) {η₀ : Character} {u₀ : O} (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) : Prop :=
  σ.modulus = (excluded F₀.character R₀).modulus ∧ ∀ n : O, elementCoeff σ n = elementCoeff (excluded F₀.character R₀) n

/-- A parent equal to an excluded natural row of the fixed dictionary is presented by it. -/
theorem parentPresentation_of_eq {σ η₀ : Character} {u₀ : O} {F₀ : NaturalRow η₀ u₀} {R₀ : Ideal O}
    (h : σ = excluded F₀.character R₀) : ParentPresentation σ F₀ R₀ := by
  subst h
  exact ⟨rfl, fun _ => rfl⟩

/-- Exact dictionary identity for the physical column character, with the
unit indexed only by its arithmetic label. The parent is presented by an
excluded natural row of the fixed dictionary. -/
theorem actual_geometry_column_dictionary {ι : Type*} [Fintype ι]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : ParentPresentation s.η F₀ R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK key j))
      (u₀*(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀
        (geometryFirstLabel s R seed K Z ξ hK key j):O)*
        primeSubsetGenerator (fun p : CommonIndex
          (geometryFirstLabel s R seed K Z ξ hK key j).1.1
          (geometryFirstLabel s R seed K Z ξ hK key j).1.2=>p.val)
          (geometryFirstLabel s R seed K Z ξ hK key j).2.val*
        firstSourceNumerator (!reflected) (geometryFirstLabel s R seed K Z ξ hK key j)))
    (I : Ideal O) :
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK key j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  let l := geometryFirstLabel s R seed K Z ξ hK key j
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · have hu := Classical.choose_spec (uniform_first_left_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.left_modulus
    have hm' : F.left.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη.1] using hm
    have he := fixed_pair_left_element F
    simp only [hη.2] at he
    change idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dite_eq_left hc]
    intro G
    exact hu j.2.2.1 F.left hm' he G I
  · have hu := Classical.choose_spec (uniform_first_right_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.right_modulus
    have hm' : F.right.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη.1] using hm
    have he := fixed_pair_right_element F
    simp only [hη.2] at he
    change idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dite_eq_left hc]
    intro G
    exact hu j.2.2.2⁻¹ F.right hm' he G I

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
