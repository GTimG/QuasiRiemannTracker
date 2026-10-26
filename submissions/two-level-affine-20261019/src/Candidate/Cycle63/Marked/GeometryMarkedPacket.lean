import Candidate.Cycle63.Marked.DeletionGeometry
import Candidate.Cycle63.Moment.JointHighDensity

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion
open CenteredMomentCanonicalFirst Cycle63Moment
open IdealMobiusDivisorSum

/-- A geometric second row supplies a fixed-dictionary coefficient identity,
polynomial Euler holes, and both source-support gates required for weighted
joint multiplicity. The fixed dictionary does not depend on either allocation. -/
theorem eventually_geometry_marked_packet
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Bfirst Bmask bΦ : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι α Label : Type}[Fintype ι][Fintype α][DecidableEq α][Fintype Label],
      ∀(reflected second : Bool)(s : Input ι)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
        (row : secondLiveRows (fun l=>(datum l).block))
        (_hparent : (datum row.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin column)
        (hfirst : first row.val.1=geometryFirstLabel s R seed K Z ξ hK bin column)
        (_hR : (datum row.val.1).R≠0)(ψ : RayCharacter),
      ((geometryFirstSource s R seed K Z ξ hK bin column.1).C.absNorm:ℝ)≤Z^Bfirst→
      ∀(st : NaturalState Z Bmask bΦ)(z : O)(hz : st.radial.keep z),
      st.character=(datum row.val.1).τ ψ→
      st.puncture=(datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C)→
      z=(if second then -row.val.2.2.2.val else row.val.2.2.2.val)→
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf:=geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin
        column datum first row hfirst
      let rawKey:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left u₀ unit hf
      let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
      let index:=(geometryDictionaryRay reflected s R seed K Z ξ hK bin column,ψ)
      let holes:=(datum row.val.1).input.η.modulus*
        ((datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C))
      holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) ∧
      (∀I,idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index)
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I) ∧
      (Supported key.val.1.1.1 ∧ key.val.1.1.2≠0 ∧
        Supported key.val.2.1.1 ∧ key.val.2.1.2≠0) ∧
      (primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 ∧
        primeSupport key.val.2.1.1=primeSupport key.val.2.1.2) := by
  filter_upwards [Deletion26.eventually_geometry_holes_cap (excluded F₀.character R₀) Bfirst Bmask]
    with Z he
  refine ⟨he.1,?_⟩
  intro ι α Label _ _ _ _ reflected second s hη R seed K ξ hK bin column datum first row
    hparent hfirst hR ψ hnorm st z hz hchar hpuncture hrow left unit hf rawKey key index holes
  have hholes:=he.2 reflected second s hη R seed K ξ hK bin column (datum row.val.1) st
    hparent hpuncture hnorm
  have hd:=actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin column datum first row hparent hfirst hR ψ
  have hmask (I : Ideal O) :
      idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index) (nonzeroJointSourceRow key).val
        (nonzeroJointSourceRow key).property).character holes) I := by
    have transfer (χ χ' : Character) (u v : O) (hu : u≠0) (hv : v≠0)
        (hc : χ=χ') (hr : u=v) :
        (naturalRow χ u hu).character=(naturalRow χ' v hv).character := by
      subst χ';subst v;rfl
    have hv : (if second then -row.val.2.2.2.val else row.val.2.2.2.val)≠0 :=
      hrow ▸ st.row_ne_zero z hz
    rw [transfer _ _ _ _ _ hv hchar hrow,hpuncture]
    exact hd.2 I
  have hfirstSupport : Supported key.val.1.1.1 ∧ Supported key.val.1.1.2 ∧
      primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 := by
    have heq : key.val.1=geometryFirstLabel s R seed K Z ξ hK bin column := by
      cases second <;> exact hfirst
    rw [heq]
    exact ⟨(geometryFirstSource s R seed K Z ξ hK bin column.1).hC,
      (geometryFirstSource s R seed K Z ξ hK bin column.1).hD,
      (geometryFirstSource s R seed K Z ξ hK bin column.1).sameSupport⟩
  refine ⟨hholes.1,hholes.2,hmask,?_,?_⟩
  · refine ⟨hfirstSupport.1,hfirstSupport.2.1.1,?_⟩
    cases second <;> exact ⟨(datum row.val.1).hC,(datum row.val.1).hD.1⟩
  · refine ⟨hfirstSupport.2.2,?_⟩
    cases second <;> exact (datum row.val.1).sameSupport

end
end OAI.SevenEighths.Cycle63InitialMass
