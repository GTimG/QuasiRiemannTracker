/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Extra-Newton-puncture version of the checked actual modified first packet.
Packet structure adapted from Zhongpai Gao, PR63, Apache-2.0;
source head 52419a826d4a8465cdeb56aaa2d471c489221d1d. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyMask
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths Filter CompletedGauss CenteredMomentEnergyState
open CenteredMomentFirstSourceConductorCaps
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass Record12518109Raw
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- The same actual marked packet after an extra common Newton puncture.
The polynomial cost uses the full retained NaturalState puncture bound; no
independent estimate for the assignment divisor is substituted. -/
theorem eventually_marked_packet_extra
    (η₀ : Character)
    (Bfirst Bmask bΦ : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι α Label : Type}[Fintype ι][DecidableEq ι][Fintype α][DecidableEq α][Fintype Label],
      ∀(reflected second : Bool)(s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(hη : s.η=η₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
        (datum : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
        (row : secondLiveRows (fun l=>(datum l).block))
        (hparent : (datum row.val.1).input.η=columnCharacter reflected s modifier R seed K Z ξ hK bin column)
        (hfirst : first row.val.1=firstLabel s modifier R seed K Z ξ hK bin column)
        (hR : (datum row.val.1).R≠0)(ψ : RayCharacter)(J : Ideal O)(hJ : J≠0),
      ((source s modifier R seed K Z ξ hK bin column.1).C.absNorm:ℝ)≤Z^Bfirst→
      ∀(st : NaturalState Z Bmask bΦ)(z : O)(hz : st.radial.keep z),
      st.character=(datum row.val.1).τ ψ→
      st.puncture=((datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C))*J→
      z=(if second then -row.val.2.2.2.val else row.val.2.2.2.val)→
      let left:=!reflected
      let unit:=fun l=>(fixedParentUnit left s.η l:O)
      let hf:=first_frequency_ne_zero reflected s modifier R seed K Z ξ hK bin
        column datum first row hfirst
      let rawKey:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left 1 unit hf
      let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
      let index:=(dictionaryRay reflected s modifier R seed K Z ξ hK bin column,ψ)
      let holes:=(datum row.val.1).input.η.modulus*st.puncture
      holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) ∧
      (∀I,idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index)
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I) ∧
      (Supported key.val.1.1.1 ∧ key.val.1.1.2≠0 ∧
        Supported key.val.2.1.1 ∧ key.val.2.1.2≠0) ∧
      (primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 ∧
        primeSupport key.val.2.1.1=primeSupport key.val.2.1.2) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (fixedPresentationCost*(η₀.modulus.absNorm:ℝ))] with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro ι α Label _ _ _ _ _ reflected second s modifier hη R seed K ξ hK bin column datum first row
    hparent hfirst hR ψ J hJ hnorm st z hz hchar hpuncture hrow left unit hf rawKey key index holes
  have hholes : holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) := by
    refine ⟨mul_ne_zero (datum row.val.1).input.η.modulus_ne_bot st.puncture_ne_zero,?_⟩
    have hcap:=column_modulus_cap reflected s modifier R seed K Z ξ hK bin column
    rw [←hparent,hη] at hcap
    have hZp : 0<Z:=zero_lt_one.trans hZ
    dsimp only [holes]
    simp only [map_mul,Nat.cast_mul]
    calc
      _≤(fixedPresentationCost*(η₀.modulus.absNorm:ℝ)*
          ((source s modifier R seed K Z ξ hK bin column.1).C.absNorm:ℝ)^2)*Z^Bmask :=
        mul_le_mul hcap st.puncture_bound (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)) (sq_nonneg _))
      _≤(Z*(Z^Bfirst)^2)*Z^Bmask := by gcongr
      _=Z^(1:ℝ)*(Z^Bfirst)^2*Z^Bmask := by rw [Real.rpow_one]
      _=Z^(2*Bfirst+Bmask+1) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
        congr 1
        norm_num
        ring
  have hd:=actual_natural_dictionary reflected second s modifier R seed K Z ξ hK
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
    rw [←hη]
    have hp : (datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C)≠0 := by
      apply mul_ne_zero hR
      cases second
      · exact (datum row.val.1).hC.1
      · exact (datum row.val.1).hD.1
    have he:=excluded_extra _ _ J hp hd.1 hJ hd.2 I
    have hholesJ : ((datum row.val.1).input.η.modulus*
        ((datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C)))*J=holes := by
      dsimp only [holes]
      rw [hpuncture]
      ring
    rw [hholesJ] at he
    exact he
  have hfirstSupport : Supported key.val.1.1.1 ∧ Supported key.val.1.1.2 ∧
      primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 := by
    have heq : key.val.1=firstLabel s modifier R seed K Z ξ hK bin column := by
      cases second <;> exact hfirst
    rw [heq]
    exact ⟨(source s modifier R seed K Z ξ hK bin column.1).hC,
      (source s modifier R seed K Z ξ hK bin column.1).hD,
      (source s modifier R seed K Z ξ hK bin column.1).sameSupport⟩
  refine ⟨hholes.1,hholes.2,hmask,?_,?_⟩
  · refine ⟨hfirstSupport.1,hfirstSupport.2.1.1,?_⟩
    cases second <;> exact ⟨(datum row.val.1).hC,(datum row.val.1).hD.1⟩
  · refine ⟨hfirstSupport.2.2,?_⟩
    cases second <;> exact (datum row.val.1).sameSupport

end
end QRH.Record1252270103Source.Admission.FirstFamily
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventually_marked_packet_extra
