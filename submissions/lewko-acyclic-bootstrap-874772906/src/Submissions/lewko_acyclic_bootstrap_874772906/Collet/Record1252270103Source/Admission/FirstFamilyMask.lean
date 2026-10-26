/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal fixed-parent/common-mask and full-filter transport for modified first
columns followed by either retained second sign. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Dictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.GeometryMask
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths Filter CompletedGauss CenteredMomentEnergyState
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass Record12518109Raw
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- A common additional puncture transports coefficient equality including zeros. -/
lemma excluded_extra {χ ψ : Character} (P Q J : Ideal O) (hP : P≠0) (hQ : Q≠0) (hJ : J≠0)
    (he : ∀I : Ideal O,idealCoeff (excluded χ P) I=idealCoeff (excluded ψ Q) I)
    (I : Ideal O) : idealCoeff (excluded χ (P*J)) I=idealCoeff (excluded ψ (Q*J)) I := by
  have h:=he I
  rw [excluded_ideal _ _ hP,excluded_ideal _ _ hQ] at h
  rw [excluded_ideal _ _ (mul_ne_zero hP hJ),excluded_ideal _ _ (mul_ne_zero hQ hJ)]
  by_cases hc : IsCoprime I J
  · simpa only [IsCoprime.mul_right_iff,hc,and_true] using h
  · simp only [IsCoprime.mul_right_iff,hc,and_false,ite_false]

section Actual
variable {ι α Label : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype Label]
variable (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hfirst : first r.val.1=firstLabel s modifier R seed K Z ξ hK bin j)
local notation "datum" => d r.val.1
local notation "label" => firstLabel s modifier R seed K Z ξ hK bin j
local notation "unitMap" => (fun l=>(fixedParentUnit (!reflected) s.η l:O))
local notation "baseRay" => dictionaryRay reflected s modifier R seed K Z ξ hK bin j

def rawKey (second : Bool) : NonzeroJointSourceLabel (!reflected) 1 unitMap :=
  let hf:=first_frequency_ne_zero reflected s modifier R seed K Z ξ hK bin j d first r hfirst
  let key:=secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) 1 unitMap hf
  if second then reflectedNonzeroJointLabel key else key

local notation "keyOf" => rawKey reflected s modifier R seed K Z ξ hK bin j d first r hfirst

/-- All moving first and second common masks reduce to the original fixed
factor and the first missing radical. The child R relation is explicit. -/
theorem actual_common_mask
    (hparent : (datum).input.η=columnCharacter reflected s modifier R seed K Z ξ hK bin j)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) :
    let key:=keyOf second
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z];split
      · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
      · exact (datum).rows_ne _ r.val.2.2.2.property
    let puncture:=(datum).R*(if second then (datum).D else (datum).C)
    let commonMask:=geometryRawFixedMask s R*firstSourceMissing (!reflected) label
    commonMask≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character commonMask) I := by
  intro key z hz puncture commonMask
  let src:=source s modifier R seed K Z ξ hK bin j.1
  have hfixed : geometryRawFixedMask s R≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))) hR
  have hmissing:=label_missing_nonzero (!reflected) s modifier R seed K Z ξ hK bin j
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  refine ⟨mul_ne_zero hfixed hmissing,?_⟩
  intro I
  have hd:=actual_natural_dictionary reflected second s modifier R seed K Z ξ hK bin j
    d first r hparent hfirst hdR ψ
  apply (hd.2 I).trans
  change idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
    (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
      ((datum).input.η.modulus*puncture)) I=_
  have hk : key.val.1=label := by cases second <;> exact hfirst
  have hpairs : key.val.2.1=((datum).C,(datum).D) := by cases second <;> rfl
  have hc₁ : Supported key.val.1.1.1 := by rw [hk];exact src.hC
  have hd₁ : Supported key.val.1.1.2 := by rw [hk];exact src.hD
  have hs₁ : CompletedGauss.primeSupport key.val.1.1.1=CompletedGauss.primeSupport key.val.1.1.2 := by
    rw [hk];exact src.sameSupport
  have hc₂ : Supported key.val.2.1.1 := by rw [hpairs];exact (datum).hC
  have hd₂ : Supported key.val.2.1.2 := by rw [hpairs];exact (datum).hD
  have hs₂ : CompletedGauss.primeSupport key.val.2.1.1=CompletedGauss.primeSupport key.val.2.1.2 := by
    rw [hpairs];exact (datum).sameSupport
  have hm:=actual_joint_common_mask (!reflected) second 1 unitMap key hc₁ hd₁ hs₁ hc₂ hd₂ hs₂
    (secondFixedDictionary s.η (baseRay,ψ)) (naturalRow _ _ (nonzeroJointSourceRow key).property)
    (geometryRawFixedMask s R) hfixed I
  have hp : (datum).input.η.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
        activeConductor src.C src.D} := by
    rw [hparent]
    exact column_modulus reflected s modifier R seed K Z ξ hK bin j
  have hmask : (datum).input.η.modulus*puncture=
      geometryRawFixedMask s R*(Ideal.span {primeSubsetGenerator
        (fun P : CommonIndex key.val.1.1.1 key.val.1.1.2=>P.val) key.val.1.2.val*
          activeConductor key.val.1.1.1 key.val.1.1.2}*
        ((if !reflected then key.val.1.1.1 else key.val.1.1.2)*
          (if second then key.val.2.1.2 else key.val.2.1.1))) := by
    rw [hp]
    dsimp only [puncture]
    rw [hchild,hk,hpairs]
    change (s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
          activeConductor src.C src.D})*((R*(if reflected then src.D else src.C))*
            (if second then (datum).D else (datum).C))=
      (s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*R)*
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
          activeConductor src.C src.D}*((if !reflected then src.C else src.D)*
            (if second then (datum).D else (datum).C)))
    have hc : (if reflected then src.D else src.C)=(if !reflected then src.C else src.D) := by
      cases reflected <;> rfl
    rw [hc]
    ring
  rw [hmask]
  simpa only [hk,commonMask] using hm

/-- Newton assignment divisors remain an explicit common puncture on both
sides of the exact physical dictionary. -/
theorem actual_common_mask_extra
    (hparent : (datum).input.η=columnCharacter reflected s modifier R seed K Z ξ hK bin j)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) (J : Ideal O) (hJ : J≠0) :
    let key:=keyOf second
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z];split
      · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
      · exact (datum).rows_ne _ r.val.2.2.2.property
    let puncture:=((datum).R*(if second then (datum).D else (datum).C))*J
    let commonMask:=(geometryRawFixedMask s R*J)*firstSourceMissing (!reflected) label
    commonMask≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character commonMask) I := by
  intro key z hz puncture commonMask
  have hm:=actual_common_mask reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    hparent hR hchild second ψ
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  have hp : (datum).R*(if second then (datum).D else (datum).C)≠0 := by
    apply mul_ne_zero hdR
    cases second
    · exact (datum).hC.1
    · exact (datum).hD.1
  have heq : (geometryRawFixedMask s R*firstSourceMissing (!reflected) label)*J=commonMask := by
    dsimp only [commonMask]
    ring
  refine ⟨heq ▸ mul_ne_zero hm.1 hJ,?_⟩
  intro I
  have he:=excluded_extra _ _ J hp hm.1 hJ hm.2 I
  rw [heq] at he
  exact he

/-- The fixed-inducing exclusion is transported with the literal row,
including reflection; no ordinary/exceptional branch is dropped. -/
theorem actual_initialKeep
    (hparent : (datum).input.η=columnCharacter reflected s modifier R seed K Z ξ hK bin j)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) (Q : Ideal O) :
    initialKeep (secondFixedDictionary s.η (baseRay,ψ)) Q
      (nonzeroJointSourceRow (keyOf second)).val ↔
    (if second then -r.val.2.2.2.val else r.val.2.2.2.val)≠0 ∧
      ¬FixedInducingRow ((datum).τ ψ) Q fixedBadMask 1
        (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  let key:=keyOf second
  let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
  have hz : z≠0 := by
    cases second
    · exact (datum).rows_ne _ r.val.2.2.2.property
    · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
  have hm:=actual_common_mask reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    hparent hR hchild second ψ
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  have hp : (datum).R*(if second then (datum).D else (datum).C)≠0 := by
    apply mul_ne_zero hdR
    cases second
    · exact (datum).hC.1
    · exact (datum).hD.1
  exact natural_initialKeep_of_masked_ideal_eq
    (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow ((datum).τ ψ) z hz) (nonzeroJointSourceRow key).property hz
    _ _ hm.1 hp (fun I=>(hm.2 I).symm) Q

/-- Membership of the literal second ordinary row branch supplies the full
fixed-anchor initialKeep predicate for any ray index. -/
theorem actual_ordinary_keep
    (hparent : (datum).input.η=columnCharacter reflected s modifier R seed K Z ξ hK bin j)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (χ₀ ψ : RayCharacter) (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (ho : r.val.2.2.2.val∈CenteredMomentSecondEnergySplit.partRows false
      (datum).input.η χ₀ Q m (datum).C (datum).D (datum).inactive (datum).radius) :
    initialKeep (secondFixedDictionary s.η (baseRay,ψ)) Q
      (nonzeroJointSourceRow (keyOf second)).val := by
  apply (actual_initialKeep reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    hparent hR hchild second ψ Q).mpr
  have hp:=geometry_nonexceptional_reduced_pair (datum).input.η χ₀ ψ (ψ⁻¹) Q hQ
    m hm hml hm2 (datum).C (datum).D (datum).hC (datum).hD (datum).inactive
    (datum).τ (datum).family (datum).radius r.val.2.2.2.val ho
  cases second
  · exact hp.1
  · simpa only [inv_inv,ite_true] using hp.2

end Actual

/- Packet structure adapted from Zhongpai Gao, accepted PR63, Apache-2.0;
source head 52419a826d4a8465cdeb56aaa2d471c489221d1d. The labels and
characters here belong to the literal modified source. -/
/-- A geometric second row supplies a fixed-dictionary coefficient identity,
polynomial Euler holes, and both source-support gates required for weighted
joint multiplicity. The fixed dictionary does not depend on either allocation. -/
theorem eventually_marked_packet
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
        (hR : (datum row.val.1).R≠0)(ψ : RayCharacter),
      ((source s modifier R seed K Z ξ hK bin column.1).C.absNorm:ℝ)≤Z^Bfirst→
      ∀(st : NaturalState Z Bmask bΦ)(z : O)(hz : st.radial.keep z),
      st.character=(datum row.val.1).τ ψ→
      st.puncture=(datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C)→
      z=(if second then -row.val.2.2.2.val else row.val.2.2.2.val)→
      let left:=!reflected
      let unit:=fun l=>(fixedParentUnit left s.η l:O)
      let hf:=first_frequency_ne_zero reflected s modifier R seed K Z ξ hK bin
        column datum first row hfirst
      let rawKey:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left 1 unit hf
      let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
      let index:=(dictionaryRay reflected s modifier R seed K Z ξ hK bin column,ψ)
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
  filter_upwards [eventually_holes_cap η₀ Bfirst Bmask]
    with Z he
  refine ⟨he.1,?_⟩
  intro ι α Label _ _ _ _ _ reflected second s modifier hη R seed K ξ hK bin column datum first row
    hparent hfirst hR ψ hnorm st z hz hchar hpuncture hrow left unit hf rawKey key index holes
  have hholes:=he.2 reflected second s modifier hη R seed K ξ hK bin column (datum row.val.1) st
    hparent hpuncture hnorm
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
    exact hd.2 I
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
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.excluded_extra
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_common_mask

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_common_mask_extra
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_initialKeep
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_ordinary_keep

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventually_marked_packet
