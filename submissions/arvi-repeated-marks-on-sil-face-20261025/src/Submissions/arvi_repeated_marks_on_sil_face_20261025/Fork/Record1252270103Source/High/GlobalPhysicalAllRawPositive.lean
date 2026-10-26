/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalAllRawPositive (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllRawPositive
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularRawPositive
/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.High.ModifiedAllPositive
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance modifiedAllRawTauFinite_rm : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_modified_all_raw_family_uniform_tau_rm {α : Type} [Fintype α] [DecidableEq α]
    (ηanchor η₀ : Character)
    (sourceB sourceLam sourceCap sourceMesh : ℝ)
    (hB0 : 22/23≤sourceB) (hB1 : sourceB≤1) (hlam : 1<sourceLam) (hh0 : 0≤sourceCap) (hh1 : sourceCap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource ⟨sourceB,sourceLam,0,sourceB,0,sourceCap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (qlo Q mesh : ℝ) (hqlo : 0<qlo) (hQ : qlo≤Q)
    (hQroot : Q/12≤Broot) (hdlo : dmin≤qlo/2+δ)
    (hdsource : Q+Bmask+δ≤dmax)
    (hrlower : rmin≤wmin/dmax) (hmesh : 0≤mesh)
    (hmeshmax : mesh≤sourceMesh)
    (hmeshR : mesh≤Rwidth)
    (B loss : ℝ) (hB : 0≤B) (hQB : Q≤B) (hloss : 0<loss)
    (Smax : ℝ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧∀τ : ℝ,0<τ→τ<dmin/2→4*τ<dmin*ηw→2*τ<dmin*ηslot→
      ∀P : HighSourceParameters,P.Wslot=W→P.τ=τ→P.e=e→
      (33/50)≤P.σmin→P.σmax≤(33/50)→2*B+P.Bmask+1≤Bmask→
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(_hη : s.η=ηanchor)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=FirstFamily.columnCharacter reflected s modifier R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter)(punctureExtra : κ→Ideal O)(hExtra : ∀l,punctureExtra l≠0),
      let left := !reflected
      let unit := fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
      let hf := fun l=>FirstFamily.first_frequency_ne_zero reflected s modifier R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left 1 unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀(sector : HighSector),
        ∀(a rootError width Bbox target reserve : ℝ) (i : ℕ),
      3/4  ≤  a → a  ≤  7/8 → 0<width →0≤rootError→
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ)
        (slots : κ→Finset α)(w σ v : α→ℝ)(t : κ→ℝ)(θ : α→RayQuotient.Characters M H),
      (∀l∈labels,sector=.regular→¬(Record12518109GainWholeGeometry.wholeRegularDictionary M H hH
        (secondFixedDictionary ηanchor (FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1) →
      (∀l∈labels,sector=.fixed→(Record12518109GainWholeGeometry.wholeRegularDictionary M H hH
        (secondFixedDictionary ηanchor (FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1) →
      (∀l∈labels,sector=.tiny→ rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^qlo) →
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,0 ≤ x l 2 ∧ x l 2+width ≤ Q) →
      (sector=.regular→∀l∈labels,qlo≤x l 2) →
      (∀l∈labels,0 ≤ coeff l) → (∀l∈labels,coeff l ≤ Z^(x l 0)) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=((datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*punctureExtra l)
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l))  ≤  Z^(x l 2) ∧
        a  ≤  HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          ((3*i : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left 1 unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ)  ≤  Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^(x l 1)) →
      (i:ℝ) ≤ Z^P.τ → i ≤ I →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) →(∀j,w j≤mesh*dmin) →(∑j,w j)≤Smax →
      (∀l∈labels,∀j∈slots l,wmin≤w j) →
      (∀j,P.σmin≤σ j) →(∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      dmax*(155*ε+mesh+εm+(3/4)*ζ+η)+δ+2*binWidth*Smax≤rootError →
      binWidth≤(2*a-1)/2 →
      (∀l∈labels,retainedHighExponent (2*a-1)
        (fun q=>if sector=.regular then QRH.RepeatedMarks.Source.gainC (2*a-1) sourceB sourceLam sourceCap
          (∑j∈slots l,w j) q else sectorSharpGain sector (2*a-1) (∑j∈slots l,w j) qlo q) (x l)≤target-reserve) →
      (∑l∈labels,coeff l*Z^((2*a-1)*(x l 3-∑j∈slots l,w j))*
        (∏j∈slots l,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
          (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2)≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*(1+rawGeometryHeight Z τ I)^J*Z^(target-reserve+4*width+loss+rootError)) := by
  obtain ⟨J,Cr,hCr,hr⟩:=ModifiedRegularPositive.actual_modified_regular_raw_family_uniform_tau_rm (α:=α) M H hH
    ηanchor η₀ sourceB sourceLam sourceCap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ
    qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss Smax
  obtain ⟨Cn,hCn,hn⟩:=QRH.Record1252270103Source.NonregularRawFamily.actual_modified_nonregular_raw_family
    (α:=α) M H hH ηanchor η₀ W (33/50) (33/50) hWs hW.continuous B loss hB hloss
  refine ⟨J,Cr+Cn,add_pos hCr hCn,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes
  filter_upwards [hr τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes,
    hn P hPW hPlo hPhi] with Z hreg hnon
  refine ⟨hreg.1,?_⟩
  intro κ DataLabel _ _ reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key sector a rootError width Bbox target reserve i ha ha' hwidth hroot
    hinj labels x coeff slots w σ v t θ hregular hfixed htiny hx hq hqreg hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq hrootError hνbin hpoint
  have hZ:1<Z:=by linarith [hreg.1]
  have hZp:0≤Z:=(zero_lt_one.trans hZ).le
  have hheight0:0≤rawGeometryHeight Z τ I:=raw_geometry_height_nonneg hZp I
  have hheight1:1≤(1+rawGeometryHeight Z τ I)^J:=one_le_pow₀ (by linarith)
  by_cases hs:sector=.regular
  · subst sector
    have hh:=hreg.2 reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR
      ψ punctureExtra hExtra a rootError width Bbox target reserve i ha ha' hwidth hinj
      labels x coeff slots w σ v t θ (fun l hl=>hregular l hl rfl) hx
      (fun l hl=>⟨hqreg rfl l hl,(hq l hl).2⟩) hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow
      hzero hsupport hnorm hmissing hi hiI hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq
      hrootError hνbin (by simpa only [ite_true] using hpoint)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCn.le) (by positivity)) (Real.rpow_nonneg hZp _)
  · have hh:=hnon.2 reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR
      ψ punctureExtra hExtra sector hs (2*a-1) qlo rootError Q width Bbox target reserve
      (by linarith) (by linarith) hqlo.le hroot hQB hwidth hinj
      labels x coeff slots w σ v t θ hfixed htiny hx hq hcoeff st z hz hchar hpuncture hrow
      (fun l hl=>(hzero l hl).1) hsupport hnorm hmissing hw hσlo hσhi
      (by simpa only [if_neg hs] using hpoint)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp _)
    exact (le_add_of_nonneg_left hCr.le).trans (le_mul_of_one_le_right (add_pos hCr hCn).le hheight1)

end
end QRH.Record1252270103Source.High.ModifiedAllPositive
