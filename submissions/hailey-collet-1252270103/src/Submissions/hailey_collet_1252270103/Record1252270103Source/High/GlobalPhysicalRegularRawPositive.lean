/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.PositiveRadius.SomeDictionary
import Submissions.hailey_collet_1252270103.Record12518109Natural.TwoCommonLargeSlotShell
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.VariableJointMarkedBins
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyNewtonPacket

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.High.ModifiedRegularPositive
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
local instance modifiedRegularBinsExtraTauFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_modified_regular_raw_family_uniform_tau {α : Type} [Fintype α] [DecidableEq α]
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
      ∀
        (a rootError width Bbox target reserve : ℝ) (i : ℕ),
      3/4  ≤  a → a  ≤  7/8 → 0<width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ)
        (slots : κ→Finset α)(w σ v : α→ℝ)(t : κ→ℝ)(θ : α→RayQuotient.Characters M H),
      (∀l∈labels,¬(Record12518109GainWholeGeometry.wholeRegularDictionary M H hH
        (secondFixedDictionary ηanchor (FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1) →
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,qlo ≤ x l 2 ∧ x l 2+width ≤ Q) →
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
        (fun q=>QRH.Record1252270103Source.High.gain (2*a-1) sourceB sourceLam sourceCap
          (∑j∈slots l,w j) q) (x l)≤target-reserve) →
      (∑l∈labels,coeff l*Z^((2*a-1)*(x l 3-∑j∈slots l,w j))*
        (∏j∈slots l,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
          (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2)≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*(1+rawGeometryHeight Z τ I)^J*Z^(target-reserve+4*width+loss+rootError)) := by
  classical
  obtain ⟨J,Craw,hCraw,hcount⟩:=QRH.Record1252270103Source.PositiveRadius.Some.actual_dictionary_regular_raw_max_uniform_tau (Slot:=α) M H hH
    (secondFixedDictionary ηanchor) η₀
    sourceB sourceLam sourceCap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ
    qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR
  obtain ⟨Cmult,hCmult,hbins⟩:=Geometry.actual_variable_joint_marked_binned_bound B loss hB hloss
  let Cpart : ℝ:=(Fintype.card (RayCharacter×RayCharacter):ℝ)*(2:ℝ)^Fintype.card α
  have hCpart : 0<Cpart:=by dsimp [Cpart];positivity
  refine ⟨J,Cpart*Cmult*Craw,by positivity,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes
  filter_upwards [hcount τ hτ hτzero hτheight hheight,
    FirstFamily.eventually_marked_packet_extra ηanchor B P.Bmask P.bΦ,eventually_ge_atTop (2:ℝ)] with Z hc hp hZ2
  refine ⟨hZ2,?_⟩
  intro κ DataLabel _ _ reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key a rootError width Bbox target reserve i ha ha' hwidthbin
    hinj labels x coeff slots w σ v t θ hregular hx hq hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq hrootError hνbin hpoint
  have hZ : 1<Z:=by linarith
  have hzpos : 0<Z:=zero_lt_one.trans hZ
  have hδrange : (1/2:ℝ)≤2*a-1 ∧2*a-1≤3/4:=by constructor <;> linarith
  let amplitude:=labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
    (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture)
  let index:=fun l=>(FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)
  let gain:=fun (ss : Finset α)(q : ℝ)=>QRH.Record1252270103Source.High.gain (2*a-1) sourceB sourceLam sourceCap (∑j∈ss,w j) q
  let energy:=fun l=>coeff l*Z^((2*a-1)*(x l 3-∑j∈slots l,w j))*(∏j∈slots l,max 1 ‖amplitude l j‖)^2
  let Hraw:=(1+rawGeometryHeight Z τ I)^J
  have hHraw : 0<Hraw:=by
    apply pow_pos
    have hh:=raw_geometry_height_nonneg (τ:=τ) hzpos.le I
    linarith
  have hfirstcap (l : κ)(hl : l∈labels) :
      ((CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ)≤Z^B := by
    have hh:=(hnorm l hl).1
    have hk : (key l).val.1=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column l):=by
      cases second <;> exact hfirst l
    rw [hk] at hh
    exact hh
  have hpacket (l : κ)(hl : l∈labels):=hp.2 reflected second s modifier hηs R seed K ξ hK bin (column l)
    datum first (row l) (hparent l) (hfirst l) (hR l) (ψ l) (punctureExtra l) (hExtra l) (hfirstcap l hl)
    (st l) (z l) (hz l) (hchar l) (hpuncture l) (hrow l)
  let holes:=fun l=>(datum (row l).val.1).input.η.modulus*
    (st l).puncture
  have hcount' (j : RayCharacter×RayCharacter)(ss : Finset α)(rows : Finset κ)
      (hrows : rows⊆labels.filter (fun l=>index l=j ∧slots l=ss))
      (hinjrow : Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set κ))
      (q : ℝ)(hq0 : qlo≤q)(hq1 : q≤Q)
      (hrowq : ∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^q) :
      (∑l∈rows,(∏k∈ss,max 1 ‖amplitude l k‖)^2)≤
        (Craw*Hraw)*Z^(unmarkedDensity (2*a-1)*q+(2*a-1)*(∑k∈ss,w k)-gain ss q+rootError) := by
    by_cases hempty : rows=∅
    · subst rows;simp only [Finset.sum_empty];positivity
    obtain ⟨l₀,hl₀⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
    have hmem (l : κ)(hl : l∈rows):l∈labels:=(Finset.mem_filter.mp (hrows hl)).1
    have hslots : slots l₀=ss:=(Finset.mem_filter.mp (hrows hl₀)).2.2
    have hsmall (k : α)(hk : k∈ss) : wmin≤w k := by
      rw [←hslots] at hk
      exact hsmallSlots l₀ (hmem l₀ hl₀) k hk
    let χ:=fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
    have hcoeffs (l : κ)(hl : l∈rows)(L : Ideal O) : idealCoeff (χ l) L=
        idealCoeff (excluded (naturalRow (secondFixedDictionary ηanchor j)
          (nonzeroJointSourceRow (key l)).val (nonzeroJointSourceRow (key l)).property).character (holes l)) L := by
      have hh:=(hpacket l (hmem l hl)).2.2.1 L
      change idealCoeff (χ l) L=idealCoeff (excluded (naturalRow (secondFixedDictionary ηanchor (index l)) (nonzeroJointSourceRow (key l)).val (nonzeroJointSourceRow (key l)).property).character (holes l)) L at hh
      rw [(Finset.mem_filter.mp (hrows hl)).2.1] at hh
      exact hh
    let hn : ∀l∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ l) j).residue≠1:=
      fun l _=>whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _
    have hh:=hc.2 j q a i hiI ha ha' hq0 hq1 hνbin rows
      (fun l=>nonzeroJointSourceRow (key l)) hinjrow ss w σ v t θ holes χ hrowq
      (fun l hl=>by
        have hr:=hregular l (hmem l hl)
        change ¬(wholeRegularDictionary M H hH (secondFixedDictionary ηanchor (index l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1 at hr
        rw [(Finset.mem_filter.mp (hrows hl)).2.1] at hr
        exact hr)
      (fun l hl=>(hpacket l (hmem l hl)).1)
      (fun l hl=>(hpacket l (hmem l hl)).2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hholes))
      hcoeffs hn
      (fun l hl _=>by simpa only [hPτ,hPe] using hupper l (hmem l hl))
      (fun l hl _=>by simpa only [hPτ] using (hzero l (hmem l hl)).2)
      hsmall (fun k _=>hPlo.trans (hσlo k)) (fun k _=>(hσhi k).trans hPhi)
      (fun k _=>hwm k)
      (fun l hl=>by simpa only [hPτ] using hplainfreq l (hmem l hl))
      (fun l hl k _=>by simpa only [hPτ] using hfreq l (hmem l hl) k)
    have hss : (∑k∈ss,w k)≤Smax:= (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ss) (fun k _ _=>hw k)).trans hsupply
    have hρle : Record12518109Gain.rho (2*a-1)≤1 := by
      have hd : 0≤3*(5-2*(2*a-1)):=by linarith
      have hn : 0≤10*(2*a-1):=by linarith
      have hf:=div_nonneg hn hd
      unfold Record12518109Gain.rho
      linarith
    have hνζ:=mul_le_mul_of_nonneg_right hδrange.2 hζ.le
    have hroot:=mul_le_mul_of_nonneg_left hνζ (hdmin.le.trans hdmax)
    have hδloss:=mul_le_mul_of_nonneg_right hρle hδ.le
    have hbinloss:=mul_le_mul_of_nonneg_left hss (by positivity : 0≤2*binWidth)
    have hexp : dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+
        Record12518109Gain.rho (2*a-1)*δ+2*binWidth*(∑k∈ss,w k)≤rootError := by
      nlinarith only [hroot,hδloss,hbinloss,hrootError]
    simp only [←hPW,rho_eq_original] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCraw.le hHraw.le)
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    change Record12518109Gain.rho (2*a-1)*q+(2*a-1)*(∑k∈ss,w k)-gain ss q+
      dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+Record12518109Gain.rho (2*a-1)*δ+2*binWidth*(∑k∈ss,w k) ≤ _
    have hrho : Record12518109Gain.rho (2*a-1)=unmarkedDensity (2*a-1):=rfl
    rw [hrho] at hexp ⊢
    linarith only [hexp]

  have hb:=hbins left 1 unit Z hZ2 key hinj labels x energy slots index amplitude w
    (2*a-1) qlo Q width Bbox (Craw*Hraw) rootError target reserve gain hδrange.1 hδrange.2
    (mul_nonneg hCraw.le hHraw.le) hwidthbin
    (fun ss=>by intro q r hqr;exact QRH.Record1252270103Source.High.gain_mono hδrange.1 hδrange.2 hB0 hB1 hlam hh0 hh1.le le_rfl hqr)
    hx hq hpoint (fun l hl=>by
      dsimp only [energy]
      rw [Real.rpow_add hzpos]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoeff l hl) (Real.rpow_nonneg hzpos.le _)) (sq_nonneg _))
    (fun l hl=>(hzero l hl).1)
    (fun l hl=>(hzero l hl).1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(hq l hl).2])))
    (fun l hl=>(hpacket l hl).2.2.2.1) (fun l hl=>(hpacket l hl).2.2.2.2)
    hsupport hnorm hmissing (fun j ss rows hrows hinjrow q hq0 hq1 hr=>hcount' j ss rows (by
      intro l hl
      have hm : l∈labels ∧index l=j ∧slots l=ss := by
        simpa only [Finset.mem_filter] using hrows hl
      simpa only [Finset.mem_filter] using hm) hinjrow q hq0 hq1 hr)
  have heq : (Fintype.card (RayCharacter×RayCharacter):ℝ)*(2:ℝ)^Fintype.card α*
      (((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (Cmult*(Craw*Hraw)*Z^(target-reserve+4*width+loss+rootError)))=
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        ((Cpart*Cmult*Craw)*Hraw*Z^(target-reserve+4*width+loss+rootError)) := by dsimp [Cpart];ring
  exact hb.trans_eq heq

end
end QRH.Record1252270103Source.High.ModifiedRegularPositive
#print axioms QRH.Record1252270103Source.High.ModifiedRegularPositive.actual_modified_regular_raw_family_uniform_tau
