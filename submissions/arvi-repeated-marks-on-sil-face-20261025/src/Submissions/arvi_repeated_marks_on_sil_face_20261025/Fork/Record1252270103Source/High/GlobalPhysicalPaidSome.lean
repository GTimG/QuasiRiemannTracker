/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalPaidSome (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalPaidSome
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Admission.SelectedHighCofactorFamilySome
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.High.ModifiedSelectedPaidSome
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record1252270103Finite PhysicalScalar HighScalar Record1252270103Source.Collision
open Cycle61HighGeometry Record1252270103CommonGeometry
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
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
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open SelectedHighPaid Pool
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance modifiedAnnularCofactorTauFinite_rm : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

set_option linter.unusedVariables false in
def FamilyStatement_rm {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource ⟨(highNode.B:ℝ),(highNode.L:ℝ),0,(highNode.B:ℝ),0,(highNode.cap:ℝ)⟩ sourceMesh εm)
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
    (loMass εmass : ℝ) (hloMass : 0<loMass) (hεmass : 0≤εmass)
    (Smax ap bp δrestore Brestore : ℝ) (hap : 0<ap) (hδrestore : 0<δrestore)
    (hBrestore : 0≤Brestore) (N : ℕ) (errv : ℝ) (herrv : 0<errv) (Bfirst Bsecond epsPref ell lower radiusMax lossMax : ℝ)
    (hBfirst:0≤Bfirst)(hBsecond:0≤Bsecond)(hepsPref:0<epsPref)
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax) : Prop :=
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧∃J : ℕ,∀τ : ℝ,0<τ→τ<dmin/2→4*τ<dmin*ηw→2*τ<dmin*ηslot→
      ∀P : HighSourceParameters,P.Wslot=W→P.τ=τ→P.e=e→
      (33/50)≤P.σmin→P.σmax≤(33/50)→2*B+P.Bmask+1≤Bmask→
      P.profileBound=bound→P.B₀=2→8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
      ∃control : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(Amark₁ Amark₂ Dmark Kmark : Ideal O)(Fmark : Ideal O→ℂ),
      let modifier:=markedSourceModifier Amark₁ Amark₂ Dmark Kmark Fmark
      ∀(_hη : s.η=ηanchor)
        (R seed : Ideal O)(Wa : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=FirstFamily.columnCharacter reflected s modifier R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter)(punctureExtra : κ→Ideal O)(hExtra : ∀l,punctureExtra l≠0),
      let left := !reflected
      let unit := fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
      let hf := fun l=>FirstFamily.first_frequency_ne_zero reflected s modifier R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left 1 unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
        ∀(choose : ∀l,Selection s reflected second
          (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l))
          (datum (row l).val.1).C (datum (row l).val.1).D R)
          (U : ∀l,Finset (CommonIndex (datum (row l).val.1).C (datum (row l).val.1).D))
          (upper bcell reserveGeom err reserveScalar δwidth : ℝ)(amp : κ→ℝ)
          (T : Finset α)(w σ v : α→ℝ)(t : κ→ℝ)(θ : α→RayQuotient.Characters M H),
        let annular:=3*(N:ℝ)*Real.logb Z upper
        let x:=fun l=>(choose l).coordinate (U l) Z D (amp l) ξ reserveGeom err errv annular w wmin T
        ∀(a rootError width Bbox : ℝ) (i : ℕ),
      3/4  ≤  a → a  ≤  7/8 → 0<width →0≤rootError→
      Function.Injective key →
      ∀(labels : Finset κ),
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,0 ≤ x l 2 ∧ x l 2+width ≤ Q) →
      Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      |Real.logb Z (volume s.toData)|≤B→loMass≤s.lower→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
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
      (∀j,P.σmin≤σ j) →(∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      dmax*(155*ε+mesh+εm+(3/4)*ζ+η)+δ+2*binWidth*Smax≤rootError →
      binWidth≤(2*a-1)/2 →
      1≤upper→s.upper≤upper→1≤s.lower→(∀j,s.P j=Z^(w j))→
      D*bcell-δwidth≤∑j,w j→(∑j,w j)≤D*bcell→
      δwidth+(N:ℝ)*wmin≤2*(D*(n.allowance:ℝ))→
      (∀l∈labels,T⊆(choose l).full)→
      0≤D→qlo=D/50→0≤err→
      Real.logb Z (volume s.toData)≤D*(sourceTReal n bcell+bcell)→
      (∀l∈labels,amp l≤D*sourceAReal n low bcell)→
      frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)→
      ActualGaps_rm n low (some highNode) bcell (2*a-1) reserveScalar→
      let schild:=fun l=>(choose l).finalInput
      ∀        (A₁ A₂ Rchild : κ→Ideal O)(Snew Anew : Finset (Ideal O))
        (p : κ→Profiles ap bp)(b Kcontrol : ℝ),
      Fintype.card α≤N→0≤b→bp≤b→0≤Kcontrol→GoodPair (newtonDivisorPair Snew Anew)→
      (∀l∈labels,A₁ l≠0)→(∀l∈labels,A₂ l≠0)→(∀l∈labels,A₁ l*A₂ l∣Rchild l)→
      (∀l∈labels,(st l).puncture=Rchild l*((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2))→
      (∀l∈labels,(st l).width≤P.Mcap)→
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0)→
      (∀j,w j/P.d≤P.Rwidth)→
      (∀j∈T,∀I∈CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)),
        IsCoprime I ((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2))→
      (∀l∈labels,(schild l).W₁=((p l).profile 0:ℝ→ℂ))→
      (∀l∈labels,(schild l).W₂=((p l).profile 1:ℝ→ℂ))→
      s.X₁≤Z^(P.d*P.Rplain)→s.X₂≤Z^(P.d*P.Rplain)→
      s.Y₁≤Z^(P.d*P.Rplain)→s.Y₂≤Z^(P.d*P.Rplain)→
      (∀l∈labels,b^2*(schild l).X₁*(schild l).X₂≤Z^Brestore)→
      (∀l∈labels,((p l).control control)^2≤Kcontrol)→
      ∀(pool : κ→Finset (Ideal O))(H0 radius poolMesh poolLoss BDpool BsourcePool : κ→ℝ)
        (depthPool : κ→ℕ)(phaseWeight : κ→ℝ),
      (∀l∈labels,((if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
        else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1).absNorm:ℝ)≤Z^Bfirst)→
      (∀l∈labels,((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)≤Z^Bsecond)→
      (∀l∈labels,FixedCellPoolData (pool l) Z (amp l) ell (poolMesh l) (poolLoss l)
        (BDpool l) (BsourcePool l) (depthPool l))→
      (∀l∈labels,0<H0 l)→(∀l∈labels,0≤radius l+6*amp l)→
      (∀l∈labels,radius l+6*amp l≤radiusMax)→(∀l∈labels,poolLoss l≤lossMax)→
      (∀l∈labels,PhaseBound s modifier R seed Wa D Z ξ (amp l) reserveGeom hK bin reflected second
        (column l) (datum (row l).val.1).C (datum (row l).val.1).D (U l) (choose l)
        (mainExtra s (if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
          else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1)
          (pool l) (H0 l) (radius l) (amp l) ell) lower (phaseWeight l))→
      (∑l∈labels,‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (st l).character (t l) (z l)*
        (∏j:T,normalizedSlot (st l).character (fixedBadMask*idealGenerator (Rchild l)) 1 (z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2*selectedPaidWeight (choose l) (phaseWeight l))≤
      (C*Z^(epsPref+lossMax)*forcedProfileCost s)*((max 1 (forcedProfileCost s))^2*(geometryHighFactor reflected (geometrySupportConstant N loMass ap ap) bin*
        cofactorRestorationCost δrestore Brestore Z*Kcontrol*
        ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (1+rawGeometryHeight Z τ I)^J*
        Z^(((1-unmarkedDensity (2*a-1))*(frequencyLoss Z 32 ξ+reserveGeom)+unmarkedDensity (2*a-1)*err+errv)-D*((n.highFee:ℝ)+reserveScalar)+(2*a-1)*annular+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N+B*εmass)))

theorem actual_selected_annular_cofactor_family_uniform_tau_rm {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource ⟨(highNode.B:ℝ),(highNode.L:ℝ),0,(highNode.B:ℝ),0,(highNode.cap:ℝ)⟩ sourceMesh εm)
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
    (loMass εmass : ℝ) (hloMass : 0<loMass) (hεmass : 0≤εmass)
    (Smax ap bp δrestore Brestore : ℝ) (hap : 0<ap) (hδrestore : 0<δrestore)
    (hBrestore : 0≤Brestore) (N : ℕ) (errv : ℝ) (herrv : 0<errv) (Bfirst Bsecond epsPref ell lower radiusMax lossMax : ℝ)
    (hBfirst:0≤Bfirst)(hBsecond:0≤Bsecond)(hepsPref:0<epsPref)
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax) :
    FamilyStatement_rm M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax := by
  obtain ⟨Cpref,hCpref,hpref⟩:=uniform_selected_paid_sum N Bfirst Bsecond epsPref ell lower radiusMax
    hBfirst hBsecond hepsPref hell hlowerPref hradiusMax
  have source := QRH.Record1252270103Source.Admission.SelectedHighCofactorFamilySome.actual_selected_annular_cofactor_family_uniform_tau_rm (α:=α) M H hH ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv
  obtain ⟨bound,hbound,J,hsource⟩:=source
  refine ⟨bound,hbound,J,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  obtain ⟨control,Csource,hCsource,hcount⟩:=hsource τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  refine ⟨control,Cpref*Csource,mul_pos hCpref hCsource,?_⟩
  filter_upwards [hcount] with Z hc
  refine ⟨hc.1,?_⟩
  intro κ DataLabel _ _ reflected second s Amark₁ Amark₂ Dmark Kmark Fmark modifier hηs R seed Wa D ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key choose U upper bcell reserveGeom err reserveScalar δwidth amp T w σ v t θ
    annular x a rootError width Bbox i ha ha' hwidthbin hroot0
    hinj labels hx hq hseed hz₁ hz₂ hsource hAbox hlower hs₁ hs₂ st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hupperZero hw hwm hsupply hσlo hσhi hfreq hplainfreq hrootError hνbin
    hu hsu hsl hwP htotallo htotalhi hwidthloss hT hD hqloD herr hA hamp hOmega hg
    schild A₁ A₂ Rchild Snew Anew p b Kcontrol hN hb hbp hKcontrol hd hA₁ hA₂ hAR hchildpuncture
    hwidth hradial hwr havoid hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hcut hcontrol
  intro pool H0 radius poolMesh poolLoss BDpool BsourcePool depthPool phaseWeight
    hcapFirst hcapSecond hpool hH0 hrad0 hrad hpoolLoss hphase
  let cost:=fun l=>‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (st l).character (t l) (z l)*
        (∏j:T,normalizedSlot (st l).character (fixedBadMask*idealGenerator (Rchild l)) 1 (z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2
  have hs := hc.2 reflected second s Amark₁ Amark₂ Dmark Kmark Fmark hηs R seed Wa D ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra choose U upper bcell reserveGeom err reserveScalar δwidth amp T w σ v t θ a rootError width Bbox i ha ha' hwidthbin hroot0 hinj labels hx hq hseed hz₁ hz₂ hsource hAbox hlower hs₁ hs₂ st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI hupperZero hw hwm hsupply hσlo hσhi hfreq hplainfreq hrootError hνbin hu hsu hsl hwP htotallo htotalhi hwidthloss hT hD hqloD herr hA hamp hOmega hg A₁ A₂ Rchild Snew Anew p b Kcontrol hN hb hbp hKcontrol hd hA₁ hA₂ hAR hchildpuncture hwidth hradial hwr havoid hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hcut hcontrol
  have hp:=hpref s hN modifier R seed Wa D Z ξ reserveGeom εmass hK bin reflected second hεmass
    labels column (fun l=>(datum (row l).val.1).C) (fun l=>(datum (row l).val.1).D)
    U choose pool amp H0 radius poolMesh poolLoss BDpool BsourcePool depthPool lossMax phaseWeight cost
    (fun l _=>(datum (row l).val.1).hC) hcapFirst hcapSecond hpool hH0 hrad0 hrad hpoolLoss hphase
    (fun _ _=>sq_nonneg _)
  apply hp.trans
  have hz:0<Z:=lt_of_lt_of_le (by norm_num) hc.1
  have hn:0≤Cpref*Z^(epsPref+lossMax)*forcedProfileCost s:=
    mul_nonneg (mul_nonneg hCpref.le (Real.rpow_nonneg hz.le _)) (forcedProfileCost_nonneg s)
  apply (mul_le_mul_of_nonneg_left hs hn).trans_eq
  ring
end
end QRH.Record1252270103Source.High.ModifiedSelectedPaidSome
