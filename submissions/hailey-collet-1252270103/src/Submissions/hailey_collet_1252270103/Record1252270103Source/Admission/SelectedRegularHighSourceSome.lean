/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected rows enter the genuine buffered HIGH source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalPaidSome
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBufferedPaidSome
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighSource
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighSourceSome
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
local instance modifiedAnnularCofactorTauFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


open CenteredMomentAddedZeroUniform
open High.BufferedSelectedPaidSome SelectedRegularHighSource
open Cycle61Moment.LowBranch SelectedRegularSourceData SelectedRegularGeometryCaps

set_option linter.unusedVariables false in
def ModifierAt {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax) (J:ℕ)(τ:ℝ)(P:HighSourceParameters)(control:Finset (ℕ×ℕ))(C Z:ℝ) {ρ DataLabel:Type}[Nonempty ρ][Fintype DataLabel](reflected second:Bool)(s:Input α)(modifier:Tuple α→ℂ) : Prop :=
      ∀(_hη : s.η=ηanchor)
        (R seed : Ideal O)(Wa : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : ρ→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : ρ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=FirstFamily.columnCharacter reflected s modifier R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : ρ→RayCharacter)(punctureExtra : ρ→Ideal O)(hExtra : ∀l,punctureExtra l≠0),
      let left := !reflected
      let unit := fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
      let hf := fun l=>FirstFamily.first_frequency_ne_zero reflected s modifier R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left 1 unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
        ∀(choose : ∀l,Selection s reflected second
          (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l))
          (datum (row l).val.1).C (datum (row l).val.1).D R)
          (U : ∀l,Finset (CommonIndex (datum (row l).val.1).C (datum (row l).val.1).D))
          (upper bcell reserveGeom err reserveScalar δwidth : ℝ)(amp : ρ→ℝ)
          (T : Finset α)(w σ v : α→ℝ)(t : ρ→ℝ)(θ : α→RayQuotient.Characters M H),
        let annular:=3*(N:ℝ)*Real.logb Z upper
        let x:=fun l=>(choose l).coordinate (U l) Z D (amp l) ξ reserveGeom err errv annular w wmin T
        ∀(q rootError width Bbox : ℝ),
      1/2≤q → 0<width →0≤rootError→
      Function.Injective key →
      ∀(labels : Finset ρ),
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,0 ≤ x l 2 ∧ x l 2+width ≤ Q) →
      Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      |Real.logb Z (volume s.toData)|≤B→loMass≤s.lower→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
      ∀ st : ρ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : ρ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=((datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*punctureExtra l)
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^(x l 2)) →
      ∀select:ρ→BufferIndex e,
      (∀l∈labels,RetainedZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) e (Z^P.τ) (select l)) →
      (∀l∈labels,(q+1)/2≤bufferValue e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left 1 unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ)  ≤  Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^(x l 1)) →
      (∀j,0≤w j) →(∀j,w j≤mesh*dmin) →(∑j,w j)≤Smax →
      (∀j,P.σmin≤σ j) →(∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|≤Z^P.τ) →
      (∀l∈labels,|t l|≤Z^P.τ) →
      dmax*(155*ε+mesh+εm+(3/4)*ζ+η)+δ+2*binWidth*Smax≤rootError →
      binWidth≤1/4 →
      1≤upper→s.upper≤upper→1≤s.lower→(∀j,s.P j=Z^(w j))→
      D*bcell-δwidth≤∑j,w j→(∑j,w j)≤D*bcell→
      δwidth+(N:ℝ)*wmin≤2*(D*(n.allowance:ℝ))→
      (∀l∈labels,T⊆(choose l).full)→
      0≤D→qlo=D/50→0≤err→
      Real.logb Z (volume s.toData)≤D*(sourceTReal n bcell+bcell)→
      (∀l∈labels,amp l≤D*sourceAReal n low bcell)→
      frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)→
      (∀ν∈Set.Icc q (3/4),ActualGaps n low (some highNode) bcell ν reserveScalar)→
      let schild:=fun l=>(choose l).finalInput
      ∀        (A₁ A₂ Rchild : ρ→Ideal O)(Snew Anew : Finset (Ideal O))
        (p : ρ→Profiles ap bp)(b Kcontrol : ℝ),
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
      ∀(pool : ρ→Finset (Ideal O))(H0 radius poolMesh poolLoss BDpool BsourcePool : ρ→ℝ)
        (depthPool : ρ→ℕ)(phaseWeight : ρ→ℝ),
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
      ∑p∈highBins e q,
        (C*Z^(epsPref+lossMax)*forcedProfileCost s)*((max 1 (forcedProfileCost s))^2*(geometryHighFactor reflected (geometrySupportConstant N loMass ap ap) bin*
        cofactorRestorationCost δrestore Brestore Z*Kcontrol*
        ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (1+rawGeometryHeight Z τ I)^J*
        Z^(((1-unmarkedDensity (2*bufferValue e p-1))*(frequencyLoss Z 32 ξ+reserveGeom)+unmarkedDensity (2*bufferValue e p-1)*err+errv)-D*((n.highFee:ℝ)+reserveScalar)+(2*bufferValue e p-1)*annular+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N+B*εmass)))


set_option linter.unusedVariables false in
def SourceAt {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax) (J:ℕ)(τ:ℝ)(P:HighSourceParameters)(control:Finset (ℕ×ℕ))(C Z:ℝ) : Prop :=
      ∀{ρ DataLabel:Type}[Nonempty ρ][Fintype DataLabel],
      ∀(reflected second:Bool)(s:Input α)(Amark₁ Amark₂ Dmark Kmark:Ideal O)(Fmark:Ideal O→ℂ),
      ModifierAt M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax J τ P control C Z (ρ:=ρ) (DataLabel:=DataLabel) reflected second s (markedSourceModifier Amark₁ Amark₂ Dmark Kmark Fmark)

set_option linter.unusedVariables false in
def ActualAt {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax)
    (R₀:Ideal O)(hR₀:R₀≠0)(err Af ηR ηchar ηwidth:ℝ)
    (herr:0<err)(hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth)
    (hkeyBudget:SelectedSecondKeyCaps.coarseExponent Af 2 2≤B)
    (hfirstBudget:Af≤Bfirst)(hsecondBudget:2≤Bsecond)
    (hβhi:HeckeZeroSupremum.beta≤7/8) (J:ℕ)(τ:ℝ)(P:HighSourceParameters)(control:Finset (ℕ×ℕ))(C Z:ℝ) : Prop :=
      ∀{Label Row:Type}[Fintype Label](rows:Finset Row)[Nonempty rows]
        (a:SelectedRegularSourceData.Anchor α Z)(fam:SelectedRegularSourceData.Family a Label)
        (second:Bool)(g:SelectedRegularSourceData.Selected fam Row rows second),
      let reflected:=fam.reflected
      let s:=fam.s
      let modifier:=fam.modifier
      let R:=fam.R
      let seed:=fam.seed
      let D:=fam.D
      let ξ:=fam.ξ
      let hK:=fam.hK
      let bin:=fam.bin
      let column:=g.column
      let datum:=fam.datum
      let first:=fam.first
      let row:=g.row
      let key:=g.key
      let choose:=g.sel
      let U:=fun l=>(g.datum l).inactive
      let amp:=fun l=>fam.amp (g.row l).val.1.1
      let reserveGeom:=fam.reserve
      ∀(Amark₁ Amark₂ Dmark Kmark:Ideal O)(Fmark:Ideal O→ℂ),
      modifier=markedSourceModifier Amark₁ Amark₂ Dmark Kmark Fmark→s.η=ηanchor→R=R₀→
      ∀(Wa:𝓢(ℝ,ℂ))(upper bcell reserveScalar δwidth:ℝ)
        (T:Finset α)(w σ v:α→ℝ)(t:rows→ℝ)(θ:α→RayQuotient.Characters M H),
      let annular:=3*(N:ℝ)*Real.logb Z upper
      let x:=g.x err errv annular w wmin T
      ∀(q rootError width Bbox:ℝ),1/2≤q→0<width→0≤rootError→Function.Injective key→
      D=1→0≤ξ→ξ≤1→ξ≤err→0≤reserveGeom→
      (∀l,amp l=sourceAReal n low bcell)→0≤sourceAReal n low bcell→sourceFReal n low bcell≤1→
      0≤frequencyLoss Z 32 ξ+reserveGeom-err→
      sourceRadius s≤Z^Af→(∀l,sourceRadius (fam.input (g.row l).val.1.1)≤Z^(2:ℝ))→
      (∀l,fam.Tsec (g.row l).val.1.1=firstMainFourierScale reflected (Z^D) (volume s) Z ξ
        (3*amp l) reserveGeom 2 N (first (row l).val.1))→
      (g.L.absNorm:ℝ)≤Z^(4:ℝ)→fam.m≠0→fam.Q≤Ideal.span {(72:O)}→goodLambda∣fam.m→(2:O)∣fam.m→
      ∀(hQM: fam.Q≤M)(hQη:fam.Q≤η₀.modulus)
        (poolNewton Snew Anew:Finset (Ideal O))(depthNewton:ℕ)(ampNewton:ℝ),
      Snew⊆poolNewton→Anew⊆Snew→Snew.card≤depthNewton→0≤ampNewton→
      (∀p∈poolNewton,p≠0)→(∀p∈poolNewton,(p.absNorm:ℝ)≤Z^ampNewton)→
      ηR+Af+2+8+(depthNewton:ℝ)*ampNewton≤P.Bmask→
      ∃st:rows→NaturalState Z P.Bmask P.bΦ,
      ∃hfixed:∀l,(st l).fixedModulus=fam.Q,
      ∃keep:∀l,(st l).radial.keep (g.z l),
      ∃select:rows→BufferIndex e,
      (∀l,(st l).character=g.τ l ∧
        (st l).puncture=Selection.puncture (g.sel l)*((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2) ∧
        (st l).width≤P.Mcap ∧
        RetainedZeroBin M H hH (st l) η₀ ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη)
          (g.z l) (keep l) e (Z^P.τ) (select l) ∧
        (bufferValue e (select l)<(q+1)/2→ActualLow M H hH (st l) η₀
          ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη) ((q+1)/2) e
          (3*((select l).1.val+1:ℕ)*Z^P.τ) (g.z l)) ∧
        1≤((st l).radial.profile (‖eisEmbedding (g.z l)‖^2/(st l).radial.scale)).re ∧
        (st l).radial.profile (‖eisEmbedding (g.z l)‖^2/(st l).radial.scale)≠0 ∧
        SelectedSecondKeyCaps.KeyCaps (g.key l) Z B
          (Real.logb Z ((firstSourceMissing (!fam.reflected) (g.key l).val.1).absNorm:ℝ)) ∧
        rawFrequencyNorm (nonzeroJointSourceRow (g.key l))≤Z^(x l 2)) ∧
      (let labels:=Finset.univ.filter (fun l=>(q+1)/2≤bufferValue e (select l))
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,0 ≤ x l 2 ∧ x l 2+width ≤ Q) →
      |Real.logb Z (volume s.toData)|≤B→loMass≤s.lower→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
      (∀j,0≤w j) →(∀j,w j≤mesh*dmin) →(∑j,w j)≤Smax →
      (∀j,P.σmin≤σ j) →(∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|≤Z^P.τ) →
      (∀l∈labels,|t l|≤Z^P.τ) →
      dmax*(155*ε+mesh+εm+(3/4)*ζ+η)+δ+2*binWidth*Smax≤rootError →
      binWidth≤1/4 →
      1≤upper→s.upper≤upper→1≤s.lower→(∀j,s.P j=Z^(w j))→
      D*bcell-δwidth≤∑j,w j→(∑j,w j)≤D*bcell→
      δwidth+(N:ℝ)*wmin≤2*(D*(n.allowance:ℝ))→
      (∀l∈labels,T⊆(choose l).full)→
      0≤D→qlo=D/50→0≤err→
      Real.logb Z (volume s.toData)≤D*(sourceTReal n bcell+bcell)→
      (∀l∈labels,amp l≤D*sourceAReal n low bcell)→
      frequencyLoss Z 32 ξ+reserveGeom≤D*(n.allowance:ℝ)→
      (∀ν∈Set.Icc q (3/4),ActualGaps n low (some highNode) bcell ν reserveScalar)→
      let schild:=fun l=>(choose l).finalInput
      let Rchild:=fun l=>Selection.puncture (choose l)
      ∀(A₁ A₂ : rows→Ideal O)
        (p : rows→Profiles ap bp)(b Kcontrol : ℝ),
      Fintype.card α≤N→0≤b→bp≤b→0≤Kcontrol→GoodPair (newtonDivisorPair Snew Anew)→
      (∀l∈labels,A₁ l≠0)→(∀l∈labels,A₂ l≠0)→(∀l∈labels,A₁ l*A₂ l∣Rchild l)→
      (∀j,w j/P.d≤P.Rwidth)→
      (∀j∈T,∀I∈CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)),
        IsCoprime I ((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2))→
      (∀l∈labels,(schild l).W₁=((p l).profile 0:ℝ→ℂ))→
      (∀l∈labels,(schild l).W₂=((p l).profile 1:ℝ→ℂ))→
      s.X₁≤Z^(P.d*P.Rplain)→s.X₂≤Z^(P.d*P.Rplain)→
      s.Y₁≤Z^(P.d*P.Rplain)→s.Y₂≤Z^(P.d*P.Rplain)→
      (∀l∈labels,b^2*(schild l).X₁*(schild l).X₂≤Z^Brestore)→
      (∀l∈labels,((p l).control control)^2≤Kcontrol)→
      ∀(pool : rows→Finset (Ideal O))(H0 radius poolMesh poolLoss BDpool BsourcePool : rows→ℝ)
        (depthPool : rows→ℕ)(phaseWeight : rows→ℝ),
      (∀l∈labels,FixedCellPoolData (pool l) Z (amp l) ell (poolMesh l) (poolLoss l)
        (BDpool l) (BsourcePool l) (depthPool l))→
      (∀l∈labels,0<H0 l)→(∀l∈labels,0≤radius l+6*amp l)→
      (∀l∈labels,radius l+6*amp l≤radiusMax)→(∀l∈labels,poolLoss l≤lossMax)→
      (∀l∈labels,PhaseBound s modifier R seed Wa D Z ξ (amp l) reserveGeom hK bin reflected second
        (column l) (datum (row l).val.1).C (datum (row l).val.1).D (U l) (choose l)
        (mainExtra s (if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
          else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1)
          (pool l) (H0 l) (radius l) (amp l) ell) lower (phaseWeight l))→
      (∑l∈labels,‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (g.τ l) (t l) (g.z l)*
        (∏j:T,normalizedSlot (g.τ l) (fixedBadMask*idealGenerator (Rchild l)) 1 (g.z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2*selectedPaidWeight (choose l) (phaseWeight l))≤
      ∑p∈highBins e q,
        (C*Z^(epsPref+lossMax)*forcedProfileCost s)*((max 1 (forcedProfileCost s))^2*(geometryHighFactor reflected (geometrySupportConstant N loMass ap ap) bin*
        cofactorRestorationCost δrestore Brestore Z*Kcontrol*
        ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (1+rawGeometryHeight Z τ I)^J*
        Z^(((1-unmarkedDensity (2*bufferValue e p-1))*(frequencyLoss Z 32 ξ+reserveGeom)+unmarkedDensity (2*bufferValue e p-1)*err+errv)-D*((n.highFee:ℝ)+reserveScalar)+(2*bufferValue e p-1)*annular+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N+B*εmass))))

set_option linter.unusedVariables false in
def FamilyStatement {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax)
    (R₀:Ideal O)(hR₀:R₀≠0)(err Af ηR ηchar ηwidth:ℝ)
    (herr:0<err)(hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth)
    (hkeyBudget:SelectedSecondKeyCaps.coarseExponent Af 2 2≤B)
    (hfirstBudget:Af≤Bfirst)(hsecondBudget:2≤Bsecond)
    (hβhi:HeckeZeroSupremum.beta≤7/8) : Prop :=
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧∃J : ℕ,∀τ : ℝ,0<τ→τ<dmin/2→4*τ<dmin*ηw→2*τ<dmin*ηslot→
      ∀P : HighSourceParameters,P.Wslot=W→P.τ=τ→P.e=e→
      (33/50)≤P.σmin→P.σmax≤(33/50)→2*B+P.Bmask+1≤Bmask→
      P.profileBound=bound→P.B₀=2→8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
      2≤P.bΦ→4+(2*Af+ηchar)+2+ηwidth≤P.Mcap→
      ∃control : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,2≤Z ∧
      ActualAt M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax R₀ hR₀ err Af ηR ηchar ηwidth herr hηR hηchar hηwidth hkeyBudget hfirstBudget hsecondBudget hβhi J τ P control C Z

private theorem point_of_source {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax)
    (R₀:Ideal O)(hR₀:R₀≠0)(err Af ηR ηchar ηwidth:ℝ)
    (herr:0<err)(hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth)
    (hkeyBudget:SelectedSecondKeyCaps.coarseExponent Af 2 2≤B)
    (hfirstBudget:Af≤Bfirst)(hsecondBudget:2≤Bsecond)
    (hβhi:HeckeZeroSupremum.beta≤7/8) (J:ℕ)(τ:ℝ)(P:HighSourceParameters)(control:Finset (ℕ×ℕ))(C Z:ℝ)
    (hd:eventualPredicate (eventual_selected_retained_data R₀ hR₀ ηanchor 2 err ηR ηchar ηwidth N
      (by norm_num) herr hηR hηchar hηwidth) Z)
    (hg:eventualPredicate (eventual_selected_geometry_caps N) Z)
    (hZT:2<Z^P.τ)(hPphi:2≤P.bΦ)(hPwidth:4+(2*Af+ηchar)+2+ηwidth≤P.Mcap)
    (hc:SourceAt M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax J τ P control C Z) :
    ActualAt M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax R₀ hR₀ err Af ηR ηchar ηwidth herr hηR hηchar hηwidth hkeyBudget hfirstBudget hsecondBudget hβhi J τ P control C Z := by
  intro Label Row _ rows _ a fam second g reflected s modifier R seed D ξ hK bin column datum first row key choose U amp reserveGeom
    Amark₁ Amark₂ Dmark Kmark Fmark hmodifier hηs hR₀eq Wa upper bcell reserveScalar δwidth T w σ v t θ annular x
    q rootError width Bbox hqmin hwidthbin hroot0 hinj hDmain hξzero hξone hξerr hreserve hampEq hAmp0 hFone hrho
    hsourceAf hchildSource hTsec hLcap hm hQmask hml hm2 hQM hQη poolNewton Snew Anew depthNewton ampNewton
    hSnew hAnew hdepthNewton hampNewton hpoolNewton0 hpoolNewton hmaskBudget
  have geom:=hg.2 (α:=α) (Label:=Label) (Row:=Row) a fam rows second g n low bcell Amark₁ Amark₂ Dmark Kmark Fmark err errv annular w wmin T
    hmodifier hDmain hξzero hξone hreserve hampEq hAmp0 hFone hrho hchildSource hTsec
  have hZτ:2<Z^P.τ:=by exact hZT
  have hp:=hd.2 (α:=α) (Label:=Label) (Row:=Row) a fam rows second g
  have hp:=hp errv annular Af 2 2 4 2 P.Bmask P.bΦ P.Mcap ampNewton w wmin T poolNewton Snew Anew depthNewton
  have hp:=hp hR₀eq hηs hξerr hsourceAf hchildSource hTsec
  have hp:=hp (fun u=>(geom u).2.2) (fun u=>(geom u).1) (fun u=>(geom u).2.1)
  have hp:=hp hmaskBudget hPwidth hPphi hLcap hSnew hAnew hdepthNewton hampNewton hpoolNewton0 hpoolNewton
  have hp:=hp hm hQmask hml hm2 M H hH η₀ hQM hQη e (Z^P.τ) q he hZτ hqmin hβ hβhi
  obtain ⟨st,hfixed,keep,select,hdata⟩:=hp
  refine ⟨st,hfixed,keep,select,?_,?_⟩
  · intro l
    rcases hdata l with ⟨_,hchar,hpuncture,hwidth,hplateau,hprofile,hpart,hlo,_,hk,hfreq⟩
    have hk' : SelectedSecondKeyCaps.KeyCaps (g.key l) Z B (x l 1) :=
      key_caps_mono (g.key l) Z _ B _ fam.hZ hkeyBudget hk
    have hlog : Real.logb Z ((firstSourceMissing (!fam.reflected) (g.key l).val.1).absNorm:ℝ) = x l 1 := by
      rw [hk'.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans fam.hZ) fam.hZ.ne'
    have hklog : SelectedSecondKeyCaps.KeyCaps (g.key l) Z B
        (Real.logb Z ((firstSourceMissing (!fam.reflected) (g.key l).val.1).absNorm:ℝ)) := by
      rw [hlog]
      exact hk'
    exact ⟨hchar,hpuncture,hwidth,hpart,hlo,hplateau,hprofile,hklog,hfreq⟩
  intro labels hx hq hAbox hlower hs₁ hs₂
    hw hwm hsupply hσlo hσhi hfreq hplainfreq hrootError hνbin
    hu hsu hsl hwP htotallo htotalhi hwidthloss hT hD hqloD herr0 hA hamp hOmega hgaps
    schild Rchild A₁ A₂ p b Kcontrol hN hb hbp hKcontrol hpair hA₁ hA₂ hAR
    hwr havoid hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hcut hcontrol
    pool H0 radius poolMesh poolLoss BDpool BsourcePool depthPool phaseWeight hpool hH0 hradius0 hradiusMax hpoolLoss hphase
  have hchar (l):(st l).character=g.τ l:=(hdata l).2.1
  have hpuncture (l):(st l).puncture=((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*g.extra Snew Anew l:=by
    change (st l).puncture=enlargedRetainedPuncture (g.datum l) second (g.extra Snew Anew l)
    exact (hdata l).2.2.1.trans (g.selected_puncture Snew Anew l).symm
  have hkc (l):SelectedSecondKeyCaps.KeyCaps (g.key l) Z B (x l 1):=by
    rcases hdata l with ⟨_,_,_,_,_,_,_,_,_,hk,_⟩
    exact key_caps_mono (g.key l) Z _ B _ fam.hZ hkeyBudget hk
  have hcommons:=selected_common_caps fam rows second g Af Bfirst Bsecond hfirstBudget hsecondBudget hsourceAf hchildSource
  have hAfB:Af≤B:=(le_max_left _ _).trans hkeyBudget
  have hsourceCap:sourceRadius s≤Z^B:=hsourceAf.trans (Real.rpow_le_rpow_of_exponent_le fam.hZ.le hAfB)
  have hs:=hc (ρ:=rows) (DataLabel:=fam.Complete) reflected second s Amark₁ Amark₂ Dmark Kmark Fmark
  rw [←hmodifier] at hs
  have hout:=hs hηs R seed Wa D ξ hK bin column datum first row
    (fun l=>(g.structural l).1) (fun l=>(g.structural l).2.1) (fun l=>(g.structural l).2.2.2)
    g.ψ (g.extra Snew Anew) (fun l=>(hdata l).1)
  have hout:=hout choose U upper bcell reserveGeom err reserveScalar δwidth amp T w σ v t θ
    q rootError width Bbox hqmin hwidthbin hroot0 hinj labels hx hq fam.seed_sf fam.zero₁ fam.zero₂ hsourceCap
  have hout:=hout hAbox hlower hs₁ hs₂ st (fun l=>(hfixed l).trans_le hQM) (fun l=>(hfixed l).trans_le hQη)
    g.z keep hchar hpuncture (fun _=>rfl)
    (fun l _=>by rcases hdata l with ⟨_,_,_,_,_,_,_,_,_,_,hf⟩;exact hf)
    select (fun l _=>by rcases hdata l with ⟨_,_,_,_,_,_,hp,_,_,_,_⟩;exact hp)
    (fun l hl=>(Finset.mem_filter.mp hl).2)
    (fun l _=>(hkc l).2.2.1) (fun l _=>(hkc l).1) (fun l _=>(hkc l).2.2.2.2.le)
  have hout:=hout hw hwm hsupply hσlo hσhi hfreq hplainfreq hrootError hνbin
    hu hsu hsl hwP htotallo htotalhi hwidthloss hT hD hqloD herr0 hA hamp hOmega hgaps
  have hout:=hout A₁ A₂ Rchild Snew Anew p b Kcontrol hN hb hbp hKcontrol hpair hA₁ hA₂ hAR
    (fun l _=>(hdata l).2.2.1) (fun l _=>(hdata l).2.2.2.1)
    (fun l _=>by rcases hdata l with ⟨_,_,_,_,_,hp,_,_,_,_,_⟩;exact hp)
  have hout:=hout hwr havoid hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hcut hcontrol
    pool H0 radius poolMesh poolLoss BDpool BsourcePool depthPool phaseWeight
    (fun l _=>(hcommons l).1) (fun l _=>(hcommons l).2)
    hpool hH0 hradius0 hradiusMax hpoolLoss hphase
  convert hout using 1 <;> simp only [hchar,schild,annular]
  apply Finset.sum_congr rfl
  intro l hl
  apply congrArg (fun z:ℂ=>‖newtonCofactorPlain (choose l).finalInput (A₁ l) (A₂ l) (Rchild l)
    b Snew Anew (g.τ l) (t l) (g.z l)*z‖^2*selectedPaidWeight (choose l) (phaseWeight l))
  apply Finset.prod_congr
  · ext j
    simp only [Finset.mem_univ]
  · intro j hj
    rfl

theorem actual_selected_regular_high_source_uniform_tau {α : Type} [Fintype α]
    (ηanchor η₀ : Character) (n low highNode : Record1252270103Finite.Source)
    (sourceMesh : ℝ)
    (hB0 : 22/23≤(highNode.B:ℝ)) (hB1 : (highNode.B:ℝ)≤1) (hlam : 1<(highNode.L:ℝ)) (hh0 : 0≤(highNode.cap:ℝ)) (hh1 : (highNode.cap:ℝ)<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (hI : bufferCount e≤I) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
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
    (hell:0<ell)(hlowerPref:0<lower)(hradiusMax:0≤radiusMax)
    (R₀:Ideal O)(hR₀:R₀≠0)(err Af ηR ηchar ηwidth:ℝ)
    (herr:0<err)(hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth)
    (hkeyBudget:SelectedSecondKeyCaps.coarseExponent Af 2 2≤B)
    (hfirstBudget:Af≤Bfirst)(hsecondBudget:2≤Bsecond)
    (hβhi:HeckeZeroSupremum.beta≤7/8) :
    FamilyStatement M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax R₀ hR₀ err Af ηR ηchar ηwidth herr hηR hηchar hηwidth hkeyBudget hfirstBudget hsecondBudget hβhi := by
  have source := QRH.Record1252270103Source.High.BufferedSelectedPaidSome.actual_buffered_selected_cofactor_family_uniform_tau M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax
  obtain ⟨bound,hbound,J,hsource⟩:=source
  refine ⟨bound,hbound,J,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain hPphi hPwidth
  obtain ⟨control,C,hC,hcount⟩:=hsource τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  refine ⟨control,C,hC,?_⟩
  filter_upwards [hcount,eventual_selected_retained_data R₀ hR₀ ηanchor 2 err ηR ηchar ηwidth N
    (by norm_num) herr hηR hηchar hηwidth,eventual_selected_geometry_caps N,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hc hd hg hZT
  refine ⟨hc.1,?_⟩
  exact point_of_source M H hH (α:=α) ηanchor η₀ n low highNode sourceMesh hB0 hB1 hlam hh0 hh1 setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I hI δ Bmask Broot wmin hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR B loss hB hQB hloss loMass εmass hloMass hεmass Smax ap bp δrestore Brestore hap hδrestore hBrestore N errv herrv Bfirst Bsecond epsPref ell lower radiusMax lossMax hBfirst hBsecond hepsPref hell hlowerPref hradiusMax R₀ hR₀ err Af ηR ηchar ηwidth herr hηR hηchar hηwidth hkeyBudget hfirstBudget hsecondBudget hβhi J τ P control C Z hd hg (by rw [hPτ];exact hZT) hPphi hPwidth hc.2

end
end QRH.Record1252270103Source.Admission.SelectedRegularHighSourceSome
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighSourceSome.actual_selected_regular_high_source_uniform_tau
