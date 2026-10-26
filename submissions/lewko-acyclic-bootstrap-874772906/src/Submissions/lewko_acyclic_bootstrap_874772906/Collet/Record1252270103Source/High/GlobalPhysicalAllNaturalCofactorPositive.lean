/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAllNaturalRawPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCofactorLargeRaw
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.TwoCommonLargeSlotShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.VariableJointMarkedBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyNewtonPacket

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.High.ModifiedAllNaturalPositive
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
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
local instance modifiedRegularCofactorTauFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_modified_all_cofactor_family_uniform_tau {α : Type} [Fintype α] [DecidableEq α]
    (ηanchor η₀ : Character)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
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
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4)
    (qlo Q mesh : ℝ) (hqlo : 0<qlo) (hQ : qlo≤Q)
    (hQroot : Q/12≤Broot) (hdlo : dmin≤qlo/2+δ)
    (hdsource : Q+Bmask+δ≤dmax)
    (hrlower : rmin≤wmin/dmax) (hmesh : 0≤mesh)
    (hmeshmax : mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm)
    (hmeshR : mesh≤Rwidth)
    (B loss : ℝ) (hB : 0≤B) (hQB : Q≤B) (hloss : 0<loss)
    (Smax ap bp δrestore Brestore : ℝ) (hap : 0<ap) (hδrestore : 0<δrestore)
    (hBrestore : 0≤Brestore) (N : ℕ) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧∃J : ℕ,∀τ : ℝ,0<τ→τ<dmin/2→4*τ<dmin*ηw→2*τ<dmin*ηslot→
      ∀P : HighSourceParameters,P.Wslot=W→P.τ=τ→P.e=e→
      (33/50)≤P.σmin→P.σmax≤(33/50)→2*B+P.Bmask+1≤Bmask→
      P.profileBound=bound→P.B₀=2→8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
      ∃control : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,2≤Z ∧
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
        (fun q=>if sector=.regular then Record12518109Gain.gain (2*a-1)
          (∑j∈slots l,w j) q else sectorSharpGain sector (2*a-1) (∑j∈slots l,w j) qlo q) (x l)≤target-reserve) →
      ∀(ι : κ→Type)[∀l,Fintype (ι l)](schild : ∀l,Input (ι l))
        (A₁ A₂ Rchild : κ→Ideal O)(Snew Anew : Finset (Ideal O))(T : Finset α)
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
      (∀l∈labels,(schild l).X₁≤Z^(P.d*P.Rplain) ∧ (schild l).X₂≤Z^(P.d*P.Rplain) ∧
        (schild l).Y₁≤Z^(P.d*P.Rplain) ∧ (schild l).Y₂≤Z^(P.d*P.Rplain))→
      (∀l∈labels,b^2*(schild l).X₁*(schild l).X₂≤Z^Brestore)→
      (∀l∈labels,((p l).control control)^2≤Kcontrol)→
      (∀l∈labels,(schild l).X₁*(schild l).X₂≤Z^(x l 3-∑j∈T,w j))→
      (∀l∈labels,slots l=largeSlots T w wmin)→
      (∑l∈labels,‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (st l).character (t l) (z l)*
        (∏j:T,normalizedSlot (st l).character (fixedBadMask*idealGenerator (Rchild l)) 1 (z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2*coeff l)≤
      cofactorRestorationCost δrestore Brestore Z*C*Kcontrol*
        ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (1+rawGeometryHeight Z τ I)^J*
        Z^(target-reserve+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N) := by
  obtain ⟨bound,hbound,hlarge⟩:=eventual_cofactor_large_raw M H hH ap bp hap N
  obtain ⟨J,Craw,hCraw,hcount⟩:=actual_modified_all_raw_family_uniform_tau (α:=α) M H hH
    ηanchor η₀
    setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ hκβ
    qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR
    B loss hB hQB hloss Smax
  refine ⟨bound,hbound,J,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  obtain ⟨control,Ccof,hCcof,hcof⟩:=hlarge P hpeq hB₀ hslot hplain
  refine ⟨control,Ccof*Craw,mul_pos hCcof hCraw,?_⟩
  filter_upwards [hcount τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes,hcof η₀] with Z hc hfam
  refine ⟨hc.1,?_⟩
  intro κ DataLabel _ _ reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key sector a rootError width Bbox target reserve i ha ha' hwidthbin hroot0
    hinj labels x coeff slots w σ v t θ hregular hfixed htiny hx hq hqreg hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq hrootError hνbin hpoint
    ι _ schild A₁ A₂ Rchild Snew Anew T p b Kcontrol hN hb hbp hKcontrol hd hA₁ hA₂ hAR hchildpuncture
    hwidth hradial hwr havoid hW₁ hW₂ hscales hcut hcontrol hbase hlargeSlots
  have hraw:=hc.2 reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR
    ψ punctureExtra hExtra sector a rootError width Bbox target reserve i ha ha' hwidthbin hroot0 hinj
    labels x coeff slots w σ v t θ hregular hfixed htiny hx hq hqreg hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow
    hzero hsupport hnorm hmissing hi hiI hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq
    hrootError hνbin hpoint
  have hcofactor:=hfam.2 labels ι schild A₁ A₂ Rchild Snew Anew T w σ v θ st hQM hQη z hz p t
    (fun l=>x l 3) coeff a b δrestore Brestore Kcontrol wmin i hN
    (by linarith) (by linarith) hi hb hbp hδrestore hBrestore hKcontrol hd hA₁ hA₂ hAR hchildpuncture
    hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq havoid hW₁ hW₂ hscales hcut hcontrol hcoeff0 hbase
  have heq : (∑l∈labels,coeff l*Z^((2*a-1)*(x l 3-∑j∈largeSlots T w wmin,w j))*
      (∏j∈largeSlots T w wmin,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
        (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2)=
      ∑l∈labels,coeff l*Z^((2*a-1)*(x l 3-∑j∈slots l,w j))*
      (∏j∈slots l,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
        (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hlargeSlots l hl]
  rw [heq] at hcofactor
  have hZp : 0≤Z:=(zero_lt_one.trans hfam.1).le
  have hfac : 0≤cofactorRestorationCost δrestore Brestore Z*Ccof*Kcontrol*
      Z^(2*P.εplain*P.d+(2*P.εslot*P.d)*N) := by
    unfold cofactorRestorationCost
    positivity
  apply hcofactor.trans
  apply (mul_le_mul_of_nonneg_left hraw hfac).trans_eq
  simp only [Real.rpow_add (zero_lt_one.trans hfam.1)]
  ring

end
end QRH.Record1252270103Source.High.ModifiedAllNaturalPositive
#print axioms QRH.Record1252270103Source.High.ModifiedAllNaturalPositive.actual_modified_all_cofactor_family_uniform_tau
