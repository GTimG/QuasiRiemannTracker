/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliarySchedule
import Candidate.Uneven.AuxiliaryLowPaidMain
import Candidate.Uneven.AuxiliaryMainLowSelectedCost
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowQuantitativePayment
import Candidate.Uneven.AuxiliaryLowPaidMain
import Candidate.Uneven.AuxiliaryMainLowFull
import Candidate.Uneven.AuxiliaryMainLowNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.AuxiliaryPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.AuxiliaryLow
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment LocalMoment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowQuantitativeDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def mainLowQuantitativeFactor 
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) : ℝ :=
  Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
    (1+|v|+height)^degree*(boxCard:ℝ)*physical*Z^exponent/seedNorm



/-- Literal buffered choice on a signed ordinary source row. It depends
on the actual natural state, never on the first shell or residual ideal. -/
def mainLowCanonicalSelector 
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)→ BufferIndex e :=
  let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
    (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
  fun z=>Classical.choose (actual_geometry_zero_partition M H hH st η₀ hQM hQη z.val
    (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
      (fun _=>True) z.val z.property).1 e T he hT hβlo hβhi)


/-- The canonical choice gives all low-kernel gates at unit weight. -/
theorem actual_main_low_canonical_payment_bins 
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    let select:=mainLowCanonicalSelector  M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi
    ∀p z,z∈mainLowPaymentRows  rows select p→ 
      st.radial.keep z ∧ ActualLow M H hH st η₀ hQM hQη (((1+Sil.Uneven.AuxiliarySource.q)/2)) e (3*(p.1.val+1:ℕ)*T) z ∧
      1 ≤ (st.radial.profile (normValue z/st.radial.scale)).re ∧
      1 ≤ p.1.val ∧ p.1.val ≤ bufferCount e := by
  intro st rows select p z hz
  have ha (x : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) x.val x.property
  obtain ⟨hzrows,hsel,hlow⟩ := (mem_main_low_payment_rows  rows select p z).mp hz
  have hg:=ha ⟨z,hzrows⟩
  have hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T p := by
    have hb:=Classical.choose_spec (actual_geometry_zero_partition M H hH st η₀ hQM hQη
      z hg.1 e T he hT hβlo hβhi)
    change GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T (select ⟨z,hzrows⟩) at hb
    rw [hsel] at hb
    exact hb
  refine ⟨hg.1,?_,hg.2.2,hbin.1,hbin.2.1⟩
  apply actual_main_low_bin_admission  M H hH st η₀ hQM hQη z hg.1 e T p hbin hlow
  simpa only [normValue_eq_embedding] using hg.2.2

/-- The same literal selector on the complete physical family, before
projector shells or low/high restrictions. `Label` may already carry the
original full-block nonzero filter and one selected first allocation. -/
def mainLowFamilyCanonicalSelector  {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ₀ l) Q m).block)→BufferIndex e :=
  fun r=>mainLowCanonicalSelector  M H hH (d r.val.1) (χ₀ r.val.1) r.val.2.1 r.val.2.2.1
    Q hQ m hm hml hm2 Z Bmask hZ second (hP r.val.1) (hPN r.val.1)
    η₀ hQM hQη e T he hT hβlo hβhi
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

private theorem mainLowQuantitativeFactor_nonneg 
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ)
    (hCg : 0 ≤ Cg)(hCs : 0 ≤ Cs)(hheight : 0 ≤ height)(hphysical : 0 ≤ physical)
    (hZ : 0 < Z)(hseed : 0 ≤ seedNorm) :
    0 ≤ mainLowQuantitativeFactor  Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold mainLowQuantitativeFactor
  positivity

/-- The four first-geometry endpoint losses cost sixteen, independently
of the moving source height and of the supported arithmetic labels. -/
theorem main_low_quantitative_factor_bin_payment 
    (Cg b Cs control v height physical Z base p exponent sideLower seedNorm : ℝ)
    (N degree boxCard : ℕ) (hZ : 1 < Z)
    (hledger : p+exponent-sideLower=4*Real.logb Z 2) :
    mainLowQuantitativeFactor  Cg b Cs control v height physical Z
      (base-sideLower+p+exponent) seedNorm N degree boxCard=
      16*mainLowQuantitativeFactor  Cg b Cs control v height physical Z
        base seedNorm N degree boxCard := by
  have he : base-sideLower+p+exponent=base+4*Real.logb Z 2 := by linarith
  unfold mainLowQuantitativeFactor
  rw [he,Real.rpow_add (zero_lt_one.trans hZ),geometry_low_bin_slack_payment Z hZ]
  ring

/-- Exact complete signed low-source sum. The selector partitions a row
once, and bins with zero index are empty by the genuine admission receipt.
This structural contraction charges only the fixed buffered-bin cardinal. -/
theorem main_low_payment_complete_cost_le 
    {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hpositive : ∀r p z,z∈mainLowPaymentRows  (ordinaryRows r) (select r) p→ 1 ≤ p.1.val)
    (hbin : ∀p : BufferIndex e,1 ≤ p.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) p,value r D z)) ≤ bound) :
    (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z) < ((1+Sil.Uneven.AuxiliarySource.q)/2) then value r D z.val else 0)) ≤ 
      (Fintype.card (BufferIndex e):ℝ)*bound := by
  classical
  have heq : (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z) < ((1+Sil.Uneven.AuxiliarySource.q)/2) then value r D z.val else 0))=
      ∑p : BufferIndex e,∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) p,value r D z) := by
    calc
      _=∑r,∑D∈Ds r,∑p : BufferIndex e,coefficient r D*
          (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) p,value r D z) := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro D _
        rw [main_low_payment_complete_low_sum ,Finset.mul_sum]
      _=∑r,∑p : BufferIndex e,∑D∈Ds r,coefficient r D*
          (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) p,value r D z) := by
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  rw [heq]
  calc
    _ ≤ ∑_p : BufferIndex e,bound := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : 1 ≤ p.1.val
      · exact hbin p hp
      · have hz : ∀r,mainLowPaymentRows  (ordinaryRows r) (select r) p=∅ := by
          intro r
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hm
          exact hp (hpositive r p z hm)
        simp only [hz,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
        exact hbound
    _=_ := by simp

set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowQuantitativeBinSpec  {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ Sil.Uneven.AuxiliarySource.kappa)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0 < supply)(hev : 0 < εv)
    (hBnorm : 0 ≤ Bnorm)(hel : 0 < εlabels)
    (ap εmass Bmass : ℝ)(hap : 0 < ap)(hemass : 0 ≤ εmass)
    (U εunion : ℝ)(hUcap : 0 ≤ U)(heunion : 0 < εunion)
    (window pad : ℝ)(hwindow : 0 ≤ window)(hpad : 0 < pad)(hL0 : 0 ≤ L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α ≤ N)(hmass : ∀j,s.M j ≤ Cs)(hsupply' : supply ≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper ≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0 ≤ w j)(hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d ≤ Rwidth)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
        (hσlo : ∀j,lo ≤ σ j)(hσhi : ∀j,σ j ≤ hi)(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
        (hT : 2 < Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2 ≤ 5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin ≤ Mrow)
        (hω : 0 ≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0 ≤ ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2 ≤ Mcap)
        (hzslot : (Sil.Uneven.AuxiliarySource.widthLo)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j)) ≤ (7/250)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Sil.Uneven.AuxiliarySource.lambda*(∑j,Real.logb Z (s.P j)) ≤ 
          Sil.Uneven.AuxiliarySource.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
        let amp:=Mrow*Sil.Uneven.AuxiliarySource.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l) ≤ Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1 ≤ Tfirst)(hp : p ≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstshell : ∀l,Tfirst ≤ ((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ) < 2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ) ≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s ≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap ≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap ≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ) ≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j) ≤ window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector  M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows  (ordinaryRows r) (select r) pbin→ 1 ≤ pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*Sil.Uneven.AuxiliarySource.lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Sil.Uneven.AuxiliarySource.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor  Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        (∀pbin : BufferIndex e,1 ≤ pbin.1.val→ 
          (∑r,∑D∈Ds r,coefficient r D*
            (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) pbin,value r D z)) ≤ 
          (16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))) ∧
        mainLowCompleteSelectedCost  ordinaryRows select Ds coefficient value ≤ 
          (Fintype.card (BufferIndex e):ℝ)*((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] geometryMainNonzeroBlocks MainLowQuantitativeBinSpec mainLowCompleteSelectedCost
  actual_geometry_selected_low_full_columns

set_option maxHeartbeats 320000 in
def actual_main_low_quantitative_bins  {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ Sil.Uneven.AuxiliarySource.kappa)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0 < supply)(hev : 0 < εv)
    (hBnorm : 0 ≤ Bnorm)(hel : 0 < εlabels)
    (ap εmass Bmass : ℝ)(hap : 0 < ap)(hemass : 0 ≤ εmass)
    (U εunion : ℝ)(hUcap : 0 ≤ U)(heunion : 0 < εunion)
    (window pad : ℝ)(hwindow : 0 ≤ window)(hpad : 0 < pad)(hL0 : 0 ≤ L) (hτgap : 2*τ < d*η) (hBmassNorm : Bmass ≤ Bnorm) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0 < Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0 < Cg ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
          MainLowQuantitativeBinSpec  (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_geometry_selected_low_full_columns  (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2,eventual_main_low_payment_high_gate  e τ d η hτ hτgap] with Z hz hg
  refine ⟨hz.1,?_⟩
  unfold MainLowQuantitativeBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical
  have hsourceNorm : CenteredMomentOriginalCommonHarmonic.sourceRadius s ≤ Z^Bnorm :=
    hsourceOriginal.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBmassNorm)
  have hfirst:=actual_main_low_first_source_gates  reflected s R seed₀ (Z^Mrow) Z ξ Bnorm
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hs₀ hw₁ hw₂ hsourceNorm bin firstIndex
  have hf:=fun l=>And.intro (hfirst l).1 (hfirst l).2.1
  have heq:=fun l=>(hfirst l).2.2.1
  have hfirstseed:=fun l=>And.intro (hfirst l).2.2.2.1 (hfirst l).2.2.2.2.1
  have hfirstnorm:=fun l=>And.intro (hfirst l).2.2.2.2.2.1 (hfirst l).2.2.2.2.2.2.1
  have hscalar:=actual_geometry_low_bin_scalar_gates s R seed₀ (Z^Mrow) Z ξ Bmass
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hZ hs₀ hw₁ hw₂
    hsourceOriginal bin reflected
  have hrad := fun l=>(hscalar.2 (firstIndex l).1.val).1
  have hgeom := fun l=>(hscalar.2 (firstIndex l).1.val).2.1
  have hside := fun l=>(hscalar.2 (firstIndex l).1.val).2.2
  have hfields (r : rows) : (g r).datum=datum r ∧
      (q r).R₂*(q r).E₂=(datum r).R*(if second then (datum r).D else (datum r).C) := ⟨rfl,rfl⟩
  let st:=fun r : rows=>retainedState Z Bmask hZ ((g r).datum.τ ray) (internalQ Q η₀)
    ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
  have hst (r : rows) : st r=retainedState Z Bmask hZ
      (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ) (internalQ Q η₀)
      ((datum r).R*(if second then (datum r).D else (datum r).C))
      (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive := by
    cases second <;> rfl
  let select:=canonical
  have hselect (r : rows):=actual_main_low_canonical_payment_bins  M H hH (datum r) (χ₀ r) χ ψ
    (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
    (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
    η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
  refine ⟨select,fun _=>rfl,fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value
  have hbins : ∀pbin : BufferIndex e,1 ≤ pbin.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) pbin,value r D z)) ≤ 
      (16*factor)*(k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) := by
    intro pbin hpbin
    have hbin:=main_low_payment_height_bin  pbin hpbin heightV height (Z^τ)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hfreqbin
    have hlow : (51/100:ℝ) ≤ ((1+Sil.Uneven.AuxiliarySource.q)/2) := by norm_num [Sil.Uneven.AuxiliarySource.q]
    have hk:=hz.2 hZ s θ w σ freq heightV height mesh (((1+Sil.Uneven.AuxiliarySource.q)/2)) pbin.1.val
      hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq
      hlow (le_refl _) hbin (hg.2.2 pbin) Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff
      reflected second R seed₀ bin t firstIndex hf heq hf₁ hw₁ hw₂ hsource
      Tfirst p exponent hTfirst hp hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
      rows hU box hbox B₂ rwitness hf₂ (fun _=>ray) hP hPN
      divisorSeed hE₂ hdivisor p₀ hp₁ hp₂
      (fun r=>mainLowPaymentRows  (ordinaryRows r) (select r) pbin) (fun _ _=>(1:ℝ))
      (fun _ _ _=>zero_le_one)
      (fun r z hz=>by
        have h:=(hselect r pbin z hz)
        change (st r).radial.keep z ∧ ActualLow M H hH (st r) η₀
          (inf_le_left.trans hQM) inf_le_right (((1+Sil.Uneven.AuxiliarySource.q)/2)) e (3*(pbin.1.val+1:ℕ)*Z^τ) z
        simpa only [hst r] using (And.intro h.1 h.2.1))
      (fun r z hz=>by
        have h:=(hselect r pbin z hz).2.2.1
        change (1:ℝ) ≤ ((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re
        simpa only [hst r,normValue_eq_embedding] using h)
      Ψ hsourceOriginal hplain₁ hplain₂ sideLower hside hpool hwindowSource hplainScale
    change (∑r : rows,∑D∈Ds r,
      (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
        normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
        (∑z∈mainLowPaymentRows  (ordinaryRows r) (select r) pbin,
          (1:ℝ)*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)) ≤ 
      mainLowQuantitativeFactor  hc.1 b Cs (p₀.control k.2.1) heightV height physical Z
        ((Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)
        (seed₀.absNorm:ℝ) N k.1 box.card*
        (k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) at hk
    have hexp : (Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels=
        exponentFull-sideLower+p+exponent := by dsimp only [exponentFull];ring
    rw [hexp,main_low_quantitative_factor_bin_payment  hc.1 b Cs (p₀.control k.2.1)
      heightV height physical Z exponentFull p exponent sideLower (seed₀.absNorm:ℝ)
      N k.1 box.card hZ hscalar.1] at hk
    simpa only [one_mul] using hk

  refine ⟨hbins,?_⟩
  have hphysical : 0 ≤ physical :=
    (geometry_high_factor_pos reflected (geometrySupportConstant N supply ap ap) bin
      (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hfactor : 0 ≤ factor := mainLowQuantitativeFactor_nonneg  hc.1 b Cs (p₀.control k.2.1)
    heightV height physical Z exponentFull (seed₀.absNorm:ℝ) N k.1 box.card
    hc.2.down.1.le (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (by positivity)
  unfold mainLowCompleteSelectedCost
  exact main_low_payment_complete_cost_le  ordinaryRows select Ds coefficient value _
    (mul_nonneg (mul_nonneg (by norm_num) hfactor) (mul_nonneg k.2.2.2.1.down.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    (fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1) hbins

end
end OAI.SevenEighths.AuxiliaryPhysical
