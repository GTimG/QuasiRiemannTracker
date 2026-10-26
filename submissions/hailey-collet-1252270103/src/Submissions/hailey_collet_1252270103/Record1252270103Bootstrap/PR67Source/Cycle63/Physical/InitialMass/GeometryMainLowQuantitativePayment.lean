import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowFull
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowQuantitativeDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable [Cycle63.AffineLedger] in
/-- Literal buffered choice on a signed ordinary source row. It depends
on the actual natural state, never on the first shell or residual ideal. -/
def mainLowCanonicalSelector
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)→ BufferIndex e :=
  let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
    (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
  fun z=>Classical.choose (actual_geometry_zero_partition M H hH st η₀ hQM hQη z.val
    (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
      (fun _=>True) z.val z.property).1 e T he hT hβlo hβhi)

variable [Cycle63.AffineLedger] in
/-- The canonical index retains the full buffered zero-bin certificate,
so high and low consumers share one literal partition. -/
theorem actual_main_low_canonical_zero_bin
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    ∀z : mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True),
      GeometryZeroBin M H hH st η₀ hQM hQη z.val
        (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
          (fun _=>True) z.val z.property).1 e T
        (mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
          hP hPN η₀ hQM hQη e T he hT hβlo hβhi z) := by
  intro st z
  exact Classical.choose_spec (actual_geometry_zero_partition M H hH st η₀ hQM hQη z.val
    (actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second hP hPN
      (fun _=>True) z.val z.property).1 e T he hT hβlo hβhi)

variable [Cycle63.AffineLedger] in
/-- The canonical choice gives all low-kernel gates at unit weight. -/
theorem actual_main_low_canonical_payment_bins
    (d : SecondInputDatum α) (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    let select:=mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi
    ∀p z,z∈mainLowPaymentRows rows select p→ 
      st.radial.keep z ∧ ActualLow M H hH st η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e (3*(p.1.val+1:ℕ)*T) z ∧
      1≤(st.radial.profile (normValue z/st.radial.scale)).re ∧
      1≤p.1.val ∧ p.1.val≤bufferCount e := by
  intro st rows select p z hz
  have ha (x : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) x.val x.property
  obtain ⟨hzrows,hsel,hlow⟩ := (mem_main_low_payment_rows rows select p z).mp hz
  have hg:=ha ⟨z,hzrows⟩
  have hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T p := by
    have hb:=Classical.choose_spec (actual_geometry_zero_partition M H hH st η₀ hQM hQη
      z hg.1 e T he hT hβlo hβhi)
    change GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T (select ⟨z,hzrows⟩) at hb
    rw [hsel] at hb
    exact hb
  refine ⟨hg.1,?_,hg.2.2,hbin.1,hbin.2.1⟩
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z hg.1 e T p hbin hlow
  simpa only [normValue_eq_embedding] using hg.2.2

variable [Cycle63.AffineLedger] in
/-- The same literal selector on the complete physical family, before
projector shells or low/high restrictions. `Label` may already carry the
original full-block nonzero filter and one selected first allocation. -/
def mainLowFamilyCanonicalSelector {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ₀ l) Q m).block)→BufferIndex e :=
  fun r=>mainLowCanonicalSelector M H hH (d r.val.1) (χ₀ r.val.1) r.val.2.1 r.val.2.2.1
    Q hQ m hm hml hm2 Z Bmask hZ second (hP r.val.1) (hPN r.val.1)
    η₀ hQM hQη e T he hT hβlo hβhi
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

/-- The first-geometry endpoint losses cost sixty-four, independently
of the moving source height and of the supported arithmetic labels. -/
theorem main_low_quantitative_factor_bin_payment
    (Cg b Cs control v height physical Z base p exponent sideLower seedNorm : ℝ)
    (N degree boxCard : ℕ) (hZ : 1<Z)
    (hledger : p+exponent-sideLower=6*Real.logb Z 2) :
    mainLowQuantitativeFactor Cg b Cs control v height physical Z
      (base-sideLower+p+exponent) seedNorm N degree boxCard=
      64*mainLowQuantitativeFactor Cg b Cs control v height physical Z
        base seedNorm N degree boxCard := by
  have he : base-sideLower+p+exponent=base+6*Real.logb Z 2 := by linarith
  unfold mainLowQuantitativeFactor
  rw [he,Real.rpow_add (zero_lt_one.trans hZ),geometry_low_bin_slack_six_payment Z hZ]
  ring

variable [Cycle63.AffineLedger] in
/-- The complete selected scalar cost, staged independently of physical
block types so the public receipt does not normalize their ancestry. -/
def mainLowCompleteSelectedCost {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) : ℝ :=
  ∑r,∑D∈Ds r,coefficient r D*
    (∑z : ordinaryRows r,if bufferValue e (select r z)<((1+Cycle63.AffineLedger.q)/2) then value r D z.val else 0)

variable [Cycle63.AffineLedger] in
/-- Exact complete signed low-source sum. The selector partitions a row
once, and bins with zero index are empty by the genuine admission receipt.
This structural contraction charges only the fixed buffered-bin cardinal. -/
theorem main_low_payment_complete_cost_le
    {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) (bound : ℝ) (hbound : 0≤bound)
    (hpositive : ∀r p z,z∈mainLowPaymentRows (ordinaryRows r) (select r) p→ 1≤p.1.val)
    (hbin : ∀p : BufferIndex e,1≤p.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z))≤bound) :
    (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z)<((1+Cycle63.AffineLedger.q)/2) then value r D z.val else 0))≤
      (Fintype.card (BufferIndex e):ℝ)*bound := by
  classical
  have heq : (∑r,∑D∈Ds r,coefficient r D*
      (∑z : ordinaryRows r,
        if bufferValue e (select r z)<((1+Cycle63.AffineLedger.q)/2) then value r D z.val else 0))=
      ∑p : BufferIndex e,∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
    calc
      _=∑r,∑D∈Ds r,∑p : BufferIndex e,coefficient r D*
          (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun D _ => ?_
        rw [main_low_payment_complete_low_sum,Finset.mul_sum]
      _=∑r,∑p : BufferIndex e,∑D∈Ds r,coefficient r D*
          (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) p,value r D z) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  rw [heq]
  calc
    _≤∑_p : BufferIndex e,bound := by
      refine Finset.sum_le_sum fun p _ => ?_
      by_cases hp : 1≤p.1.val
      · exact hbin p hp
      · have hz : ∀r,mainLowPaymentRows (ordinaryRows r) (select r) p=∅ := by
          intro r
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hm
          exact hp (hpositive r p z hm)
        simp only [hz,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
        exact hbound
    _=_ := by simp

variable [Cycle63.AffineLedger] in
set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowQuantitativeBinSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)
        (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Lslot)
        (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
        (hT : 2<Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (unit Mrow reserve ξ : ℝ)(hMmin : Mmin≤unit)(hAdm : Adm unit (frequencyLoss Z 32 ξ+reserve) ξ)
        (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
        (hzslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
        (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
          Cycle63.AffineLedger.B*unit)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
        let amp:=unit*Cycle63.AffineLedger.amp cell
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
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1≤Tfirst)(hp : p≤Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstproj : ∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val)
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
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
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let st:=fun r : rows=>retainedState Z Bmask hZ ((g r).datum.τ ray) (internalQ Q η₀)
          ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
        ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
        left₁=!reflected → u₀≠0 →
        ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
        let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
        (∀r,∀(W' : ℝ)(hW' : (st r).width≤W'),Presented η₀ Z (widenState (st r) W' hW') (mult r) Tz) →
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin→ 1≤pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        (∀pbin : BufferIndex e,1≤pbin.1.val→ 
          (∑r,∑D∈Ds r,coefficient r D*
            (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,value r D z))≤
          (64*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))) ∧
        mainLowCompleteSelectedCost ordinaryRows select Ds coefficient value≤
          (Fintype.card (BufferIndex e):ℝ)*((64*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] geometryMainNonzeroBlocks MainLowQuantitativeBinSpec mainLowCompleteSelectedCost
  actual_geometry_selected_low_full_columns

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 320000 in
def actual_main_low_quantitative_bins {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (hrow5 : LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs supply εv Bnorm εlabels Adm labelExp (Presented Bmask))
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) (hτgap : 2*τ<d*η) (hBmassNorm : Bmass≤Bnorm) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
      Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
        PLift (0<Cu) ×
        ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          MainLowQuantitativeBinSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z) := by
  intro η₀ Q hQM hQ0 hQt hQ72
  let k:=actual_geometry_selected_low_full_columns (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel hrow5
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  let hc:=k.2.2.2.2
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2,eventual_main_low_payment_high_gate e τ d η hτ hτgap] with Z hz hg
  refine ⟨hz.1,?_⟩
  unfold MainLowQuantitativeBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p _ _ _ hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstproj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray st leftR uR unitR Tz hleft hu₀ hdict _ hpres ordinaryRows canonical
  have hsourceNorm : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bnorm :=
    hsourceOriginal.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBmassNorm)
  have hfirst:=actual_main_low_first_source_gates reflected s R seed₀ (Z^Mrow) Z ξ Bnorm
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hs₀ hw₁ hw₂ hsourceNorm bin firstIndex
  have hf:=fun l=>And.intro (hfirst l).1 (hfirst l).2.1
  have heq:=fun l=>(hfirst l).2.2.1
  have hfirstseed:=fun l=>And.intro (hfirst l).2.2.2.1 (hfirst l).2.2.2.2.1
  have hfirstnorm:=fun l=>And.intro (hfirst l).2.2.2.2.2.1 (hfirst l).2.2.2.2.2.2.1
  obtain ⟨expo,sideLo,hslack,hscalar⟩:=hgate s R seed₀ (Z^Mrow) Z ξ Bmass
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hZ hs₀ hw₁ hw₂
    hsourceOriginal bin reflected
  have hrad := fun l=>(hscalar (firstIndex l).1.val).1
  have hgeom := fun l=>(hscalar (firstIndex l).1.val).2.1
  have hside := fun l=>(hscalar (firstIndex l).1.val).2.2
  have hfields (r : rows) : (g r).datum=datum r ∧
      (q r).R₂*(q r).E₂=(datum r).R*(if second then (datum r).D else (datum r).C) := ⟨rfl,rfl⟩
  have hst (r : rows) : st r=retainedState Z Bmask hZ
      (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ) (internalQ Q η₀)
      ((datum r).R*(if second then (datum r).D else (datum r).C))
      (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive := by
    cases second <;> rfl
  let select:=canonical
  have hselect (r : rows):=actual_main_low_canonical_payment_bins M H hH (datum r) (χ₀ r) χ ψ
    (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
    (by rw [←(hfields r).2];exact hP r) (by rw [←(hfields r).2];exact hPN r)
    η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
  refine ⟨select,fun _=>rfl,fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value
  have hbins : ∀pbin : BufferIndex e,1≤pbin.1.val→ 
      (∑r,∑D∈Ds r,coefficient r D*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,value r D z))≤
      (64*factor)*(k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) := by
    intro pbin hpbin
    have hbin:=main_low_payment_height_bin pbin hpbin heightV height (Z^τ)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hfreqbin
    have hlow : (51/100:ℝ)≤((1+Cycle63.AffineLedger.q)/2) := by linarith [Cycle63.AffineLedger.one_fiftieth_le_q]
    have hk:=hz.2 hZ s θ w σ freq heightV height mesh (((1+Cycle63.AffineLedger.q)/2)) pbin.1.val
      hcard hmass hsupply' hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq
      hlow (le_refl _) hbin (hg.2.2 pbin) unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff
      reflected second R seed₀ bin t firstIndex hf heq hf₁ hw₁ hw₂ hsource
      Tfirst p expo hTfirst hp hs₀ hs₀0 hinj hfirstseed hfirstproj hfirstnorm hrad hgeom hfirstshell
      rows hU box hbox B₂ rwitness hf₂ (fun _=>ray) hP hPN leftR uR unitR Tz hleft hu₀ hdict hpres
      divisorSeed hE₂ hdivisor p₀ hp₁ hp₂
      (fun r=>mainLowPaymentRows (ordinaryRows r) (select r) pbin) (fun _ _=>(1:ℝ))
      (fun _ _ _=>zero_le_one)
      (fun r z hz=>by
        have h:=(hselect r pbin z hz)
        change (st r).radial.keep z ∧ ActualLow M H hH (st r) η₀
          (inf_le_left.trans hQM) inf_le_right (((1+Cycle63.AffineLedger.q)/2)) e (3*(pbin.1.val+1:ℕ)*Z^τ) z
        simpa only [hst r] using (And.intro h.1 h.2.1))
      (fun r z hz=>by
        have h:=(hselect r pbin z hz).2.2.1
        change (1:ℝ)≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re
        simpa only [hst r,normValue_eq_embedding] using h)
      Ψ hsourceOriginal hplain₁ hplain₂ sideLo hside hpool hwindowSource hplainScale
    change (∑r : rows,∑D∈Ds r,
      (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
        normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
        (∑z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin,
          (1:ℝ)*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      mainLowQuantitativeFactor hc.1 b Cs (p₀.control k.2.1) heightV height physical Z
        ((Bmass*εmass-sideLo)+amp+p+expo+error+εv+Bnorm*εshell+εlabels)
        (seed₀.absNorm:ℝ) N k.1 box.card*
        (k.2.2.1*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) at hk
    have hexp : (Bmass*εmass-sideLo)+amp+p+expo+error+εv+Bnorm*εshell+εlabels=
        exponentFull-sideLo+p+expo := by dsimp only [exponentFull];ring
    rw [hexp,main_low_quantitative_factor_bin_payment hc.1 b Cs (p₀.control k.2.1)
      heightV height physical Z exponentFull p expo sideLo (seed₀.absNorm:ℝ)
      N k.1 box.card hZ hslack] at hk
    simpa only [one_mul] using hk

  refine ⟨hbins,?_⟩
  have hphysical : 0≤physical :=
    (geometry_high_factor_pos reflected (geometrySupportConstant N supply ap ap) bin
      (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hfactor : 0≤factor := mainLowQuantitativeFactor_nonneg hc.1 b Cs (p₀.control k.2.1)
    heightV height physical Z exponentFull (seed₀.absNorm:ℝ) N k.1 box.card
    hc.2.down.1.le (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (by positivity)
  unfold mainLowCompleteSelectedCost
  exact main_low_payment_complete_cost_le ordinaryRows select Ds coefficient value _
    (mul_nonneg (mul_nonneg (by norm_num) hfactor) (mul_nonneg k.2.2.2.1.down.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    (fun r pbin z hz=>(hselect r pbin z hz).2.2.2.1) hbins

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
