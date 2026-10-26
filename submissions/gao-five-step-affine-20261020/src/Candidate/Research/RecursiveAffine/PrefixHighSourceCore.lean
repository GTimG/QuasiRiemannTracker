/- The cut of the producer of the HIGH given at a fixed slot type: the conclusion of the top transport theorem and the
body of the HIGH given. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrefixHighSourceRows
import Candidate.Research.RecursiveAffine.PrefixHighSourceGiven
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighPayment

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RecursiveHighProvider
noncomputable section
open Cycle153HighProvider
variable {Base : Type} {base : HeckeFamily.Character → Base → HeckeFamily.Character}
open Cycle63MarkedPlain Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondInputCapacitySource
open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
attribute [local instance] geometryAffineHighPaymentSumDecidable

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
include M H hH in
set_option linter.unusedVariables false in
/-- The transport bound of the canonical HIGH rows of a parent with slots `ι` at the base `Z`, at small heights, in
the form of the top transport theorem without payment data. -/
def AffineHighTopInner {ι : Type} [Fintype ι] [DecidableEq ι] (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (W : ℝ→ℂ) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (e τ : ℝ) (he : 0<e) (μ Cs ρ δ qh : ℝ) (Nbudget : ℕ) (Sp : Finset (ℕ×ℕ)) (K Kt : ℝ)
    (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input ι)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : ι→RayQuotient.Characters M H)(w σ freq : ι→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)(hRcap : (R.absNorm:ℝ)≤Z^ρ)
    (hMrow : 0≤Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16)
    (height mesh : ℝ)(hw : ∀j,0≤w j)
    (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (μ/8))
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)(hT : 2<Z^τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t amp : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
  let first:=fun l=>geometryFirstLabel s R seed (Z^Mrow) Z (μ/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
  let omega:=frequencyLoss Z 32 (μ/64)+μ/8
  ∀(hamp0 : 0≤amp)(hamp : |amp|≤4)(homega : |omega|≤4)
    (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
  let rows:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (μ/64) (μ/8)
    (9/4) t (Fintype.card ι) hZ bin caps.zero₁ caps.zero₂ firstIndex
  let datum : rows→SecondInputDatum ι:=fun r=>geometryLowSecondDatum reflected s R seed Z Mrow amp
    (μ/64) (μ/8) (9/4) t (Fintype.card ι) hZ bin (firstIndex r.val.1)
    caps.zero₁ caps.zero₂ r.val.2
  ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
    (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
  |t|+height+2*Real.pi*(|u|+|t₀|)≤Z^τ →
  ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
  ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
  let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
    mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
      m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
      (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
  let firstMass:=fun l=>geometryFirstHighMass reflected s R seed Ψ Mrow Z (μ/64) δ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
  let childSrc:=fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
  let ordinary:=fun r=>ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
  let coefficient:=fun r=>firstMass r.val.1/volume (childSrc r.val.1)
  let select:=mainPhysicalFamilySelector second ordinary canonical
  let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) bin
  ∃(hPU : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).C)≠0)
    (hPNU : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).C)).absNorm:ℝ))
      ≤Z^(28:ℝ)),
  ∀pay : Option (FinalHighCellPayment η₀ u₀ F₀ R₀ Z s Mrow (μ/64) amp (μ/8) (μ/8) 130 w (μ/8) (μ/32)
    (μ/8) (μ/4) (μ/4) δ (μ/8) δ (3*((Nbudget:ℝ)+2)) δ (2*(μ/8)) μ (3*δ)),
  (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
      ((1+qh)/2)≤bufferValue e (select r)),
    (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card ι) 1 (1/4))*
      normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
    highNormalizedRowCost second ordinary r
      ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
      ((ordinary r.val.1).block.divisors.filter Squarefree))≤
    Z^amp*pay.elim
      (Kt*(p.control Sp)^2*side*affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed
        Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂
        (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi hPU hPNU qh
        (μ/4+μ/4+(2*(μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ))))
      (fun _=>K*(p.control Sp)^2*side*Z^(-Mrow*Cycle63.Arithmetic.lowReserve+4*μ-3*δ))

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The conclusion of the top transport theorem for slots `ι`: profile set, constants, and the transport bound at all
large `Z`. -/
def AffineHighTopConclusion {ι : Type} [Fintype ι] [DecidableEq ι] (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0) (W : ℝ→ℂ) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (e τ : ℝ) (he : 0<e) (μ Cs δ qh : ℝ) (Nbudget : ℕ) : Prop :=
  ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃K Kt : ℝ,0<K ∧ 0<Kt ∧
    ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
        AffineHighTopInner (ι:=ι) M H hH η₀ u₀ F₀ R₀ hu₀ W hbeta e τ he μ Cs 20 δ qh Nbudget Sp K Kt Q hQM hQ72 Z

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The conclusion of the top transport theorem for equal buffer widths and heights. -/
theorem AffineHighTopConclusion_congr {ι : Type} [Fintype ι] [DecidableEq ι] (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0) (W : ℝ→ℂ) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (e e' τ τ' : ℝ) (he : 0<e) (he' : 0<e') (h : e=e') (h' : τ=τ') (μ Cs δ qh : ℝ) (Nbudget : ℕ)
    (hc : AffineHighTopConclusion (ι:=ι) M H hH η₀ u₀ F₀ R₀ hu₀ W hbeta e τ he μ Cs δ qh Nbudget) :
    AffineHighTopConclusion (ι:=ι) M H hH η₀ u₀ F₀ R₀ hu₀ W hbeta e' τ' he' μ Cs δ qh Nbudget := by
  subst h h'
  exact hc

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The top transport theorem with its conclusion named. -/
theorem actual_affine_high_top {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)
    (qh : ℝ)(hqh : Cycle63.Arithmetic.q0≤qh)(hN : Fintype.card ι≤Nbudget)
    (fiberReceipt : GeometryAffineHighSelectedFiberReceipt (α:=ι) η₀ u₀ F₀ R₀ (9/4) (9/4)
      (μ/8) 3 1 (μ/64)) (δ : ℝ)(hδdef : δ=geometryAffineHighDictionaryRate μ Nbudget) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      GeometryAffineHighScheduleGates W μ δ P →
      MarkedSchedule P (Fintype.card ι) W (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain → 2*P.τ*(J+1)≤μ/8 →
      AffineHighTopConclusion (ι:=ι) M H hH η₀ u₀ F₀ R₀ hu₀ W hbeta P.e P.τ P.he μ Cs δ qh Nbudget :=
  actual_affine_high_selected_small_height_shell (α:=ι) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs 20
    Nbudget hμ hμcap hCs le_rfl qh hqh hN fiberReceipt δ hδdef

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The body of the HIGH given of the second step at the slot type `ι` and the base `Z`: `DepthTwoHighGivenAt` for the
slots of one subset. -/
def DepthTwoHighGivenSlots {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ) (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ))
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(θ : ι→RayQuotient.Characters M H)(w σ freq : ι→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤ mesh) → 0≤height → (∀i,|freq i|≤height) →
  ∀(state : NaturalState Z Bmask bΦ),state.fixedModulus=internalQ Q η₀ → state.width≤1 →
  ∀(p : Profiles ap bp)(X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
  ∀(v₁ : O)(τT Tz : ℝ),τlow≤τT → PrefixHighPresented (base η₀) τT Z state v₁ Tz →
    ((Ideal.span {v₁}).absNorm:ℝ)≤Z^(B-130) →
  let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p hap
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
  let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑i,w i)))
  ∀(length ampP loss : ℝ),
    Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length →
    amp≤ampP → lossNeeded+ε≤loss →
  ∃(unit : Bool→FirstSourceLabel→O)
    (Hb : (b : Bool)→SecondStepHighCount M H hH (extendFixedDictionary (base η₀)) η₀ Z B Tz b v₁ (unit b)),
    (∀b,(Hb b).Pays Cycle63.AffineLedger.q state.rowWidth length ampP loss) ∧
    (∀b,(Fintype.card (Hb b).Class:ℝ)≤Kclass) ∧
    GeometryAffineHighGiven (α:=ι) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT ap bp s p state.puncture 1
      state.rowWidth amp Ψ (profile_zero_of_pos p hap 0) (profile_zero_of_pos p hap 1) SH dh height
      (Kh*(Z^(-(state.rowWidth+3*g.δ-amp+ε))*(∑b,(Hb b).value)+1))

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The HIGH given at all subsets of the slots follows from the HIGH given at the slots of each subset. -/
theorem depthTwoHighGivenAt_of_slots {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (ap bp bΦ Bmask mesh ε τlow B lossNeeded : ℝ) (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ))
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ)
    (h : ∀T : Finset α,DepthTwoHighGivenSlots (base:=base) (ι:=T) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bmask mesh ε τlow B
      lossNeeded hap Ψ SH dh Kclass Kh η₀ Q hQM hQ72 Z) :
    DepthTwoHighGivenAt (base:=base) (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bmask mesh ε τlow B lossNeeded hap Ψ SH dh Kclass
      Kh η₀ Q hQM hQ72 Z :=
  fun hZ hT T => h T hZ hT

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The source gates of the actual affine constructor at the slots `ι` and the base `Z`. -/
def AffineSourceGatesAt {ι : Type} [Fintype ι] [DecidableEq ι] (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (Cs : ℝ) (η₀ : Character) (Z : ℝ) : Prop :=
  1<Z ∧ ∀(θ : ι→RayQuotient.Characters M H)(w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Bmask : ℝ}(bΦ : ℝ)(state : NaturalState Z Bmask bΦ)(p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)
    (hX₁ : 0<X₁)(hX₂ : 0<X₂),
    (∀i,0≤w i) → Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    let inp:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁)
        (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates inp p (Fintype.card ι) Cs Z

end
end OAI.SevenEighths.Cycle153RecursiveHighProvider
