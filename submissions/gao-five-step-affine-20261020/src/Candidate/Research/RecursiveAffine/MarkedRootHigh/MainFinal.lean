import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighFinalPayment
import Candidate.Research.RecursiveAffine.MarkedRootHigh.MainPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighQuantitativePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalHighLoss
import Candidate.Cycle63.Physical.InitialMass.GeometryHighLossChoice
import Candidate.Cycle63.Physical.InitialMass.GeometryHeightAbsorption
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local instance geometryMainHighFinalPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource

open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The cell payment data of the final HIGH shell: the cell data of the layers below and the final exponent inequality
of the frequency, volume, bin, loss, error, height, projector and fiber exponents against `4 μ - fees`. -/
structure FinalHighCellPayment {α : Type} [Fintype α] (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀)
    (R₀ : Ideal O) (Z : ℝ) (s : Input α) (D ξ ampExponent reserveShift εfreq B : ℝ) (w : α→ℝ)
    (εvolume width loss rawError allowance εmass heightloss ε Lprojector εprojector fiberLoss μ fees : ℝ) extends
    HighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w where
  final : frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume+4*width+loss+rawError+allowance+B*εmass+heightloss+
    B*ε+3*Lprojector*ε+εprojector+fiberLoss≤4*μ-fees

variable [Cycle63.AffineLedger] in
/-- The canonical HIGH family at small height with a single original profile and exact signed Mellin shifts. Without
payment data the bound is the transport form: the sum over the buffer bins of the binned count of the keys of the
compensated child coordinates. With the cell payment data it is the paid exponent. Source gates remain explicit; no
normalized energy estimate is a premise. -/
theorem actual_main_high_small_height_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (B Q loss ε μ fees width fiberLoss : ℝ) (hwidth : 0<width) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hQmax : Q≤130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector U : ℝ) (hLprojector : 0≤Lprojector) (hεprojector : 0<εprojector)
    (hU : 0≤U)(hUL : ((N:ℝ)+2)*U≤Lprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      2*P.τ*((J:ℝ)+1)≤Cycle63.Optimization.geometryLossCap/8 → 2*P.τ*(J+1)≤heightloss →
      ∃F G : Finset (ℕ×ℕ),∃K Kmove Cmove : ℝ,(0,0)∈F ∧ 0<K ∧ 0<Kmove ∧ 0<Cmove ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ ampExponent reserveShift baseHeight : ℝ)
        (hK : 0<Z^D)(_hR : R≠0)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
        (hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      let DataLabel:=geometryMainNonzeroBlocks reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂
      letI : Fintype ↥DataLabel:=Finset.fintypeCoeSort DataLabel
      ∀(χ₀ : DataLabel→RayCharacter)(Q₀ : DataLabel→ Ideal O)(m : DataLabel→O),
      let datum:=fun j : DataLabel=>geometryMainOrdinaryDatum reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) j.val
      let first:=fun j : DataLabel=>geometryFirstLabel s R seed (Z^D) Z ξ hK bin j.val.1.1.val
      ∀row : κ→secondLiveRows (fun l=>(datum l).block),
      let column:=fun l=>(row l).val.1.val.1.1.val
      let hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
      ∀ψ : κ→RayCharacter,
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (rawError allowance Kcontrol Cfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 0≤Cfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤Cfiber*Z^fiberLoss) →
      ∀select : κ→BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → sourceRadius s≤Z^B → lo≤ s.lower →
      ξ≤εfreq →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤Z^B) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤Z^P.τ) →
      Fintype.card α=N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(t₀ u height : ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : Profiles ap bp)(cap : ℝ),
      0≤height → (∀j,|v j|≤height) →
      |baseHeight|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ →
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤w j) →
      (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (p.control G)^2*(2*bs*Cs^N)^2≤Kcontrol →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      ∀pay : Option (FinalHighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w εvolume width loss
        rawError allowance εmass heightloss ε Lprojector εprojector fiberLoss μ fees),
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      pay.elim
        (∑q : BufferIndex P.e,(1/lowerFactor N lo ap)*((Cfiber*Z^fiberLoss)*(Kmove*Z^εprojector*(2*Z^Lprojector)^ε*
          Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          keyBinnedCount (labels.filter (fun l=>select l=q)) key
            (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
              (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
            (fun k=>Cmove*Kcontrol*(2*Z^Lprojector)^(2*ε)*
              Z^(exponentBinUpper width k 0+(2*bufferValue P.e q-1)*exponentBinUpper width k 3+rawError+allowance))))))
        (fun _=>K*Cfiber*Kcontrol*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
          Z^(-D*(Cycle153.MarkedRootPrice.lowReserve)+4*μ-fees)) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_canonical_projectors (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector U hLprojector hεprojector hU hUL
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,hevent⟩:=
    hhigh heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  let grid : ℝ := ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)
  let K : ℝ := (Fintype.card (BufferIndex P.e):ℝ)*(1/lowerFactor N lo ap)*
    Kcolumn*Cs^(2*N)*grid*C*Cprofile^2*2^(3*ε)
  have hgrid : 0<grid := by
    apply Nat.cast_pos.mpr
    apply pow_pos
    apply Finset.card_pos.mpr
    refine ⟨0,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
    · apply Int.floor_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hwidth.le
    · apply Int.le_floor.mpr
      simp only [Int.cast_zero]
      exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) hB) (abs_nonneg _)) hwidth.le
  have hK : 0<K := by
    dsimp only [K]
    have hc : 0<(Fintype.card (BufferIndex P.e):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hl := lowerFactor_pos N lo ap hlo hap
    have hcs : 0<Cs := zero_lt_one.trans_le hCs
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hc
      (div_pos (by norm_num) hl)) hKcolumn) (pow_pos hcs _)) hgrid) hC)
      (pow_pos hCprofile _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨F,G,K,Kcolumn,Cmove,hF,hK,hKcolumn,hCmove,?_⟩
  filter_upwards [hevent] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ reflected second s R seed W D ξ ampExponent reserveShift baseHeight hKfirst hR hZ bin hs₁ hs₂
    DataLabel χ₀ Q₀ m datum first row column hfirst ψ left unit hf rawKey key rawError allowance Kcontrol Cfiber
    hξ hreserve hcontrol hfiberpos labels hfiber select A x hx hseed hsource hlower
    hξε hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    t₀ u height w σ v θ p cap hheight hv hsmall hcap hmatches hscales hpadallow
    hwidthstate hradial hw hwr hσlo hσhi hW₁ hW₂ hbp₁ hbp₂ hpool hprofile hledger hψ pay
  let t : κ→ℝ := fun l=>(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))
  have hzpos : 0<Z := zero_lt_one.trans hZ
  have hshift (l : κ) : t l=baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀)) := rfl
  have hh (l : κ) (j : α) := geometry_shifted_small_outer_height (Z^P.τ) baseHeight height
    (if second then -t₀ else t₀) u (select l).1.val (v j)
    (Real.rpow_nonneg hzpos.le _) hheight (by cases second <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using hsmall) (hv j)
  have hplainheight (l : κ) := geometry_shifted_small_outer_height (Z^P.τ) baseHeight height
    (if second then -t₀ else t₀) u (select l).1.val (0:ℝ)
    (Real.rpow_nonneg hzpos.le _) hheight (by cases second <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using hsmall) (by simpa using hheight)
  have hpaid := he.2 reflected second s R seed W D ξ ampExponent reserveShift baseHeight
    hKfirst hR hZ bin hs₁ hs₂ χ₀ Q₀ m row ψ rawError allowance Kcontrol width (Cfiber*Z^fiberLoss)
    hξ hreserve hcontrol hwidth (mul_nonneg hfiberpos (Real.rpow_nonneg hzpos.le _)) labels hfiber select
    hx hseed hsource hlower hξε hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard.le hM hb₁ hb₂ hupper hwin
    t w σ v θ (fun _=>p) cap hcap hmatches hscales hpadallow hwidthstate hradial hw hwr hσlo hσhi
    (fun l _ j=>by rw [hshift]; exact (hh l j).1)
    (fun l _=>by rw [hshift]; exact (hplainheight l).2)
    (fun _ _=>⟨hW₁,hW₂,hbp₁,hbp₂⟩) hpool (fun _ _=>hprofile) hledger
    t₀ u hψ (fun _ _=>rfl) (pay.map (·.toHighCellPayment))
  rcases pay with _ | d
  · exact hpaid
  dsimp only [Option.map,Option.elim] at hpaid ⊢
  have hfinal := d.final
  let total : ℝ := frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle153.MarkedRootPrice.lowReserve)+
    4*width+loss+rawError+allowance+B*εmass+heightloss+B*ε+3*Lprojector*ε+εprojector+fiberLoss
  have heq :
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*((Cfiber*Z^fiberLoss)*
        (Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*
        (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*grid*
          (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
            Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle153.MarkedRootPrice.lowReserve)+
              4*width+loss+rawError+allowance+B*εmass+heightloss)))))) =
        K*Cfiber*Kcontrol*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^total := by
    have hp₁ : (2*Z^Lprojector)^ε=2^ε*Z^(Lprojector*ε) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hzpos.le _),←Real.rpow_mul hzpos.le]
    have hp₂ : (2*Z^Lprojector)^(2*ε)=2^(2*ε)*Z^(Lprojector*(2*ε)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hzpos.le _),←Real.rpow_mul hzpos.le]
    have ht : total=fiberLoss+εprojector+Lprojector*ε+B*ε+Lprojector*(2*ε)+
        (frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle153.MarkedRootPrice.lowReserve)+
          4*width+loss+rawError+allowance+B*εmass+heightloss) := by dsimp only [total]; ring
    rw [hp₁,hp₂,ht]
    dsimp only [K]
    rw [show 3*ε=ε+2*ε by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
    simp only [Real.rpow_add hzpos]
    ring
  change _≤_ at hpaid
  rw [heq] at hpaid
  apply hpaid.trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp only [total]
    linarith only [hfinal]
  · have hs:=geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)
    positivity

variable [Cycle63.AffineLedger] in
/-- A genuine canonical high-family estimate with a single original profile,
exact signed Mellin shifts and the paid exponent. Source gates remain explicit;
no normalized energy estimate is a premise. The density degree precedes P. -/
theorem actual_main_high_final_small_height {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (B Q loss ε μ fees width fiberLoss : ℝ) (hwidth : 0<width) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hQmax : Q≤130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector U : ℝ) (hLprojector : 0≤Lprojector) (hεprojector : 0<εprojector)
    (hU : 0≤U)(hUL : ((N:ℝ)+2)*U≤Lprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      2*P.τ*((J:ℝ)+1)≤Cycle63.Optimization.geometryLossCap/8 → 2*P.τ*(J+1)≤heightloss →
      ∃F G : Finset (ℕ×ℕ),∃K : ℝ,(0,0)∈F ∧ 0<K ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ ampExponent reserveShift baseHeight : ℝ)
        (hK : 0<Z^D)(_hR : R≠0)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
        (hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      let DataLabel:=geometryMainNonzeroBlocks reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂
      letI : Fintype ↥DataLabel:=Finset.fintypeCoeSort DataLabel
      ∀(χ₀ : DataLabel→RayCharacter)(Q₀ : DataLabel→ Ideal O)(m : DataLabel→O),
      let datum:=fun j : DataLabel=>geometryMainOrdinaryDatum reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) j.val
      let first:=fun j : DataLabel=>geometryFirstLabel s R seed (Z^D) Z ξ hK bin j.val.1.1.val
      ∀row : κ→secondLiveRows (fun l=>(datum l).block),
      let column:=fun l=>(row l).val.1.val.1.1.val
      let hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
      ∀ψ : κ→RayCharacter,
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (bAmpl rawError allowance Kcontrol Cfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 0≤Cfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤Cfiber*Z^fiberLoss) →
      ∀select : κ→BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → sourceRadius s≤Z^B → lo≤ s.lower →
      Cycle63.Optimization.firstCellTop≤bAmpl → bAmpl≤Cycle153.MarkedRootPrice.top → D=1 → 0≤D → |D|≤B → |A|≤B → |ampExponent|≤B →
      |frequencyLoss Z 32 ξ+reserveShift|≤B → frequencyLoss Z 32 ξ+reserveShift≤Cycle63.Optimization.frequencyLossCap → εfreq≤B → ξ≤εfreq →
      A≤D*Cycle153.MarkedRootPrice.totalA bAmpl → ampExponent≤D*Cycle153.MarkedRootPrice.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤Z^B) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤Z^P.τ) →
      Fintype.card α=N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(t₀ u height : ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : Profiles ap bp)(cap : ℝ),
      0≤height → (∀j,|v j|≤height) →
      |baseHeight|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ →
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (bAmpl-Cycle63.Optimization.cellMesh)*D≤∑j,w j →
      (∑j,w j)≤Cycle153.MarkedRootPrice.top →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤w j) → (∀j,w j≤ markedRawMesh*markedCoreMin) →
      (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (p.control G)^2*(2*bs*Cs^N)^2≤Kcontrol →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume+4*width+loss+rawError+allowance+B*εmass+heightloss+
        B*ε+3*Lprojector*ε+εprojector+fiberLoss≤4*μ-fees →
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      K*Cfiber*Kcontrol*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(-D*(Cycle153.MarkedRootPrice.lowReserve)+4*μ-fees) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_main_high_small_height_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε μ fees width fiberLoss hwidth
    hB hQ hQB hQmax hloss hε hap N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector U hLprojector hεprojector hU hUL Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,K,_,_,hF,hK,_,_,hevent⟩:=hhigh heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  refine ⟨F,G,K,hF,hK,?_⟩
  filter_upwards [hevent] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ reflected second s hη R seed W D ξ ampExponent reserveShift baseHeight hKfirst hR hZ bin hs₁ hs₂
    DataLabel χ₀ Q₀ m datum first row column hfirst ψ left unit hf rawKey key bAmpl rawError allowance Kcontrol Cfiber
    hξ hreserve hcontrol hfiberpos labels hfiber select A x hx hseed hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    t₀ u height w σ v θ p cap hheight hv hsmall hcap hmatches hsupply hsupplyUpper hscales hpadallow
    hwidthstate hradial hw hwmarked hwr hσlo hσhi hW₁ hW₂ hbp₁ hbp₂ hpool hprofile hledger hψ hfinal
  exact he.2 reflected second s R seed W D ξ ampExponent reserveShift baseHeight hKfirst hR hZ bin hs₁ hs₂ χ₀
    Q₀ m row ψ rawError allowance Kcontrol Cfiber hξ hreserve hcontrol hfiberpos labels hfiber select hx hseed
    hsource hlower hξε hnorm st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂
    hupper hwin t₀ u height w σ v θ p cap hheight hv hsmall hcap hmatches hscales hpadallow hwidthstate
    hradial hw hwr hσlo hσhi hW₁ hW₂ hbp₁ hbp₂ hpool hprofile hledger hψ
    (some ⟨⟨bAmpl,hbAmpl,hbAmpl',hDunit,hD,hDcap,hA,hamp,homega,homegaSmall,hεfreqB,htotalA,hampcap,
      hsupply,hsupplyUpper,hwmarked,hη⟩,hfinal⟩)


end
end OAI.SevenEighths.Cycle153RootHigh

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_main_high_final_small_height
