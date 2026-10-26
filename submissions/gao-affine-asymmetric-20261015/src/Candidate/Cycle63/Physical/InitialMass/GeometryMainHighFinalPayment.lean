import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighQuantitativePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalHighLoss
import Candidate.Cycle63.Physical.InitialMass.GeometryHighLossChoice
import Candidate.Cycle63.Physical.InitialMass.GeometryHeightAbsorption

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
open scoped Classical BigOperators SchwartzMap ContDiff
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
local notation "O" => HeckeFamily.O
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
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


/-- A genuine canonical high-family estimate with a single original profile,
exact signed Mellin shifts and the paid exponent. Source gates remain explicit;
no normalized energy estimate is a premise. The density degree precedes P. -/
theorem actual_main_high_final_small_height {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
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
      2*P.τ*((J:ℝ)+1)≤1/800000000 → 2*P.τ*(J+1)≤heightloss →
      ∃F G : Finset (ℕ×ℕ),∃K : ℝ,(0,0)∈F ∧ 0<K ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ ampExponent reserveShift baseHeight : ℝ)
        (hK : 0<Z^D)(_hR : R≠0)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
        (hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      let DataLabel:=geometryMainNonzeroBlocks reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂
      letI : Fintype ↥DataLabel:=Finset.fintypeCoeSort DataLabel
      ∀(χ₀ : DataLabel→RayCharacter)(Q₀ : DataLabel→Ideal O)(m : DataLabel→O),
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
      0≤ξ → 0≤reserveShift → 0 ≤ Kcontrol → 0≤Cfiber →
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
      3401/100000≤bAmpl → bAmpl≤1/25 → D=1 → 0≤D → |D|≤B → |A|≤B → |ampExponent|≤B →
      |frequencyLoss Z 32 ξ+reserveShift|≤B → frequencyLoss Z 32 ξ+reserveShift≤1/1000 → εfreq≤B → ξ≤εfreq →
      A≤D*Cycle63.Arithmetic.totalA bAmpl → ampExponent≤D*Cycle63.Arithmetic.amp bAmpl →
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
      (∀l∈labels,21/25≤bufferValue P.e (select l)) →
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
      (17/500)*D≤∑j,w j →
      (∑j,w j)≤1/25 →
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
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤rawError →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume+4*width+loss+rawError+allowance+B*εmass+heightloss+
        B*ε+3*Lprojector*ε+εprojector+fiberLoss≤4*μ-fees →
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      K*Cfiber*Kcontrol*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(-D*(720486667/30493190000000)+4*μ-fees) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_canonical_projectors (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector U hLprojector hεprojector hU hUL
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hevent⟩:=
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
  let t : κ→ℝ := fun l=>(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))
  have hzpos : 0<Z := zero_lt_one.trans hZ
  have hshift (l : κ) : t l=baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀)) := rfl
  have hh (l : κ) (j : α) := geometry_shifted_small_outer_height (Z^P.τ) baseHeight height
    (if second then -t₀ else t₀) u (select l).1.val (v j)
    (Real.rpow_nonneg hzpos.le _) hheight (by cases second <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using hsmall) (hv j)
  have hplainheight (l : κ) := geometry_shifted_small_outer_height (Z^P.τ) baseHeight height
    (if second then -t₀ else t₀) u (select l).1.val (0:ℝ)
    (Real.rpow_nonneg hzpos.le _) hheight (by cases second <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using hsmall) (by simpa using hheight)
  have hpaid := he.2 reflected second s hη R seed W D ξ ampExponent reserveShift baseHeight
    hKfirst hR hZ bin hs₁ hs₂ χ₀ Q₀ m row ψ bAmpl rawError allowance Kcontrol width (Cfiber*Z^fiberLoss)
    hξ hreserve hcontrol hwidth (mul_nonneg hfiberpos (Real.rpow_nonneg hzpos.le _)) labels hfiber select
    hx hseed hsource hlower hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard.le hM hb₁ hb₂ hupper hwin
    t w σ v θ (fun _=>p) cap hcap hmatches hsupply hsupplyUpper hscales hpadallow hwidthstate hradial hw hwmarked hwr hσlo hσhi
    (fun l _ j=>by rw [hshift]; exact (hh l j).1)
    (fun l _=>by rw [hshift]; exact (hplainheight l).2)
    (fun _ _=>⟨hW₁,hW₂,hbp₁,hbp₂⟩) hpool (fun _ _=>hprofile) hledger
    t₀ u hψ (fun _ _=>rfl)
  let total : ℝ := frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(720486667/30493190000000)+
    4*width+loss+rawError+allowance+B*εmass+heightloss+B*ε+3*Lprojector*ε+εprojector+fiberLoss
  have heq :
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*((Cfiber*Z^fiberLoss)*
        (Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*
        (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*grid*
          (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
            Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(720486667/30493190000000)+
              4*width+loss+rawError+allowance+B*εmass+heightloss)))))) =
        K*Cfiber*Kcontrol*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^total := by
    have hp₁ : (2*Z^Lprojector)^ε=2^ε*Z^(Lprojector*ε) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hzpos.le _),←Real.rpow_mul hzpos.le]
    have hp₂ : (2*Z^Lprojector)^(2*ε)=2^(2*ε)*Z^(Lprojector*(2*ε)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hzpos.le _),←Real.rpow_mul hzpos.le]
    have ht : total=fiberLoss+εprojector+Lprojector*ε+B*ε+Lprojector*(2*ε)+
        (frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(720486667/30493190000000)+
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

/-- A profile norm gate independent of every physical index. -/
theorem geometry_main_high_profile_norm {ap bp : ℝ}
    (p : Profiles ap bp) (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (i : Fin 2) (x : ℝ) :
    ‖p.profile i x‖≤ sourceControl S (p.profile i) := by
  exact (SchwartzMap.norm_le_seminorm ℝ (p.profile i) x).trans
    (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=S) (x:=p.profile i) (i:=(0,0)) hS)

/-- Genuine all-height coarse cost after amplification, with source profile controls. -/
def MainHighAmplifiedCoarseProfileSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap bp εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset (secondLiveRows (fun q=>(datum q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (height : rows→ℝ)(Ds : rows→Finset (Ideal O))(p : Profiles ap bp)(S : Finset (ℕ×ℕ)),
      (0,0)∈S → s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        (firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
          (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex r.val.val.1.1).1.val)/
          volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      Z^(-a)*(∑r : rows,cost r)≤K*(p.control S)^2*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^exponent

theorem actual_main_high_original_amplified_coarse_profiles {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α=N) {bp : ℝ}
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,
      MainHighAmplifiedCoarseProfileSpec (α:=α) N B Cs b bs window plainCap lo ap bp εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  obtain ⟨K,hK,hevent⟩ := actual_main_high_original_coarse_side_payment (α:=α)
    η₀ u₀ F₀ R₀ hu₀ N hα.le B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  refine ⟨K,hK,?_⟩
  filter_upwards [hevent] with Z hc
  unfold MainHighAmplifiedCoarseProfileSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hD habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W height Ds p S hS hW₁ hW₂ hDs cost
  have hnorm := geometry_main_high_profile_norm p S hS
  have hraw : (∑r : rows,cost r)≤K*(p.control S)^2*
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) := hc hZ (Label:=Label) reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hD habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc
    rows second W height Ds ((p.control S)^2) (sourceControl S (p.profile 0)) (sourceControl S (p.profile 1))
    (sq_nonneg _) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    (fun x=>by rw [hW₁]; exact hnorm 0 x) (fun x=>by rw [hW₂]; exact hnorm 1 x) (by rfl) hDs
  have hscale : Z^(-a)≤1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hZ.le (neg_nonpos.mpr ha)
    simpa only [Real.rpow_zero] using hh
  have hbnd : 0≤K*(p.control S)^2*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
        8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.le (sq_nonneg _))
      (geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
        (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  exact (mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hbnd)

/-- Exact normalized physical cost for an arbitrary ordinary row subset.
The residual divisor filter and both signed Mellin shifts are unchanged. -/
theorem geometry_main_high_physical_row_sum {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (lo ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows (fun l=>(d l).block))) :
    (∑r∈rows,∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N lo ap second d coefficient t u r.val D)=
    ∑r∈rows,(coefficient r.val.1*((d r.val.1).K/lowerFactor N lo ap)*
      normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
      highNormalizedRowCost second d r
        ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.1).block.divisors.filter Squarefree) := by
  apply Finset.sum_congr rfl
  intro r _
  rw [actual_second_residual_ideals_label]
  cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]

/-- An ordinary subset has the exact same physical cost in its injective
original source image, including the literal residual-divisor set. -/
theorem geometry_main_high_physical_original_image {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (lo ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (χ : Label→RayCharacter) (Q : Label→Ideal O) (m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (coefficient : Label→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))) :
    (∑r∈rows,∑D∈secondResidualIdeals
      (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block) r.val,
      mainNormalizedPhysicalCost N lo ap second
        (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l)) coefficient t u r.val D)=
    ∑r∈rows.image (ordinaryHighOriginalRow d χ Q m hrows),
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N lo ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [geometry_main_high_physical_row_sum N lo ap second
    (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l)) coefficient t u rows]
  rw [Finset.sum_image (fun r _ z _ heq=>ordinary_high_original_row_injective d χ Q m hrows heq)]
  apply Finset.sum_congr rfl
  intro r _
  rw [ordinary_high_original_row_cost d χ Q m hrows r second]
  have hlabel : (ordinaryHighOriginalRow d χ Q m hrows r).val.1=r.val.1 := rfl
  rw [hlabel]
  have hdiv : (ordinarySecondDatum (d r.val.1) (χ r.val.1) (Q r.val.1) (m r.val.1)).block.divisors=
    (d r.val.1).block.divisors := rfl
  rw [hdiv]
  congr 1

/-- The ordinary physical subset embeds into a larger original label family
without changing its mass, divisor filter, rays or signed frequency. -/
theorem geometry_main_high_physical_full_original_image {α Label Original : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label] [Fintype Original]
    (embed : Label→Original) (hinj : Function.Injective embed)
    (N : ℕ) (lo ap : ℝ) (second : Bool) (d : Original→SecondInputDatum α)
    (χ : Label→RayCharacter) (Q : Label→Ideal O) (m : Label→O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (coefficient : Original→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows
      (fun l=>(ordinarySecondDatum (d (embed l)) (χ l) (Q l) (m l)).block))) :
    (∑r∈rows,∑D∈secondResidualIdeals
      (fun l=>(ordinarySecondDatum (d (embed l)) (χ l) (Q l) (m l)).block) r.val,
      mainNormalizedPhysicalCost N lo ap second
        (fun l=>ordinarySecondDatum (d (embed l)) (χ l) (Q l) (m l))
        (fun l=>coefficient (embed l)) t u r.val D)=
    ∑r∈(rows.image (ordinaryHighOriginalRow (fun l=>d (embed l)) χ Q m hrows)).image
        (highSelectedLiveRowEmbedding d embed),
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N lo ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [geometry_main_high_physical_original_image N lo ap second
    (fun l=>d (embed l)) χ Q m hrows (fun l=>coefficient (embed l)) t u rows]
  rw [Finset.sum_image (fun r _ z _ heq=>Subtype.ext (high_selected_row_embedding_injective d embed hinj (congrArg Subtype.val heq)))]
  apply Finset.sum_congr rfl
  intro r _
  rfl

/-- Source-only coarse contract for an arbitrary selected ordinary subset. -/
def MainHighSelectedPhysicalCoarseSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap bp εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      let Selected := mainLowSelectedNonzeroRows reflected s R seed Z Dfirst a ξ reserve b t N hZ bin hs₁ hs₂ firstIndex
      letI : Fintype ↥Selected := Finset.fintypeCoeSort Selected
      ∀(χ : Selected→RayCharacter)(Q : Selected→Ideal O)(m : Selected→O),
      let ordinary := fun q : Selected=>ordinarySecondDatum (datum q.val) (χ q) (Q q) (m q)
      ∀(rows : Finset (secondLiveRows (fun q=>(ordinary q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (t₀ u : ℝ)(p : Profiles ap bp)(S : Finset (ℕ×ℕ)),
      (0,0)∈S → s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
      let coefficient := fun q : Selected=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex q.val.1).1.val / volume (ordinary q).input
      Z^(-a)*(∑r∈rows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
        mainNormalizedPhysicalCost N lo ap second ordinary coefficient t₀ u r.val L)≤
        K*(p.control S)^2*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^exponent

private theorem geometry_main_high_scalar_normalization (a v k l n c : ℝ) :
    (a/v)*(k/l)*n*c=a*(k/v)*n/l*c := by ring

/-- A genuine coarse bound on the same selected ORIGINAL full-nonzero
carrier as the high consumer, valid at every height. It has no high saving. -/
theorem main_high_selected_physical_coarse_of_source {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap bp εmass ξ U exponent K Z : ℝ)
    (hcoarse : MainHighAmplifiedCoarseProfileSpec (α:=α) N B Cs b bs window plainCap lo ap bp εmass ξ U exponent K Z) :
    MainHighSelectedPhysicalCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap bp εmass ξ U exponent K Z := by
  unfold MainHighSelectedPhysicalCoarseSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hD habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    Selected χ Q m ordinary rows second W t₀ u p S hS hW₁ hW₂ coefficient
  let rawCoefficient : Index→ℝ := fun q=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
    (firstIndex q.1).1.val / volume (datum q).input
  have hrows : ∀q : Selected,(datum q.val).rows=sourceRows
    (datum q.val).C (datum q.val).D (datum q.val).inactive (datum q.val).radius := fun _=>rfl
  let image := (rows.image (ordinaryHighOriginalRow (fun q : Selected=>datum q.val) χ Q m hrows)).image
    (highSelectedLiveRowEmbedding (Selected:=↥Selected) (Original:=Index) datum Subtype.val)
  have hi := geometry_main_high_physical_full_original_image (α:=α) (Label:=↥Selected) (Original:=Index) Subtype.val Subtype.val_injective
    N lo ap second datum χ Q m hrows rawCoefficient t₀ u rows
  change (∑r∈rows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
    mainNormalizedPhysicalCost N lo ap second ordinary coefficient t₀ u r.val L)=_ at hi
  rw [hi]
  have hc := hcoarse hZ (Label:=Label) reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hD habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc
    image second W
    (fun r=>(datum r.val.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
    (fun r=>(datum r.val.val.1).block.divisors.filter Squarefree) p S hS hW₁ hW₂
    (fun r L hL=>Finset.mem_filter.mp hL)
  let rawCost : secondLiveRows (fun q=>(datum q).block)→ℝ := fun r=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin (firstIndex r.val.1.1).1.val *
      (firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hKfirst bin (firstIndex r.val.1.1).1.val)/
        volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hKfirst bin t (firstIndex r.val.1.1)))*
      normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive/lowerFactor N lo ap*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree)
  have hsum := Finset.sum_coe_sort image rawCost
  change Z^(-a)*(∑r : image,rawCost r.val)≤
    K*(p.control S)^2*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^exponent at hc
  rw [hsum] at hc
  let imageCost : secondLiveRows (fun q=>(datum q).block)→ℝ := fun r=>
    (rawCoefficient r.val.1*((datum r.val.1).K/lowerFactor N lo ap)*
      normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
    highNormalizedRowCost second datum r
      ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
      ((datum r.val.1).block.divisors.filter Squarefree)
  have hcost (r : secondLiveRows (fun q=>(datum q).block)) : imageCost r=rawCost r := by
    exact geometry_main_high_scalar_normalization
      (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin (firstIndex r.val.1.1).1.val)
      (volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hKfirst bin t (firstIndex r.val.1.1)))
      (firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hKfirst bin (firstIndex r.val.1.1).1.val))
      (lowerFactor N lo ap)
      (normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)
      (highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))
  change Z^(-a)*(∑r∈_,imageCost r)≤_
  apply le_of_eq_of_le ?_ hc
  congr 1
  refine Finset.sum_congr (f:=imageCost) (g:=rawCost) ?_ (fun r _=>hcost r)
  ext r
  simp only [image,Finset.mem_image]

/-- Genuine all-height physical coarse payment with original profile controls. -/
theorem actual_main_high_final_all_height_coarse {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α=N) {bp : ℝ}
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,
      MainHighSelectedPhysicalCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap bp εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  obtain ⟨K,hK,hevent⟩ := actual_main_high_original_amplified_coarse_profiles (α:=α)
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  refine ⟨K,hK,?_⟩
  filter_upwards [hevent] with Z hc
  exact main_high_selected_physical_coarse_of_source N B Cs b bs window plainCap lo ap bp εmass ξ U _ K Z hc

/-- A selected finite live-row family pays exactly its injective image in the
full original physical family. The first coefficient and residual filter are
pulled back before either ordinary/high partition or quantitative payment. -/
theorem geometry_main_high_selected_live_cost_image {α Selected Original : Type*}
    [Fintype α] [DecidableEq α] [Fintype Selected] [Fintype Original]
    (d : Original→SecondInputDatum α) (embed : Selected→Original)
    (hinj : Function.Injective embed) (N : ℕ) (lo ap : ℝ) (second : Bool)
    (coefficient : Original→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows (fun l=>(d (embed l)).block))) :
    (∑r∈rows,∑D∈secondResidualIdeals (fun l=>(d (embed l)).block) r.val,
      mainNormalizedPhysicalCost N lo ap second (fun l=>d (embed l))
        (fun l=>coefficient (embed l)) t u r.val D)=
    ∑r∈rows.image (highSelectedLiveRowEmbedding d embed),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
        mainNormalizedPhysicalCost N lo ap second d coefficient t u r.val D := by
  rw [Finset.sum_image (fun r _ z _ heq=>Subtype.ext
    (high_selected_row_embedding_injective d embed hinj (congrArg Subtype.val heq)))]
  rfl

/-- The final source rates pay the precise exponent used by the consumer,
including both joint-key fiber losses. This is arithmetic, not an energy premise. -/
theorem geometry_final_main_high_consumer_ledger
    (μ d Bmass Bnorm U B Lproj omega rawError allowance : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj)
    (hω : omega≤33*μ/128) (hraw : rawError≤μ/4) (ha : allowance≤μ/4) :
    let δ := geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let massRate := geometryFinalMassRate μ δ B
    omega+μ/8+μ/8+4*(μ/32)+μ/8+rawError+allowance+B*massRate+μ/8+
      B*δ+3*Lproj*δ+δ+2*(μ/8)+3*δ≤4*μ := by
  intro δ massRate
  have rates := geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have hh := geometry_final_high_loss_budget μ d Bmass Bnorm U B Lproj omega rawError allowance (3*δ) N
    hμ hd hm hn hU hB hL hω hraw ha (by nlinarith [rates.1])
  nlinarith only [hh]

/-- The final high loss schedule leaves the required strict saving at seed one. -/
theorem geometry_final_main_high_exponent_saving (εaffine : ℝ) (hε : 0<εaffine) :
    -(720486667/30493190000000:ℝ)+4*geometryLossUnit 1 εaffine≤-(7/60000000:ℝ) :=
  geometry_high_width_one_exponent_saving εaffine (4*geometryLossUnit 1 εaffine) hε le_rfl

/-- A physical side factor accompanies both branches of the height splice.
The coarse branch contributes its polynomial degree, without a high saving claim. -/
theorem geometry_main_high_all_height_splice
    (coarse target τ : ℝ) (hτ : 0<τ) (smallDegree : ℕ) :
    ∃degree : ℕ,∀Z height energy Ksmall Kcoarse control side : ℝ,
      1≤Z → 1≤height → 0≤Ksmall → 0≤Kcoarse → 0≤control → 0≤ side →
      (height≤Z^τ → energy≤Ksmall*control*side*Z^target*height^smallDegree) →
      energy≤Kcoarse*control*side*Z^coarse →
      energy≤(Ksmall+Kcoarse)*control*side*Z^target*height^degree := by
  obtain ⟨degree,hd⟩ := geometry_extend_height_bound coarse target τ hτ smallDegree
  refine ⟨degree,?_⟩
  intro Z height energy Ks Kc control side hZ hh hKs hKc hc hs hsmall hcoarse
  have hb := hd Z height energy Ks Kc (control*side) hZ hh hKs hKc (mul_nonneg hc hs)
    (fun ht=>by simpa only [mul_assoc] using hsmall ht)
    (by simpa only [mul_assoc] using hcoarse)
  simpa only [mul_assoc] using hb

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_high_final_small_height

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_high_original_amplified_coarse_profiles
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_main_high_consumer_ledger
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_all_height_splice

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_profile_norm
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_final_main_high_exponent_saving

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_physical_row_sum
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_physical_original_image

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_physical_full_original_image
#print axioms OAI.SevenEighths.Cycle63InitialMass.main_high_selected_physical_coarse_of_source

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_high_final_all_height_coarse
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_high_selected_live_cost_image
