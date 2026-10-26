import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Research.RecursiveAffine.MarkedRootHigh.MainProjectors
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCoarseFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryHighCoarseGates
import Candidate.Cycle63.Moment.HighParameters
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 40000000
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
local instance geometryMainHighPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

variable [Cycle63.AffineLedger] in
theorem actual_geometry_main_high_canonical_projectors {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hQmax : Q≤130)
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
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn Cmove : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧ 0<Cmove ∧
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
        (rawError allowance Kcontrol width Wfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 0<width →
      0≤Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤Wfiber) →
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
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(cap : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤w j) →
      (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      ∀pay : Option (HighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w),
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      pay.elim
        (∑q : BufferIndex P.e,(1/lowerFactor N lo ap)*(Wfiber*
          (Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          keyBinnedCount (labels.filter (fun l=>select l=q)) key
            (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
              (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
            (fun k=>Cmove*Kcontrol*(2*Z^Lprojector)^(2*ε)*
              Z^(exponentBinUpper width k 0+(2*bufferValue P.e q-1)*exponentBinUpper width k 3+rawError+allowance))))))
        (fun _=>(Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*
          (Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle153.MarkedRootPrice.lowReserve)+4*width+loss+
            rawError+allowance+B*εmass+heightloss))))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_buffered_projectors (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector hLprojector hεprojector
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,hevent⟩:=
    hhigh heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  refine ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,?_⟩
  filter_upwards [hevent] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ reflected second s R seed W D ξ ampExponent reserveShift baseHeight hK hR hZ bin hs₁ hs₂
    DataLabel χ₀ Q₀ m datum first row column hfirst ψ left unit hf rawKey key rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select A x hq hseed hsource hlower
    hξε hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    t w σ v θ p cap hcap hmatches hscales hpadallow
    hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hpool hcontrol hledger
    t₀ u hψ hshift pay
  let globalDs:=mainHighProjectorUnion datum
  let Ds : κ→Finset (Ideal O):=fun _=>globalDs
  let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
  let B₁ : ∀l,actualAllocations s.pools (C₁ l):=fun l=>(row l).val.1.val.1.2
  let t₁ : κ→ℝ:=fun _=>baseHeight
  have hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
  have hR' : ∀l,(datum (row l).val.1).R≠0:=fun l=>actual_geometry_child_puncture_ne_zero
    reflected s R seed hR (Z^D) Z ξ hK bin (column l)
  have hradius : ∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
    (firstMainFourierScale reflected (Z^D) (volume s) Z ξ (3*ampExponent)
      reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ:=fun _ _=>rfl
  have hf₁ : ∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0:=by
    intro l _
    exact (Finset.mem_filter.mp (row l).val.1.property).2.1
  have hprojectors:=actual_main_high_original_projector_union reflected s R seed
    Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ χ₀ Q₀ m (fun j : DataLabel=>j.val) U hU hcard hpool
  have hDs : ∀l∈labels,∀L∈Ds l,Squarefree L:=fun _ _ L hL=>(hprojectors L hL).1
  have hnormL : ∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ)≤Z^Lprojector:=fun _ _ L hL=>
    (hprojectors L hL).2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hUL)
  let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
  have hseed₂ : ∀l∈labels,(datum (row l).val.1).seed∣E l:=by
    intro l _
    have h:=actual_main_high_seed_gates reflected s R seed Z D ampExponent ξ reserveShift b baseHeight
      N hZ bin hs₁ hs₂ (χ₀ (row l).val.1) (Q₀ (row l).val.1) (m (row l).val.1) (row l).val.1.val
    cases second
    · exact h.1
    · exact h.2
  have hpaid:=he.2 reflected second s R seed W D ξ hK bin column datum first row hparent hfirst hR' ψ
    ampExponent reserveShift rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select hq
    hseed hs₁ hs₂ hsource hlower hξε hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ (fun l=>(datum (row l).val.1).seed) t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u (fun _ _=>rfl) (fun _ _=>HEq.rfl) (fun _ _=>rfl) (fun _ _=>rfl) hψ hshift pay
  apply (mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hpaid
  apply main_high_residual_sum_le_union datum (fun l=>(row l).val) labels
  intro l _ L
  dsimp only [mainNormalizedPhysicalCost]
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact div_nonneg (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l))
          (volume_pos (datum (row l).val.1).input).le
      · exact div_nonneg (datum (row l).val.1).K_pos.le (lowerFactor_pos N lo ap hlo hap).le
    · exact (normalizer_pos _ _ (datum (row l).val.1).hC _).le
  · split <;> exact sq_nonneg _

end
end OAI.SevenEighths.Cycle153RootHigh

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_geometry_main_high_canonical_projectors
