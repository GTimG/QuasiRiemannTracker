import Candidate.Target830.High.Coordinates
import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Target830.High.GeometryHighColumn
import Candidate.Cycle63.Physical.InitialMass.GeometryHighWeightedSelection
import Candidate.Cycle63.Physical.InitialMass.GeometryHighWindow

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Cycle63InitialMass
open Target830 Marked830Plain
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M  ≤  H)

/-- Full finite high-source column energy from the genuine high density
bound and the bounded joint-key fibers. The maximizing representative keeps
both physical scalar factors inside its cost. No energy bound is assumed. -/
theorem actual_geometry_full_high_columns {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1 ≤ 3/4)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (plane : SourcePlane)(N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule830 P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000 →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      (1+plane.q)/2  ≤  β → β  ≤  7/8 → 0  ≤  Kcontrol → 1  ≤  T → 0<width →
      0 ≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ) ≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      17/500 ≤ bAmpl → bAmpl ≤ 1/25 → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B → frequencyLoss Z 32 ξ+reserveShift ≤ frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
      A ≤ D*plane.total bAmpl → ampExponent ≤ D*plane.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ) ≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ) ≤ Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β  ≤  HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      i ≤ bufferCount P.e →
      (∀l∈labels,β ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l)
        (z l) (hz l) ((3*i:ℕ)*Z^P.τ)) →
      (i:ℝ) ≤ Z^P.τ →
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      s.b₁ ≤ bs → s.b₂ ≤ bs → s.upper ≤ b →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      let R₂:=fun l=>(datum (row l).val.1).R
      let outer:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
      let hE : ∀l,Supported (E l):=fun l=>by
        dsimp only [E]; split <;> first | exact (datum (row l).val.1).hD | exact (datum (row l).val.1).hC
      ∀(seed₂ : κ→Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (17/500)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-sourceWidthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  rawMesh830*rawCore830) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T ≤ (L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      (∑l∈labels,balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
          (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2)) ≤ 
      Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass)))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_selected_high_columns (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    plane N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hmarked hslot hplain hmarkedHeight
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hmarked hslot hplain hmarkedHeight
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E R₂ outer hE seed₂ t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
  have hZ : 1<Z:=(by norm_num : (1:ℝ)<2).trans_le he.1
  have hZpos : 0<Z:=zero_lt_one.trans hZ
  let cost (l : κ):=balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
    outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
      (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2)
  let rhs:=Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
    (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
      Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass)))
  have hrhs : 0 ≤ rhs := by
    dsimp only [rhs]
    apply mul_nonneg (by positivity)
    exact mul_nonneg (mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)) (by positivity)
  have hc (l : κ) : 0 ≤ cost l := by
    have houter : 0 ≤ outer l := by
      dsimp only [outer]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZpos.le _)
        (div_nonneg (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*ampExponent)
          reserveShift hZpos _).le (volume_pos (firstChild l)).le))
        (normalizer_pos _ _ (datum (row l).val.1).hC _).le
    exact mul_nonneg (mul_nonneg
      (balanced_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin _ hZpos.le) houter)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  by_cases hnil : labels=∅
  · subst labels
    simp only [Finset.sum_empty]
    exact mul_nonneg hWfiber hrhs
  have hnonempty:=Finset.nonempty_iff_ne_empty.mpr hnil
  obtain ⟨pick,hpick,hinj,hsum⟩:=high_family_max_selection
    (fun r : labels=>key r.val) (fun r=>cost r.val) Wfiber hWfiber (fun r=>hc r.val) hfiber
  let Keys:=Finset.univ.image (fun r : labels=>key r.val)
  let selected (j : Keys):κ:=(pick j).val
  have hmem (j : Keys) : selected j∈labels:=(pick j).property
  haveI : Nonempty Keys := by
    obtain ⟨l,hl⟩:=hnonempty
    exact ⟨⟨key l,Finset.mem_image.mpr ⟨⟨l,hl⟩,Finset.mem_univ _,rfl⟩⟩⟩
  have hh:=he.2 (κ:=Keys) reflected second s hη R seed W D ξ hK bin
    (fun j=>column (selected j)) datum first (fun j=>row (selected j))
    (fun j=>hparent (selected j)) (fun j=>hfirst (selected j)) (fun j=>hR (selected j))
    (fun j=>ψ (selected j)) β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i
    hβ hβ' hKcontrol hT hwidthbin
    (show Function.Injective (fun j : Keys=>key (selected j)) from hinj) Finset.univ
    (fun j _=>hq (selected j) (hmem j)) hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap
    (fun j _=>hnorm (selected j) (hmem j)) (fun j _=>hradius (selected j) (hmem j))
    (fun j=>st (selected j)) (fun j=>hQM (selected j)) (fun j=>hQη (selected j))
    (fun j=>z (selected j)) (fun j=>hz (selected j)) (fun j=>hchar (selected j))
    (fun j=>hpuncture (selected j)) (fun j=>hrow (selected j))
    (fun j _=>hzero (selected j) (hmem j)) (fun j _=>hsupport (selected j) (hmem j))
    hibuffer (fun j _=>hcurrent (selected j) (hmem j)) hi hcard hM hb₁ hb₂ hupper hwin
    (fun j=>B₁ (selected j)) (fun j=>t₁ (selected j)) (fun j _=>hf₁ (selected j) (hmem j))
    (fun j=>seed₂ (selected j)) (fun j=>t (selected j)) w σ v θ (fun j=>p (selected j))
    (fun j=>Ds (selected j)) cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    (fun j _=>hseed₂ (selected j) (hmem j)) (fun j _=>hwidth (selected j) (hmem j))
    (fun j _=>hradial (selected j) (hmem j)) (fun j _=>hzeroUpper (selected j) (hmem j))
    hw hwmarked hwr hσlo hσhi (fun j _=>hheight (selected j) (hmem j))
    (fun j _=>hplainheight (selected j) (hmem j)) (fun j _=>hW (selected j) (hmem j))
    (fun j _=>hDs (selected j) (hmem j)) (fun j _=>hdyad (selected j) (hmem j))
    (fun j _=>hcontrol (selected j) (hmem j)) hledger
  have hselected : (∑j : Keys,cost (selected j)) ≤ rhs := by
    simpa only [cost,selected,rhs] using hh
  change (∑l∈labels,cost l) ≤ Wfiber*rhs
  rw [←Finset.sum_coe_sort labels cost]
  exact hsum.trans (mul_le_mul_of_nonneg_left hselected hWfiber)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_full_high_columns
