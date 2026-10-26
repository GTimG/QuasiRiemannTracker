import Candidate.Target836.High836.GeometryMarkedBins
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Target836.High836.VariableJointMarkedBins
import Candidate.Cycle63.Marked.GeometryUniformMarkedCount
import Candidate.Cycle63.Density.CountingSetup

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
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
open Cycle63MarkedPlain CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M  ≤  H)

theorem actual_geometry_marked_paid_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1 ≤ 94/125)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)(hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound → MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/800000000 →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
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
        (a rawError allowance Kcontrol T width Bbox target reserve : ℝ) (i : ℕ),
      2089/2500  ≤  a → a  ≤  17/20 → 0  ≤  Kcontrol → 1  ≤  T → 0<width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,(4/5:ℝ) ≤ x l 2 ∧ x l 2+width ≤ Q) →
      (∀l∈labels,0 ≤ coeff l) → (∀l∈labels,coeff l ≤ Z^(x l 0)) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B →
      |Real.logb Z (volume s.toData)| ≤ B → lo ≤  s.lower →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l))  ≤  Z^(x l 2) ∧
        a  ≤  HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          ((3*i : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ)  ≤  Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^(x l 1)) →
      (i:ℝ) ≤ Z^P.τ → i ≤ bufferCount P.e →
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      s.b₁ ≤ bs → s.b₂ ≤ bs → s.upper ≤ b →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
      ∀(C₁ R₁ : κ→Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R₂ : κ→Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      Real.logb Z (preVolume s.toData) ≤ Araw → pad ≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R₂ l*E l)) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  markedRawMesh*markedCoreMin) →
      (∑j,w j) ≤ 1/25 → (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T ≤ (L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      (∀l∈labels,x l 3=Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ)) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      (∀l∈labels,retainedHighExponent (2*a-1)
        (fun q=>(Marked836.VariableSupply.coefficient (2*a-1))*min
          (∑j∈largeSlots (Cycle63CommonSupply.originalSlots
            (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>k.val.val))
            w (markedTinyWidth N),w j) ((13/400)*((122/125)*q))) (x l) ≤ 
              geometryHighSide reflected (Real.logb Z (volume s.toData))
                (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)+target-reserve) →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))) ≤ 
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-reserve+4*width+loss+rawError+allowance+B*εmass+(1/200000:ℝ))) := by
  obtain ⟨bound,hbound,J,hbinned⟩ := actual_geometry_marked_binned_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper
      B Q loss ε hB hQ hQB hQmax hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hP hslot hplain hheight
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hbinned P hboundeq hP hslot hplain hheight
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key a rawError allowance Kcontrol T width Bbox target reserve i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hx hq hcoeff0 hcoeff hseed hz₁ hz₂ hsource hAbox hlower
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hmesh hsupply hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hx3 hrawError hpoint
  have hZ : 1<Z := by linarith [he.1]
  have hzpos : 0<Z := zero_lt_one.trans hZ
  let side := fun l=>geometryHighSide reflected (Real.logb Z (volume s.toData))
    (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let scale := factor*Z^(B*εmass)
  let mass := fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)
  let xc := fun l=>compensatedHighCoordinates (x l) (side l)
  let cc := fun l=>mass l*coeff l/scale
  have hfactor : 0<factor := geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have hscale : 0<scale := mul_pos hfactor (Real.rpow_pos_of_pos hzpos _)
  have hsbox (l : κ) : |side l| ≤ 5*B := by
    apply geometry_high_side_box reflected _ B _ hB hAbox
    intro j
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val j
    exact ⟨Real.logb_nonneg hZ hn.1,(Real.logb_le_iff_le_rpow hZ
      (zero_lt_one.trans_le hn.1)).mpr hn.2⟩
  have hcc (l : κ)(hl : l∈labels) : cc l ≤ Z^(xc l 0) := by
    apply (div_le_iff₀ hscale).mpr
    have hs₁ (u : ℝ)(hu : s.W₁ u≠0) : ap ≤ u := by
      have hw : ((p l).profile 0) u≠0 := by
        simpa only [←(hW l hl).1] using hu
      exact ((p l).support 0 hw).1
    have hs₂ (u : ℝ)(hu : s.W₂ u≠0) : ap ≤ u := by
      have hw : ((p l).profile 1) u≠0 := by
        simpa only [←(hW l hl).2.1] using hu
      exact ((p l).support 1 hw).1
    have hm:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z ξ B εmass
      hZ hK hεmass hcard hlower hseed hz₁ hz₂ hsource hs₁ hs₂ bin (column l)
    have hh:=compensated_high_coefficient Z (mass l) (coeff l) factor (B*εmass) (side l) (x l)
      hzpos (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l)) hm
      (hcoeff l hl)
    simpa only [scale,xc,mul_comm] using hh
  have hxc (l : κ)(hl : l∈labels) : ∀j,-(Bbox+5*B) ≤ xc l j ∧ xc l j ≤ Bbox+5*B :=
    compensated_high_coordinate_box (x l) (side l) Bbox (5*B) (hx l hl) (hsbox l)
  have hcc0 (l : κ)(hl : l∈labels) : 0 ≤ cc l := by
    exact div_nonneg (mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l))
      (hcoeff0 l hl)) hscale.le
  have hp (l : κ)(hl : l∈labels) : retainedHighExponent (2*a-1)
      (fun q=>(Marked836.VariableSupply.coefficient (2*a-1))*min
        (∑j∈largeSlots (Cycle63CommonSupply.originalSlots
          (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>k.val.val))
          w (markedTinyWidth N),w j) ((13/400)*((122/125)*q))) (xc l) ≤ target-reserve := by
    have hh:=hpoint l hl
    have hx2 : xc l 2 = x l 2 := by
      simp [xc,compensatedHighCoordinates,childHighCoordinates]
    have hxe : highExponentValue (2*a-1) (xc l) =
        highExponentValue (2*a-1) (x l)-side l :=
      compensated_high_exponent (2*a-1) (side l) (x l)
    dsimp only [retainedHighExponent] at hh ⊢
    rw [hxe,hx2]
    change highExponentValue (2*a-1) (x l)-_ ≤  side l+target-reserve at hh
    linarith only [hh]
  have hj:=he.2 reflected second s hη R seed (Z^D) ξ hK bin column datum first row hparent hfirst hR ψ
    a rawError allowance Kcontrol T width (Bbox+5*B) target reserve i ha ha' hKcontrol hT hwidthbin hinj
    labels xc cc hxc (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (2:Fin 4)≠0 by decide,ite_false,add_zero] using hq) hcc0 hcc
    st hQM hQη z hz hchar hpuncture hrow
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (2:Fin 4)≠0 by decide,ite_false,add_zero] using hzero)
    hsupport hnorm
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (1:Fin 4)≠0 by decide,ite_false,add_zero] using hmissing)
    hi hiI hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hmesh hsupply hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (3:Fin 4)≠0 by decide,ite_false,add_zero] using hx3) hrawError hp
  have hh:=mul_le_mul_of_nonneg_left hj hscale.le
  calc
    _=scale*(∑l∈labels,cc l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
      retainedAllocationCost (src l) L alloc (z l))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [cc,mass]
      field_simp [ne_of_gt hscale]
    _ ≤ _ := hh
    _=_ := by
      dsimp only [scale,factor]
      simp only [Real.rpow_add hzpos]
      ring

end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.actual_geometry_marked_paid_shell
