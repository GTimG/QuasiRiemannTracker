import Candidate.Uneven.BootstrapMonotone
import Candidate.Cycle63.Marked.ShellFactor
import Candidate.Cycle63.Marked.TwoCommonLargeSlotShell
import Candidate.Target830.High.VariableJointMarkedBins
import Candidate.Target830.Source.Valuation
import Candidate.Uneven.BootstrapGeometryUniform
import Candidate.Cycle63.Density.CountingSetup

/- Original module: Candidate.Uneven.BootstrapGainMonotone. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem physicalGain_monotone {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (S : ℝ) :
    Monotone (physicalGain d S) := by
  intro D D' hD
  exact FiniteGain.gain_mono (coefficient_nonneg hd0 hd1).1
    (coefficient_nonneg hd0 hd1).2 le_rfl hD


end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.BootstrapHighBins. -/
section
/- Seven-face physical shell; all source and mesh assumptions retained. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Cycle63InitialMass
open Target830
open SaturatedPlain BootstrapPlain
noncomputable section
open scoped Classical BigOperators ContDiff
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
open Cycle63MarkedPlain Marked830Plain CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M  ≤  H)

/-- Joint finite-bin high density for the physical geometric rows. The outside
weight stays inside each selected shell; only the fixed bin count is charged. -/
theorem actual_geometry_bootstrap_binned_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : HeckeZeroSupremum.beta ≤ 7/8)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)(hQmax : Q ≤ 130)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound → FineMarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=> geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=> secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=> if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width Bbox target reserve : ℝ) (i : ℕ),
      81/100  ≤  a → a ≤ 83/100 → 0  ≤  Kcontrol → 1  ≤  T → 0< width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,(4/5:ℝ) ≤ x l 2 ∧ x l 2+width ≤ Q) →
      (∀l∈labels,0 ≤ coeff l) → (∀l∈labels,coeff l ≤ Z^(x l 0)) →
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
      let first := fun l=> child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      Real.logb Z (preVolume s.toData) ≤ Araw → pad ≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  bootstrapRawMesh*fineRawCore) →
      (∑j,w j) ≤ 1/25 → (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T ≤ (L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=> commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      (∀l∈labels,x l 3=Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ)) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      (∀l∈labels,retainedHighExponent (2*a-1)
        (fun q=> Sil.Uneven.Bootstrap.physicalGain (2*a-1)
          (∑j∈largeSlots (Cycle63CommonSupply.originalSlots
            (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=> k.val.val))
            w (fineRawTiny N),w j) q) (x l) ≤ target-reserve) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))) ≤ 
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-reserve+4*width+loss+rawError+allowance+fineHighRawFee)) := by
  obtain ⟨bound,hbound,hsource⟩ := actual_two_common_large_slot_shell
    (α:=α) (bp:=bp) M H hH η₀ ε hε hap N Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨bΦ₀,hbΦ₀,hrad₀⟩ := radialMajorant_support_bound
  let bΦ := max 2 bΦ₀
  have hbΦ : 2 ≤ bΦ := le_max_left _ _
  have hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
    intro x hx
    change x ≤ max 2 bΦ₀
    have hxbound : x ≤ bΦ₀ := hrad₀ hx
    exact hxbound.trans (le_max_right 2 bΦ₀)
  obtain ⟨J,hcount⟩ := BootstrapPlain.actual_geometry_uniform_marked_count (Slot:=α) M H hH η₀ u₀ F₀ R₀ hu₀ B
    canonicalDensityCountingSetup N hB
    Wslot bΦ hWslotSupport hWslotSmooth hbΦ hrad hMarkedBeta hMarkedUpper
  obtain ⟨Cmult,hCmult,hbins⟩ := actual_variable_joint_marked_binned_bound B loss hB hloss
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hP hslot hplain hheight
  obtain ⟨F,G,Cprofile,Csrc,hF,hCprofile,hCsrc,hsource⟩ :=
    hsource P hboundeq hP.slotCap hslot hplain
  obtain ⟨Craw,hCraw,hcount⟩ := hcount P hP hslot hplain (by convert hheight using 1 <;> norm_num)
  let Cpart : ℝ := (Fintype.card (RayCharacter×RayCharacter):ℝ)*(2:ℝ)^(Fintype.card α)
  have hCpart : 0< Cpart := by dsimp only [Cpart]; positivity
  refine ⟨F,G,Cprofile,Csrc*Cpart*Cmult*Craw,hF,hCprofile,by positivity,?_⟩
  filter_upwards [hsource,hcount,eventually_geometry_marked_packet η₀ u₀ F₀ R₀ hu₀ B P.Bmask P.bΦ]
    with Z hs hc hp
  refine ⟨hs.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key a rawError allowance Kcontrol T width Bbox target reserve i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hx hq hcoeff0 hcoeff st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hmesh hsupply hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol
    hx3 hrawError hpoint
  have hZ : 1< Z := by linarith [hs.1]
  have hzpos : 0< Z := zero_lt_one.trans hZ
  have hδ : (31/50:ℝ) ≤ 2*a-1 ∧ 2*a-1 ≤ 33/50 := by
    constructor <;> linarith
  let slots := fun l=> largeSlots (Cycle63CommonSupply.originalSlots
    (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=> k.val.val)) w (fineRawTiny N)
  let amplitude := labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
    (fun l=> excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture)
  let index := fun l=>(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)
  let gain := fun (s : Finset α) (q : ℝ)=>
    Sil.Uneven.Bootstrap.physicalGain (2*a-1) (∑j∈s,w j) q
  let energy := fun l=> coeff l*Z^((2*a-1)*(x l 3-∑j∈slots l,w j))*(∏j∈slots l,max 1 ‖amplitude l j‖)^2
  have hfirstcap (l : κ)(hl : l∈labels) :
      ((geometryFirstSource s R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ) ≤ Z^B := by
    have hh := (hnorm l hl).1
    have hk : (key l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l) := by
      cases second <;> exact hfirst l
    rw [hk] at hh
    exact hh
  have hpacket (l : κ)(hl : l∈labels) := hp.2 reflected second s hη R seed K ξ hK bin (column l)
    datum first (row l) (hparent l) (hfirst l) (hR l) (ψ l) (hfirstcap l hl)
    (st l) (z l) (hz l) (hchar l) (hpuncture l) (hrow l)
  have hcount' (j : RayCharacter×RayCharacter)(ss : Finset α)(rows : Finset κ)
      (hrows : rows⊆labels.filter (fun l=> index l=j ∧ slots l=ss))
      (hinjrow : Set.InjOn (fun l=> nonzeroJointSourceRow (key l)) (↑rows:Set κ))
      (q : ℝ)(hq0 : (4/5:ℝ) ≤ q)(hq1 : q ≤ Q)
      (hrowq : ∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q) :
      (∑l∈rows,(∏k∈ss,max 1 ‖amplitude l k‖)^2) ≤ 
        Craw*Z^(unmarkedDensity (2*a-1)*q+(2*a-1)*(∑k∈ss,w k)-gain ss q+fineHighRawFee) := by
    by_cases hempty : rows=∅
    · subst rows;simp only [Finset.sum_empty];positivity
    obtain ⟨l₀,hl₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hmem (l : κ)(hl : l∈rows) : l∈labels := (Finset.mem_filter.mp (hrows hl)).1
    have hslots : slots l₀=ss := (Finset.mem_filter.mp (hrows hl₀)).2.2
    have hsmall (k : α)(hk : k∈ss) : fineRawTiny N ≤ w k := by
      rw [←hslots] at hk
      exact (Finset.mem_filter.mp hk).2
    have hh := hc.2 q hq0 (hq1.trans hQmax) j reflected second s hη R seed K ξ hK bin
      column datum first row hparent hfirst hR ψ rows hinjrow
      (fun l hl=>(Finset.mem_filter.mp (hrows hl)).2.1)
      (fun l hl=> hfirstcap l (hmem l hl)) st hQM hQη z hz hchar hpuncture hrow hrowq
      ss w σ v t θ a i hiI (by linarith) (by linarith) hsmall
      (fun k _=> hmesh k) (fun k _=> hwr k) (fun k _=> hσlo k) (fun k _=> hσhi k)
      (fun l hl=> hwidth l (hmem l hl)) (fun l hl=> hradial l (hmem l hl))
      (fun l hl=> hupper l (hmem l hl)) (fun l hl=>(hzero l (hmem l hl)).2)
      (fun l hl k _=> hfreq l (hmem l hl) k) (fun l hl=> hplainfreq l (hmem l hl))
      (surviving_width_upper ss w (1/25) hw hsupply) 0 (by norm_num)
    simpa only [Real.rpow_zero,one_mul,amplitude,hP.slot,gain,mul_comm,mul_left_comm,mul_assoc,←Target830.Source.Valuation.rho_eq_local] using hh
  have hb := hbins left u₀ unit Z hs.1 key hinj labels x energy slots index amplitude w
    (2*a-1) (4/5) Q width Bbox Craw (fineHighRawFee) target reserve gain hδ.1 (by linarith only [hδ.2]) hCraw.le hwidthbin
    (fun ss=> Sil.Uneven.Bootstrap.physicalGain_monotone hδ.1 hδ.2 (∑j∈ss,w j))
    hx hq hpoint (fun l hl=> by
      dsimp only [energy]
      rw [Real.rpow_add hzpos]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoeff l hl) (Real.rpow_nonneg hzpos.le _))
        (sq_nonneg _))
    (fun l hl=>(hzero l hl).1)
    (fun l hl=>(hzero l hl).1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(hq l hl).2])))
    (fun l hl=>(hpacket l hl).2.2.2.1) (fun l hl=>(hpacket l hl).2.2.2.2)
    hsupport hnorm hmissing (fun j ss rows hrows hinjrow q hq0 hq1 hrowq =>
      hcount' j ss rows (by simpa only [Finset.subset_iff, Finset.mem_filter] using hrows)
        hinjrow q hq0 hq1 hrowq)
  have he := hs.2 labels st hQM hQη z hz a allowance Kcontrol T i (by linarith) (by linarith)
    hKcontrol hT hi s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ E R₂ pick t w σ v θ
    p Ds cap Araw (fineRawTiny N) hcap hmatches hscales hAraw hpadallow hf₂ hstateMask hwidth
    hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad coeff hcoeff0 hcontrol
  have hsumeq : (∑l∈labels,coeff l*
      Z^((2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ)-∑k∈slots l,w k))*
      (∏k∈slots l,max 1 ‖amplitude l k‖)^2)=∑l∈labels,energy l := by
    apply Finset.sum_congr rfl;intro l hl;rw [←hx3 l hl]
  change _ ≤ Csrc*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
    Z^(allowance+pad+2*P.εplain*P.d+(2*P.εslot*P.d)*N)*
    (∑l∈labels,coeff l*Z^((2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
      Real.logb Z ((E l).absNorm:ℝ)-∑k∈slots l,w k))*(∏k∈slots l,max 1 ‖amplitude l k‖)^2) at he
  rw [hsumeq] at he
  have hfac : 0 ≤ Csrc*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
      Z^(allowance+pad+2*P.εplain*P.d+(2*P.εslot*P.d)*N) := by positivity
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hb hfac).trans
  let count : ℝ := ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)
  have hpow : Z^(allowance+pad+2*P.εplain*P.d+(2*P.εslot*P.d)*N)*
      Z^(target-reserve+4*width+loss+fineHighRawFee) ≤ 
      Z^(target-reserve+4*width+loss+rawError+allowance+fineHighRawFee) := by
    rw [←Real.rpow_add hzpos]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith only [hrawError]
  have hheightfactor : (1:ℝ) ≤ (1+3*(i+1:ℕ)*Z^P.τ)^J := by
    apply one_le_pow₀
    exact le_add_of_nonneg_right
      (mul_nonneg (by positivity) (Real.rpow_nonneg hzpos.le _))
  exact Cycle63MarkedPlain.marked_shell_scalar_factor
    Csrc Cpart Cmult Craw Cprofile Kcontrol ((2*T)^(2*ε))
    ((1+3*(i+1:ℕ)*Z^P.τ)^J) count
    (Z^(allowance+pad+2*P.εplain*P.d+(2*P.εslot*P.d)*N))
    (Z^(target-reserve+4*width+loss+fineHighRawFee))
    (Z^(target-reserve+4*width+loss+rawError+allowance+fineHighRawFee))
    hCsrc.le hCpart.le hCmult.le hCraw.le hKcontrol
    (Real.rpow_nonneg (by linarith only [hT]) _) hheightfactor
    (Nat.cast_nonneg _) (Real.rpow_nonneg hzpos.le _) hpow

end
end OAI.SevenEighths.TargetHigh830
end
