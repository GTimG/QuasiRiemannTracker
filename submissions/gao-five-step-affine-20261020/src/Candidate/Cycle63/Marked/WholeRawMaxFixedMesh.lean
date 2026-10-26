import Candidate.Cycle63.Marked.WholeRawGates
import Candidate.Cycle63.Marked.WholePaddedCoreFixedMesh
import Candidate.Cycle63.Marked.AmplitudeCap
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily ProbePhysical LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
open Deletion26
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual whole-family max-product count on raw frequencies. Every small
sixth-root fiber is counted by the marked source; large roots use the
verified ordinary density. Only literal source, buffer, and slot gates remain. -/
theorem actual_whole_raw_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→ Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0<ordloss) (htail : 0<tailε) (htailmax : tailε≤5/7)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost) :
    ∃J : ℕ,∀(Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss : ℝ) (I : ℕ)
    (_hDmin : 0< Dmin) (_hDmax : Dmin≤ Dmax) (_hκroot : 0≤κroot) (_hκrootmax : κroot<1/6)
    (_hdsmall : dmin≤ Dmin*(1-6*κroot)) (_hdlarge : Dmax+pad≤ dmax)
    (_hBmask : 0≤ Bmask) (_hCcap : 0≤ Ccap) (_hslotloss : slotloss≤ binWidth*wmin)
    (_hpad : 0< pad) (_hwmin : 0< wmin) (_hdmin : 0< dmin) (_hdmax : dmin≤ dmax) (_hτ : 0<τ)
    (_hτzero : τ< dmin/2) (_hτheight : 4*τ< dmin*ηw)
    (_hε : 0<ε) (_hεsmall : ε≤1/1000) (_he : 0< e) (_he' : e<1/1000)
    (_hκw : 0<κw) (_hκw' : κw≤1) (_hηw : 0≤ηw)
    (_hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
      ∃C : ℝ,0<C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀D : ℝ,Dmin≤ D → D≤ Dmax →
      ∀(rows : Finset NonzeroFrequency)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : NonzeroFrequency→ℝ)(θ : Slot→RayQuotient.Characters M H)
        (χ : NonzeroFrequency→ Character)(holes : NonzeroFrequency→ Ideal O),
      (∀u∈rows,rawFrequencyNorm u≤ U^D) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      (∀u∈rows,holes u≠0) → (∀u∈rows,((holes u).absNorm:ℝ)≤ U^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop →
      0≤ mesh → mesh≤ markedPlainMesh (Cycle63.Optimization.plainCapacityCost) εm → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh*dmin) →
      0≤ height → 2*Real.pi*U^(τ/2)+(3*i:ℕ)*U^τ≤ height →
      (∀s∈slots,|v s|≤ height) → (∀u∈rows,|t u|≤ height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a≤ zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,(max 1 ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2
        ≤ Ccap*U^((2*a-1)*w s+slotloss)) →
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      let A:=(2*a-1+2*binWidth)*S+dmax*(156*ε+mesh+εm+ηloss)+pad*ρ
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2)≤
        C*(1+height)^J*U^(D*(ρ+ordloss)+A-
          min (Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D)) (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  have hcount := actual_whole_padded_core_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ηloss
    hWs hW hbΦ hrad hbin hη hεm hβ hκβ
  obtain ⟨E,J,hcount⟩ := hcount
  let Dict:=FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)
  obtain ⟨J₀,C₀,D₀,hC₀,hD₀,hlift⟩ := actual_marked_raw_from_small_roots Dict ordloss tailε
    hordloss htail htailmax
  refine ⟨J+J₀,?_⟩
  intro Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBmask hCcap hslotloss hpad hwmin
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw pad wmin I
    hpad hwmin hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  let Csmall := (4:ℝ)^Fintype.card Slot*C+(E.card:ℝ)
  have hCs : 0< Csmall := by dsimp [Csmall];positivity
  refine ⟨(Csmall+C₀)*D₀,by positivity,?_⟩
  filter_upwards [hcount,
    eventually_raw_clean_slot_comparison (wholeAnchorMask M H hH η₀)
      (wholeAnchorMask_ne_zero M H hH η₀) W 1 2 lo hi Bmask (Dmax*κroot) wmin
      (by norm_num) hWs hW.continuous hBmask (mul_nonneg (hDmin.trans_le hDmax).le hκroot) hwmin,
    eventually_amplitude_cap Ccap slotloss binWidth wmin hbin hwmin hslotloss,
    eventually_amplitude_cap (4*Ccap) slotloss binWidth wmin hbin hwmin hslotloss]
    with U hcount hclose hrawcap hcorecap
  refine ⟨hcount.1,?_⟩
  intro D hD hD' rows slots w σ v t θ χ holes hrow hw hlo hhi hholes hholecap hcoeff
    a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht hχ hnext hcurrent hslot S ρ A
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hUp : 0< U := zero_lt_one.trans hcount.1
  have hDp : 0< D := hDmin.trans_le hD
  have hUraw : 1< U^D := Real.one_lt_rpow hcount.1 hDp
  have hrawScale (x : ℝ) : (U^D)^(x/D)=U^x := by
    rw [←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hDp.ne']
  have hρ : 2/7≤ρ := unmarkedDensity_ge_two_sevenths (by linarith)
  have hdpmax : 0< dmax := hdmin.trans_le hdmax
  have hA : (2*a-1+2*binWidth)*S≤ A := by
    dsimp [A]
    have hL : 0≤156*ε+mesh+εm+ηloss := by positivity
    linarith only [mul_nonneg hdpmax.le hL,mul_nonneg hpad.le (show 0≤ρ by linarith only [hρ])]
  let f := fun u:NonzeroFrequency=>(∏s∈slots,max 1 ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2
  have hpoint (u : NonzeroFrequency) (hu : u∈rows) : f u≤ U^A := by
    apply (max_product_power_envelope slots (wholeRawSlot M H hH η₀ W U w σ v t θ χ u)
      U (2*a-1) binWidth w hcount.1.le (by linarith)
      (fun s hs=>(hwmin.trans_le (hw s hs)).le) (fun s hs=>hrawcap.2 (2*a-1) (w s) (hw s hs) _ ?_)).trans
    · exact Real.rpow_le_rpow_of_exponent_le hcount.1.le hA
    · have hn:=le_max_right (1:ℝ) ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hslot u hu s hs)
  have hheight : (3*i:ℕ)*U^τ≤ height := by
    have hp : 0≤2*Real.pi*U^(τ/2) := by positivity
    linarith
  have hR : ∀u∈rows,rawFrequencyNorm u≤ U^D ∧ orientedActualZeroRow Dict.data (fun _=>false) a height u := by
    intro u hu
    refine ⟨hrow u hu,whole_maximum_to_actual_zero_row M H hH η η₀ (χ u) u (holes u)
      (hholes u hu) (hcoeff u hu) (hχ u hu) a _ height (by linarith) (hcurrent ⟨u,hu⟩) hheight⟩
  have hsmall (B : NZIdeal) (hB : (B.val.absNorm:ℝ)≤(U^D)^κroot) :
      (∑u∈sixthFreeFiber rows B,f (sixthFrequencyEquiv (u,B)))≤
        (Csmall*(1+height)^J)*U^(A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))*
          (U^D/(B.val.absNorm:ℝ)^6)^(ρ+ordloss) := by
    let Y:=U^D/(B.val.absNorm:ℝ)^6
    have hBN : 1≤(B.val.absNorm:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hBp : 0<(B.val.absNorm:ℝ) := zero_lt_one.trans_le hBN
    obtain ⟨q,hq,hq0,hq1,hqbase,hqscale⟩ := core_window_scale (U^D) _ κroot
      hUraw hBN hκrootmax hB
    let d:=D*q+pad
    have hd : 0< d := by dsimp [d];positivity
    have hDcore : dmin≤ D*(1-6*κroot) := hdsmall.trans
      (mul_le_mul_of_nonneg_right hD (by linarith))
    have hdmin' : dmin≤ d := by
      have hm:=mul_le_mul_of_nonneg_left hq0 hDp.le
      dsimp [d];linarith
    have hdmax' : d≤ dmax := by
      have hm:=mul_le_mul_of_nonneg_left hq1 hDp.le
      dsimp [d];linarith
    have hbase : U^d=Y*U^pad := by
      dsimp [d,Y]
      rw [Real.rpow_add hUp,Real.rpow_mul hUp.le,hqbase]
    have hBglobal : (B.val.absNorm:ℝ)≤ U^(Dmax*κroot) := by
      apply hB.trans
      rw [←Real.rpow_mul hUp.le]
      exact Real.rpow_le_rpow_of_exponent_le hcount.1.le
        (mul_le_mul_of_nonneg_right hD' hκroot)
    have hY : 1≤ Y := (Real.one_le_rpow hUraw.le (by linarith : 0≤1-6*κroot)).trans
      (small_root_window (U^D) _ κroot hUraw hBN hB).1
    let F:=(sixthFreeFiber rows B).filter (fun u=>u∉E)
    let raw:=fun u:FreeRow=>sixthFrequencyEquiv (u,B)
    let tc:=fun u:FreeRow=>t (raw u)
    let χc:=fun u:FreeRow=>χ (raw u)
    let Rc:=fun u:FreeRow=>B.val*holes (raw u)
    let Qc:=wholeCleanSlot M H hH η η₀ W U w σ v tc θ
    let Qp:=fun (u:FreeRow)(s:Slot)=>naturalSlot
      (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
      (primePool M H 2 (U^(w s)))
      (heightCoefficient (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) K) (tc u)) (U^(w s))
    have hmem (u:FreeRow) (hu:u∈F) : raw u∈rows :=
      sixth_fiber_raw_mem rows B u (Finset.mem_filter.mp hu).1
    have hQnorm (u:FreeRow)(s:Slot) : ‖Qp u s‖=‖Qc u s‖ :=
      wholeCleanSlot_height_norm M H hH η η₀ W U hUp w σ v tc θ u s
    have hnear (u:FreeRow)(hu:u∈F)(s:Slot)(hs:s∈slots) :
        ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ (raw u) s-Qp u s‖≤1/2 :=
      hclose.2 η (relativeCharacter M H hH η₀ (θ s)) (χ (raw u)) u B (holes (raw u))
        (hholes _ (hmem u hu)) (hholecap _ (hmem u hu)) hBglobal (hcoeff _ (hmem u hu))
        (primePool M H 2 (U^(w s))) (fun K hK=>(Finset.mem_filter.mp hK).2.1)
        (w s) (σ s) (v s) (tc u) (hw s hs) (hlo s hs) (hhi s hs)
    have hQ (u:FreeRow)(hu:u∈F)(s:Slot)(hs:s∈slots) : ‖Qc u s‖≤(U^(w s))^((2*a-1)/2+binWidth) := by
      rw [←hQnorm]
      apply hcorecap.2 (2*a-1) (w s) (hw s hs)
      have hp:=slot_cap_of_nearby
        (wholeRawSlot M H hH η₀ W U w σ v t θ χ (raw u) s) (Qp u s)
        (Ccap*U^((2*a-1)*w s+slotloss)) (hslot _ (hmem u hu) s hs)
        (by rw [norm_sub_rev];exact hnear u hu s hs)
      have hn:=le_max_right (1:ℝ) ‖Qp u s‖
      calc
        ‖Qp u s‖^2≤(max 1 ‖Qp u s‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ ≤ 4*(Ccap*U^((2*a-1)*w s+slotloss)) := hp
        _ = _ := by ring
    have hfreq : 2*Real.pi*(U^d)^(τ/(2*dmax))+(3*i:ℕ)*U^τ≤ height := by
      apply le_trans _ hf
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _≤(U^dmax)^(τ/(2*dmax)) := Real.rpow_le_rpow (Real.rpow_nonneg hUp.le _)
          (Real.rpow_le_rpow_of_exponent_le hcount.1.le hdmax') (by positivity)
        _=U^(τ/2) := by rw [←Real.rpow_mul hUp.le];congr 1;field_simp
    let hc : ∀u∈F,∀j,(wholeSourceFamily M H hH η₀ (χc u) j).residue≠1 :=
      fun u hu=>hχ _ (hmem u hu)
    have hcore:=hcount.2 Y d hdmin' hdmax' hbase F slots w σ v tc θ
      (fun u hu=>(Finset.mem_filter.mp hu).2)
      (fun u hu=>sixth_fiber_core_norm rows B (U^D) hrow u (Finset.mem_filter.mp hu).1)
      hw hlo hhi χc Rc (fun u hu=>mul_ne_zero B.property (hholes _ (hmem u hu)))
      (fun u hu=>sixth_core_mask_coefficients η (χc u) u B (holes (raw u))
        (hholes _ (hmem u hu)) (hcoeff _ (hmem u hu)))
      a mesh height i hiI ha0 ha hmesh hmeshmax hbin'
      (fun s hs=>(hwm s hs).trans (mul_le_mul_of_nonneg_left hdmin' hmesh)) hh hfreq hv
      (fun u hu=>ht _ (hmem u hu)) hc
      (fun u=>hnext ⟨raw u.val,hmem u.val u.property⟩)
      (fun u=>hcurrent ⟨raw u.val,hmem u.val u.property⟩) hQ
    have hcore' : (∑u∈F,(∏s∈slots,max 1 ‖Qc u s‖)^2)≤
        (C*(1+height)^J)*(U^(A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))*Y^(ρ+ordloss)) := by
      apply hcore.trans
      have he : (2*a-1+2*binWidth)*S-Cycle63.Optimization.markedGain (2*a-1) S d+
          dmax*(156*ε+mesh+εm+ηloss)+pad*VariableSupply.density (2*a-1)=
          A-Cycle63.Optimization.markedGain (2*a-1) S d := by dsimp [A,ρ,VariableSupply.density,unmarkedDensity];ring
      change _≤_
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul
      · apply Real.rpow_le_rpow_of_exponent_le hcount.1.le
        have hdcore : (1-6*κroot)*D≤d := by
          have hm:=mul_le_mul_of_nonneg_left hq0 hDp.le
          dsimp [d];linarith only [hm,hpad]
        have hm := Cycle63.Optimization.markedGain_mono_frequency (d := 2*a-1) (S := S) (by linarith only [ha0, Cycle63.Arithmetic.q0_bounds.1]) (by linarith only [ha, Cycle63.Optimization.markedBinTop_bounds.2]) hdcore
        linarith only [hm]
      · exact Real.rpow_le_rpow_of_exponent_le hY (by change ρ≤ρ+ordloss;linarith)
      · positivity
      · positivity
    have hgain : Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D)≤D*(1-6*κroot)*(ρ+ordloss) := by
      have hm := Cycle63.Optimization.markedGain_le_capacity (d := 2*a-1) (S := S) (F := (1-6*κroot)*D) (by linarith only [ha0, Cycle63.Arithmetic.q0_bounds.1]) (by linarith only [ha, Cycle63.Optimization.markedBinTop_bounds.2])
      have hb : Cycle63.Optimization.capCoefficient (2*a-1)≤ρ+ordloss := by
        linarith [Cycle63.Optimization.capCoefficient_lt ⟨ha0, ha⟩]
      have hn:=mul_le_mul_of_nonneg_right hb (mul_nonneg (by linarith only [hκrootmax] : 0≤1-6*κroot) hDp.le)
      linarith only [hm,hn]
    have hgain' : (Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D≤(1-6*κroot)*(ρ+ordloss) := by
      apply (div_le_iff₀ hDp).mpr
      linarith only [hgain]
    have henv:=small_root_exception_envelope (U^D) _ κroot (ρ+ordloss) (A/D)
      ((Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D) hUraw hBN hB (by linarith) hgain'
    have hdiff : A/D-(Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D=
        (A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D := by ring
    rw [hdiff,hrawScale,hrawScale] at henv
    have hext:=finite_exception_weighted_extension (sixthFreeFiber rows B) E (fun u=>f (raw u))
      ((4:ℝ)^slots.card*(C*(1+height)^J)) (U^A)
      (U^(A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))*Y^(ρ+ordloss)) (by positivity) henv
      (fun u hu=>hpoint _ (sixth_fiber_raw_mem rows B u hu)) ?_
    · apply hext.trans
      rw [mul_assoc (Csmall*(1+height)^J)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h4 : (4:ℝ)^slots.card≤(4:ℝ)^Fintype.card Slot :=
        pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ slots)
      have hhJ : 1≤(1+height)^J := one_le_pow₀ (by linarith)
      have hP : 0≤(1+height)^J := zero_le_one.trans hhJ
      dsimp [Csmall]
      linarith only [mul_le_mul_of_nonneg_right h4 (mul_nonneg hC.le hP),
        mul_le_mul_of_nonneg_left hhJ (show 0≤(E.card:ℝ) by positivity)]
    · calc
        _≤(4:ℝ)^slots.card*(∑u∈F,(∏s∈slots,max 1 ‖Qc u s‖)^2) := by
          rw [Finset.mul_sum]
          have hpAll:=Finset.sum_le_sum (s:=F) (fun u hu=>
            max_slot_product_comparison slots
              (wholeRawSlot M H hH η₀ W U w σ v t θ χ (raw u)) (Qp u) (hnear u hu))
          simp only [hQnorm] at hpAll
          convert hpAll using 1
          congr 1
          ext u
          simp [F]
        _≤(4:ℝ)^slots.card*((C*(1+height)^J)*
            (U^(A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))*Y^(ρ+ordloss))) :=
          mul_le_mul_of_nonneg_left hcore' (by positivity)
        _=_ := by ring
  have hsmall' (B:NZIdeal) (hB:(B.val.absNorm:ℝ)≤(U^D)^κroot) := hsmall B hB
  have hsum:=hlift J Csmall hCs.le (fun _=>false) a height (U^D) κroot (A/D)
    ((Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D) (by linarith) (by linarith) hh hUraw.le hκroot rows f hR
    (fun u hu=>by rw [hrawScale];exact hpoint u hu)
    (fun B hB=>by
      rw [show A/D-(Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D=
        (A-Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D))/D by ring,hrawScale]
      exact hsmall B hB)
  apply hsum.trans_eq
  congr 1
  rw [←Real.rpow_mul hUp.le]
  congr 1
  rw [mul_sub,mul_add,mul_min_of_nonneg _ _ hDp.le,mul_div_cancel₀ _ hDp.ne',mul_div_cancel₀ _ hDp.ne']
  dsimp only [ρ]
  ring_nf

end
end OAI.SevenEighths.Cycle63MarkedPlain
