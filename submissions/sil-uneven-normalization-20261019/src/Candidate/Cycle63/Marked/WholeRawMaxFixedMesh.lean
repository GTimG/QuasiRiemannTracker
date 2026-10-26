import Candidate.Cycle63.Marked.WholeCoreGates
import Candidate.Cycle63.Marked.WholeBufferedMaxFixedMesh
import Candidate.Cycle63.Marked.DeletionRawPadded
import Candidate.Cycle63.Marked.WholeRawGates
import Candidate.Cycle63.Marked.AmplitudeCap

/- Original module: Candidate.Cycle63.Marked.WholePaddedCoreFixedMesh. -/
section

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual padded core source count in physical slot widths. The finite
exception set, modulus padding, embedding cap, inverse conductor threshold,
and both buffered-maximum transports are proved inside this adapter. -/
theorem actual_whole_padded_core_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃E : Finset FreeRow,∃J : ℕ,∀(dmin dmax τ ε e κw ηw pad wmin : ℝ) (I : ℕ)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
      ∃C : ℝ,0< C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀Y d : ℝ,dmin≤ d → d≤ dmax → U^d=Y*U^pad →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀u∈rows,u∉E) → (∀u∈rows,rowNorm u≤ Y) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh*d) →
      0≤ height → 2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ≤ height →
      (∀s∈slots,|v s|≤ height) → (∀u∈rows,|t u|≤ height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a≤ zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖
        ≤(U^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖)^2)≤
        C*(1+height)^J*
        (U^((2*a-1+2*binWidth)*(∑s∈slots,w s)-(224/1755)*min (∑s∈slots,w s) ((13/400)*d)+
          dmax*(156*ε+mesh+εm+ηloss)+pad*VariableSupply.density (2*a-1))*
          Y^VariableSupply.density (2*a-1)) := by
  obtain ⟨E,hE⟩ := whole_core_exception_set M H hH η η₀ bad hbad0 hbadTop hbad72
  obtain ⟨J,hcount⟩ := actual_whole_max_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨E,J,?_⟩
  intro dmin dmax τ ε e κw ηw pad wmin I hpad hwmin hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_whole_core_norm_caps M H hH η η₀ pad hpad,
    eventually_whole_core_inverse_large M H hH η η₀ wmin hwmin]
    with U hcount hnorms hlarge
  refine ⟨hcount.1,?_⟩
  intro Y d hd hd' hbase rows slots w σ v t θ hrows hrow hw hlo hhi
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht
    hχ hnext hcurrent hQ
  have hUp : 0< U := zero_lt_one.trans hcount.1
  have hdp : 0< d := hdmin.trans_le hd
  have hscale (s : Slot) : (U^d)^(w s/d)=U^(w s) := by
    rw [←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hdp.ne']
  have hYs : 0< Y*U^pad := hbase ▸ Real.rpow_pos_of_pos hUp d
  have hY : 0< Y := (mul_pos_iff.mp hYs).elim (fun h=>h.1)
    (fun h=>False.elim ((not_lt_of_ge (Real.rpow_nonneg hUp.le _)) h.2))
  have he := hcount.2 d hd hd' rows slots (fun s=>w s/d) σ v t θ
    (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hdp) hlo hhi
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).1)
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.1)
    (fun u hu=>(hE u).mp (hrows u hu))
    (fun s hs j=>by rw [hscale];exact hlarge.2 (w s) (hw s hs) j)
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin'
    (fun s hs=>(div_le_iff₀ hdp).mpr (hwm s hs)) hh hf hv ht hχ hnext hcurrent
    (fun u hu j=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.2 j)
    (fun u hu s hs=>by rw [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',hscale];exact hQ u hu s hs)
  simp only [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',←Finset.sum_div] at he
  have heq : VariableSupply.density (2*a-1)+(2*a-1)*((∑s∈slots,w s)/d)-
      (224/1755)*min ((∑s∈slots,w s)/d) (13/400)+
      156*ε+mesh+εm+2*binWidth*((∑s∈slots,w s)/d)+ηloss =
      VariableSupply.density (2*a-1)+(2*a-1+2*binWidth)*((∑s∈slots,w s)/d)-
        (224/1755)*min ((∑s∈slots,w s)/d) (13/400)+(156*ε+mesh+εm+ηloss) := by
    ring
  rw [heq] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Deletion26.rescaled_marked_power_padded U Y d d dmax pad
    (VariableSupply.density (2*a-1)) (2*a-1+2*binWidth) (∑s∈slots,w s)
    (224/1755) (13/400) (156*ε+mesh+εm+ηloss) hcount.1.le hY hdp le_rfl hd' hbase
    (by norm_num) (by norm_num) (by positivity)

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_whole_padded_core_weighted_fixedmesh
end

/- Original module: Candidate.Cycle63.Marked.WholeRawMaxFixedMesh. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily ProbePhysical LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
open Deletion26
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual whole-family max-product count on raw frequencies. Every small
sixth-root fiber is counted by the marked source; large roots use the
verified ordinary density. Only literal source, buffer, and slot gates remain. -/
theorem actual_whole_raw_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0<ordloss) (htail : 0<tailε) (htailmax : tailε≤5/7)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃J : ℕ,∀(Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss : ℝ) (I : ℕ)
    (hDmin : 0< Dmin) (hDmax : Dmin≤ Dmax) (hκroot : 0≤κroot) (hκrootmax : κroot<1/6)
    (hdsmall : dmin≤ Dmin*(1-6*κroot)) (hdlarge : Dmax+pad≤ dmax)
    (hBmask : 0≤ Bmask) (hCcap : 0≤ Ccap) (hslotloss : slotloss≤ binWidth*wmin)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2),
      ∃C : ℝ,0<C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀D : ℝ,Dmin≤ D → D≤ Dmax →
      ∀(rows : Finset NonzeroFrequency)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : NonzeroFrequency→ℝ)(θ : Slot→RayQuotient.Characters M H)
        (χ : NonzeroFrequency→Character)(holes : NonzeroFrequency→Ideal O),
      (∀u∈rows,rawFrequencyNorm u≤ U^D) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      (∀u∈rows,holes u≠0) → (∀u∈rows,((holes u).absNorm:ℝ)≤ U^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
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
          min ((224/1755)*min S ((13/400)*((1-6*κroot)*D))) (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  obtain ⟨E,J,hcount⟩ := actual_whole_padded_core_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
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
    nlinarith [mul_nonneg hdpmax.le hL,mul_nonneg hpad.le (show 0≤ρ by linarith)]
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
        (Csmall*(1+height)^J)*U^(A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))*
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
        (C*(1+height)^J)*(U^(A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))*Y^(ρ+ordloss)) := by
      apply hcore.trans
      have he : (2*a-1+2*binWidth)*S-(224/1755)*min S ((13/400)*d)+
          dmax*(156*ε+mesh+εm+ηloss)+pad*VariableSupply.density (2*a-1)=
          A-(224/1755)*min S ((13/400)*d) := by dsimp [A,ρ,VariableSupply.density,unmarkedDensity];ring
      change _≤_
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul
      · apply Real.rpow_le_rpow_of_exponent_le hcount.1.le
        have hdcore : (1-6*κroot)*D≤d := by
          have hm:=mul_le_mul_of_nonneg_left hq0 hDp.le
          dsimp [d];nlinarith
        have hm:=min_le_min_left S (mul_le_mul_of_nonneg_left hdcore (show 0≤(13/400:ℝ) by norm_num))
        linarith
      · exact Real.rpow_le_rpow_of_exponent_le hY (by change ρ≤ρ+ordloss;linarith)
      · positivity
      · positivity
    have hgain : (224/1755)*min S ((13/400)*((1-6*κroot)*D))≤D*(1-6*κroot)*(ρ+ordloss) := by
      have hm := mul_le_mul_of_nonneg_left (min_le_right S ((13/400)*((1-6*κroot)*D)))
        (show 0≤(224/1755:ℝ) by norm_num)
      have hb : (224/1755)*(13/400)≤ρ+ordloss := by linarith
      have hn:=mul_le_mul_of_nonneg_right hb (mul_nonneg (by linarith : 0≤1-6*κroot) hDp.le)
      nlinarith
    have hgain' : ((224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D≤(1-6*κroot)*(ρ+ordloss) := by
      apply (div_le_iff₀ hDp).mpr
      nlinarith [hgain]
    have henv:=small_root_exception_envelope (U^D) _ κroot (ρ+ordloss) (A/D)
      (((224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D) hUraw hBN hB (by linarith) hgain'
    have hdiff : A/D-((224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D=
        (A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D := by ring
    rw [hdiff,hrawScale,hrawScale] at henv
    have hext:=finite_exception_weighted_extension (sixthFreeFiber rows B) E (fun u=>f (raw u))
      ((4:ℝ)^slots.card*(C*(1+height)^J)) (U^A)
      (U^(A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))*Y^(ρ+ordloss)) (by positivity) henv
      (fun u hu=>hpoint _ (sixth_fiber_raw_mem rows B u hu)) ?_
    · apply hext.trans
      rw [mul_assoc (Csmall*(1+height)^J)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h4 : (4:ℝ)^slots.card≤(4:ℝ)^Fintype.card Slot :=
        pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ slots)
      have hhJ : 1≤(1+height)^J := one_le_pow₀ (by linarith)
      dsimp [Csmall]
      nlinarith [mul_le_mul_of_nonneg_right h4 (mul_nonneg hC.le (by positivity)),
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
            (U^(A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))*Y^(ρ+ordloss))) :=
          mul_le_mul_of_nonneg_left hcore' (by positivity)
        _=_ := by ring
  have hsmall' (B:NZIdeal) (hB:(B.val.absNorm:ℝ)≤(U^D)^κroot) := hsmall B hB
  have hsum:=hlift J Csmall hCs.le (fun _=>false) a height (U^D) κroot (A/D)
    (((224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D) (by linarith) (by linarith) hh hUraw.le hκroot rows f hR
    (fun u hu=>by rw [hrawScale];exact hpoint u hu)
    (fun B hB=>by
      rw [show A/D-((224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D=
        (A-(224/1755)*min S ((13/400)*((1-6*κroot)*D)))/D by ring,hrawScale]
      exact hsmall B hB)
  apply hsum.trans_eq
  congr 1
  rw [←Real.rpow_mul hUp.le]
  congr 1
  rw [mul_sub,mul_add,mul_min_of_nonneg _ _ hDp.le,mul_div_cancel₀ _ hDp.ne',mul_div_cancel₀ _ hDp.ne']
  dsimp only [ρ]
  ring


end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_whole_raw_max_weighted_fixedmesh
end
