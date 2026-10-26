import Candidate.Cycle63.Marked.WholeCoreGates
import Candidate.Cycle63.Marked.DeletionRawPadded
import Candidate.Cycle63.Arithmetic.Constants

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
theorem actual_whole_padded_core_weighted {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth ηloss : ℝ)
    (dmin dmax τ ε e κw ηw pad wmin : ℝ) (I : ℕ)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost) :
    ∃E : Finset FreeRow,∃meshmax : ℝ,0< meshmax ∧ ∃J : ℕ,∃C : ℝ,0< C ∧
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
      Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop →
      0≤ mesh → mesh≤ meshmax → binWidth≤(2*a-1)/2 →
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
        (U^((2*a-1+2*binWidth)*(∑s∈slots,w s)-(Cycle63.Optimization.liveRate (2*a-1))*min (∑s∈slots,w s) ((Cycle63.Optimization.inverseWidthCap)*d)+
          dmax*(156*ε+mesh+εm+ηloss)+pad*VariableSupply.density (2*a-1))*
          Y^VariableSupply.density (2*a-1)) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  obtain ⟨E,hE⟩ := whole_core_exception_set M H hH η η₀ bad hbad0 hbadTop hbad72
  obtain ⟨meshmax,hm,J,C,hC,hcount⟩ := actual_whole_max_weighted (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ηloss
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he'
    hκw hκw' hηw hbudget hWs hW hbΦ hrad hbin hη hεm hβ hκβ
  refine ⟨E,meshmax,hm,J,C,hC,?_⟩
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
      (Cycle63.Optimization.liveRate (2*a-1))*min ((∑s∈slots,w s)/d) (Cycle63.Optimization.inverseWidthCap)+
      156*ε+mesh+εm+2*binWidth*((∑s∈slots,w s)/d)+ηloss =
      VariableSupply.density (2*a-1)+(2*a-1+2*binWidth)*((∑s∈slots,w s)/d)-
        (Cycle63.Optimization.liveRate (2*a-1))*min ((∑s∈slots,w s)/d) (Cycle63.Optimization.inverseWidthCap)+(156*ε+mesh+εm+ηloss) := by
    ring
  rw [heq] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Deletion26.rescaled_marked_power_padded U Y d d dmax pad
    (VariableSupply.density (2*a-1)) (2*a-1+2*binWidth) (∑s∈slots,w s)
    (Cycle63.Optimization.liveRate (2*a-1)) (Cycle63.Optimization.inverseWidthCap) (156*ε+mesh+εm+ηloss) hcount.1.le hY hdp le_rfl hd' hbase
    (VariableSupply.liveRate_bounds ha0 (by linarith)).1 Cycle63.Optimization.inverseWidthCap_pos.le
    (by positivity)

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_whole_padded_core_weighted
