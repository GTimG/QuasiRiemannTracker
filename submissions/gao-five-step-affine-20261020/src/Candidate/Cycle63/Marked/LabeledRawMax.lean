import Candidate.Cycle63.Marked.WholeRawMaxFixedMesh
import Candidate.Cycle63.Marked.FiniteRowPullback
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

def labeledRawSlot {Row Slot : Type} (η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (w σ v : Slot→ℝ) (t : Row→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (χ : Row→ Character) (u : Row) (s : Slot) : ℂ :=
  naturalSlot (χ u) (primePool M H 2 (U^(w s)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I) (t u)) (U^(w s))

/-- The actual raw max-product estimate retains finite geometric labels,
including their chosen heights, masks and buffered zero data. -/
theorem actual_labeled_raw_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
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
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
      Set.InjOn row (↑rows:Set Row)→∀(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)
        (χ : Row→ Character)(holes : Row→ Ideal O),
      (∀u∈rows,rawFrequencyNorm (row u)≤ U^D) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      (∀u∈rows,holes u≠0) → (∀u∈rows,((holes u).absNorm:ℝ)≤ U^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η (row u).val (row u).property).character (holes u)) K) →
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
      (∀u∈rows,∀s∈slots,(max 1 ‖labeledRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2
        ≤ Ccap*U^((2*a-1)*w s+slotloss)) →
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      let A:=(2*a-1+2*binWidth)*S+dmax*(156*ε+mesh+εm+ηloss)+pad*ρ
      (∑u∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2)≤
        C*(1+height)^J*U^(D*(ρ+ordloss)+A-
          min (Cycle63.Optimization.markedGain (2*a-1) S ((1-6*κroot)*D)) (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  obtain ⟨J,hcount⟩:=actual_whole_raw_max_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ηloss ordloss tailε
    hordloss htail htailmax hWs hW hbΦ hrad hbin hη hεm hβ hκβ
  refine ⟨J,?_⟩
  intro Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBmask hCcap hslotloss hpad hwmin
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩:=hcount Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBmask hCcap hslotloss hpad hwmin
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with U hc
  refine ⟨hc.1,?_⟩
  intro D hD hD' Row _ rows row hinj slots w σ v t θ χ holes hrow hw hlo hhi hholes hholecap hcoeff
    a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht hχ hnext hcurrent hslot S ρ A
  let back:=Cycle63FiniteRows.pullback rows row
  have hbmem (u : NonzeroFrequency)(hu : u∈rows.image row):back u∈rows:=
    Cycle63FiniteRows.pullback_mem rows row hu
  have hbrow (u : NonzeroFrequency)(hu : u∈rows.image row):row (back u)=u:=
    Cycle63FiniteRows.row_pullback rows row hu
  have hback (l : Row)(hl : l∈rows):back (row l)=l:=
    Cycle63FiniteRows.pullback_row rows row hinj hl
  have hχ' : ∀u∈rows.image row,∀j,(wholeSourceFamily M H hH η₀ (χ (back u)) j).residue≠1:=
    fun u hu=>hχ _ (hbmem u hu)
  have hb:=hc.2 D hD hD' (rows.image row) slots w σ v (fun u=>t (back u)) θ
    (fun u=>χ (back u)) (fun u=>holes (back u))
    (fun u hu=>by simpa only [hbrow u hu] using hrow _ (hbmem u hu)) hw hlo hhi
    (fun u hu=>hholes _ (hbmem u hu)) (fun u hu=>hholecap _ (hbmem u hu))
    (fun u hu K=>by
      have h:=hcoeff _ (hbmem u hu) K
      change idealCoeff (χ (back u)) K=idealCoeff
        (excluded (naturalRow η (row (back u)).val (row (back u)).property).character (holes (back u))) K at h
      rw [hbrow u hu] at h
      exact h)
    a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv
    (fun u hu=>ht _ (hbmem u hu)) hχ'
    (fun u=>hnext ⟨back u.val,hbmem u.val u.property⟩)
    (fun u=>hcurrent ⟨back u.val,hbmem u.val u.property⟩)
    (fun u hu s hs=>hslot _ (hbmem u hu) s hs)
  convert hb using 1
  symm
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [wholeRawSlot,labeledRawSlot,hback l hl]

end
end OAI.SevenEighths.Cycle63MarkedPlain
