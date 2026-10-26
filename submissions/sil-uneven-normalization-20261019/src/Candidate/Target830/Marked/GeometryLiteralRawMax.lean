import Candidate.Cycle63.Marked.LabeledRawMax
import Candidate.Target830.Marked.WholeRawMaxFixedMesh
import Candidate.Cycle63.Marked.FiniteRowPullback
import Candidate.Cycle63.Marked.GeometryRawGates

/- Original module: Candidate.Target830.Marked.LabeledRawMax. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Marked830Plain
open OAI.SevenEighths.Cycle63MarkedPlain
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

/-- The actual raw max-product estimate retains finite geometric labels,
including their chosen heights, masks and buffered zero data. -/
theorem actual_labeled_raw_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
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
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hεm : 0<εm)
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
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
      Set.InjOn row (↑rows:Set Row)→∀(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)
        (χ : Row→Character)(holes : Row→Ideal O),
      (∀u∈rows,rawFrequencyNorm (row u)≤ U^D) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      (∀u∈rows,holes u≠0) → (∀u∈rows,((holes u).absNorm:ℝ)≤ U^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η (row u).val (row u).property).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      31/50≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ markedPlainMesh (3/4+2*Δ) εm → binWidth≤(2*a-1)/2 →
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
          min (Marked830.VariableSupply.physicalGain (2*a-1) S ((1-6*κroot)*D)) (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  obtain ⟨J,hcount⟩:=actual_whole_raw_max_weighted_fixedmesh (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss ordloss tailε
    hordloss htail htailmax hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
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
  apply Finset.sum_congr rfl
  intro l hl
  simp only [wholeRawSlot,labeledRawSlot,hback l hl]

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_labeled_raw_max_weighted_fixedmesh
end

/- Original module: Candidate.Target830.Marked.GeometryStateRawMax. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Marked830Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle63Moment Cycle63InitialMass
open ProbeHighRowFamily ProbePhysical HeckeDetectorFiberPartition CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The marked raw estimate for literal natural states. Its only row
presentation gates are the coefficient and hole identities supplied by
`eventually_geometry_marked_packet`; the whole-family nonprincipality,
individual amplitudes, fixed bad ideals and polynomial height are discharged. -/
theorem actual_geometry_state_raw_max_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (setup : DensityCountingSetup)
    (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0 < ordloss) (htail : 0 < tailε) (htailmax : tailε ≤ 5/7)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hbin : 0 < binWidth) (hη : 0 < ηloss)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ=0) (hεm : 0 < εm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4+2*Δ) :
    ∃J : ℕ,∀(P : HighSourceParameters),P.Wslot=W → P.B₀=2 →
    lo ≤ P.σmin → P.σmax ≤ hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    ∀(Dmin Dmax dmin dmax ε κw ηw pad wmin κroot Bholes : ℝ) (I : ℕ),
    0 < Dmin → Dmin ≤ Dmax → 0 ≤ κroot → κroot < 1/6 →
    dmin ≤ Dmin*(1-6*κroot) → Dmax+pad ≤ dmax → 0 ≤ Bholes →
    2*P.εslot*P.d ≤ binWidth*wmin →
    0 < pad → 0 < wmin → 0 < dmin → dmin ≤ dmax →
    P.τ < dmin/2 → 4*P.τ < dmin*ηw →
    0 < ε → ε ≤ 1/1000 → 0 < κw → κw ≤ 1 → 0 ≤ ηw →
    12*P.e*((22:ℝ)+2)+8*κw+2*ηw ≤ ε/2 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,Dmin ≤ D → D ≤ Dmax →
      ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
      Set.InjOn row (↑rows:Set Row) →
      ∀(st : Row→NaturalState Z P.Bmask P.bΦ)
        (hQM : ∀l,(st l).fixedModulus ≤ M)(hQη : ∀l,(st l).fixedModulus ≤ η₀.modulus)
        (z : Row→O)(hz : ∀l,(st l).radial.keep (z l))
        (holes : Row→Ideal O),
      (∀l∈rows,rawFrequencyNorm (row l) ≤ Z^D) →
      (∀l∈rows,holes l≠0) → (∀l∈rows,((holes l).absNorm:ℝ) ≤ Z^Bholes) →
      (∀l∈rows,∀K,idealCoeff
        (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
          (st l).puncture) K =
        idealCoeff (excluded (naturalRow η (row l).val (row l).property).character (holes l)) K) →
      ∀(slots : Finset Slot)(w σ v : Slot→ℝ)(t : Row→ℝ)
        (θ : Slot→RayQuotient.Characters M H)(a mesh : ℝ)(i : ℕ),
      i ≤ I → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      0 ≤ mesh → mesh ≤ markedPlainMesh (3/4+2*Δ) εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,wmin ≤ w s) → (∀s∈slots,w s ≤ mesh*dmin) →
      (∀s∈slots,w s/P.d ≤ P.Rwidth) →
      (∀s∈slots,P.σmin ≤ σ s) → (∀s∈slots,σ s ≤ P.σmax) →
      (∀l∈rows,(st l).width ≤ P.Mcap) →
      (∀l∈rows,(st l).radial.profile
        (‖ConcreteTraceCRT.eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈rows,geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀l∈rows,a ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        ((3*i:ℕ)*Z^P.τ)) →
      (∀l∈rows,∀s∈slots,|t l+v s|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈rows,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      let A:=(2*a-1+2*binWidth)*S+dmax*(156*ε+mesh+εm+ηloss)+pad*ρ
      (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*(1+geometryRawHeight Z P.τ I)^J*Z^(D*(ρ+ordloss)+A-
          min (Marked830.VariableSupply.physicalGain (2*a-1) S ((1-6*κroot)*D))
            (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  let bad : WholeSourceIndex M H→Ideal O:=fun _=>markedFixedIdeal M
  have hb (j : WholeSourceIndex M H):=
    marked_fixed_ideal_gates M (wholeSourceAnchor M H hH η₀ j)
  obtain ⟨J,hraw⟩:=actual_labeled_raw_max_weighted_fixedmesh (Slot:=Slot) M H hH η η₀ bad
    (fun j=>(hb j).1) (fun j=>(hb j).2.1) (fun j=>(hb j).2.2.1) (fun j=>(hb j).2.2.2)
    setup W lo hi bΦ Δ εm binWidth ηloss ordloss tailε
    hordloss htail htailmax hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨J,?_⟩
  intro P hPW hPB hPlo hPhi hslot hplain Dmin Dmax dmin dmax ε κw ηw pad wmin κroot Bholes I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBholes hslotloss hpad hwmin hdmin hdmax
    hτzero hτheight hε hεsmall hκw hκw' hηw hbudget
  obtain ⟨Ccap,hCcap,hcaps⟩:=actual_retained_slot_caps M H hH P hslot hplain
  obtain ⟨C,hC,hraw⟩:=hraw Dmin Dmax dmin dmax P.τ ε P.e κw ηw pad wmin κroot
    Bholes Ccap (2*P.εslot*P.d) I hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBholes
    (zero_le_one.trans hCcap) hslotloss hpad hwmin hdmin hdmax P.hτ hτzero hτheight
    hε hεsmall P.he P.he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,hcaps η₀,(tendsto_rpow_atTop P.hτ).eventually
    (eventually_ge_atTop (I:ℝ))] with Z hr hc hI
  refine ⟨hr.1,?_⟩
  intro D hD hD' Row _ rows row hinj st hQM hQη z hz holes hrow hholes hholecap hcoeff
    slots w σ v t θ a mesh i hiI ha0 ha hmesh hmeshmax hbin' hw hwm hwr hlo hhi
    hwidth hradial hnext hcurrent hfreq hplainfreq χ S ρ A
  have hZ : 0 < Z:=zero_lt_one.trans hr.1
  have hi : (i:ℝ) ≤ Z^P.τ:=(by exact_mod_cast hiI : (i:ℝ) ≤ I).trans hI
  have hn : ∀l∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ l) j).residue≠1 :=
    fun l _=>whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _
  have hcap : ∀l∈rows,∀s∈slots,
      (max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2 ≤
        Ccap*Z^((2*a-1)*w s+2*P.εslot*P.d) := by
    intro l hl s hs
    have hh:=hc.2 (st l) (hwidth l hl) (hQM l) (hQη l) (z l) (hz l) a i
      (by linarith) (by linarith) hi (hradial l hl) (hnext l hl)
      (w s) (σ s) (t l) (v s) (θ s) (hwmin.le.trans (hw s hs)) (hwr s hs)
      (hlo s hs) (hhi s hs) (hfreq l hl s hs)
    simpa only [labeledRawSlot,χ,hPB,hPW] using hh
  by_cases he : rows.Nonempty
  · obtain ⟨l₀,hl₀⟩:=he
    exact hr.2 D hD hD' rows row hinj slots w σ v t θ χ holes hrow hw
      (fun s hs=>hPlo.trans (hlo s hs)) (fun s hs=>(hhi s hs).trans hPhi)
      hholes hholecap hcoeff a mesh (geometryRawHeight Z P.τ I) i hiI ha0 ha hmesh hmeshmax hbin' hwm
      (geometry_raw_height_nonneg hZ.le I)
      (geometry_raw_height_zero hr.1.le P.hτ.le i I hiI)
      (fun s hs=>geometry_raw_height_frequency hZ.le i I hiI (hplainfreq l₀ hl₀) (hfreq l₀ hl₀ s hs))
      (fun l hl=>geometry_raw_height_time hZ.le i I hiI (hplainfreq l hl)) hn
      (fun l=>hnext l.val l.property) (fun l=>hcurrent l.val l.property) hcap
  · have he' : rows=∅:=Finset.not_nonempty_iff_eq_empty.mp he
    rw [he',Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC.le
      (pow_nonneg (add_nonneg zero_le_one (geometry_raw_height_nonneg hZ.le I)) J))
      (Real.rpow_nonneg hZ.le _)

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_geometry_state_raw_max_fixedmesh
end

/- Original module: Candidate.Target830.Marked.GeometryLiteralRawMax. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Marked830Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle63Moment Cycle63InitialMass
open ProbeHighRowFamily ProbePhysical HeckeDetectorFiberPartition CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
open CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion
open CenteredMomentCanonicalFirst IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Literal geometric rows inherit the marked raw estimate with their actual
fixed dictionary, Euler holes, buffered maxima, and retained source slots. -/
theorem actual_geometry_literal_raw_max_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0 < ordloss) (htail : 0 < tailε) (htailmax : tailε ≤ 5/7)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hbin : 0 < binWidth) (hη : 0 < ηloss)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ=0) (hεm : 0 < εm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4+2*Δ) :
    ∃J : ℕ,∀(P : HighSourceParameters),P.Wslot=W → P.B₀=2 →
    lo ≤ P.σmin → P.σmax ≤ hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    ∀(Dmin Dmax dmin dmax ε κw ηw pad wmin κroot : ℝ) (I : ℕ),
    0 < Dmin → Dmin ≤ Dmax → 0 ≤ κroot → κroot < 1/6 →
    dmin ≤ Dmin*(1-6*κroot) → Dmax+pad ≤ dmax → 0 ≤ 2*Bfirst+P.Bmask+1 →
    2*P.εslot*P.d ≤ binWidth*wmin →
    0 < pad → 0 < wmin → 0 < dmin → dmin ≤ dmax →
    P.τ < dmin/2 → 4*P.τ < dmin*ηw →
    0 < ε → ε ≤ 1/1000 → 0 < κw → κw ≤ 1 → 0 ≤ ηw →
    12*P.e*((22:ℝ)+2)+8*κw+2*ηw ≤ ε/2 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,Dmin ≤ D → D ≤ Dmax →
      ∀{ι α Row DataLabel : Type}[Fintype ι][Fintype α][DecidableEq α][Nonempty Row][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input ι)(hηs : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : Row→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (gRow : Row→secondLiveRows (fun l=>(datum l).block))
        (hparent : ∀l,(datum (gRow l).val.1).input.η=
          geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (gRow l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (hR : ∀l,(datum (gRow l).val.1).R≠0)(ψ : Row→RayCharacter),
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf:=fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀
        s R seed K Z ξ hK bin (column l) datum first (gRow l) (hfirst l)
      let rawKey:=fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (gRow l) left u₀ unit (hf l)
      let key:=fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀rows : Finset Row,
      Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set Row) →
      (∀l∈rows,(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)=index₀) →
      (∀l∈rows,((geometryFirstSource s R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ)≤Z^Bfirst) →
      ∀(st : Row→NaturalState Z P.Bmask P.bΦ)
        (hQM : ∀l,(st l).fixedModulus ≤ M)(hQη : ∀l,(st l).fixedModulus ≤ η₀.modulus)
        (z : Row→O)(hz : ∀l,(st l).radial.keep (z l)),
      (∀l,(st l).character=(datum (gRow l).val.1).τ (ψ l)) →
      (∀l,(st l).puncture=(datum (gRow l).val.1).R*
        (if second then (datum (gRow l).val.1).D else (datum (gRow l).val.1).C)) →
      (∀l,z l=if second then -(gRow l).val.2.2.2.val else (gRow l).val.2.2.2.val) →
      (∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^D) →
      ∀(slots : Finset Slot)(w σ v : Slot→ℝ)(t : Row→ℝ)
        (θ : Slot→RayQuotient.Characters M H)(a mesh : ℝ)(i : ℕ),
      i ≤ I → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      0 ≤ mesh → mesh ≤ markedPlainMesh (3/4+2*Δ) εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,wmin ≤ w s) → (∀s∈slots,w s ≤ mesh*dmin) →
      (∀s∈slots,w s/P.d ≤ P.Rwidth) →
      (∀s∈slots,P.σmin ≤ σ s) → (∀s∈slots,σ s ≤ P.σmax) →
      (∀l∈rows,(st l).width ≤ P.Mcap) →
      (∀l∈rows,(st l).radial.profile
        (‖ConcreteTraceCRT.eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈rows,geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀l∈rows,a ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        ((3*i:ℕ)*Z^P.τ)) →
      (∀l∈rows,∀s∈slots,|t l+v s|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈rows,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      let A:=(2*a-1+2*binWidth)*S+dmax*(156*ε+mesh+εm+ηloss)+pad*ρ
      (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*(1+geometryRawHeight Z P.τ I)^J*Z^(D*(ρ+ordloss)+A-
          min (Marked830.VariableSupply.physicalGain (2*a-1) S ((1-6*κroot)*D))
            (D*κroot*(6*(ρ+ordloss)-1-tailε))) := by
  obtain ⟨J,hstate⟩:=actual_geometry_state_raw_max_fixedmesh (Slot:=Slot) M H hH
    (secondFixedDictionary η₀ index₀) η₀ setup W lo hi bΦ Δ εm binWidth ηloss ordloss tailε
    hordloss htail htailmax hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨J,?_⟩
  intro P hPW hPB hPlo hPhi hslot hplain Dmin Dmax dmin dmax ε κw ηw pad wmin κroot I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBholes hslotloss hpad hwmin hdmin hdmax
    hτzero hτheight hε hεsmall hκw hκw' hηw hbudget
  obtain ⟨C,hC,hstate⟩:=hstate P hPW hPB hPlo hPhi hslot hplain
    Dmin Dmax dmin dmax ε κw ηw pad wmin κroot (2*Bfirst+P.Bmask+1) I
    hDmin hDmax hκroot hκrootmax hdsmall hdlarge hBholes hslotloss hpad hwmin hdmin hdmax
    hτzero hτheight hε hεsmall hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hstate,eventually_geometry_marked_packet η₀ u₀ F₀ R₀ hu₀ Bfirst P.Bmask P.bΦ]
    with Z he hp
  refine ⟨he.1,?_⟩
  intro D hD hD' ι α Row DataLabel _ _ _ _ _ reflected second s hηs R seed K ξ hK bin
    column datum first gRow hparent hfirst hR ψ left unit hf rawKey key rows hinj hindex hfirstcap
    st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a mesh i hiI ha0 ha hmesh hmeshmax hbin' hw hwm hwr hlo hhi
    hwidth hradial hnext hcurrent hfreq hplainfreq χ S ρ A
  let holes:=fun l=>(datum (gRow l).val.1).input.η.modulus*
    ((datum (gRow l).val.1).R*(if second then (datum (gRow l).val.1).D else (datum (gRow l).val.1).C))
  have hpacket (l : Row)(hl : l∈rows):=hp.2 reflected second s hηs R seed K ξ hK bin (column l)
    datum first (gRow l) (hparent l) (hfirst l) (hR l) (ψ l) (hfirstcap l hl)
    (st l) (z l) (hz l) (hchar l) (hpuncture l) (hzrow l)
  have hholes : ∀l∈rows,holes l≠0:=fun l hl=>(hpacket l hl).1
  have hholecap : ∀l∈rows,((holes l).absNorm:ℝ)≤Z^(2*Bfirst+P.Bmask+1):=
    fun l hl=>(hpacket l hl).2.1
  have hcoeff : ∀l∈rows,∀I,idealCoeff (χ l) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index₀)
        (nonzeroJointSourceRow (key l)).val (nonzeroJointSourceRow (key l)).property).character
          (holes l)) I := by
    intro l hl I
    have hh:=(hpacket l hl).2.2.1 I
    rw [hindex l hl] at hh
    exact hh
  exact he.2 D hD hD' rows (fun l=>nonzeroJointSourceRow (key l)) hinj st hQM hQη z hz holes
    hrow hholes hholecap hcoeff slots w σ v t θ a mesh i hiI ha0 ha hmesh hmeshmax hbin'
    hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_geometry_literal_raw_max_fixedmesh
end
