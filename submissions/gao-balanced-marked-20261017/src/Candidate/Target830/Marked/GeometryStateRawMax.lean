import Candidate.Target830.Marked.LabeledRawMax
import Candidate.Cycle63.Marked.GeometryRawGates

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
