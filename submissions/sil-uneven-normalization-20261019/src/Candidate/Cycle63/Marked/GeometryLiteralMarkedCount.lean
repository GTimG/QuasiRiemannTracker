import Candidate.Cycle63.Marked.GeometryRawGates
import Candidate.Cycle63.Physical.InitialMass.MarkedParameters
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule

/- Original module: Candidate.Cycle63.Marked.GeometryRawBudget. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators

/-- Pay the polynomial geometric height and an optional multiplicative
normalization loss in the actual raw count. -/
theorem marked_geometry_raw_bound_paid
    (Z τ D S ρ δ μ normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hD0 : 0 ≤ D) (hD : D ≤ 130) (hS : S ≤ 1/25)
    (hρ0 : (19/54:ℝ) ≤ ρ) (hρ : ρ ≤ 1)
    (hμ : μ ≤ 1/100000000) (hnorm : normfee ≤ μ/32) (hheight : τ*(J:ℝ) ≤ μ/8)
    (hbound : Q ≤ C*(1+geometryRawHeight Z τ I)^J*
      Z^(D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
        131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
        min ((224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
          (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100))))) :
    Z^normfee*Q ≤ (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*ρ+δ*S-(224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ)) := by
  have hp : 0 < Z:=zero_lt_one.trans_le hZ
  let E:=D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
    131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
    min ((224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100)))
  have he : E+normfee+τ*(J:ℝ) ≤
      D*ρ+δ*S-(224/1755)*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ) :=
    marked_raw_exponent_paid D S ρ δ markedRawMesh μ normfee (τ*(J:ℝ))
      hD0 hD hS hρ0 hρ marked_raw_mesh_gates.2.2 hμ hnorm hheight
  calc
    Z^normfee*Q ≤ Z^normfee*(C*(1+geometryRawHeight Z τ I)^J*Z^E) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hp.le _)
    _ ≤ Z^normfee*(C*((1+2*Real.pi+6*(I+1:ℕ))^J*Z^(τ*(J:ℝ)))*Z^E) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      exact mul_le_mul_of_nonneg_left (geometry_raw_height_power hZ hτ I J) hC
    _ = (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*Z^(E+normfee+τ*(J:ℝ)) := by
      rw [Real.rpow_add hp,Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg hC (pow_nonneg (by positivity) _))

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.marked_geometry_raw_bound_paid
end

/- Original module: Candidate.Cycle63.Marked.GeometryStateRawMax. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
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
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1/1000) (hεm : 0 < εm)
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
      i ≤ I → 17/25 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
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
          min ((224/1755)*min S ((13/400)*((1-6*κroot)*D)))
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
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_geometry_state_raw_max_fixedmesh
end

/- Original module: Candidate.Cycle63.Marked.GeometryLiteralRawMax. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
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
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1/1000) (hεm : 0 < εm)
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
      i ≤ I → 17/25 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
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
          min ((224/1755)*min S ((13/400)*((1-6*κroot)*D)))
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
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_geometry_literal_raw_max_fixedmesh
end

/- Original module: Candidate.Cycle63.Marked.GeometryLiteralMarkedCount. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
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

/-- The scheduled literal geometric count pays all detector, root, mask,
height and optional normalization errors in a single fixed reserve. -/
theorem actual_geometry_literal_marked_count {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (N : ℕ)(μ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hBfirst : 0≤Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 94/125) :
    ∃J : ℕ,∀(P : HighSourceParameters),MarkedSchedule P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ μ/8 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,(4/5:ℝ) ≤ D → D ≤ 130 →
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
        (θ : Slot→RayQuotient.Characters M H)(a : ℝ)(i : ℕ),
      i ≤ bufferCount P.e → 17/25 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      (∀s∈slots,markedTinyWidth N ≤ w s) → (∀s∈slots,w s ≤ markedRawMesh*markedCoreMin) →
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
      (∑s∈slots,w s) ≤ 1/25 →
      ∀normfee : ℝ,normfee ≤ μ/32 →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          (224/1755)*min S ((13/400)*((122/125)*D))+(1/200000:ℝ)) := by
  obtain ⟨J,hraw⟩:=actual_geometry_literal_raw_max_fixedmesh (Slot:=Slot) M H hH
    η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup W lo hi bΦ (1/1000) markedRate markedBinWidth
    markedRate markedRate (9/100) (by norm_num [markedRate]) (by norm_num) (by norm_num)
    hWs hW hbΦ hrad (by norm_num [markedBinWidth]) (by norm_num [markedRate])
    (by norm_num) (by norm_num) (by norm_num [markedRate]) hβ (by convert hκβ using 1 <;> norm_num)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hBholes : 0≤2*Bfirst+P.Bmask+1:=by linarith [hP.mask]
  obtain ⟨C,hC,hraw⟩:=hraw P hP.slot hP.slotCap hP.sigmaLo hP.sigmaHi hslot hplain
    (4/5) 130 markedCoreMin 131 markedRate markedWitnessRate markedWitnessRate markedPad
    (markedTinyWidth N) markedRootCutoff (bufferCount P.e)
    (by norm_num) (by norm_num) (by norm_num [markedRootCutoff])
    (by norm_num [markedRootCutoff]) (by norm_num [markedCoreMin,markedRootCutoff])
    (by norm_num [markedPad]) hBholes hP.slotLoss (by norm_num [markedPad])
    (marked_tiny_width_gates N).1 (by norm_num [markedCoreMin]) (by norm_num [markedCoreMin])
    hP.heightZero hP.heightWitness (by norm_num [markedRate]) (by norm_num [markedRate])
    (by norm_num [markedWitnessRate,markedRate]) (by norm_num [markedWitnessRate,markedRate])
    (by norm_num [markedWitnessRate,markedRate]) hP.buffer
  refine ⟨C*(1+2*Real.pi+6*(bufferCount P.e+1:ℕ))^J,by positivity,?_⟩
  filter_upwards [hraw] with Z he
  refine ⟨he.1,?_⟩
  intro D hD hD' ι α Row DataLabel _ _ _ _ _ reflected second s hηs R seed K ξ hK bin
    column datum first gRow hparent hfirst hR ψ left unit hf rawKey key rows hinj hindex hfirstcap
    st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a i hiI ha0 ha hw hwm hwr hlo hhi
    hwidth hradial hnext hcurrent hfreq hplainfreq hS normfee hnorm χ S ρ
  have hh:=he.2 D hD hD' reflected second s hηs R seed K ξ hK bin column datum first gRow
    hparent hfirst hR ψ rows hinj hindex hfirstcap st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a markedRawMesh i hiI ha0 ha marked_raw_mesh_gates.1.le
    (by convert marked_raw_mesh_gates.2.1 using 1 <;> norm_num)
    (by norm_num [markedBinWidth];linarith) hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
  have hρ0 : (19/54:ℝ)≤ρ := by
    have hden : 0 < 3*(5-2*(2*a-1)) := by linarith
    change 19/54 ≤ 1-10*(2*a-1)/(3*(5-2*(2*a-1)))
    have hq : 10*(2*a-1)/(3*(5-2*(2*a-1))) ≤ 35/54 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    linarith
  have hρ : ρ≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
  have ht : P.τ*(J:ℝ)≤μ/8:=by nlinarith [P.hτ,Nat.cast_nonneg (α:=ℝ) J]
  have hb:=marked_geometry_raw_bound_paid Z P.τ D S ρ (2*a-1) μ normfee C
    (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2)
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS hρ0 hρ hμcap hnorm ht (by simpa only [add_assoc] using hh)
  convert hb using 1 <;> norm_num [markedRootCutoff]

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_geometry_literal_marked_count
end
