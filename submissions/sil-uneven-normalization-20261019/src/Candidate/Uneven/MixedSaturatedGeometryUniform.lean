import Candidate.Uneven.SaturatedGeometryState
import Candidate.Uneven.SaturatedRawFee

/- Original module: Candidate.Uneven.MixedSaturatedGeometryLiteral. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.SaturatedPlain
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
theorem actual_geometry_literal_raw_max_fixedmesh_mixed_anchor {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0 < ordloss) (htail : 0 < tailε) (htailmax : tailε ≤ 1/2)
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
      let unit:=fun l=>(firstDictionaryUnit left ηcoarse u₀ F₀ R₀ l:O)
      let hf:=fun l=>geometry_first_frequency_ne_zero reflected ηcoarse u₀ F₀ R₀ hu₀
        s R seed K Z ξ hK bin (column l) datum first (gRow l) (hfirst l)
      let rawKey:=fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (gRow l) left u₀ unit (hf l)
      let key:=fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀rows : Finset Row,
      Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set Row) →
      (∀l∈rows,(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)=index₀) →
      (∀l∈rows,((geometryFirstSource s R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ)≤ Z^Bfirst) →
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
      i ≤ I → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 3/4 →
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
      let A:=(2*a-1+2*binWidth)*S+dmax*(402*ε+mesh+εm+ηloss)+pad*ρ
      (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*(1+geometryRawHeight Z P.τ I)^J*Z^(D*(ρ+ordloss)+A-
          min (Sil.Uneven.Saturated.physicalGain (2*a-1) S D)
            (D*κroot*(6*(ρ+ordloss-3/200)-1-tailε))) := by
  obtain ⟨J,hstate⟩:=actual_geometry_state_raw_max_fixedmesh (Slot:=Slot) M H hH
    (secondFixedDictionary ηcoarse index₀) η₀ setup W lo hi bΦ Δ εm binWidth ηloss ordloss tailε
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
  filter_upwards [hstate,eventually_geometry_marked_packet ηcoarse u₀ F₀ R₀ hu₀ Bfirst P.Bmask P.bΦ]
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
  have hholecap : ∀l∈rows,((holes l).absNorm:ℝ)≤ Z^(2*Bfirst+P.Bmask+1):=
    fun l hl=>(hpacket l hl).2.1
  have hcoeff : ∀l∈rows,∀I,idealCoeff (χ l) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary ηcoarse index₀)
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
end OAI.SevenEighths.SaturatedPlain
end

/- Original module: Candidate.Uneven.MixedSaturatedGeometryPaid. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.SaturatedPlain
open Marked830Plain
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

/-- The scheduled literal geometric count pays all detector, root, mask,
height and optional normalization errors in a single fixed reserve. -/
theorem actual_geometry_literal_marked_count_mixed_anchor {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (N : ℕ)(hBfirst : 0≤ Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4) :
    ∃J : ℕ,∀(P : HighSourceParameters),FineMarkedSchedule P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
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
      let unit:=fun l=>(firstDictionaryUnit left ηcoarse u₀ F₀ R₀ l:O)
      let hf:=fun l=>geometry_first_frequency_ne_zero reflected ηcoarse u₀ F₀ R₀ hu₀
        s R seed K Z ξ hK bin (column l) datum first (gRow l) (hfirst l)
      let rawKey:=fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (gRow l) left u₀ unit (hf l)
      let key:=fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀rows : Finset Row,
      Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set Row) →
      (∀l∈rows,(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)=index₀) →
      (∀l∈rows,((geometryFirstSource s R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ)≤ Z^Bfirst) →
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 3/4 →
      (∀s∈slots,fineRawTiny N ≤ w s) → (∀s∈slots,w s ≤ fineRawMesh*fineRawCore) →
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
      ∀normfee : ℝ,normfee ≤ 1/1000000000000 →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Sil.Uneven.Saturated.physicalGain (2*a-1) S D+fineHighRawFee) := by
  obtain ⟨J,hraw⟩:=actual_geometry_literal_raw_max_fixedmesh_mixed_anchor (Slot:=Slot) M H hH
    ηcoarse η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup W lo hi bΦ 0 fineRawRate fineRawBin
    fineRawRate fineRawRate fineRawTail (by norm_num [fineRawRate])
    (by norm_num [fineRawTail]) (by norm_num [fineRawTail]) hWs hW hbΦ hrad
    (by norm_num [fineRawBin]) (by norm_num [fineRawRate])
    (by norm_num) rfl (by norm_num [fineRawRate]) hβ (by simpa using hκβ)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hBholes : 0≤2*Bfirst+P.Bmask+1 := by linarith [hP.mask]
  have hroot : (0:ℝ)≤1/100 ∧ (1/100:ℝ)<1/6 := by norm_num
  obtain ⟨C,hC,hraw⟩:=hraw P hP.slot hP.slotCap hP.sigmaLo hP.sigmaHi hslot hplain
    (4/5) 130 fineRawCore 131 fineRawRate fineRawWitness fineRawWitness fineRawPad
    (fineRawTiny N) (1/100) (bufferCount P.e)
    (by norm_num) (by norm_num) hroot.1 hroot.2 (by norm_num [fineRawCore])
    (by norm_num [fineRawPad,fineRawRate]) hBholes hP.slotLoss
    (by norm_num [fineRawPad,fineRawRate]) (fine_raw_tiny_gates N).1
    (by norm_num [fineRawCore]) (by norm_num [fineRawCore]) hP.heightZero hP.heightWitness
    (by norm_num [fineRawRate]) (by norm_num [fineRawRate])
    (by norm_num [fineRawWitness]) (by norm_num [fineRawWitness])
    (by norm_num [fineRawWitness]) hP.buffer
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
    slots w σ v t θ a fineRawMesh i hiI ha0 ha fine_raw_mesh_gates.1.le
    (by simpa using fine_raw_mesh_gates.2.1)
    (by norm_num [fineRawBin];linarith) hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
  have hρ : ρ≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
  have ht : P.τ*(J:ℝ)≤1/1000000000000 := by
    nlinarith [P.hτ,Nat.cast_nonneg (α:=ℝ) J]
  exact raw_bound_paid Z P.τ D S (2*a-1) normfee C
    (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2)
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS ha0 ha hnorm ht
    (by simpa only [Sil.Uneven.Saturated.rho,unmarkedDensity,χ,S,add_assoc] using hh)

end
end OAI.SevenEighths.SaturatedPlain
end

/- Original module: Candidate.Uneven.MixedSaturatedGeometryUniform. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.SaturatedPlain
open Marked830Plain
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

/-- One height degree and one scale threshold work for every fixed member
of the finite geometric dictionary, before either common allocation. -/
theorem actual_geometry_uniform_marked_count_mixed_anchor {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Bfirst : ℝ)(setup : DensityCountingSetup)
    (N : ℕ)(hBfirst : 0≤Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4) :
    ∃J : ℕ,∀(P : HighSourceParameters),FineMarkedSchedule P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,(4/5:ℝ) ≤ D → D ≤ 130 →
      ∀index₀ : RayCharacter×RayCharacter,
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
      let unit:=fun l=>(firstDictionaryUnit left ηcoarse u₀ F₀ R₀ l:O)
      let hf:=fun l=>geometry_first_frequency_ne_zero reflected ηcoarse u₀ F₀ R₀ hu₀
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 3/4 →
      (∀s∈slots,fineRawTiny N ≤ w s) → (∀s∈slots,w s ≤ fineRawMesh*fineRawCore) →
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
      ∀normfee : ℝ,normfee ≤ 1/1000000000000 →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Sil.Uneven.Saturated.physicalGain (2*a-1) S D+fineHighRawFee) := by
  have hex (index₀ : RayCharacter×RayCharacter):=
    actual_geometry_literal_marked_count_mixed_anchor (Slot:=Slot) M H hH ηcoarse η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup
      N hBfirst W lo hi bΦ hWs hW hbΦ hrad hβ hκβ
  choose Ji hcounts using hex
  let J:=Finset.univ.sup Ji
  have hJ (index₀ : RayCharacter×RayCharacter):Ji index₀≤J:=
    Finset.le_sup (f:=Ji) (Finset.mem_univ index₀)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hheighti (index₀ : RayCharacter×RayCharacter) :
      2*P.τ*((Ji index₀:ℝ)+1)≤1/1000000000000 := by
    have hi : (Ji index₀:ℝ)≤J:=by exact_mod_cast hJ index₀
    exact (mul_le_mul_of_nonneg_left (by linarith : (Ji index₀:ℝ)+1≤J+1)
      (mul_nonneg (by norm_num) P.hτ.le)).trans hheight
  choose C hC hcount using (fun index₀=>hcounts index₀ P hP hslot hplain (hheighti index₀))
  let Cmax:=max 1 (∑index₀,C index₀)
  have hCmax : 0<Cmax:=(zero_lt_one.trans_le (le_max_left _ _))
  have hCi (index₀ : RayCharacter×RayCharacter):C index₀≤Cmax:=
    (Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ index₀)).trans (le_max_right _ _)
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr hcount] with Z he
  refine ⟨(he (1,1)).1,?_⟩
  intro D hD hD' index₀ ι α Row DataLabel _ _ _ _ _ reflected second s hηs R seed K ξ hK bin
    column datum first gRow hparent hfirst hR ψ left unit hf rawKey key rows hinj hindex hfirstcap
    st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a i hiI ha0 ha hw hwm hwr hlo hhi
    hwidth hradial hnext hcurrent hfreq hplainfreq hS normfee hnorm χ S ρ
  have hh:=(he index₀).2 D hD hD' reflected second s hηs R seed K ξ hK bin column datum first gRow
    hparent hfirst hR ψ rows hinj hindex hfirstcap st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a i hiI ha0 ha hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
    hS normfee hnorm
  exact hh.trans (mul_le_mul_of_nonneg_right (hCi index₀)
    (Real.rpow_nonneg (zero_lt_one.trans (he index₀).1).le _))

end
end OAI.SevenEighths.SaturatedPlain
end
