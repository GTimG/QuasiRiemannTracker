import Candidate.Cycle63.Marked.GeometryStateRawMax

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
