import Candidate.Research.RecursiveAffine.MarkedRange.LiteralMarkedCount
import Candidate.Cycle63.Moment.JointHighDensity

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle153MarkedPlain
open Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle63Moment Cycle63InitialMass
open ProbeHighRowFamily ProbePhysical HeckeDetectorFiberPartition CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
open CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion
open CenteredMomentCanonicalFirst IdealMobiusDivisorSum
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- One height degree and one scale threshold work for every fixed member
of the finite geometric dictionary, before either common allocation. -/
theorem actual_geometry_uniform_marked_count {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Bfirst : ℝ)(setup : DensityCountingSetup)
    (N : ℕ)(μ Smax : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hBfirst : 0≤Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ Cycle63.Optimization.plainCapacityCost) :
    ∃J : ℕ,∀(P : HighSourceParameters),MarkedSchedule P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ μ/8 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,(4/5:ℝ) ≤ D → D ≤ 130 →
      ∀index₀ : RayCharacter×RayCharacter,
      ∀{ι α Row DataLabel : Type}[Fintype ι][Fintype α][DecidableEq α][Nonempty Row][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input ι)(_hηs : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : Row→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (gRow : Row→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (gRow l).val.1).input.η=
          geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (gRow l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (gRow l).val.1).R≠0)(ψ : Row→RayCharacter),
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
      i ≤ bufferCount P.e → Cycle63.Arithmetic.q0 ≤ 2*a-1 → 2*a-1 ≤ (2/3:ℝ) →
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
      (∑s∈slots,w s) ≤ Smax →
      ∀normfee : ℝ,normfee ≤ μ/32 →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Cycle63.Optimization.markedGain (2*a-1) S ((Cycle63.Optimization.coreFactor)*D)+(Cycle63.Optimization.markedLossAt Smax)) := by
  have hex (index₀ : RayCharacter×RayCharacter):=
    actual_geometry_literal_marked_count (Slot:=Slot) M H hH η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup
      N μ Smax hμ hμcap hBfirst W lo hi bΦ hWs hW hbΦ hrad hβ hκβ
  choose Ji hcounts using hex
  let J:=Finset.univ.sup Ji
  have hJ (index₀ : RayCharacter×RayCharacter):Ji index₀≤J:=
    Finset.le_sup (f:=Ji) (Finset.mem_univ index₀)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hheighti (index₀ : RayCharacter×RayCharacter) :
      2*P.τ*((Ji index₀:ℝ)+1)≤μ/8 := by
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
end OAI.SevenEighths.Cycle153MarkedPlain

#print axioms OAI.SevenEighths.Cycle153MarkedPlain.actual_geometry_uniform_marked_count
