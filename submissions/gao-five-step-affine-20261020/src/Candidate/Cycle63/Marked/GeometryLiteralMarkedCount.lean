import Candidate.Cycle63.Marked.GeometryLiteralRawMax
import Candidate.Cycle63.Marked.GeometryRawBudget
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Cycle63.Moment.JointHighDensity

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
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

/-- The scheduled literal geometric count pays all detector, root, mask,
height and optional normalization errors in a single fixed reserve. -/
theorem actual_geometry_literal_marked_count {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (N : ℕ)(μ : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hBfirst : 0≤Bfirst)
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
      i ≤ bufferCount P.e → Cycle63.Arithmetic.q0 ≤ 2*a-1 → 2*a-1 ≤ Cycle63.Optimization.markedBinTop →
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
      (∑s∈slots,w s) ≤ Cycle63.Optimization.slotTop →
      ∀normfee : ℝ,normfee ≤ μ/32 →
      let χ:=fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Cycle63.Optimization.markedGain (2*a-1) S ((Cycle63.Optimization.coreFactor)*D)+Cycle63.Optimization.markedLoss) := by
  obtain ⟨J,hraw⟩:=actual_geometry_literal_raw_max_fixedmesh (Slot:=Slot) M H hH
    η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup W lo hi bΦ markedRate markedBinWidth
    markedRate markedRate Cycle63.Optimization.tailSlack (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])
    (by norm_num [Cycle63.Optimization.tailSlack, Cycle63.Optimization.allowanceUnit])
    (by norm_num [Cycle63.Optimization.tailSlack, Cycle63.Optimization.allowanceUnit])
    hWs hW hbΦ hrad (by norm_num [markedBinWidth, Cycle63.Optimization.markedBinWidth, Cycle63.Optimization.allowanceUnit])
    (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) hβ hκβ
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hBholes : 0≤2*Bfirst+P.Bmask+1:=by linarith [hP.mask]
  obtain ⟨C,hC,hraw⟩:=hraw P hP.slot hP.slotCap hP.sigmaLo hP.sigmaHi hslot hplain
    (4/5) 130 markedCoreMin 131 markedRate markedWitnessRate markedWitnessRate markedPad
    (markedTinyWidth N) markedRootCutoff (bufferCount P.e)
    (by norm_num) (by norm_num)
    (by unfold markedRootCutoff; linarith [Cycle63.Optimization.markedRootCutoff_bounds.1])
    (by unfold markedRootCutoff; linarith [Cycle63.Optimization.markedRootCutoff_bounds.2])
    (by unfold markedCoreMin markedRootCutoff Cycle63.Optimization.coreFactor; linarith)
    (by norm_num [markedPad, Cycle63.Optimization.markedPad, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) hBholes hP.slotLoss (by norm_num [markedPad, Cycle63.Optimization.markedPad, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])
    (marked_tiny_width_gates N).1 markedCoreMin_pos
    (by unfold markedCoreMin; linarith [Cycle63.Optimization.coreFactor_bounds.2])
    hP.heightZero hP.heightWitness (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) (by norm_num [markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])
    (by norm_num [markedWitnessRate, markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) (by norm_num [markedWitnessRate, markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])
    (by norm_num [markedWitnessRate, markedRate, Cycle63.Optimization.markedRate, Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]) hP.buffer
  refine ⟨C*(1+2*Real.pi+6*(bufferCount P.e+1:ℕ))^J,by positivity,?_⟩
  filter_upwards [hraw] with Z he
  refine ⟨he.1,?_⟩
  intro D hD hD' ι α Row DataLabel _ _ _ _ _ reflected second s hηs R seed K ξ hK bin
    column datum first gRow hparent hfirst hR ψ left unit hf rawKey key rows hinj hindex hfirstcap
    st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a i hiI ha0 ha hw hwm hwr hlo hhi
    hwidth hradial hnext hcurrent hfreq hplainfreq hS normfee hnorm χ S ρ
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hh:=he.2 D hD hD' reflected second s hηs R seed K ξ hK bin column datum first gRow
    hparent hfirst hR ψ rows hinj hindex hfirstcap st hQM hQη z hz hchar hpuncture hzrow hrow
    slots w σ v t θ a markedRawMesh i hiI ha0 ha marked_raw_mesh_gates.1.le
    (by convert marked_raw_mesh_gates.2.1 using 1)
    (by norm_num [markedBinWidth, Cycle63.Optimization.markedBinWidth, Cycle63.Optimization.allowanceUnit];linarith) hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
  have hρ : ρ≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
  have ht : P.τ*(J:ℝ)≤μ/8:=by nlinarith [P.hτ,Nat.cast_nonneg (α:=ℝ) J]
  have hb:=marked_geometry_raw_bound_paid Z P.τ D S ρ (2*a-1) μ normfee C
    (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2)
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS ⟨ha0, ha⟩ (le_of_eq rfl) hρ hμcap
    hnorm ht (by simpa only [add_assoc] using hh)
  convert hb using 1; norm_num [markedRootCutoff, Cycle63.Optimization.coreFactor]

end
end OAI.SevenEighths.Cycle63MarkedPlain
