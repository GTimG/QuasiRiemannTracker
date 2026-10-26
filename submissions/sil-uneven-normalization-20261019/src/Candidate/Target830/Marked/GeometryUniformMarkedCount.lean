import Candidate.Target830.Marked.ParametersBridge
import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Marked.GeometryRawGates
import Candidate.Target830.High.Channels

/- Original module: Candidate.Target830.High.RawBudget. -/
section

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.TargetHigh830

/-- The ordinary density increment helps; the literal large-root truncation
cost must still be paid as a positive raw fee. -/
theorem raw_gain_defect (G D root rho ordinaryLoss tailLoss : ℝ)
    (hD : 0≤ D) (hroot : 0≤ root) (hordinary : 0≤ ordinaryLoss) (htail : 0≤ tailLoss) :
    min G (D*root*(6*rho-1))-D*root*tailLoss ≤
      min G (D*root*(6*(rho+ordinaryLoss)-1-tailLoss)) := by
  have hn := mul_nonneg (mul_nonneg hD hroot) htail
  have ho := mul_nonneg (mul_nonneg hD hroot) hordinary
  apply le_min
  · linarith [min_le_left G (D*root*(6*rho-1))]
  · nlinarith [min_le_right G (D*root*(6*rho-1))]

/-- Complete exponent comparison after the actual detector/root/height
and normalization costs have been included in the single raw allowance. -/
theorem raw_exponent_payment (G D root rho ordinaryLoss tailLoss main extra fee : ℝ)
    (hD : 0≤ D) (hroot : 0≤ root) (hordinary : 0≤ ordinaryLoss) (htail : 0≤ tailLoss)
    (hfee : extra+D*root*tailLoss≤ fee) :
    main+extra-min G (D*root*(6*(rho+ordinaryLoss)-1-tailLoss)) ≤
      main-min G (D*root*(6*rho-1))+fee := by
  have hg := raw_gain_defect G D root rho ordinaryLoss tailLoss hD hroot hordinary htail
  linarith

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.raw_gain_defect
#print axioms OAI.SevenEighths.TargetHigh830.raw_exponent_payment
end

/- Original module: Candidate.Target830.High.RawFee. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open Marked830Plain Cycle63MarkedPlain Target830
open scoped BigOperators

theorem raw_fee830 (plane : SourcePlane) (D S rho mesh normfee heightfee : ℝ)
    (hD : D ≤ 130) (hS : S ≤ 1/25) (hrho : rho ≤ 1)
    (hmesh : mesh ≤ rawRate830) (hnorm : normfee ≤ 1/1000000000)
    (hheight : heightfee ≤ 1/1000000000) :
    D*rawRate830+2*rawBin830*S+
      131*(156*rawRate830+mesh+rawRate830+rawRate830)+rawPad830*rho+
      normfee+heightfee+D*plane.rootCutoff*rawTail830 ≤ highRawFee := by
  have hroot : plane.rootCutoff ≤ 7/1000 := by
    cases plane <;> norm_num [SourcePlane.rootCutoff]
  have hn : 0 ≤ rawTail830 := by norm_num [rawTail830]
  have hDroot : D*plane.rootCutoff ≤ 130*(7/1000) := by
    have hp : 0 ≤ plane.rootCutoff := by cases plane <;> norm_num [SourcePlane.rootCutoff]
    nlinarith
  have ht:=mul_le_mul_of_nonneg_right hDroot hn
  norm_num [rawRate830,rawBin830,rawPad830,rawTail830,highRawFee] at *
  linarith

/-- The literal detector/root output pays all additions and keeps both
branches of the exact G/root minimum. -/
theorem raw_bound_paid830 (plane : SourcePlane)
    (Z tau D S rho delta normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1 ≤ Z) (htau : 0 ≤ tau) (hC : 0 ≤ C)
    (hD0 : 0 ≤ D) (hD : D ≤ 130) (hS : S ≤ 1/25) (hrho : rho ≤ 1)
    (hnorm : normfee ≤ 1/1000000000) (hheight : tau*(J:ℝ) ≤ 1/1000000000)
    (hbound : Q ≤ C*(1+geometryRawHeight Z tau I)^J*
      Z^(D*(rho+rawRate830)+(delta+2*rawBin830)*S+
        131*(156*rawRate830+rawMesh830+rawRate830+rawRate830)+rawPad830*rho-
        min (Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D))
          (D*plane.rootCutoff*(6*(rho+rawRate830)-1-rawTail830)))) :
    Z^normfee*Q ≤ (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*rho+delta*S-min
        (Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D))
        (D*plane.rootCutoff*(6*rho-1))+highRawFee) := by
  have hp : 0< Z := zero_lt_one.trans_le hZ
  have hroot : 0 ≤ plane.rootCutoff := by cases plane <;> norm_num [SourcePlane.rootCutoff]
  let G:=Marked830.VariableSupply.physicalGain delta S ((1-6*plane.rootCutoff)*D)
  let E:=D*(rho+rawRate830)+(delta+2*rawBin830)*S+
    131*(156*rawRate830+rawMesh830+rawRate830+rawRate830)+rawPad830*rho-
      min G (D*plane.rootCutoff*(6*(rho+rawRate830)-1-rawTail830))
  have hfee:=raw_fee830 plane D S rho rawMesh830 normfee (tau*(J:ℝ)) hD hS hrho
    raw_mesh830_gates.2.2 hnorm hheight
  have hdef:=raw_gain_defect G D plane.rootCutoff rho rawRate830 rawTail830 hD0 hroot
    (by norm_num [rawRate830]) (by norm_num [rawTail830])
  have he : E+normfee+tau*(J:ℝ) ≤ D*rho+delta*S-
      min G (D*plane.rootCutoff*(6*rho-1))+highRawFee := by
    dsimp only [E]
    nlinarith only [hfee,hdef]
  calc
    _ ≤ Z^normfee*(C*(1+geometryRawHeight Z tau I)^J*Z^E) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hp.le _)
    _ ≤ Z^normfee*(C*((1+2*Real.pi+6*(I+1:ℕ))^J*Z^(tau*(J:ℝ)))*Z^E) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      exact mul_le_mul_of_nonneg_left (geometry_raw_height_power hZ htau I J) hC
    _ = (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*Z^(E+normfee+tau*(J:ℝ)) := by
      rw [Real.rpow_add hp,Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
      (by positivity)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.raw_fee830
#print axioms OAI.SevenEighths.TargetHigh830.raw_bound_paid830
end

/- Original module: Candidate.Target830.Marked.GeometryLiteralMarkedCount. -/
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

/-- The scheduled literal geometric count pays all detector, root, mask,
height and optional normalization errors in a single fixed reserve. -/
theorem actual_geometry_literal_marked_count {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (index₀ : RayCharacter×RayCharacter)(Bfirst : ℝ)(setup : DensityCountingSetup)
    (plane : Target830.SourcePlane)(N : ℕ)(hBfirst : 0≤ Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4) :
    ∃J : ℕ,∀(P : HighSourceParameters),MarkedSchedule830 P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,(4/5:ℝ) ≤ D → D ≤ 130 →
      ∀{ι α Row DataLabel : Type}[Fintype ι][Fintype α][DecidableEq α][Nonempty Row][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input ι)(hηs : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : Row→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (gRow : Row→secondLiveRows (fun l=>(datum l).block))
        (hparent : ∀l,(datum (gRow l).val.1).input.η=
          geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (gRow l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (hR : ∀l,(datum (gRow l).val.1).R≠0)(ψ : Row→RayCharacter),
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf:=fun l=> geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀
        s R seed K Z ξ hK bin (column l) datum first (gRow l) (hfirst l)
      let rawKey:=fun l=> secondEncodedNonzeroRow (fun k=>(datum k).block) first (gRow l) left u₀ unit (hf l)
      let key:=fun l=> if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀rows : Finset Row,
      Set.InjOn (fun l=> nonzeroJointSourceRow (key l)) (↑rows:Set Row) →
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      (∀s∈slots,rawTiny830 N ≤ w s) → (∀s∈slots,w s ≤ rawMesh830*rawCore830) →
      (∀s∈slots,w s/P.d ≤ P.Rwidth) →
      (∀s∈slots,P.σmin ≤ σ s) → (∀s∈slots,σ s ≤ P.σmax) →
      (∀l∈rows,(st l).width ≤ P.Mcap) →
      (∀l∈rows,(st l).radial.profile
        (‖ConcreteTraceCRT.eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈rows,geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀l∈rows,a ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        ((3*i:ℕ)*Z^P.τ)) →
      (∀l∈rows,∀s∈slots,|t l+v s|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈rows,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∑s∈slots,w s) ≤ 1/25 →
      ∀normfee : ℝ,normfee ≤ 1/1000000000 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          min (Marked830.VariableSupply.physicalGain (2*a-1) S ((1-6*plane.rootCutoff)*D))
            (D*plane.rootCutoff*(6*ρ-1))+Target830.highRawFee) := by
  obtain ⟨J,hraw⟩:=actual_geometry_literal_raw_max_fixedmesh (Slot:=Slot) M H hH
    η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup W lo hi bΦ 0 rawRate830 rawBin830
    rawRate830 rawRate830 rawTail830 (by norm_num [rawRate830])
    (by norm_num [rawTail830]) (by norm_num [rawTail830]) hWs hW hbΦ hrad
    (by norm_num [rawBin830]) (by norm_num [rawRate830])
    (by norm_num) rfl (by norm_num [rawRate830]) hβ (by simpa using hκβ)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hBholes : 0≤2*Bfirst+P.Bmask+1 := by linarith [hP.mask]
  have hroot : 0≤ plane.rootCutoff ∧ plane.rootCutoff<1/6 := by
    cases plane <;> norm_num [Target830.SourcePlane.rootCutoff]
  obtain ⟨C,hC,hraw⟩:=hraw P hP.slot hP.slotCap hP.sigmaLo hP.sigmaHi hslot hplain
    (4/5) 130 rawCore830 131 rawRate830 rawWitness830 rawWitness830 rawPad830
    (rawTiny830 N) plane.rootCutoff (bufferCount P.e)
    (by norm_num) (by norm_num) hroot.1 hroot.2 (raw_core830_bound plane)
    (by norm_num [rawPad830,rawRate830]) hBholes hP.slotLoss
    (by norm_num [rawPad830,rawRate830]) (raw_tiny830_gates N).1
    (by norm_num [rawCore830]) (by norm_num [rawCore830]) hP.heightZero hP.heightWitness
    (by norm_num [rawRate830]) (by norm_num [rawRate830])
    (by norm_num [rawWitness830]) (by norm_num [rawWitness830])
    (by norm_num [rawWitness830]) hP.buffer
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
    slots w σ v t θ a rawMesh830 i hiI ha0 ha raw_mesh830_gates.1.le
    (by simpa using raw_mesh830_gates.2.1)
    (by norm_num [rawBin830];linarith) hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
  have hρ : ρ≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
  have ht : P.τ*(J:ℝ)≤1/1000000000 := by
    nlinarith [P.hτ,Nat.cast_nonneg (α:=ℝ) J]
  exact TargetHigh830.raw_bound_paid830 plane Z P.τ D S ρ (2*a-1) normfee C
    (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2)
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS hρ hnorm ht
    (by simpa only [add_assoc] using hh)

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_geometry_literal_marked_count
end

/- Original module: Candidate.Target830.Marked.GeometryUniformMarkedCount. -/
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

/-- One height degree and one scale threshold work for every fixed member
of the finite geometric dictionary, before either common allocation. -/
theorem actual_geometry_uniform_marked_count {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Bfirst : ℝ)(setup : DensityCountingSetup)
    (plane : Target830.SourcePlane)(N : ℕ)(hBfirst : 0≤ Bfirst)
    (W : ℝ→ℂ) (lo hi bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0 < bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ 3/4) :
    ∃J : ℕ,∀(P : HighSourceParameters),MarkedSchedule830 P N W lo hi →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000 →
      ∃C : ℝ,0 < C ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀D : ℝ,(4/5:ℝ) ≤ D → D ≤ 130 →
      ∀index₀ : RayCharacter×RayCharacter,
      ∀{ι α Row DataLabel : Type}[Fintype ι][Fintype α][DecidableEq α][Nonempty Row][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input ι)(hηs : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : Row→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (gRow : Row→secondLiveRows (fun l=>(datum l).block))
        (hparent : ∀l,(datum (gRow l).val.1).input.η=
          geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (gRow l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (hR : ∀l,(datum (gRow l).val.1).R≠0)(ψ : Row→RayCharacter),
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf:=fun l=> geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀
        s R seed K Z ξ hK bin (column l) datum first (gRow l) (hfirst l)
      let rawKey:=fun l=> secondEncodedNonzeroRow (fun k=>(datum k).block) first (gRow l) left u₀ unit (hf l)
      let key:=fun l=> if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀rows : Finset Row,
      Set.InjOn (fun l=> nonzeroJointSourceRow (key l)) (↑rows:Set Row) →
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      (∀s∈slots,rawTiny830 N ≤ w s) → (∀s∈slots,w s ≤ rawMesh830*rawCore830) →
      (∀s∈slots,w s/P.d ≤ P.Rwidth) →
      (∀s∈slots,P.σmin ≤ σ s) → (∀s∈slots,σ s ≤ P.σmax) →
      (∀l∈rows,(st l).width ≤ P.Mcap) →
      (∀l∈rows,(st l).radial.profile
        (‖ConcreteTraceCRT.eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈rows,geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀l∈rows,a ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        ((3*i:ℕ)*Z^P.τ)) →
      (∀l∈rows,∀s∈slots,|t l+v s|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈rows,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∑s∈slots,w s) ≤ 1/25 →
      ∀normfee : ℝ,normfee ≤ 1/1000000000 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          min (Marked830.VariableSupply.physicalGain (2*a-1) S ((1-6*plane.rootCutoff)*D))
            (D*plane.rootCutoff*(6*ρ-1))+Target830.highRawFee) := by
  have hex (index₀ : RayCharacter×RayCharacter):=
    actual_geometry_literal_marked_count (Slot:=Slot) M H hH η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup
      plane N hBfirst W lo hi bΦ hWs hW hbΦ hrad hβ hκβ
  choose Ji hcounts using hex
  let J:=Finset.univ.sup Ji
  have hJ (index₀ : RayCharacter×RayCharacter):Ji index₀≤ J:=
    Finset.le_sup (f:=Ji) (Finset.mem_univ index₀)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hheighti (index₀ : RayCharacter×RayCharacter) :
      2*P.τ*((Ji index₀:ℝ)+1)≤1/1000000000 := by
    have hi : (Ji index₀:ℝ)≤ J:=by exact_mod_cast hJ index₀
    exact (mul_le_mul_of_nonneg_left (by linarith : (Ji index₀:ℝ)+1≤ J+1)
      (mul_nonneg (by norm_num) P.hτ.le)).trans hheight
  choose C hC hcount using (fun index₀=> hcounts index₀ P hP hslot hplain (hheighti index₀))
  let Cmax:=max 1 (∑index₀,C index₀)
  have hCmax : 0< Cmax:=(zero_lt_one.trans_le (le_max_left _ _))
  have hCi (index₀ : RayCharacter×RayCharacter):C index₀≤ Cmax:=
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
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.actual_geometry_uniform_marked_count
end
