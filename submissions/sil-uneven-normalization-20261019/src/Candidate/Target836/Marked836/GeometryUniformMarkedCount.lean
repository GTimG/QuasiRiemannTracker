import Candidate.Cycle63.Physical.InitialMass.MarkedParameters
import Candidate.Target836.Marked836.MarkedRate
import Candidate.Cycle63.Marked.GeometryRawGates
import Candidate.Target836.Marked836.GeometryLiteralRawMax
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule

/- Original module: Candidate.Target836.Marked836.MarkedParameters. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Marked836Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section

/-- The original sixth-root cutoff pays the changing coefficient, using the
actual density at the same zero bin. No independent density is substituted. -/
theorem marked_tail_dominates (D ρ ordloss S δ : ℝ) (hD : 0≤ D)
    (hδ0 : (839/1250:ℝ)≤δ) (hδ : δ≤7/10)
    (hρ : Marked836.VariableSupply.density δ≤ρ) (hord : 0≤ ordloss) :
    min (Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+ordloss)-1-(9/100))) =
        Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)) := by
  apply min_eq_left
  have hc := Marked836.VariableSupply.coefficient_nonneg (show 13/20≤δ by linarith) hδ
  have hcap := mul_le_mul_of_nonneg_left
    (min_le_right S ((13/400)*((1-6*markedRootCutoff)*D))) hc
  have ht := Marked836.VariableSupply.old_root_tail_dominates (show 13/20≤δ by linarith) hδ
  have htd := mul_le_mul_of_nonneg_right ht hD
  have hr := mul_le_mul_of_nonneg_left hρ (show 0≤ D/250 by positivity)
  have ho := mul_nonneg hD hord
  dsimp [markedRootCutoff] at hcap ⊢
  nlinarith

/-- The accepted mesh, bin, padding and height prices remain explicit. -/
theorem marked_raw_exponent_paid (D S ρ δ mesh μ normfee heightfee : ℝ)
    (hD0 : 0≤ D) (hD : D≤130) (hS : S≤1/25)
    (hδ0 : (839/1250:ℝ)≤δ) (hδ : δ≤7/10)
    (hρeq : ρ=Marked836.VariableSupply.density δ)
    (hρ : ρ≤1) (hmesh : mesh≤ markedRate)
    (hμ : μ≤1/100000000) (hnorm : normfee≤μ/32) (hheight : heightfee≤μ/8) :
    D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
      131*(156*markedRate+mesh+markedRate+markedRate)+markedPad*ρ-
      min (Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D)))
        (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100)))+normfee+heightfee≤
      D*ρ+δ*S-Marked836.VariableSupply.coefficient δ*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ) := by
  rw [marked_tail_dominates D ρ markedRate S δ hD0 hδ0 hδ
    (by rw [hρeq]) (by norm_num [markedRate])]
  have h := marked_raw_error_budget D S ρ mesh μ normfee heightfee
    hD hS hρ hmesh hμ hnorm hheight
  nlinarith

end
end OAI.SevenEighths.Marked836Plain
#print axioms OAI.SevenEighths.Marked836Plain.marked_tail_dominates
#print axioms OAI.SevenEighths.Marked836Plain.marked_raw_exponent_paid
end

/- Original module: Candidate.Target836.Marked836.GeometryRawBudget. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Marked836Plain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators

/-- Pay the polynomial geometric height and an optional multiplicative
normalization loss in the actual raw count. -/
theorem marked_geometry_raw_bound_paid
    (Z τ D S ρ δ μ normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hD0 : 0 ≤ D) (hD : D ≤ 130) (hS : S ≤ 1/25)
    (hδ0 : (839/1250:ℝ) ≤ δ) (hδ : δ ≤ 7/10)
    (hρeq : ρ = Marked836.VariableSupply.density δ) (hρ : ρ ≤ 1)
    (hμ : μ ≤ 1/100000000) (hnorm : normfee ≤ μ/32) (hheight : τ*(J:ℝ) ≤ μ/8)
    (hbound : Q ≤ C*(1+geometryRawHeight Z τ I)^J*
      Z^(D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
        131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
        min ((Marked836.VariableSupply.coefficient δ)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
          (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100))))) :
    Z^normfee*Q ≤ (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*ρ+δ*S-(Marked836.VariableSupply.coefficient δ)*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ)) := by
  have hp : 0 < Z:=zero_lt_one.trans_le hZ
  let E:=D*(ρ+markedRate)+(δ+2*markedBinWidth)*S+
    131*(156*markedRate+markedRawMesh+markedRate+markedRate)+markedPad*ρ-
    min ((Marked836.VariableSupply.coefficient δ)*min S ((13/400)*((1-6*markedRootCutoff)*D)))
      (D*markedRootCutoff*(6*(ρ+markedRate)-1-(9/100)))
  have he : E+normfee+τ*(J:ℝ) ≤
      D*ρ+δ*S-(Marked836.VariableSupply.coefficient δ)*min S ((13/400)*((1-6*markedRootCutoff)*D))+(1/200000:ℝ) :=
    marked_raw_exponent_paid D S ρ δ markedRawMesh μ normfee (τ*(J:ℝ))
      hD0 hD hS hδ0 hδ hρeq hρ marked_raw_mesh_gates.2.2 hμ hnorm hheight
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
end OAI.SevenEighths.Marked836Plain
#print axioms OAI.SevenEighths.Marked836Plain.marked_geometry_raw_bound_paid
end

/- Original module: Candidate.Target836.Marked836.GeometryLiteralMarkedCount. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Marked836Plain
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
    (N : ℕ)(μ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hBfirst : 0≤ Bfirst)
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
      i ≤ bufferCount P.e → 839/1250 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      (∀s∈slots,markedTinyWidth N ≤ w s) → (∀s∈slots,w s ≤ markedRawMesh*markedCoreMin) →
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
      ∀normfee : ℝ,normfee ≤ μ/32 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          (Marked836.VariableSupply.coefficient (2*a-1))*min S ((13/400)*((122/125)*D))+(1/200000:ℝ)) := by
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
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS ha0 ha rfl hρ hμcap hnorm ht (by simpa only [add_assoc] using hh)
  convert hb using 1 <;> norm_num [markedRootCutoff]

end
end OAI.SevenEighths.Marked836Plain
#print axioms OAI.SevenEighths.Marked836Plain.actual_geometry_literal_marked_count
end

/- Original module: Candidate.Target836.Marked836.GeometryUniformMarkedCount. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.Marked836Plain
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
    (N : ℕ)(μ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hBfirst : 0≤ Bfirst)
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
      i ≤ bufferCount P.e → 839/1250 ≤ 2*a-1 → 2*a-1 ≤ 7/10 →
      (∀s∈slots,markedTinyWidth N ≤ w s) → (∀s∈slots,w s ≤ markedRawMesh*markedCoreMin) →
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
      ∀normfee : ℝ,normfee ≤ μ/32 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          (Marked836.VariableSupply.coefficient (2*a-1))*min S ((13/400)*((122/125)*D))+(1/200000:ℝ)) := by
  have hex (index₀ : RayCharacter×RayCharacter):=
    actual_geometry_literal_marked_count (Slot:=Slot) M H hH η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup
      N μ hμ hμcap hBfirst W lo hi bΦ hWs hW hbΦ hrad hβ hκβ
  choose Ji hcounts using hex
  let J:=Finset.univ.sup Ji
  have hJ (index₀ : RayCharacter×RayCharacter):Ji index₀≤ J:=
    Finset.le_sup (f:=Ji) (Finset.mem_univ index₀)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hheighti (index₀ : RayCharacter×RayCharacter) :
      2*P.τ*((Ji index₀:ℝ)+1)≤μ/8 := by
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
end OAI.SevenEighths.Marked836Plain
#print axioms OAI.SevenEighths.Marked836Plain.actual_geometry_uniform_marked_count
end
