import Candidate.Uneven.BootstrapCoefficients
import Candidate.Uneven.FineSchedule
import Candidate.Cycle63.Marked.GeometryRawGates
import Candidate.Uneven.BootstrapSchedule
import Candidate.Uneven.BootstrapGeometryLiteral

/- Original module: Candidate.Uneven.BootstrapTail. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem tail_reserve {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    offset d 4+1/1000 ≤ (6*(Saturated.rho d-3/200)-1-1/1000)/100 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2))) := by
    have he : (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2)))=469456465036100*(d-31/50)^0*(33/50-d)^3+1834792222980700*(d-31/50)^1*(33/50-d)^2+2272901589251000*(d-31/50)^2*(33/50-d)^1+881010854306400*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (127168237500000+(-146028426000000*d)+(38064452400000*(d^2))) := by
    have he : (127168237500000+(-146028426000000*d)+(38064452400000*(d^2)))=47370351805440+2432648173200000*(d-31/50)^0*(33/50-d)^2+2394583720800000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hsmall : 0 < 2543364750-2920568520*d+761289048*d^2 := by
    nlinarith only [hden]
  have he : (6*(Saturated.rho d-3/200)-1-1/1000)/100-offset d 4-1/1000=
      (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2)))/(127168237500000+(-146028426000000*d)+(38064452400000*(d^2))) := by
    norm_num [Saturated.rho,offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have h := div_nonneg hn hden.le
  rw [←he] at h
  linarith only [h]

theorem tail_absorbs_gain {d S D loss tail : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hD : 0 ≤ D) (hloss : 0 ≤ loss) (htail : tail ≤ 1/1000) :
    physicalGain d S D ≤ D*(1/100)*(6*(Saturated.rho d+loss-3/200)-1-tail) := by
  have hg := FiniteGain.gain_le (slope d) (offset d) S D 4
  have hz : slope d 4=0 := by norm_num [slope]
  rw [hz,zero_mul,zero_add] at hg
  have ht : offset d 4 ≤ (6*(Saturated.rho d+loss-3/200)-1-tail)/100 := by
    linarith [tail_reserve hd0 hd1]
  have hmul := mul_le_mul_of_nonneg_right ht hD
  apply hg.trans
  nlinarith only [hmul]

end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.BootstrapRawFee. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.BootstrapPlain
noncomputable section
open Marked830Plain Cycle63MarkedPlain
open SaturatedPlain
open Sil.Uneven.Saturated (rho)
open Sil.Uneven.Bootstrap
open scoped BigOperators

theorem raw_fee (D S r mesh normfee heightfee : ℝ)
    (hD : D≤130) (hS : S≤1/25) (hr : r≤1)
    (hmesh : mesh≤ fineRawRate) (hnorm : normfee≤1/1000000000000)
    (hheight : heightfee≤1/1000000000000) :
    D*fineRawRate+2*fineRawBin*S+
      131*(402*fineRawRate+mesh+fineRawRate+fineRawRate)+fineRawPad*r+
      normfee+heightfee≤ fineHighRawFee := by
  norm_num [fineRawRate,fineRawBin,fineRawPad,fineHighRawFee] at *
  linarith

theorem raw_bound_paid (Z tau D S delta mesh normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1≤ Z) (htau : 0≤ tau) (hC : 0≤ C)
    (hD0 : 0≤ D) (hD : D≤130) (hS : S≤1/25) (hmesh : mesh≤ fineRawRate)
    (hd0 : 31/50≤ delta) (hd : delta≤33/50)
    (hnorm : normfee≤1/1000000000000) (hheight : tau*(J:ℝ)≤1/1000000000000)
    (hbound : Q≤ C*(1+geometryRawHeight Z tau I)^J*
      Z^(D*(rho delta+fineRawRate)+(delta+2*fineRawBin)*S+
        131*(402*fineRawRate+mesh+fineRawRate+fineRawRate)+fineRawPad*rho delta-
        min (physicalGain delta S D)
          (D*(1/100)*(6*(rho delta+fineRawRate-3/200)-1-fineRawTail)))) :
    Z^normfee*Q≤(C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*rho delta+delta*S-physicalGain delta S D+fineHighRawFee) := by
  have hp : 0< Z := zero_lt_one.trans_le hZ
  have hr : rho delta≤1 := by
    unfold rho
    have hh : 0≤10*delta/(3*(5-2*delta)) := div_nonneg (by linarith) (by linarith)
    linarith
  have htail := tail_absorbs_gain (S:=S) hd0 hd hD0
    (show 0≤ fineRawRate by norm_num [fineRawRate])
    (show fineRawTail≤1/1000 by norm_num [fineRawTail])
  rw [min_eq_left htail] at hbound
  let E:=D*(rho delta+fineRawRate)+(delta+2*fineRawBin)*S+
    131*(402*fineRawRate+mesh+fineRawRate+fineRawRate)+fineRawPad*rho delta-
      physicalGain delta S D
  have hfee:=raw_fee D S (rho delta) mesh normfee (tau*(J:ℝ)) hD hS hr
    hmesh hnorm hheight
  have he : E+normfee+tau*(J:ℝ)≤ D*rho delta+delta*S-physicalGain delta S D+fineHighRawFee := by
    dsimp only [E]
    nlinarith only [hfee]
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
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) (by positivity)

end
end OAI.SevenEighths.BootstrapPlain
end

/- Original module: Candidate.Uneven.BootstrapGeometryPaid. -/
section

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.BootstrapPlain
open Marked830Plain SaturatedPlain
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
    (N : ℕ)(hBfirst : 0≤ Bfirst)
    (W : ℝ→ℂ) (bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2 ≤ bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃J : ℕ,∀(P : HighSourceParameters),FineMarkedSchedule P N W (33/50) (33/50) →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      (∀s∈slots,fineRawTiny N ≤ w s) → (∀s∈slots,w s ≤ bootstrapRawMesh*fineRawCore) →
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
      ∀normfee : ℝ,normfee ≤ 1/1000000000000 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Sil.Uneven.Bootstrap.physicalGain (2*a-1) S D+fineHighRawFee) := by
  obtain ⟨J,hraw⟩:=actual_geometry_literal_raw_max_fixedmesh (Slot:=Slot) M H hH
    η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup W bΦ 0 fineRawRate fineRawBin
    fineRawRate fineRawRate fineRawTail (by norm_num [fineRawRate])
    (by norm_num [fineRawTail]) (by norm_num [fineRawTail]) hWs hW hbΦ hrad
    (by norm_num [fineRawBin]) (by norm_num [fineRawRate])
    (by norm_num) rfl (by norm_num [fineRawRate]) hβ (by simpa using hβhi)
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
    slots w σ v t θ a bootstrapRawMesh i hiI ha0 ha bootstrap_raw_mesh_gates.1.le
    (by simpa using bootstrap_raw_mesh_gates.2.1)
    bootstrap_raw_mesh_gates.2.2.2
    (by norm_num [fineRawBin];linarith) hw hwm hwr hlo hhi hwidth hradial hnext hcurrent hfreq hplainfreq
  have hρ : ρ≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
  have ht : P.τ*(J:ℝ)≤1/1000000000000 := by
    nlinarith [P.hτ,Nat.cast_nonneg (α:=ℝ) J]
  exact raw_bound_paid Z P.τ D S (2*a-1) bootstrapRawMesh normfee C
    (∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2)
    (bufferCount P.e) J he.1.le P.hτ.le hC.le (by linarith) hD' hS bootstrap_raw_mesh_gates.2.2.1 ha0 ha hnorm ht
    (by simpa only [Sil.Uneven.Saturated.rho,unmarkedDensity,χ,S,add_assoc] using hh)

end
end OAI.SevenEighths.BootstrapPlain
end

/- Original module: Candidate.Uneven.BootstrapGeometryUniform. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace OAI.SevenEighths.BootstrapPlain
open Marked830Plain SaturatedPlain
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
    (N : ℕ)(hBfirst : 0≤ Bfirst)
    (W : ℝ→ℂ) (bΦ : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2 ≤ bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃J : ℕ,∀(P : HighSourceParameters),FineMarkedSchedule P N W (33/50) (33/50) →
    8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
    2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
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
      i ≤ bufferCount P.e → 31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      (∀s∈slots,fineRawTiny N ≤ w s) → (∀s∈slots,w s ≤ bootstrapRawMesh*fineRawCore) →
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
      ∀normfee : ℝ,normfee ≤ 1/1000000000000 →
      let χ:=fun l=> excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      Z^normfee*(∑l∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s‖)^2) ≤
        C*Z^(D*ρ+(2*a-1)*S-
          Sil.Uneven.Bootstrap.physicalGain (2*a-1) S D+fineHighRawFee) := by
  have hex (index₀ : RayCharacter×RayCharacter):=
    actual_geometry_literal_marked_count (Slot:=Slot) M H hH η₀ u₀ F₀ R₀ hu₀ index₀ Bfirst setup
      N hBfirst W bΦ hWs hW hbΦ hrad hβ hβhi
  choose Ji hcounts using hex
  let J:=Finset.univ.sup Ji
  have hJ (index₀ : RayCharacter×RayCharacter):Ji index₀≤ J:=
    Finset.le_sup (f:=Ji) (Finset.mem_univ index₀)
  refine ⟨J,?_⟩
  intro P hP hslot hplain hheight
  have hheighti (index₀ : RayCharacter×RayCharacter) :
      2*P.τ*((Ji index₀:ℝ)+1)≤1/1000000000000 := by
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
end OAI.SevenEighths.BootstrapPlain
end
