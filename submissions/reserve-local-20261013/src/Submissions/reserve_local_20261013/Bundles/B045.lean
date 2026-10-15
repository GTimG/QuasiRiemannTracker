/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B003
import Submissions.local44_20261013.Bundles.B009
import Submissions.reserve_local_20261013.Bundles.B030
import Submissions.reserve_local_20261013.Bundles.B032
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.reserve_local_20261013.Bundles.B036
import Submissions.reserve_local_20261013.Bundles.B041
import Submissions.reserve_local_20261013.Bundles.B042
import Submissions.reserve_local_20261013.Bundles.B043
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowBranchSum

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighSource ; sha256 4fa79d9872854e133096e970152faa3bb08f9631149e64e4fe6d57c97a3d8d1b -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighSource.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=> balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:7/10≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤ Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hx (X:ℝ):X≤ Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=> Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤ Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 7/10≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=> le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSource

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighSource -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorLabels ; sha256 a4ab9d58b61d3ba6e3374f170a21bd828df344255d5cf9e4c8759981b38a8fa9 -/
section




/-! Summing positive coefficient masses over all independent error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem finite_label_damped_mass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (A : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ) (hN : ∀ i e, 0 < N i e)
    (weight : ι → ℂ) (B : ι → ℝ) (L rho M : ℝ)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) ≤ M*B i) :
    Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ∧
    (∑' e : Σ i, α i, ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ≤
      M * ∑ i, ‖weight i‖*B i := by
  have he (i : ι) (e : α i) : ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho = ‖weight i‖ *
      (‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) := by
    rw [norm_mul]
    ring
  have hfs (i : ι) : Summable (fun e => ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho) := by
    simp_rw [he]
    exact (hs i).mul_left _
  have hsum : Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) := by
    apply (summable_sigma_of_nonneg (fun e => by have := hN e.1 e.2; positivity)).mpr
    exact ⟨hfs,(hasSum_fintype _).summable⟩
  refine ⟨hsum,?_⟩
  rw [hsum.tsum_sigma,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp_rw [he,tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)).trans_eq (by ring)

theorem errorProductSize_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (P : ι → ProbePhysical.PrimeIdeal) (hP : Function.Injective P) :
    errorProductSize u (Finset.univ.image P) = ∏ i, 2880 * errorSize u (P i) := by
  unfold errorProductSize
  calc
    _ = ∏ Q ∈ Finset.univ.image P, 2880 * errorSize u Q :=
      Finset.prod_coe_sort _ _
    _ = _ := Finset.prod_image hP.injOn

theorem error_label_mass_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) =
      ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  calc
    _ = ∑ P : ∀ i, T i, ∏ i, 2880 * ‖weight i (P i)‖ * errorSize u (P i).val := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [norm_prod,errorProductSize_image u _ (hdis P),←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := (Fintype.prod_sum (fun i => fun P : T i =>
      2880 * ‖weight i P‖ * errorSize u P.val)).symm

theorem error_label_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) (B : ι → ℝ)
    (hm : ∀ i, (∑ P : T i, ‖weight i P‖ * errorSize u P.val) ≤ B i) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) ≤
      ∏ i, 2880 * B i := by
  rw [error_label_mass_factor u T hdis weight]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg (fun P hP => mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) (errorSize_nonneg u P.val))
  · intro i hi
    calc
      _ = 2880 * ∑ P : T i, ‖weight i P‖ * errorSize u P.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P hP
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by norm_num)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorLabels -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPacketMellin ; sha256 6e01f732f9e73496113f84a10556a91fbd052ea4d6a7f24868964f58af20b5a9 -/
section



/-! Mellin inversion of the actual numerator with the complete error packet. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

instance correctionIndex_countable (S : Finset (Ideal O)) (u : FreeRow) :
    Countable (CorrectionIndex S u) := by unfold CorrectionIndex EulerIndex; infer_instance
instance errorPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) : Countable (ErrorPacketIndex S u T) := by
  unfold ErrorPacketIndex
  infer_instance

theorem error_packet_central_summable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ))) := by
  have hC := (continuedCorrection_coefficient_mass firsteps (1 / 2)
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx hz (by norm_num) hmargin).1
  have hE := (hasSum_fintype (fun j : T → Fin 4 => ‖errorTupleCoefficient η u T hT x z j‖ *
    (errorTupleScale T j : ℝ)^(-(1 / 2 : ℝ)))).summable
  exact weighted_product_summable _ _ _ _ (1 / 2) hE hC

theorem actual_error_packet_mellin (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0 < Y) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
      (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
      ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
          η u x ((1 / 2 : ℂ) + t * I) z)) =
    (Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' e : ErrorPacketIndex S u T,
      errorPacketCoefficient S hS η u T hT x z e *
        (errorPacketScale S u T e : ℂ)^(-(1 / 2 : ℂ)) *
        HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
          (Y / (errorPacketScale S u T e : ℝ)) 0 0 := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1 / 2 : ℂ) + t * I) z hQ hx hz
    (by simp; norm_num) (by simpa using hmargin)
  simp_rw [he]
  exact MellinReconstruction.weighted_numerator_mellin (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY
    (errorPacketCoefficient S hS η u T hT x z) (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)

theorem reconstructed_numerator_bound {κ : Type*} [Countable κ]
    (χ : Character) (W : ℝ → ℂ) (a b Y L rho M B : ℝ)
    (hsupp : Function.support W ⊆ Icc a b) (hY : 0 < Y) (hM : 0 ≤ M)
    (A : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (hmass : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho))
    (hmb : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ B)
    (hpoly : ∀ i, N i ≤ b * Y → ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho) :
    ‖(Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' i,
      A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
        Y^(-(1 / 2 : ℝ)) * (M * B) := by
  have hpoly' (i : κ) : ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho := by
    by_cases hi : N i ≤ b * Y
    · exact hpoly i hi
    · rw [MellinReconstruction.polynomial_zero_of_scale_cutoff χ W a b Y (N i)
        hsupp hY (hN i) (lt_of_not_ge hi),norm_zero]
      exact mul_nonneg hM (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) rho)
  have hbound (i : κ) :
      ‖A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * (‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i)]
    rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (‖A i‖ * (N i)^(-(1 / 2 : ℝ))) * (M * max 1 (L * N i)^rho) :=
        mul_le_mul_of_nonneg_left (hpoly' i) (by have := hN i; positivity)
      _ = _ := by ring
  have hs := (hmass.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hn := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound (hmass.mul_left M))
  rw [tsum_mul_left] at hn
  have hm := hn.trans (mul_le_mul_of_nonneg_left hmb hM)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
  rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hY.le _)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPacketMellin -/

/- BEGIN ORIGINAL MODULE Global.Final.Baseline ; sha256 7e950b1de18478339cf1284dc43a31693828da6141a0e2bd8494a02c1f1b3537 -/
section



/-! The original OpenAI 7/8 initialization supplies only the coarse upper
bound needed to choose the variable moment parameter.  No improved endpoint
is used.  Apache-2.0 OpenAI/math family003 attribution retained. -/
namespace Submission20261012.Global.FinalAssembly
open OAI.SevenEighths

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : Submission20261012.Global.theta < HeckeZeroSupremum.beta) :
    (7/10:ℝ) ≤ 2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ) ∧
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
  have hlo := Submission20261012.Global.theta_gt_half
  have htheta : (874:ℝ)/1000 < Submission20261012.Global.theta := by
    norm_num [Submission20261012.Global.theta, Submission20261012.Endpoint.theta]
  have hhi := baseline_beta
  constructor
  · linarith
  constructor <;> linarith
end Submission20261012.Global.FinalAssembly

#print axioms Submission20261012.Global.FinalAssembly.baseline_beta
end
/- END ORIGINAL MODULE Global.Final.Baseline -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowSlotScales ; sha256 820b1732142a60a43e989dbf924c9c6f6b82a2c2bdf2d01b6b1c0f1284654274 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSlotScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_ge_one {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    1≤ elementNorm (∏i : J,(a i).val) := by
  have hn : (∏i : J,(a i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=> hslots i.val _ (a i).property)
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hn))

lemma lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (b Z : ℝ) (hb : 1≤ b) (hZ : 1≤ Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤ b^K*Z^(Submission20261012.Global.ell:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤ Submission20261012.Global.ell :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> hell i)).trans hsum
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=> by unfold elementNorm;positivity)
      (fun i _=> hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤ b^K*Z^(Submission20261012.Global.ell:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (b : ℝ) (hb : 1≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤ Z^(Submission20261012.Global.ly:ℝ)/L ∧
      1≤(Z^(Submission20261012.Global.ly:ℝ)/L)^2/lowPhysicalScale C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowSlotScales -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowBranchSum ; sha256 00cc9c07c3b70d1c9b552b6b87fe5727f10e2101d7536386dd2eca950d4b9421 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowBranchSum.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_low_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0< kK) (hkP : 0< kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1< Z₀ ∧ 0< C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤ Z^Lrow → (kP*QP)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_low_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowBranchSum -/
