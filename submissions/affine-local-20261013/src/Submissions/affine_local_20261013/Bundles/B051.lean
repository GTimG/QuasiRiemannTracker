/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.affine_local_20261013.Bundles.B032
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B036
import Submissions.affine_local_20261013.Bundles.B041
import Submissions.affine_local_20261013.Bundles.B044
import Submissions.affine_local_20261013.Bundles.B045
import Submissions.affine_local_20261013.Bundles.B047
import Submissions.affine_local_20261013.Bundles.B048
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveBalancedAdmission ; sha256 a8653de76c80cd6f134539255137b1d436976782aeb47f9adfdb4bd944e7764a -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveBalancedAdmission.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open Cycle25CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α]
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

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open Cycle25CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤ N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=> le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1< Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:7/10≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    (balancedSource).X₁≤ Z^L ∧ (balancedSource).X₂≤ Z^L ∧
    (balancedSource).Y₁≤ Z^L ∧ (balancedSource).Y₂≤ Z^L := by
  have hp:0< Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=> hw i))
  have hxy:X₁*X₂≤ volume balancedSource:=by
    change X₁*X₂≤ X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤ Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤ Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:7/10≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    1≤ s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤ s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤ s.width ∧
    volume balancedSource≤ Z^s.width ∧ Real.logb Z (volume balancedSource)≤ s.width ∧
    volume balancedSource≤ Z^L ∧
    (s.puncture.absNorm:ℝ)≤ Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.Cycle25CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveBalancedAdmission -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighAssemblyBounded ; sha256 fd56169588c056d9bf962c35adadd1524b6dd1a833b3382d8e2b63dc444683b0 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighAssemblyBounded.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighAssemblyBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyPositiveHighSource (balancedInput)
open Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open Cycle25CenteredMomentEnergyPositiveHighSourceBounded Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
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

open Cycle25CenteredMomentEnergyPositiveHighAssembly (low_restrict)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e→ 0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
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
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+e+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+e+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hLuUpper,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,max_le hLuUpper hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) le_rfl hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) le_rfl hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 e Lslot κ η₀ Q K he hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 e Lslot κ η₀ Q K he hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighAssemblyBounded

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighAssemblyBounded -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.DilationBoxes ; sha256 f1944cd1037ce284477644095554a7f2de25ead3a4f5716bf57e37a1fed26451 -/
section



/-! Finitely many exponent boxes for the actual compactly truncated dilation.
The box count depends on the chosen small width, not on the row scale. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem exponent_boxes_cover (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi) := by
  induction n with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · simpa using ht
    · have hpow : 1 ≤ U^xi := Real.one_le_rpow hU hxi
      have ht1 : t ≤ 1 := by simpa using hupper
      simpa using ht1.trans hpow
  | succ n ih =>
    by_cases hsmall : t ≤ U^((n : ℝ)*xi)
    · obtain ⟨j,hj,hlo,hhi⟩ := ih hsmall
      refine ⟨j,?_,hlo,hhi⟩
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (by omega))
    · refine ⟨n,Finset.mem_range.mpr (by omega),(le_of_lt (lt_of_not_ge hsmall)),?_⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hupper

/-- Compact support bounds every active coefficient dilation by a fixed power of U. -/
theorem active_dilation_upper (U xi L N b Y : ℝ) (n : ℕ)
    (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hL : L ≤ 1) (hN : 0 ≤ N)
    (hcut : N ≤ b*Y) (hY : b*Y ≤ U^((n : ℝ)*xi)) :
    max 1 (L*N) ≤ U^((n : ℝ)*xi) := by
  apply max_le
  · exact Real.one_le_rpow hU (mul_nonneg (Nat.cast_nonneg _) hxi)
  · exact (mul_le_mul_of_nonneg_right hL hN).trans
      (by simpa only [one_mul] using hcut.trans hY)

def dilationBox (U xi : ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  if h : ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi)
  then Classical.choose h else 0

theorem dilationBox_mem (U xi : ℝ) (n : ℕ) (t : ℝ) :
    dilationBox U xi n t ∈ Finset.range (n+1) := by
  unfold dilationBox
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem dilationBox_spec (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    U^((dilationBox U xi n t : ℝ)*xi) ≤ t ∧
      t ≤ U^(((dilationBox U xi n t : ℝ)+1)*xi) := by
  have he := exponent_boxes_cover U xi hU hxi n t ht hupper
  rw [dilationBox,dif_pos he]
  exact (Classical.choose_spec he).2

theorem dilation_weight_bound (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t rho : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) (hrho : 0 ≤ rho) :
    t^(-rho) ≤ U^(-rho*(dilationBox U xi n t : ℝ)*xi) := by
  have hlo := (dilationBox_spec U xi hU hxi n t ht hupper).1
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (U^((dilationBox U xi n t : ℝ)*xi))^(-rho) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU0 _) hlo (neg_nonpos.mpr hrho)
    _ = _ := by rw [←Real.rpow_mul hU0.le]; congr 1; ring

theorem finite_box_partition {κ : Type*} (U xi : ℝ) (n : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) :
    (∑ j ∈ Finset.range (n+1), if dilationBox U xi n (t e) = j then f e else 0) = f e := by
  rw [Finset.sum_eq_single (dilationBox U xi n (t e))]
  · simp
  · intro j hj hne
    simp only [ite_eq_right (Ne.symm hne)]
  · intro hn
    exact False.elim (hn (dilationBox_mem U xi n (t e)))

def boxSeriesTerm {κ : Type*} (U xi : ℝ) (n j : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) : ℂ := if dilationBox U xi n (t e) = j then f e else 0

theorem boxSeries_summable_norm {κ : Type*} (U xi : ℝ) (n j : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    Summable (fun e => ‖boxSeriesTerm U xi n j t f e‖) := by
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro e
  unfold boxSeriesTerm
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f e)

theorem tsum_box_decomposition {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1), ∑' e, boxSeriesTerm U xi n j t f e := by
  rw [←Summable.tsum_finsetSum (fun j hj => (boxSeries_summable_norm U xi n j t f hf).of_norm)]
  apply tsum_congr
  intro e
  exact (finite_box_partition U xi n t f e).symm

theorem norm_tsum_le_boxes {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    ‖∑' e, f e‖ ≤ ∑ j ∈ Finset.range (n+1), ‖∑' e, boxSeriesTerm U xi n j t f e‖ := by
  rw [tsum_box_decomposition U xi n t f hf]
  exact norm_sum_le _ _

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.DilationBoxes -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorIntegrable ; sha256 521057b704b7aa1f0ffa22f43bbec20d54a2a236355d782dd2fc10a1f0c69ca4 -/
section



/-! Absolute integrability before the finite error subsets are interchanged. -/
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem actual_error_packet_integrable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (hη : ∀P∈T,IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀P∈T,(4:ℝ)≤ P.val.absNorm)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0< Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*I)*
      ((∏P:T,rawErrorSlot η u P.val (hT P.val P.property) x ((1/2:ℂ)+t*I) z)*
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x ((1/2:ℂ)+t*I) z)) := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1/2:ℂ)+t*I) z hQ hx hz (by simp;norm_num) (by simpa using hmargin)
  simp_rw [he]
  simp only [HeckeOrigin.continued,ite_eq_right hrow]
  have hh := MellinReconstruction.coefficient_series_integrable
    (errorPacketCoefficient S hS η u T hT x z) (fun e=>(errorPacketScale S u T e:ℝ))
    (fun e=> lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) (1/2)
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)
    _ (MellinReconstruction.reconstruction_kernel_integrable (rowCharacter S hS.prime u) hrow
      W a b ha hsupp hW Y hY)
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh

def finsetImageEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α→β) (hf : Function.Injective f) : s≃s.image f :=
  Equiv.ofBijective (fun i:s=>⟨f i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩)
    ⟨by intro i j hij;apply Subtype.ext;exact hf (congrArg Subtype.val hij),by
      intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩⟩

theorem error_product_image {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val) (x w z : ℂ) :
    (∏i∈I,rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z := by
  rw [←Finset.prod_coe_sort I]
  exact Fintype.prod_equiv (finsetImageEquiv I P hP) _ _ (fun _=> rfl)

theorem weightedErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I P hPS W Yp x w z=
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)*
      ((∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (I.image P))
          (markedSourceExclusions S hS (I.image P)) η u x w z) := by
  unfold weightedErrorTuple
  rw [Finset.prod_mul_distrib,error_product_image S hS η u I P hP hPS hT]
  ring


theorem weightedErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (P : Fin K → HeckeInverseAmplification.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (hη : ∀Q∈I.image P,IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈I.image P,(4:ℝ)≤ Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0< Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      weightedErrorTuple S hS η u I P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    (I.image P) hT hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)
  apply hi.congr
  filter_upwards with t
  rw [weightedErrorTuple_packet S hS η u I P hP hPS hT]
  ring

theorem partialErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    partialErrorTuple S hS η u I T hT P W Yp x w z=
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x w z) := by
  have hp : (∏i:I,rawErrorSlot η u (P i).val
      (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z)=
      ∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z := by
    let e : I ≃ Finset.univ.image (fun i:I=>(P i).val) :=
      Equiv.ofBijective (fun i=>⟨(P i).val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
        ⟨by intro i j hij;exact hP (congrArg Subtype.val hij),by
          intro Q
          obtain ⟨i,hi,hieq⟩ := Finset.mem_image.mp Q.property
          exact ⟨i,Subtype.ext hieq⟩⟩
    exact Fintype.prod_equiv e _ _ (fun _=> rfl)
  unfold partialErrorTuple
  rw [Finset.prod_mul_distrib,hp]
  ring

theorem partialErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (hη : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),(4:ℝ)≤ Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0< Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    _ hTS hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)
  apply hi.congr
  filter_upwards with t
  rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  ring

theorem partialErrorTuple_mellin {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z)=
    (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:I=>(P i).val)) hTS x z W1 Y := by
  simp_rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  unfold errorNumeratorIntegral
  rw [show (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z)))=
      (fun t : ℝ=>(∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
        ((Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z))) by funext t;ring]
  rw [integral_const_mul]
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorIntegrable -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelPrimeBound ; sha256 9822a4b9282a8b937f084cd5a33d299edeadb3c9f8c215f88e9ece567be546ad -/
section



/-! All physical error labels have the same Y^(-4/25) factor as a main prime
slot. Constants are uniform over subsets of a fixed finite slot family. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem error_label_prime_product_bound (epsilon c d B : ℝ) (K : ℕ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ K → ∀ (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
      (Y : ι → ℝ) (W : ι → ℝ → ℂ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∏ i, ∑ P : T i, 2880 *
        ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
          errorSize u P.val) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  let eta : ℝ := epsilon / (K+1)
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  obtain ⟨C0,hC0,hslot⟩ := error_coefficient_slot_sum eta c d B heta hc hd hB
  let C1 : ℝ := max 1 (2880*C0)
  have hC1 : 1 ≤ C1 := le_max_left _ _
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C1^K,pow_pos hC1pos _,?_⟩
  intro ι _ _ hcard u T Y W hY hWS hWB z hz
  let Nu : ℝ := (Ideal.span {u.val} : Ideal O).absNorm
  have hNu : 1 ≤ Nu := by
    have hn : (Ideal.span {u.val} : Ideal O).absNorm ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    dsimp only [Nu]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hNupos : 0 < Nu := lt_of_lt_of_le zero_lt_one hNu
  have hEach (i : ι) :
      (∑ P : T i, 2880 * ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
        (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) ≤
      C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (hslot u (T i) (Y i) (hY i) (W i) (hWS i) (hWB i) z hz)
      (show (0 : ℝ) ≤ 2880 by norm_num)
    calc
      _ = 2880 * (∑ P : T i, ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
          (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro P hP; ring
      _ ≤ 2880 * (C0 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := hh
      _ ≤ _ := by
        calc
          _ = (2880*C0) * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by ring
          _ ≤ C1 * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (Real.rpow_nonneg hNupos.le _) (Real.rpow_nonneg ((zero_le_one.trans (hY i))) _))
          _ = _ := by ring
  calc
    _ ≤ ∏ i, (C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun P _ => mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
          (errorSize_nonneg u P.val))
      · intro i hi
        exact hEach i
    _ = C1^(Fintype.card ι) * Nu^(eta*(Fintype.card ι : ℝ)) *
        ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow]
      rw [show (Nu^eta)^(Fintype.card ι) = Nu^(eta*(Fintype.card ι : ℝ)) by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNupos.le]]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (zero_le_one.trans (hY i)) _))
      apply mul_le_mul (pow_le_pow_right₀ hC1 hcard) _ (Real.rpow_nonneg hNupos.le _) (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hNu
      dsimp only [eta]
      have hcardR : (Fintype.card ι : ℝ) ≤ K := by exact_mod_cast hcard
      have hden : (0 : ℝ) < K+1 := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelPrimeBound -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowNominalGeometry ; sha256 bb8f2c1d74a809188aa7144cb20f75e07d503507dbfbba341b96119596972108 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNominalGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i∈J,ell i

def lowSelectedLength {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) : ℝ := ∑i : SelectedSlot J,ell i.val

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (J : Finset (Fin K)) :
    0≤ lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤ Submission20261012.Global.ell ∧
    0≤ lowSelectedLength ell J ∧ lowSelectedLength ell J≤ Submission20261012.Global.ell-lowUnselectedLength ell J := by
  have hu : 0≤ lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=> hell i)
  have hs : 0≤ lowSelectedLength ell J := Finset.sum_nonneg (fun i _=> hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowUnselectedProduct_norm_lower {K : ℕ} (ell : Fin K→ℝ)
    (a Z : ℝ) (ha : 0< a) (hZ : 0< Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→a*Z^(ell i)≤ elementNorm x)
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    (min 1 a)^K*Z^(lowUnselectedLength ell J)≤ elementNorm (∏i : J,(p i).val) := by
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤ a^J.card*Z^(lowUnselectedLength ell J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_of_le_one (le_of_lt (lt_min zero_lt_one ha)) (min_le_left _ _) hc).trans
        (pow_le_pow_left₀ (by positivity) (min_le_right _ _) _)
    _=∏i : J,a*Z^(ell i.val) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := Finset.prod_le_prod₀ (fun _ _=> by positivity) (fun i _=> hslots i.val _ (p i).property)

lemma originalPool_element_lower (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤ a) (hab : a≤ b) (hY : 0< Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : a*Y≤ elementNorm n := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  simpa only [mul_comm] using (pool_norm_bounds R S ha hab hY P hP).1.le

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0< Z) :
    lowPhysicalScale C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)=
      elementNorm C.generator*Z^((1-Submission20261012.Global.ell):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(Submission20261012.Global.lx:ℝ)*Z^(Submission20261012.Global.ly:ℝ)=Z^((1-Submission20261012.Global.ell):ℝ) := by rw [←Real.rpow_add hZ,Submission20261012.Global.length_sum]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0< Z) (hc : 0< c) (hL : c*Z^d≤ L) :
    lowPhysicalScale C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^((1-Submission20261012.Global.ell)-2*d:ℝ) := by
  have hl : 0< L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source C Z L hZ]
  calc
    _≤ elementNorm C.generator*Z^((1-Submission20261012.Global.ell):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ (1-Submission20261012.Global.ell) (2*d)]
      ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0< Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

lemma lowSelectedCaps_product {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (J : Finset (Fin K)) (Z b : ℝ) (hZ : 1≤ Z) :
    (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤
      (max 1 b)^K*Z^(lowSelectedLength ell J) := by
  have hc : Fintype.card (SelectedSlot J)≤ K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  calc
    _≤∏i : SelectedSlot J,max 1 b*Z^(ell i.val) := by
      apply Finset.prod_le_prod₀ (fun _ _=> le_trans zero_le_one (le_max_left _ _))
      intro i hi
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i.val))
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _=(max 1 b)^(Fintype.card (SelectedSlot J))*Z^(lowSelectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowNominalGeometry -/
