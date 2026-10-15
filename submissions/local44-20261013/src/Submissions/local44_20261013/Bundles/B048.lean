/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B004
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B010
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B041
import Submissions.local44_20261013.Bundles.B045
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighParameters ; sha256 6aef892106a45d31118b48121465d91cd38bd4b3e75bdb32b446f00ebf8735d0 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighParameters.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighParameters
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

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1< Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1< Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤ Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:7/10≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤ s.width:=by
  have hv:0< CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤ N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=> le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤ N)(hZ:1< Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0< s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=> le_rfl)
  have hconst:0≤ Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighParameters

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighParameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighSourceBounded ; sha256 e68ada5fde60e2f8f902463c27f2dcf3e815582f9318260a6d6922311874a71e -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighSourceBounded.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSourceBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceLiveBounded CenteredMomentEnergyOriginalSource
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

open Cycle25CenteredMomentEnergyPositiveHighSource

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
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
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
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
          (1+|t|+height)^J*Z^(s.width+e+ε):=hreference
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
end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighSourceBounded

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighSourceBounded -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorIntegral ; sha256 7dbe518afc46e6c6b48f757cbf95984be86a51f855546f3e2242af4e53ed896e -/
section


/-! The actual complete-w error numerator, bounded after reconstructing its
Dirichlet polynomial.  No pointwise bound on L along the central line is used. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def errorNumeratorIntegral (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
    (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
    HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
    ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
        η u x ((1 / 2 : ℂ) + t * I) z))

theorem actual_error_numerator_bound (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y M : ℝ) (hY : 0 < Y) (hM : 0 ≤ M)
    (hpoly : ∀ N : ℝ, 1 ≤ N → N ≤ b * Y →
      ‖HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W (Y / N) 0 0‖ ≤
        M * max 1 (L * N)^rho) :
    ‖errorNumeratorIntegral S hS η u T hT x z W Y‖ ≤
      Y^(-(1 / 2 : ℝ)) * (M * (2 *
        (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) * errorProductSize u T))) := by
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hmarginc : 1 + firsteps ≤ x.re + 1 / 2 := by linarith
  have he := actual_error_packet_mellin S hS firsteps hfirst η u hrow T hT hη x z hQ
    hx' hz.ge hmarginc W a b ha hsupp hW Y hY
  change ‖_‖ ≤ _
  rw [show errorNumeratorIntegral S hS η u T hT x z W Y = _ from he]
  obtain ⟨hmass,hmb⟩ := error_packet_damped_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho L hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hL hcap
  apply reconstructed_numerator_bound (rowCharacter S hS.prime u) W a b Y L rho M _
    hsupp hY hM (errorPacketCoefficient S hS η u T hT x z)
    (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) hmass hmb
  intro e hecut
  exact hpoly _ (by exact_mod_cast errorPacketScale_one_le S u T e) hecut

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorIntegral -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelPacket ; sha256 fbb573d9153e8f64563215d9cc6d68cee92e5f70a4ba5d0874cd7a194c9f19a9 -/
section



/-! The complete coefficient packet after summing all physical error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def labelPrimes (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) :
    Finset ProbePhysical.PrimeIdeal := Finset.univ.image (fun i => (P i).val)

theorem labelSupported (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
    (P : ∀ i, T i) : ∀ Q ∈ labelPrimes T P, Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad _ (hT i _ (P i).property)

def LabelPacketIndex (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) := Σ P : ∀ i, T i, ErrorPacketIndex S u (labelPrimes T P)

def errorPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset ProbePhysical.PrimeIdeal) : ErrorPacketIndex S u T :=
  ⟨(fun _ => 0), (fun _ => 0), ⟨∅, fun _ => 0⟩⟩

def labelPacketBase (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (P : ∀ i, T i) : LabelPacketIndex S u T :=
  ⟨P,errorPacketBase S u (labelPrimes T P)⟩

instance labelPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) : Countable (LabelPacketIndex S u T) := by
  unfold LabelPacketIndex
  infer_instance

def labelPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ i P, P ∈ T i → P.val ∉ S) (weight : ∀ i, T i → ℂ) (x z : ℂ)
    (e : LabelPacketIndex S u T) : ℂ :=
  (∏ i, weight i (e.1 i)) *
    errorPacketCoefficient S hS η u (labelPrimes T e.1) (labelSupported S hS T hT e.1) x z e.2

def labelPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (e : LabelPacketIndex S u T) : ℝ≥0 := errorPacketScale S u (labelPrimes T e.1) e.2

theorem labelPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (T : ι → Finset ProbePhysical.PrimeIdeal) (e : LabelPacketIndex S u T) :
    1 ≤ labelPacketScale S u T e := errorPacketScale_one_le S u (labelPrimes T e.1) e.2

/-- Uniform in every error-label tuple, row, finite exclusion set and height. -/
theorem actual_label_packet_mass (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (weight : ∀ i, T i → ℂ) (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        (C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon) *
          ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  obtain ⟨C,hC,hpref⟩ := coefficient_prefactor_subpower epsilon hepsilon
  refine ⟨C,hC,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
  have hL : 0 ≤ L := div_nonneg hCu0 (mul_nonneg hCcond.le (by positivity))
  let M := C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon
  have hpacket (P : ∀ i, T i) :
      Summable (fun e : ErrorPacketIndex S u (labelPrimes T P) =>
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ∧
      (∑' e : ErrorPacketIndex S u (labelPrimes T P),
        ‖errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z e‖ *
        (errorPacketScale S u (labelPrimes T P) e : ℝ)^(-(1 / 2 : ℝ)) *
        max 1 (L * (errorPacketScale S u (labelPrimes T P) e : ℝ))^rho) ≤
        M * errorProductSize u (labelPrimes T P) := by
    have hηP : ∀ Q ∈ labelPrimes T P, IsCoprime Q.val η.modulus := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hη i _ (P i).property
    have hQP : ∀ Q ∈ labelPrimes T P, (4 : ℝ) ≤ Q.val.absNorm := by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact_mod_cast hS.tail.norm_four _ (hT i _ (P i).property)
    have hc := actual_conductor_packet_cap u (labelPrimes T P) (labelSupported S hS T hT P)
      Ccond Cu hCcond hCu
    obtain ⟨hs,hm⟩ := error_packet_damped_mass S hS firsteps hfirst η u (labelPrimes T P)
      (labelSupported S hS T hT P) hηP x z alpha eps rho L hQP halpha halpha1 heps heps1 hx hz
      hrho hrho1 hline hleft hmargin hL hc
    refine ⟨hs,hm.trans ?_⟩
    have hp := mul_le_mul_of_nonneg_right (hpref (markExclusions S (labelPrimes T P)) u)
      (errorProductSize_nonneg u (labelPrimes T P))
    simpa only [mul_assoc,M] using hp
  have hh := finite_label_damped_mass
    (fun P => errorPacketCoefficient S hS η u (labelPrimes T P) (labelSupported S hS T hT P) x z)
    (fun P e => (errorPacketScale S u (labelPrimes T P) e : ℝ))
    (fun P e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u (labelPrimes T P) e))
    (fun P => ∏ i, weight i (P i)) (fun P => errorProductSize u (labelPrimes T P)) L rho M
    (fun P => (hpacket P).1) (fun P => (hpacket P).2)
  refine ⟨hh.1,?_⟩
  change _ ≤ M * _
  exact hh.2.trans_eq (congrArg (fun t : ℝ => M*t) (error_label_mass_factor u T hdis weight))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLabelPacket -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.PacketFourth ; sha256 fb7ec41648127fc6482420bfe3ca535930a94101f718545688911657e970370e -/
section




/-! Fourth-moment removal of row-dependent numerator coefficient packets. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25WeightedNumeratorReflection

theorem packet_fourth_selection {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho : ℝ) (Q : ι → ℂ) (M E : ℝ)
    (hM : 0 ≤ M)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖S i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e‖^4 * ‖Q i‖^2) ≤ M^4 * E := by
  let D (i : ι) (e : α i) : ℝ := max 1 (L i * N i e)^rho
  have hD (i : ι) (e : α i) : 0 < D i e :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) rho
  let w (i : ι) (e : α i) := A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * (D i e : ℂ)
  let f (i : ι) (e : α i) := (S i e / (D i e : ℂ)) * (Real.sqrt ‖Q i‖ : ℂ)
  have hnorm (i : ι) (e : α i) : ‖w i e‖ =
      ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L i * N i e)^rho := by
    dsimp only [w]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i e),
      show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num,
      Complex.norm_real,Real.norm_of_nonneg (hD i e).le]
  have hw : ∀ i, Summable (fun e => ‖w i e‖) := by
    intro i
    simpa only [hnorm] using hs i
  have hwm : ∀ i, (∑' e, ‖w i e‖) ≤ M := by
    intro i
    simpa only [hnorm] using hm i
  have hf : ∀ e : ∀ i, α i, (∑ i, ‖f i (e i)‖^4) ≤ E := by
    intro e
    simpa only [f,norm_mul_sqrt_fourth,D] using hselection e
  have hh := weighted_fourth_selection base w f M E hM hw hwm hf
  have he (i : ι) (e : α i) : w i e * f i e =
      (A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    dsimp only [w,f]
    have hd : (D i e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hD i e).ne'
    field_simp
  have hsum (i : ι) : (∑' e, w i e * f i e) =
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    simp_rw [he]
    exact tsum_mul_right
  simpa only [hsum,norm_mul_sqrt_fourth] using hh.2

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.PacketFourth -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowOriginalPools ; sha256 364968c063c7cbe65272280ff5b0c3822515bc971ebbff59717d48e88a2d3d3a -/
section




/-! Adapted from OpenAI/math family003, module Detector.LowOriginalPools at openai/math fd4aeeb2e
(the pruned source fork c388e88e6 no longer has it, so this file imports that module's own
imports). Changed physical geometry and explicit compensation bookkeeping.
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

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤ a) (hab : a≤ b) (hY : 0< Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤ Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b : ℝ) (ha : 0≤ a) (hab : a≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧
      let T := fun i=> canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤ Z^(Submission20261012.Global.ly:ℝ)/L ∧
      1≤(Z^(Submission20261012.Global.ly:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤ Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowOriginalPools -/
