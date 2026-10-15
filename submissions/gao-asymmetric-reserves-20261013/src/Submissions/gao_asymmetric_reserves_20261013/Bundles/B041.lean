/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B009
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B020
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B022
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B025
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B032
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B035
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B036
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins

/- BEGIN ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionSymmetric ; sha256 f252ea3b7002e09f2908a8b93e804f9ff82ce3bf07ee6447acf1a80a09200eab -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionSymmetric.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyOriginalHighReflectionPower
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

omit [DecidableEq α] in
lemma energy_swap (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₂ W₁ pool β P X₂ X₁ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      positiveSlotRow η m A z W₂ W₁ pool β P t X₂ X₁:=by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [hh]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1< Z)(hwidth:0< width)
    (hX₁:0< X₁)(hX₂:0< X₂)
    (hshort:width/4≤ min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤ X₁ ∧ Z^(width/4)≤ X₂ ∧
    Z^(width/4)≤ comparisonFirst Z width ∧
    Z^(width/4)≤ comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤ length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤ length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0< X)(h:width/4≤ length Z X):
      length Z X=Real.logb Z X ∧ width/4≤ Real.logb Z X:=by
    have he:=Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX
    have hp:0< Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionSymmetric -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceLiveBounded ; sha256 5315c421b95a718569ef44761a2046706a663ad6276d3d1cf125b45fec45fa02 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLiveBounded.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLiveBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=
    Cycle25CenteredMomentEnergyReferenceRobustBounded.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=Cycle25CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases Cycle25CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=Cycle25CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLiveBounded

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceLiveBounded -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceLivePower ; sha256 6ef6e07c9a95ee7ca5cced0576032a67bacada2fac2ae13bf34e0a755eebd44d -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLivePower.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLivePower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=
    Cycle25CenteredMomentEnergyReferenceRobustPower.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=Cycle25CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases Cycle25CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=Cycle25CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLivePower

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceLivePower -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorMassDamping ; sha256 6f40896e0fb14e7a4351d4f933b0b28c716b8de44ebc5803288e07f5a25b6835 -/
section



/-! Two-line absolute coefficient masses and actual conductor absorption. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

theorem coefficient_left_weight (A : ℂ) (N L rho : ℝ) (hN : 0 < N) (hL : 0 ≤ L) :
    ‖A‖ * N ^ (-(1 / 2 : ℝ)) * (L * N)^rho =
      L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.mul_rpow hL hN.le]
  calc
    _ = L^rho * ‖A‖ * (N^(-(1 / 2 : ℝ)) * N^rho) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN]
      rw [show -(1 / 2 : ℝ) + rho = -(1 / 2 - rho) by ring]
      ring

theorem coefficient_max_weight_bound (A : ℂ) (N L rho : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hrho : 0 ≤ rho) :
    ‖A‖ * N^(-(1 / 2 : ℝ)) * max 1 (L * N)^rho ≤
      ‖A‖ * N^(-(1 / 2 : ℝ)) + L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.rpow_max zero_le_one (mul_nonneg hL hN.le) hrho,Real.one_rpow]
  have ht : 0 ≤ (L * N)^rho := Real.rpow_nonneg (mul_nonneg hL hN.le) rho
  calc
    _ ≤ ‖A‖ * N^(-(1 / 2 : ℝ)) * (1 + (L * N)^rho) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le (by linarith) (by linarith)
    _ = _ := by rw [mul_add,mul_one,coefficient_left_weight A N L rho hN hL]

theorem mass_deficit_absorption (M B D L rho : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hmass : M ≤ B * D^rho) (hcap : L * D ≤ 1) :
    L^rho * M ≤ B := by
  calc
    _ ≤ L^rho * (B * D^rho) :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hL rho)
    _ = B * (L * D)^rho := by rw [Real.mul_rpow hL hD]; ring
    _ ≤ B * 1^rho := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hL hD) hcap hrho) hB
    _ = B := by rw [Real.one_rpow,mul_one]

theorem two_line_coefficient_mass {ι : Type*} (A : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 < N i) (L rho B : ℝ) (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hc : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ))))
    (hl : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 - rho))))
    (hcm : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ))) ≤ B)
    (hlm : L^rho * (∑' i, ‖A i‖ * (N i)^(-(1 / 2 - rho))) ≤ B) :
    Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ∧
    (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ 2 * B := by
  have hmajor := hc.add (hl.mul_left (L^rho))
  have hbound (i : ι) := coefficient_max_weight_bound (A i) (N i) L rho (hN i) hL hrho
  have hs : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) :=
    hmajor.of_nonneg_of_le (fun i => by have := hN i; positivity) hbound
  refine ⟨hs, ?_⟩
  have hm := hs.tsum_le_tsum hbound hmajor
  rw [hc.tsum_add (hl.mul_left _),tsum_mul_left] at hm
  linarith

theorem error_packet_damped_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ∧
    (∑' e : ErrorPacketIndex S u T, ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ≤
      2 * (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
        errorProductSize u T) := by
  obtain ⟨hl,hlm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
  obtain ⟨hc,hcm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps 0 hQ halpha halpha1 heps heps1 hx hz (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith)
  simp only [sub_zero,Real.rpow_zero,mul_one] at hc hcm
  have hB : 0 ≤ 579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
      errorProductSize u T := mul_nonneg (by positivity) (errorProductSize_nonneg u T)
  apply two_line_coefficient_mass _ _
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    L rho _ hL hrho hc hl hcm
  exact mass_deficit_absorption _ _ _ _ _ hB
    (le_trans zero_le_one (errorProductDeficit_one_le u T)) hL hrho hlm hcap

theorem actual_conductor_packet_cap (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 < C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    (Cu / (C * (Ideal.span {u.val} : Ideal O).absNorm)) * errorProductDeficit u T ≤ 1 := by
  have hN : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hh := conductor_repeated_deficit u T hT C Cu hC.le hCu
  rw [div_mul_eq_mul_div]
  exact (div_le_one (mul_pos hC hN)).mpr hh

/-- The coefficient-series prefactor costs arbitrarily little row norm,
uniformly in the finite exclusions and selected labels. -/
theorem coefficient_prefactor_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (u : FreeRow),
      2 * (579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound
    579 epsilon (by norm_num) hepsilon
  refine ⟨2 * C * Real.exp (1 / 2),by positivity,?_⟩
  intro S u
  have hc : (579 : ℝ)^(ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (Real.exp_pos (1 / 2)).le) (by norm_num : (0 : ℝ) ≤ 2)
  exact hh.trans_eq (by ring)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorMassDamping -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SourcePrimeBins ; sha256 2bc986ae8b79a8af656d4f2df1380ba181bcf1913224eb284d9fe69573eaab6a -/
section




/-! The original canonical prime-amplitude estimates, specialized to the new
source slots and the two external heights of the full-w representation. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
namespace OAI.SevenEighths.Cycle25NumeratorHighFinalAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical
open HeckeInverseAmplification ProbeMellinBoundary HeckePrimeAmplitudeBins

 theorem weighted_source_prime_bins {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      let g := amplitude (Z^(D.ell j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.ell j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.ell j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (Cycle25.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) D.rmin τ D.ε D.e D.κ D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.e_pos D.e_small
    D.kappa_pos D.cost_pos.le D.t_pos (by norm_num) D.phase_budget D.epsilon_gap
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : D.rmin ≤ D.ell j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.1
    nlinarith only [hh,hd',D.rmin_pos]
  have hrhi : D.ell j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.2
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.ell j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

end OAI.SevenEighths.Cycle25NumeratorHighFinalAssembly
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SourcePrimeBins -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SourceScalar ; sha256 bf51411f6a00bb2f291edc1a726834b3e1073a2a134b2c2b803780e682647ed1 -/
section



/-! The actual calibrated scalar and physical frequency at an enlarged moment
base. The .68t factor is retained explicitly when replacing the dyad's lower edge. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem source_frequency_scalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ∀Z d t U : ℝ,0 < Z → U=Z^d →
      Z^(d-2*t) ≤ rowNorm u → rowNorm u ≤ U →
      ‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*U^(2*eps)*
          U^(-(17/50:ℝ))*Z^((17/25)*t) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_arithmetic_bound e eps he he' heps S hS hmax
  refine ⟨C,hC,?_⟩
  intro η u ι _ ψ B a H i hB ha hatop hH hnext x z hx hz hxim Z d t U hZ hU hlo hhi
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hxim
  have hU0 : 0 < U := by rw [hU];exact Real.rpow_pos_of_pos hZ _
  have hNu0 : 0 < rowNorm u := (Real.rpow_pos_of_pos hZ _).trans_le hlo
  have hs := hbound η u ψ B a H i hB ha hatop hH hnext x z hx hz hxim
  have hs' : ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*U^(2*eps)*(3+H)^(2*eps) := by
    apply hs.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNu0.le hhi (by positivity)) (by positivity)) (by positivity)
  have hf : ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤
      U^(-(17/50:ℝ))*Z^((17/25)*t) := by
    apply (frequencyWeight_dyad_bound u z (Z^(d-2*t)) (17/50)
      (Real.rpow_pos_of_pos hZ _) (by norm_num) hz hlo).trans_eq
    rw [hU,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  rw [norm_mul]
  apply (mul_le_mul hf hs' (norm_nonneg _) (by positivity)).trans_eq
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SourceScalar -/
