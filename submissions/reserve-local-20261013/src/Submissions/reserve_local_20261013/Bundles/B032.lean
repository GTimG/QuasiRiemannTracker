/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.reserve_local_20261013.Bundles.B010
import Submissions.reserve_local_20261013.Bundles.B027
import Submissions.reserve_local_20261013.Bundles.B029
import Submissions.reserve_local_20261013.Bundles.B030
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple

/- BEGIN ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionOriginal ; sha256 159662b4a87ee81535d96f7f642eb684fe29af866f6b57ce92920162e1bb8eb9 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionOriginal.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open Cycle25CenteredMomentEnergyOriginalHighReflectionDeleted CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_high_from_low
    (epsilonDelete:ℝ)(hepsilonDelete:0< epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0< C ∧ 0< D ∧ 0< Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi≤ s.width/16 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=> bslot) (fun _=> Bslot) (fun _=> hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_original_from_low (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t X₁ X₂ _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤ L:=by linarith [s.width_nonneg]
    have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionOriginal

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionOriginal -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceRobustOriginal ; sha256 4cbc36cf7b4b2161e9916a55dbc5857185c476c2323eecf3ce1878d3e0c8a41e -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceRobustOriginal.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open Cycle25CenteredMomentEnergyReferenceRobustDeletedEnergy CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_reference_from_low_robust
    (epsilonDelete:ℝ)(hepsilonDelete:0< epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hdefect:0≤ defect)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0< C ∧ 0< D ∧ 0< Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi+13*defect/8≤ s.width/16 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-defect≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=> bslot) (fun _=> Bslot) (fun _=> hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_energy_from_low_robust (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi defect saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hdefect hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤ L:=by linarith [s.width_nonneg]
    have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustOriginal

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceRobustOriginal -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorDeficit ; sha256 281f03a45cd9fe06a40a490c9582b573ca2e01ed40ea429716d8c180c66a083e -/
section



/-! The exact multiplicative conductor deficit of repeated physical error primes. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem repeated_prime_square_dvd (u : FreeRow) (P : HeckeInverseAmplification.PrimeIdeal) (hs : Supported P.val)
    (hj : 2 ≤ multiplicity (primaryGenerator P.val) u.val) :
    P.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hm : p ^ multiplicity p u.val ∣ u.val := ⟨unitPart u p hp, (unitPart_spec u p hp).1⟩
  have hdiv : p ^ 2 ∣ u.val := (pow_dvd_pow p hj).trans hm
  rw [←span_primaryGenerator_of_supported P.val hs,Ideal.span_singleton_pow]
  exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hdiv

def repeatedErrorPrimes (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) : Finset HeckeInverseAmplification.PrimeIdeal :=
  T.filter (fun P => P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val)

theorem repeated_deficit_product (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) :
    (∏ P : T, (repeatedDeficit u P.val : ℝ)) =
      ∏ P ∈ repeatedErrorPrimes u T, (P.val.absNorm : ℝ) := by
  calc
    _ = ∏ P ∈ T, (repeatedDeficit u P : ℝ) := Finset.prod_coe_sort T _
    _ = _ := by
      simp only [repeatedDeficit,repeatedErrorPrimes,Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro P hP
      split_ifs <;> rfl


theorem radical_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) :
    ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
        (Ideal.span {u.val} : Ideal O).absNorm := by
  let R := repeatedErrorPrimes u T
  have hdiv (P : R) : P.val.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
    have hm := Finset.mem_filter.mp P.property
    exact repeated_prime_square_dvd u P.val (hT P.val hm.1) hm.2.2
  have hh := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    (fun P : R => P.val.val) (fun P => P.val.property)
    (fun P Q h => Subtype.ext (Subtype.ext h)) (fun _ => 2)
    (fun _ => by norm_num) hdiv
  simp only [show (2 : ℕ) - 1 = 1 by norm_num,pow_one] at hh
  have hh' : ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : R, (P.val.val.absNorm : ℝ)) ≤ (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast hh
  rw [repeated_deficit_product]
  have he := Finset.prod_coe_sort R (fun P : HeckeInverseAmplification.PrimeIdeal => (P.val.absNorm : ℝ))
  rw [he] at hh'
  exact hh'

theorem conductor_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 ≤ C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    Cu * (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
      C * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hd := radical_repeated_deficit u T hT
  have hn : 0 ≤ ∏ P : T, (repeatedDeficit u P.val : ℝ) :=
    Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)
  exact (mul_le_mul_of_nonneg_right hCu hn).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hC)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorDeficit -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorPrimeSum ; sha256 1502c784706a8910e45abd7c199cc534de3693d21d61137b477f7b8a396126aa -/
section



/-! Summing actual positive error coefficient majorants over a physical prime slot. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem errorSize_nonneg (u : FreeRow) (P : ProbePhysical.PrimeIdeal) :
    0 ≤ errorSize u P := by
  unfold errorSize
  split_ifs <;> positivity

theorem error_coefficient_slot_sum (epsilon c d B : ℝ) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
      (Y : ℝ), 1 ≤ Y → ∀ (W : ℝ → ℂ), Function.support W ⊆ Set.Icc c d →
      (∀ y, ‖W y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∑ P : T, ‖W ((P.val.val.absNorm : ℝ) / Y) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
        errorSize u P.val) ≤ C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          Y^(-(4 / 25 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    epsilon c d (-(4 / 25 : ℝ)) 1 B 1 hepsilon hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro u T Y hY W hWS hWB z hz
  let f : T → Ideal O := fun P => P.val.val
  have hf : Function.Injective f := fun P Q h => Subtype.ext (Subtype.ext h)
  let E : T → ℂ := fun P => (errorSize u P.val : ℂ)
  let G : T → ℂ := fun P => ((f P).absNorm : ℂ)^(1 / 2 : ℂ) * E P
  have hnorm (P : T) : ‖G P‖ ≤ 1 *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 : ℝ) else 1) := by
    have hQ0 : (0 : ℝ) < (f P).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
    have hQ1 : (1 : ℝ) ≤ (f P).absNorm := by
      exact_mod_cast Nat.succ_le_of_lt (show 0 < (f P).absNorm from by exact_mod_cast hQ0)
    have hn : ‖((f P).absNorm : ℂ)^(1 / 2 : ℂ)‖ = ((f P).absNorm : ℝ)^(1 / 2 : ℝ) := by
      rw [show ((f P).absNorm : ℂ) = (((f P).absNorm : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
      norm_num
    dsimp only [G,E]
    rw [norm_mul,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (errorSize_nonneg u P.val)]
    change ((f P).absNorm : ℝ)^(1 / 2 : ℝ) *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 / 2 : ℝ)
       else ((f P).absNorm : ℝ)^(-(51 / 100 : ℝ))) ≤ _
    by_cases hdiv : f P ∣ Ideal.span {u.val}
    · rw [ite_eq_left hdiv,ite_eq_left hdiv,one_mul,←Real.rpow_add hQ0]
      norm_num
    · rw [ite_eq_right hdiv,ite_eq_right hdiv,one_mul,←Real.rpow_add hQ0]
      exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num :
        (1 / 2 : ℝ) + -(51 / 100 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero _)
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _ => P.val.property.ne_zero) W hWS hWB G (fun P _ => hnorm P)
    (z - 1 / 2) (by simp only [Complex.sub_re]; rw [hz]; norm_num)
  have heq (P : T) :
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^((z - 1 / 2) - 1) * G P =
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^(z - 1) * E P := by
    have hn : ((f P).absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _),←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simp only [heq,norm_mul,E,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (errorSize_nonneg u _)] at hb
  simpa only [f,norm_mul] using hb

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorPrimeSum -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorFinitePacket ; sha256 fe661178e1a23003c4983994a653f56f8bc6848f6974b02fe372753c0e71b6e8 -/
section


/-! Finite products of physical local coefficient polynomials. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def finiteCoefficient {ι : Type*} [Fintype ι] {n : ℕ} (c : ι → Fin n → ℂ)
    (j : ι → Fin n) : ℂ := ∏ i, c i (j i)

def finiteScale {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (j : ι → Fin n) : ℝ≥0 := ∏ i, Q i ^ (j i).val

theorem finiteScale_one_le {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (j : ι → Fin n) : 1 ≤ finiteScale Q j := by
  exact Finset.one_le_prod (fun i _ => one_le_pow₀ (hQ i))

theorem finite_packet_term {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (j : ι → Fin n) :
    (∏ i, c i (j i) * ((Q i : ℂ)^(-w))^(j i).val) =
      finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Finset.prod_mul_distrib]
  unfold finiteCoefficient finiteScale
  congr 1
  have hh := map_prod (positiveCpowHom (-w)) (fun i => Q i ^ (j i).val) Finset.univ
  simpa only [map_pow,positiveCpowHom,MonoidHom.coe_mk,OneHom.coe_mk] using hh.symm

theorem finite_packet_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) :
    (∏ i, ∑ j : Fin n, c i j * ((Q i : ℂ)^(-w))^j.val) =
      ∑ j : ι → Fin n, finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_packet_term Q c w j

theorem finite_packet_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (c : ι → Fin n → ℂ) (sigma : ℝ) :
    (∑ j : ι → Fin n, ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma)) =
      ∏ i, ∑ j : Fin n, ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖ := by
  have he (j : ι → Fin n) : ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma) =
      ∏ i, ‖c i (j i) * ((Q i : ℂ)^(-(sigma : ℂ)))^(j i).val‖ := by
    rw [←norm_prod,finite_packet_term,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by
        have hh := finiteScale_one_le Q hQ j
        exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simp only [Complex.neg_re,Complex.ofReal_re]
  simp_rw [he]
  exact (Fintype.prod_sum (fun i : ι => fun j : Fin n =>
    ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖)).symm

def errorCoefficientVector (η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (P : T) : Fin 4 → ℂ :=
  (actualErrorCoefficients η u P.val (hT P.val P.property) x z).vector

def errorTupleCoefficient (η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (j : T → Fin 4) : ℂ :=
  finiteCoefficient (errorCoefficientVector η u T hT x z) j

def errorTupleScale (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (j : T → Fin 4) : ℝ≥0 :=
  finiteScale (fun P : T => primeScale P.val) j

theorem error_product_expansion (η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    (∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x w z) =
      ∑ j : T → Fin 4, errorTupleCoefficient η u T hT x z j * (errorTupleScale T j : ℂ)^(-w) := by
  calc
    _ = ∏ P : T, ∑ j : Fin 4, errorCoefficientVector η u T hT x z P j *
        ((primeScale P.val : ℂ)^(-w))^j.val := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [errorCoefficientVector,cubic_vector_eval,actual_error_expansion η u P.val _
        (hη P.val P.property) x w z (hQ P.val P.property) hx hz]
      rfl
    _ = _ := finite_packet_expansion (fun P : T => primeScale P.val)
      (errorCoefficientVector η u T hT x z) w

theorem error_product_coefficient_mass (η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (∑ j : T → Fin 4, ‖errorTupleCoefficient η u T hT x z j‖ *
      (errorTupleScale T j : ℝ)^(-(1 / 2 - rho))) ≤
      ∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho := by
  have hmass := finite_packet_mass (fun P : T => primeScale P.val)
    (fun P => primeScale_one_le P.val) (errorCoefficientVector η u T hT x z) (1 / 2 - rho)
  apply le_trans (le_of_eq hmass)
  apply Finset.prod_le_prod₀
  · intro P hP
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P hP
    unfold errorCoefficientVector
    rw [cubic_vector_mass _ _ _ (by
      have hh := primeScale_one_le P.val
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simpa only [Complex.ofReal_re,primeScale,NNReal.coe_natCast] using
      actual_error_coefficient_mass η u P.val _ (hη P.val P.property)
        x z alpha eps rho (hQ P.val P.property) halpha halpha1 heps heps1 hx hz hrho hrho1 hline

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorFinitePacket -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorTupleRestoration ; sha256 51758d9c1c2fe0e5d07c8400505263b0b180aba217f64cb17a6c194440f2c3dc -/
section



/-! Exact finite error expansion of the original numerator, without division
by a local correction factor or changing any selected-prime zero extension. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem quotient_free_finite_expansion {α : Type*} [DecidableEq α]
    (T : Finset α) (C : Finset α→ℂ) (G E H M : α→ℂ)
    (hrestore : ∀I⊆T,C I=C T*(∏i∈T\I,H i))
    (hlocal : ∀i∈T,G i=E i+H i*M i) :
    C T*(∏i∈T,G i)=∑I∈T.powerset,C I*(∏i∈I,E i)*(∏i∈T\I,M i) := by
  rw [Finset.prod_congr rfl hlocal,Finset.prod_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrestore I (Finset.mem_powerset.mp hI),Finset.prod_mul_distrib]
  ring

lemma markExclusions_mark (S : Finset (Ideal O)) (I J : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    markExclusions (markExclusions S I) J=markExclusions S (I∪J) := by
  simp only [markExclusions,Finset.image_union,Finset.union_assoc]

theorem continuedCorrection_restore_indexed {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) (I : Finset (Fin K)) :
    continuedCorrection (markExclusions S (I.image P)) (markedSourceExclusions S hS (I.image P)) η u x w z=
      continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i∈Finset.univ\I,supportedCorrection η u (P i) x w z := by
  have hj : ∀Q∈(Finset.univ\I).image P,Q.val∉markExclusions S (I.image P) := by
    intro Q hQ
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hQ
    rw [mem_markExclusions]
    rintro (hs|hi)
    · exact hPS j hs
    · obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_sdiff.mp hj).2 (hP hkj ▸ hk)
  have heq : markExclusions (markExclusions S (I.image P)) ((Finset.univ\I).image P)=
      markExclusions S (Finset.univ.image P) := by
    rw [markExclusions_mark,←Finset.image_union,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have hh := continuedCorrection_restore eps (markExclusions S (I.image P))
    (markedSourceExclusions S hS (I.image P)) (marked_firstTail eps S htail (I.image P))
    ((Finset.univ\I).image P) hj η u x w z hx hz hw hxw
  simpa only [heq,Finset.prod_image hP.injOn] using hh

def rawPhysicalSlot (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))

theorem rawPhysicalSlot_split (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    rawPhysicalSlot η u P hs x w z = rawErrorSlot η u P hs x w z +
      supportedCorrection η u P x w z*(-star (idealRowHom u.val P.val)) := by
  unfold rawPhysicalSlot rawErrorSlot
  ring

theorem actual_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
      (∏i,rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∑I∈Finset.univ.powerset,
        continuedCorrection (markExclusions S (I.image P))
          (markedSourceExclusions S hS (I.image P)) η u x w z*
        (∏i∈I,rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)*
        (∏i∈Finset.univ\I,(-star (idealRowHom u.val (P i).val))) := by
  apply quotient_free_finite_expansion Finset.univ
    (fun I=> continuedCorrection (markExclusions S (I.image P))
      (markedSourceExclusions S hS (I.image P)) η u x w z)
    (fun i=> rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=> rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=> supportedCorrection η u (P i) x w z)
    (fun i=>-star (idealRowHom u.val (P i).val))
  · intro I hI
    exact continuedCorrection_restore_indexed eps S hS htail P hP hPS η u x w z hx hz hw hxw I
  · intro i hi
    exact rawPhysicalSlot_split η u (P i) _ x w z

def physicalSlotWeight (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)

def weightedErrorTuple {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (I.image P))
    (markedSourceExclusions S hS (I.image P)) η u x w z*
    ∏i∈I,physicalSlotWeight (P i) (W i) (Y i) z*
      rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z

def physicalMainTuple {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) : ℂ :=
  ∏i∈Finset.univ\I,physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val))

def numeratorFreeRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x

theorem actual_weighted_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
      (∏i,physicalSlotWeight (P i) (W i) (Y i) z*
        rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I P hPS W Y x w z*
        physicalMainTuple u I P W Y z := by
  apply quotient_free_finite_expansion Finset.univ
    (fun I=> continuedCorrection (markExclusions S (I.image P))
      (markedSourceExclusions S hS (I.image P)) η u x w z)
    (fun i=> physicalSlotWeight (P i) (W i) (Y i) z*
      rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=> physicalSlotWeight (P i) (W i) (Y i) z*
      rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=> supportedCorrection η u (P i) x w z)
    (fun i=> physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val)))
  · intro I hI
    exact continuedCorrection_restore_indexed eps S hS htail P hP hPS η u x w z hx hz hw hxw I
  · intro i hi
    rw [rawPhysicalSlot_split]
    ring

/-- Exact expansion of the actual calibrated tuple: the reciprocal and
principal factor are independent of w; all selected-prime factors are retained. -/
theorem calibratedTupleValue_error_subsets {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      numeratorFreeRowScalar S hS hmax η u x z*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      (∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I P hPS W Y x w z*
        physicalMainTuple u I P W Y z) := by
  rw [←actual_weighted_quotient_free_expansion eps S hS htail P hP hPS η u W Y x w z hx hz hw hxw,
    calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold numeratorFreeRowScalar physicalSlotWeight rawPhysicalSlot
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorTupleRestoration -/
