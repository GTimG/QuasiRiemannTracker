/- Copyright (c) 2026 Sil. Apache-2.0.
Full positive first energy: exact four-component allocation assembly.
The actual exceptional part added back is precisely the one subtracted
in nonexceptionalPart, with the SAME sourceNormCap and fourth-power scale.
-/
import Candidate.FourthPower.MixedFirstLiveEnergy
import Candidate.FourthPower.MixedFirstActualNonexceptional
import Candidate.FourthPower.MixedFirstAllocatedRemainders
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstWindowBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstFourParts
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondWindowBudget CenteredMomentFirstWindowBudgets
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalSecondZero MixedCommonCoefficient MixedCommonRestriction
open MixedFirstLiveSource MixedFirstLiveEnergy MixedFirstActualNonexceptional
open MixedFirstAllocatedRemainders MixedPoissonLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The original first residual energy at K4, with its exact outside 1/W. -/
def actualEnergy (s : Source ι a b) (ha : 0<a) (C G : Id) (hG : Supported G)
    (seed D : Id) (τ : Character) (t K W : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (CenteredMomentFirstPhysicalSource.element C G hG.1 (sourceColumns s))
    (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 (sourceColumns s))
    (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 (sourceColumns s)=>
      originalResidual s ha seed G D I*heightCoeff τ t I)
    ballProfile (16*K*W^4)).re/W

/-- No new exceptional estimate is assumed here. This is the literal
partEnergy summand corresponding to the nonexceptional difference. -/
def allocatedExceptional (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G D : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  allocationSum s G (fun B=>
    let live := allocatedLiveSource s hb cover G B
    ‖partEnergy true τ χ₀ Q m t (sourceColumns live) (sourceCoefficient live ha D)
      ballProfile (16*K*W^4) Tsec Z ξ (sourceNormCap live.P b live.T live.d)/(W:ℂ)‖)

/-- Match the quantitative exceptional ledger's real division by W. -/
theorem allocated_exceptional_norm_div (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G D : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (hW : 0≤W) (Q : Id) (m : O) (χ₀ : RayCharacter) :
    allocatedExceptional s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀=
      allocationSum s G (fun B=>
        let live := allocatedLiveSource s hb cover G B
        ‖partEnergy true τ χ₀ Q m t (sourceColumns live) (sourceCoefficient live ha D)
          ballProfile (16*K*W^4) Tsec Z ξ (sourceNormCap live.P b live.T live.d)‖/W) := by
  simp only [allocatedExceptional,norm_div,Complex.norm_real,Real.norm_of_nonneg hW]

/-- The four ACTUAL allocated components, all on the same live sources.
Indices are zero, nonexceptional, exceptional, discarded in that order. -/
def components (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G D : Id) (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) : Fin 4→ℝ :=
  ![allocatedZero s ha hb cover G D τ t K W,
    allocatedPart s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀,
    allocatedExceptional s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀,
    allocatedDiscarded s ha hb cover G D τ t K W Tsec Z ξ]

theorem components_sum (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G D : Id) (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) :
    (∑i,components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i)=
      allocatedZero s ha hb cover G D τ t K W+
      allocatedPart s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀+
      allocatedExceptional s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀+
      allocatedDiscarded s ha hb cover G D τ t K W Tsec Z ξ := by
  simp [components,Fin.sum_univ_succ] <;> ring

private theorem allocation_sum_nonneg (s : Source ι a b) (G : Id)
    (F : actualAllocations (tuplePools s) G→ℝ) (hF : ∀B,0≤F B) :
    0≤allocationSum s G F :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (hF B)))

theorem components_nonneg (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G D : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) (i : Fin 4) :
    0≤components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i := by
  have hz : 0≤allocatedZero s ha hb cover G D τ t K W :=
    allocation_sum_nonneg s G _ (fun _=>norm_nonneg _)
  have hn : 0≤allocatedPart s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ :=
    mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  have he : 0≤allocatedExceptional s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ :=
    allocation_sum_nonneg s G _ (fun _=>norm_nonneg _)
  have ht : 0≤allocatedDiscarded s ha hb cover G D τ t K W Tsec Z ξ :=
    allocation_sum_nonneg s G _ (fun _=>norm_nonneg _)
  fin_cases i
  · exact hz
  · exact hn
  · exact he
  · exact ht

/-- Positive Cauchy is applied to the WHOLE first energy. Only then is
each live source split. Division by W is distributed exactly through
the actual finite allocation sum; no Fourier component is compared to
an unallocated residual. This theorem has no analytical bound premise. -/
theorem actual_energy_four_parts (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (C G seed D : Id)
    (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C=
      QRH.Record1252270103KernelMass.primeSupport G) (hseed : seed∣G)
    (τ : Character) (t K W Tsec Z ξ : ℝ) (hK : 0<K) (hW : 0<W)
    (Q : Id) (m : O) (χ₀ : RayCharacter) :
    actualEnergy s ha C G hG seed D τ t K W≤
      ∑i,components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i := by
  have he := actual_common_energy s ha hb cover C G seed D hC hG hCG hseed
    τ t ballProfile (16*K*W^4) (by positivity) (fun _=>ballProfile_nonneg _)
  have hdiv : actualEnergy s ha C G hG seed D τ t K W≤
      allocationSum s G (fun B=>
        let live := allocatedLiveSource s hb cover G B
        (sourceGaussEnergy (sourceColumns live) (sourceCoefficient live ha D)
          (heightCoeff τ t) ballProfile (16*K*W^4)).re/W) := by
    simpa only [actualEnergy,allocationSum,Finset.sum_div,mul_div_assoc] using
      div_le_div_of_nonneg_right he hW.le
  apply hdiv.trans
  rw [components_sum]
  dsimp only [allocatedZero,allocatedPart,allocatedExceptional,allocatedDiscarded,
    allocationSum,nonexceptionalPart]
  simp only [←Finset.sum_add_distrib,←mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let live := allocatedLiveSource s hb cover G B
  exact live_density_four_parts live ha D τ t K W (frequencyRadius Tsec Z ξ) hK hW
    (partEnergy true τ χ₀ Q m t (sourceColumns live) (sourceCoefficient live ha D)
      ballProfile (16*K*W^4) Tsec Z ξ (sourceNormCap live.P b live.T live.d)/(W:ℂ))

private theorem window_budget_mono (J : ℕ) (t A B : ℝ) (h : A≤B) :
    windowBudget J t A≤windowBudget J t B :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

/-- The genuine two-side square-root/window expansion. There are all
sixteen component pairs, including zero/tail/exceptional cross terms.
The two sides are the actual C and D first residual presentations. -/
theorem actual_pair_sixteen_parts (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (C D seed L : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : QRH.Record1252270103KernelMass.primeSupport C=
      QRH.Record1252270103KernelMass.primeSupport D) (hseedC : seed∣C) (hseedD : seed∣D)
    (τ₁ τ₂ : Character) (t₁ t₂ K W Tsec Z ξ : ℝ) (hK : 0<K) (hW : 0<W)
    (Q : Id) (m : O) (χ₀ : RayCharacter) (J₁ J₂ : ℕ) (twindow : ℝ) :
    windowBudget J₁ twindow (actualEnergy s ha D C hC seed L τ₁ t₁ K W)*
      windowBudget J₂ twindow (actualEnergy s ha C D hD seed L τ₂ t₂ K W)≤
    ∑i : Fin 4,∑j : Fin 4,
      windowBudget J₁ twindow (components s ha hb cover C L τ₁ t₁ K W Tsec Z ξ Q m χ₀ i)*
      windowBudget J₂ twindow (components s ha hb cover D L τ₂ t₂ K W Tsec Z ξ Q m χ₀ j) := by
  have hleft := actual_energy_four_parts s ha hb cover D C seed L hD hC hCD.symm hseedC
    τ₁ t₁ K W Tsec Z ξ hK hW Q m χ₀
  have hright := actual_energy_four_parts s ha hb cover C D seed L hC hD hCD hseedD
    τ₂ t₂ K W Tsec Z ξ hK hW Q m χ₀
  have hw := mul_le_mul
    (window_budget_mono J₁ twindow _ _ hleft) (window_budget_mono J₂ twindow _ _ hright)
    (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  apply hw.trans
  exact windowBudget_pair_sum Finset.univ Finset.univ
    (components s ha hb cover C L τ₁ t₁ K W Tsec Z ξ Q m χ₀)
    (components s ha hb cover D L τ₂ t₂ K W Tsec Z ξ Q m χ₀)
    (fun i _=>components_nonneg s ha hb cover C L τ₁ t₁ K W Tsec Z ξ Q m χ₀ i)
    (fun j _=>components_nonneg s ha hb cover D L τ₂ t₂ K W Tsec Z ξ Q m χ₀ j)
    J₁ J₂ twindow

end
end Candidate.FourthPower.MixedFirstFourParts
