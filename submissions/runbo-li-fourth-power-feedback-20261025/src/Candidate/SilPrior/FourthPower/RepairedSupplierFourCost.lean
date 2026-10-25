/- Copyright (c) 2026 Sil. Apache-2.0.
Finite integration mechanism for the four ACTUAL original-scale grouped
components. Component bounds are explicit inputs to this mechanism;
their analytic suppliers live in separate modules. No extra Cauchy is
performed on either branch.
-/
import Candidate.SilPrior.FourthPower.RepairedComponentRawCost
import Candidate.SilPrior.FourthPower.RepairedSupplierSplit

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedSupplierFourCost
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstColumns CenteredMomentFirstAmplificationChoice
open CenteredMomentHeckeColumnWindow CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open MixedPrincipalPair MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency
open OuterFreshRows OuterFreshConsumer OuterFreshSource OuterFreshSelected
open RepairedGroupedConsumer RepairedRawSupplier RepairedComponentRawCost RepairedSupplierSplit
open OuterFreshWindowPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem finite_supplier_of_four (q : Data ι) (hP : ∀ i,0 < q.P i)
    (x : activeFrozen q) (s : Source (RestIndex q) a b) (ha : 0 < a)
    (hm : Matches q x.val s ha) (τ : Character) (χ₀ : RayCharacter) (Q : Id)
    (t K T Z ζ H : ℝ) (rows : Finset O) (hK : 0 < K)
    (hH : ∀ I ∈ fixedPool q x.val s (residualSeed q x),(I.absNorm:ℝ) ≤ H)
    (A₀ Aₙ Aₑ Aₜ : ℝ) (hA₀ : 0 ≤ A₀) (hAₙ : 0 ≤ Aₙ) (hAₑ : 0 ≤ Aₑ) (hAₜ : 0 ≤ Aₜ)
    (hzero : ∀ ξ : RayCharacter,supplierFront q x.val*
      ‖selectedSum q x.val τ (fun y => outerZero q x.val y s (residualSeed q x) τ ξ t K)‖ ≤
        A₀*rawSupplierCost q x.val (residualSeed q x))
    (hnonexceptional : ∀ ξ : RayCharacter,supplierFront q x.val*
      ‖selectedSum q x.val τ (fun y => fixedPart false q x.val y s (residualSeed q x)
        τ ξ χ₀ Q t ballProfile K T Z ζ H)‖ ≤ Aₙ*rawSupplierCost q x.val (residualSeed q x))
    (hexceptional : ∀ ξ : RayCharacter,supplierFront q x.val*
      ‖selectedSum q x.val τ (fun y => fixedPart true q x.val y s (residualSeed q x)
        τ ξ χ₀ Q t ballProfile K T Z ζ H)‖ ≤ Aₑ*rawSupplierCost q x.val (residualSeed q x))
    (htail : ∀ ξ : RayCharacter,supplierFront q x.val*
      ‖selectedSum q x.val τ (fun y => secondDiscardedEnergy τ t (sourceColumns s)
        (outerColumn q x.val y (residualSeed q x) ξ) ballProfile K T Z ζ)‖ ≤
          Aₜ*rawSupplierCost q x.val (residualSeed q x)) :
    (∑ k ∈ rows,(ballProfile (‖eisEmbedding k‖^2/K)).re*
      ‖MixedSupplierFourthRow.frozenWeight q x.val*originalFamily q x.val τ t k‖^2) ≤
      (256*(A₀+Aₙ+Aₑ+Aₜ))*rawSupplierCost q x.val (residualSeed q x) := by
  have hx := (Finset.mem_filter.mp x.property).2.1
  have hfw := (Finset.mem_filter.mp x.property).2.2
  obtain ⟨seed,hseed,hbound⟩ := uniform_supplier_grouped_four q x.val hx s ha hm
  have hseedEq := residualSeed_unique q x seed (hseed hfw)
  rw [hseedEq] at hbound
  have he := hbound τ t rows K T Z ζ H hK hH χ₀ Q
  let Cost := rawSupplierCost q x.val (residualSeed q x)
  have hcost : 0 ≤ Cost := rawSupplierCost_nonneg q hP x.val _
  let A := (A₀+Aₙ+Aₑ+Aₜ)*Cost
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hfour (ξ : RayCharacter) : supplierFront q x.val *
      groupedFourCost q x.val s (residualSeed q x) τ ξ χ₀ Q t K T Z ζ H ≤ A := by
    have hh := add_le_add (add_le_add (add_le_add (hzero ξ) (hnonexceptional ξ)) (hexceptional ξ)) (htail ξ)
    convert hh using 1 <;> dsimp only [A,Cost,groupedFourCost] <;> ring
  have hsum : (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
      (supplierFront q x.val*groupedFourCost q x.val s (residualSeed q x) τ ξ χ₀ Q t K T Z ζ H)) ≤ 256*A := by
    calc
      _ ≤ ∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*A :=
        Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ξ _ =>
          mul_le_mul_of_nonneg_left (hfour ξ) (norm_nonneg _)))
      _ = (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)*A := by
        simp only [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right firstPhaseTable_mass hA
  apply he.trans
  calc
    _ = ∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
        (supplierFront q x.val*groupedFourCost q x.val s (residualSeed q x) τ ξ χ₀ Q t K T Z ζ H) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      unfold supplierFront
      ring
    _ ≤ 256*A := hsum
    _ = _ := by dsimp only [A,Cost]; ring

end
end Candidate.SilPrior.FourthPower.RepairedSupplierFourCost
