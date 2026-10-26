/- Copyright (c) 2026 Sil. Apache-2.0.
Actual finite small supplier reaches its constructed sigma energy with
the ORIGINAL residual seed. Empty selection removes only a proved
cardinality factor, never an extra branchwise Cauchy count.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSmallEmptyGauss
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedRawSupplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallSupplier
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Candidate.FourthPower.MixedSupplierPositive
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstColumns CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentOriginalChildEnergy
open MixedPrincipalPair MixedPrincipalWindow MixedSupplierFourthRow MixedSupplierSource
open MixedSupplierOuterActive MixedSupplierOriginalFrequency
open OuterFreshWindowPair OuterFreshConsumer
open RepairedRawSupplier RepairedSmallCharacter RepairedSmallEmptyGauss
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem empty_supplier_sigma (q : Data ι) (hJ : q.J=∅)
    (x : activeFrozen q) (s : Source (RestIndex q) a b) (ha : 0<a)
    (hm : Matches q x.val s ha) (hf : Supported (frozenProduct q x.val)) (τ : Character) :
    ∃σ : RayCharacter → Character,
      (∀ξ,(σ ξ).modulus.absNorm≤τ.modulus.absNorm*
        (ReferenceCubicCharacter.conductorConstant*(frozenProduct q x.val).absNorm)*
          (Ideal.span {(12:O)}).absNorm) ∧
      (∀ξ,∀I : Id,Supported I → ∀t : ℝ,
        heightCoeff (σ ξ) t I=heightCoeff τ t I*
          (CanonicalRowCompletion.idealRowHom (primaryGenerator (frozenProduct q x.val)) I)^2*
          rayCharacter ξ (primaryGenerator I)) ∧
      ∀(t K : ℝ)(rows : Finset O),0<K →
      (∑k∈rows,(ballProfile (‖eisEmbedding k‖^2/K)).re*
        ‖MixedSupplierFourthRow.frozenWeight q x.val*originalFamily q x.val τ t k‖^2)≤
      ‖MixedSupplierFourthRow.frozenWeight q x.val‖^2*
        (256*∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
          (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha (residualSeed q x))
            (heightCoeff (σ ξ) t) ballProfile K).re) := by
  choose σ hmod hheight hind using fun ξ : RayCharacter =>
    exists_supplier_character τ (frozenProduct q x.val) hf ξ
  refine ⟨σ,hmod,hheight,?_⟩
  intro t K rows hK
  have hx := (Finset.mem_filter.mp x.property).2.1
  have hfw := (Finset.mem_filter.mp x.property).2.2
  obtain ⟨seed,hseed,hbound⟩ := uniform_supplier_energies q x.val hx s ha hm
  have hseedEq := residualSeed_unique q x seed (hseed hfw)
  rw [hseedEq] at hbound
  have he := hbound τ t rows ballProfile K hK (fun z=>ballProfile_nonneg _)
  let E (ξ : RayCharacter) :=
    (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha (residualSeed q x))
      (heightCoeff (σ ξ) t) ballProfile K).re
  have hE (ξ : RayCharacter) : 0≤E ξ :=
    source_gauss_nonneg _ _ _ ballProfile K hK (fun z=>ballProfile_nonneg _)
  have hs (ξ : RayCharacter) := empty_selected_energy_le q hJ x.val s ha hm
    (residualSeed q x) τ (σ ξ) ξ (hheight ξ) t ballProfile K hK
    (fun z=>ballProfile_nonneg _)
  have hsum :
      (∑y∈activeSelected q,∑χ : RayCharacter,∑ξ : RayCharacter,
        ‖pairCoeff firstPhaseTable χ ξ‖*selectedPositiveWeight q x.val y τ*
          (sourceGaussEnergy (sourceColumns s) (outerColumn q x.val y (residualSeed q x) ξ)
            (heightCoeff τ t) ballProfile K).re)≤
      ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ := by
    calc
      _=∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
          (∑y∈activeSelected q,selectedPositiveWeight q x.val y τ*
            (sourceGaussEnergy (sourceColumns s) (outerColumn q x.val y (residualSeed q x) ξ)
              (heightCoeff τ t) ballProfile K).re) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ξ hξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _≤_ := Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ξ _ =>
        mul_le_mul_of_nonneg_left (hs ξ) (norm_nonneg _)))
  have hR : 0≤∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ :=
    Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun ξ _ => mul_nonneg (norm_nonneg _) (hE ξ)))
  have hcard : ((activeSelected q).card:ℝ)≤1 := by exact_mod_cast empty_active_card q hJ
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _≤(256*((activeSelected q).card:ℝ))*
        (∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _≤(256*1)*(∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hR
    _=_ := by ring

/-- Finite ray summation, with the same constant preceding both rays. -/
theorem ray_energy_bound (E : RayCharacter → ℝ) (A : ℝ) (hA : 0≤A)
    (hE : ∀ξ,E ξ≤A) :
    (∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ)≤256*A := by
  calc
    _≤∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*A :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ξ _ =>
        mul_le_mul_of_nonneg_left (hE ξ) (norm_nonneg _)))
    _=(∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)*A := by
      simp only [Finset.sum_mul]
    _≤_ := mul_le_mul_of_nonneg_right firstPhaseTable_mass hA

end
end Candidate.FourthPower.RepairedSmallSupplier
