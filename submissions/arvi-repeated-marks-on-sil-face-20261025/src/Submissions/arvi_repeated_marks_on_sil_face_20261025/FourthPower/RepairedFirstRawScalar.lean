/- Copyright (c) 2026 Sil. Apache-2.0.
Exact selected-unit dictionary and paired first-reference arithmetic.
Both common allowances and the original u denominator remain until
the proved physical prefactor cancels them. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedFirstRawWindows
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstPhysicalBudget
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstCommonSum
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RestoredFirstRemainders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedFirstRawScalar
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentFirstRetainedActive CenteredMomentFirstSectorLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication
open MixedFirstExceptionalNormalization MixedFirstReferencePair MixedFirstPhysicalBudget MixedFirstCommonSum
open RestoredFirstRemainders RepairedFirstRawSides
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem retained_selected_one (s : Source ι a b) (ha : 0 < a) (η : Character)
    (m A : O) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedEnergy η m A t (sourceColumns s) (selectedCoefficient s ha 1 1) Φ K X Z ξ=
      retainedEnergy η m A t (sourceColumns s) (sourceCoefficient s ha 1) Φ K X Z ξ := by
  rw [retained_energy_sum,retained_energy_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [selected_one_on_supported s ha 1 I (Finset.mem_filter.mp hI).2,
    selected_one_on_supported s ha 1 J (Finset.mem_filter.mp hJ).2]

theorem block_selected_one (s : Source ι a b) (ha : 0 < a) (η : Character) (m A : O) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (sourceColumns s) (selectedCoefficient s ha 1 1) C D hC hD E rows Φ V K K₀ H₀ A₀ B₀=
      block η m A t (sourceColumns s) (sourceCoefficient s ha 1) C D hC hD E rows Φ V K K₀ H₀ A₀ B₀ := by
  have hl (I : columns C C hC.1 (sourceColumns s)) :
      coefficient η m A t (selectedCoefficient s ha 1 1) C I=
        coefficient η m A t (sourceCoefficient s ha 1) C I := by
    have hI : Supported I.val := by simpa only [element_span] using element_supported C C hC.1 (sourceColumns s) I
    unfold coefficient
    rw [selected_one_on_supported s ha 1 (C*I.val) ((supported_mul_iff _ _).mpr ⟨hC,hI⟩)]
  have hr (I : columns C D hD.1 (sourceColumns s)) :
      coefficient η m A t (selectedCoefficient s ha 1 1) D I=
        coefficient η m A t (sourceCoefficient s ha 1) D I := by
    have hI : Supported I.val := by simpa only [element_span] using element_supported C D hD.1 (sourceColumns s) I
    unfold coefficient
    rw [selected_one_on_supported s ha 1 (D*I.val) ((supported_mul_iff _ _).mpr ⟨hD,hI⟩)]
  simp only [block,hl,hr]

theorem unit_prefactor (s : Source ι a b) (hunit : s.d=(1,1)) (η : Character)
    (C D : Id) (E : Finset (CommonIndex C D)) (K : ℝ) :
    referencePrefactor s η C D E K (Real.log 4)=
      (4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*commonWeight C D E := by
  rw [common_weight_physical]
  simp only [referencePrefactor,hunit,pairNorm,mul_one,map_one,Nat.cast_one,div_one,
    Real.exp_log (by norm_num : (0:ℝ) < 4)]
  ring

/-- The paired reference theorem is used on the ACTUAL first block.
Its two allowances are not removed separately. Nu^-1 occurs on both
sides and remains Nu^-1 after the square root. -/
theorem window_pair_reference (s : Source ι a b) (ha : 0 < a)
    (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (E : Finset (CommonIndex C D))
    (χ ξ : RayCharacter) (rows : Finset O) (Φ : 𝓢(ℝ,ℂ))
    (K K₀ H₀ A₀ B₀ Z A loss : ℝ) (hK : 0 < K) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀)
    (hZ : 1 < Z) (hA : 0 ≤ A) (u : Id) (J : ℕ)
    (hne : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s) (sourceCoefficient s ha 1)
      C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀≠0) :
    let F := fixedPair η C D hC E χ (ξ⁻¹)
    (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      (windowBudget J t (sideBudget s F.left C D u A Z loss)*
        windowBudget J t (sideBudget s F.right D C u A Z loss)) ≤
      referencePrefactor s η C D E K (Real.log 4)*(windowMass J t)^2*
        (A*Z^loss/(u.absNorm:ℝ)) := by
  intro F
  let cost := A*Z^loss/(u.absNorm:ℝ)
  have hc : 0 ≤ cost := div_nonneg (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (Nat.cast_nonneg _)
  have hwin : ∀i y,(fun _ : Fin 4 => logAnnulus) i y≠0 → |y| ≤ Real.log 4 := by
    intro i y hy
    have hh := logAnnulus_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩
  have hp := actual_source_reference_pair s ha 1 η (fixedBadMask*idealGenerator s.R) 1 t
    C D hC hD hCD E χ (ξ⁻¹) F rows Φ (fun _ => logAnnulus)
    K K₀ H₀ A₀ B₀ (Real.log 4) Z cost cost hK hA₀ hB₀ hZ hc hc hwin hne
  have hl : 0 ≤ sideBudget s F.left C D u A Z loss := sideBudget_nonneg _ _ _ _ _ _ _ _ hA (zero_lt_one.trans hZ).le
  have hprod : windowBudget J t (sideBudget s F.left C D u A Z loss)*
      windowBudget J t (sideBudget s F.right D C u A Z loss)=
      Real.sqrt (sideBudget s F.left C D u A Z loss*sideBudget s F.right D C u A Z loss)*
        (windowMass J t)^2 := by
    rw [Real.sqrt_mul hl]
    unfold windowBudget windowMass
    ring
  rw [hprod]
  have hroot : Real.sqrt (cost*cost)=cost := by
    rw [←pow_two,Real.sqrt_sq_eq_abs,abs_of_nonneg hc]
  rw [hroot] at hp
  change (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      Real.sqrt ((reference F.left C D (sourceVolume s) Z*cost)*
        (reference F.right D C (sourceVolume s) Z*cost)) ≤
      referencePrefactor s η C D E K (Real.log 4)*cost at hp
  have hleft : sideBudget s F.left C D u A Z loss=reference F.left C D (sourceVolume s) Z*cost := by
    unfold sideBudget
    dsimp only [cost]
    ring
  have hright : sideBudget s F.right D C u A Z loss=reference F.right D C (sourceVolume s) Z*cost := by
    unfold sideBudget
    dsimp only [cost]
    ring
  rw [hleft,hright]
  convert mul_le_mul_of_nonneg_right hp (sq_nonneg (windowMass J t)) using 1 <;>
    dsimp only [cost] <;> ring

end
end Candidate.FourthPower.RepairedFirstRawScalar

