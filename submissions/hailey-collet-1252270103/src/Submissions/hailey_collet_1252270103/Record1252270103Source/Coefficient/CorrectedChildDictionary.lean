/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual allocated modified children retain their divisor seed and row selector
while the genuine second character family is transported to its fixed anchor. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedMarkedCompleted
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.CoupledAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open Record1252270103Second RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem canonical_family_rowWeight (η τ : Character) (χ : RayCharacter) (C : Ideal O) (A : O)
    (hτ : ∀I : Ideal O,Supported I→IsCoprime C I→∀t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (I : Ideal O) (hC : IsCoprime C I) (z : O) (t : ℝ) :
    rowWeight τ fixedBadMask 1 z t I=
      rowWeight (childCharacter η χ) fixedBadMask 1 (A*z) t I := by
  by_cases hI : Supported I
  · rw [rowWeight_split τ fixedBadMask 1 z t I,
      rowWeight_split (childCharacter η χ) fixedBadMask 1 (A*z) t I,
      ←heightCoeff_eq_fixed_rowWeight τ t I hI,
      ←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI,hτ I hI hC t,
      idealRowHom_argument_mul]
    simp only [heightCoeff,child_ideal_primary η χ I hI]
    ring
  · rw [rowWeight_zero_of_not_supported τ fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _) I hI,
      rowWeight_zero_of_not_supported (childCharacter η χ) fixedBadMask 1 (A*z) t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hI]

theorem modified_source_family_row (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R seed : Ideal O) (hCR : C∣R) (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀I : Ideal O,Supported I→IsCoprime C I→∀t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (z : O) (t : ℝ) :
    modifiedSourceRow s modifier R seed τ t z=
      modifiedSourceRow s modifier R seed (childCharacter η χ) t (A*z) := by
  unfold modifiedSourceRow
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v=0
  · simp only [hp,mul_zero,zero_mul]
  · have hc : IsCoprime (finiteTupleProduct v) R := by
      by_contra hn
      exact hp (by simp only [profileCoefficient,ite_eq_right hn,mul_zero,zero_mul])
    rw [canonical_family_rowWeight η τ χ C A hτ _
      (hc.symm.of_isCoprime_of_dvd_left hCR) z t]

/-- The original allocation identity and the original character-family
identity commute. The seed L is retained literally on both sides. -/
theorem marked_child_energy_family_rows (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D K C R L : Ideal O) (B : actualAllocations s.pools C)
    (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀I : Ideal O,Supported I→IsCoprime C I→∀t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    childDivisorEnergy s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) C R L B τ t keep Φ H=
      ∑'z : O,if keep z then
        ‖modifiedSourceRow (child s C R B τ t)
          (Collision.markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
            (D*C) (K*Collision.markedProduct B.val) (poolCorrection P))
          (R*C) L (childCharacter η χ) t (A*z)‖^2*
            (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0 := by
  have hB : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  have hm := funext (Collision.markedSourceModifier_common_allocation A₁ A₂ D K C (poolCorrection P) B.val hB)
  unfold childDivisorEnergy
  rw [hm,source_energy_eq_modified_rows]
  apply tsum_congr
  intro z
  split_ifs
  · rw [modified_source_family_row _ _ C (R*C) L (dvd_mul_left _ _) η τ χ A hτ z t]
  · rfl

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.canonical_family_rowWeight
#print axioms OAI.SevenEighths.Record1252270103Source.modified_source_family_row
#print axioms OAI.SevenEighths.Record1252270103Source.marked_child_energy_family_rows
