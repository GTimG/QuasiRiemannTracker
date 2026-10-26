/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorRemainder

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CanonicalQuadraticSieve CenteredMomentPrimeElements RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Constants and thresholds are fixed before choosing the original live subset.
Each subset retains its actual cardinality in its source and Fourier cutoff. -/
theorem uniform_actual_affine_main_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, 3401/100000 ≤ beta ∧ beta ≤ 1/25 →
      Real.logb Z (volume s) ≤ Cycle63.Arithmetic.totalA beta →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
      geometryAffineMainSourceTotal s Ψ Z (Cycle63.Arithmetic.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (Cycle63.Arithmetic.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ := by
  have data (T : Finset α) := eventual_actual_affine_main_remainder (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone Ψ t reflected key
  apply (hz T hZ s p caps beta hb hcone Ψ t reflected key).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

/-- The extracted source and retained norm keep the same single prime average
while constants and thresholds are collected over original slot subsets. -/
theorem uniform_actual_affine_error_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, 3401/100000 ≤ beta ∧ beta ≤ 1/25 →
      Real.logb Z (volume s) ≤ Cycle63.Arithmetic.totalA beta →
    ∀ P : Finset (Ideal O), P.Nonempty →
      (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^(Cycle63.Arithmetic.amp beta)) →
      (∀ q : elementPool P, ∀ i I, I ∈ s.slots i → IsCoprime (Ideal.span {q.val}) I) →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
    ∀ υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1 : ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)) key →
          elementPool P → Fin 3 → RayCharacter → Character,
      (56/(P.card : ℝ)) * geometryAffineErrorSourceTotal s Ψ Z (Cycle63.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      (56/(P.card : ℝ)) * ‖geometryAffineErrorRetainedSum s Ψ Z (Cycle63.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  have data (T : Finset α) := eventual_actual_affine_error_remainder (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  apply (hz T hZ s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.uniform_actual_affine_main_remainder
#print axioms OAI.SevenEighths.Cycle63InitialMass.uniform_actual_affine_error_remainder
