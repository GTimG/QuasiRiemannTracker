import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorRemainder
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CanonicalQuadraticSieve CenteredMomentPrimeElements RayFourExpansion

variable [Cycle63.AffineLedger] in
/-- Constants and thresholds are fixed before choosing the original live subset, at a parent with puncture `R`, seed `seed` and
radial scale `Z^Mrow`. Each subset retains its actual cardinality in its source and Fourier cutoff. -/
theorem uniform_actual_affine_main_parent_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ (R seed : Ideal O) (Mrow : ℝ), Squarefree seed → 0 ≤ Mrow → Mrow ≤ 1 →
    ∀ beta : ℝ, Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA beta →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
      geometryAffineMainSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(Cycle63.AffineLedger.zeroSaving : ℝ) + (1 - Mrow)) / (seed.absNorm : ℝ) +
      ‖geometryMainRetainedSum reflected s R seed Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key Mrow (Real.logb Z (volume s))
        (fun q => normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q))‖ := by
  have data (T : Finset α) := eventual_actual_affine_main_parent_remainder (ι := T) Cs μ hCs hμ hcap
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
  intro hZ T s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone Ψ t reflected key
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hseedNorm : 0 < (seed.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  apply (hz T hZ s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone Ψ t reflected key).trans
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ hseedNorm.le
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact hside
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

/-- Constants and thresholds are fixed before choosing the original live subset. Each subset retains its actual cardinality in its
source and Fourier cutoff: the parent bound at the unit puncture and seed and the radial scale one. -/
theorem uniform_actual_affine_main_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA beta →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
      geometryAffineMainSourceTotal s 1 1 Ψ Z 1 (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨C, hC, hparent⟩ := uniform_actual_affine_main_parent_remainder (α := α) Cs μ hCs hμ hcap
  refine ⟨C, hC, ?_⟩
  filter_upwards [hparent] with Z hZpar
  intro hZ T s p caps beta hb hcone Ψ t reflected key
  refine (hZpar hZ T s p caps 1 1 1 squarefree_one zero_le_one le_rfl beta hb hcone Ψ t reflected key).trans_eq ?_
  rw [sub_self, add_zero, show ((1 : Ideal O).absNorm : ℝ) = 1 by simp, div_one]
  rfl

variable [Cycle63.AffineLedger] in
/-- The extracted source and retained norm keep the same single prime average while constants and thresholds are collected over
original slot subsets, at a parent with puncture `R`, seed `seed` and radial scale `Z^Mrow`. -/
theorem uniform_actual_affine_error_parent_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ (R seed : Ideal O) (Mrow : ℝ), Squarefree seed → 0 ≤ Mrow → Mrow ≤ 1 →
    ∀ beta : ℝ, Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA beta →
    ∀ P : Finset (Ideal O), P.Nonempty →
      (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^(Cycle63.AffineLedger.amp beta)) →
      (∀ q : elementPool P, ∀ i I, I ∈ s.slots i → IsCoprime (Ideal.span {q.val}) I) →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
    ∀ υ : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key →
          elementPool P → Fin 3 → RayCharacter → Character,
      (56/(P.card : ℝ)) * geometryAffineErrorSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(Cycle63.AffineLedger.zeroSaving : ℝ) + (1 - Mrow)) / (seed.absNorm : ℝ) +
      (56/(P.card : ℝ)) * ‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  have data (T : Finset α) := eventual_actual_affine_error_parent_remainder (ι := T) Cs μ hCs hμ hcap
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
  intro hZ T s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hseedNorm : 0 < (seed.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  apply (hz T hZ s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone P hne hp hbad hpcap hcop Ψ t
    reflected key υ).trans
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ hseedNorm.le
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact hside
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

/-- The extracted source and retained norm keep the same single prime average while constants and thresholds are collected over
original slot subsets: the parent bound at the unit puncture and seed and the radial scale one. -/
theorem uniform_actual_affine_error_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA beta →
    ∀ P : Finset (Ideal O), P.Nonempty →
      (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^(Cycle63.AffineLedger.amp beta)) →
      (∀ q : elementPool P, ∀ i I, I ∈ s.slots i → IsCoprime (Ideal.span {q.val}) I) →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
    ∀ υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1 : ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)) key →
          elementPool P → Fin 3 → RayCharacter → Character,
      (56/(P.card : ℝ)) * geometryAffineErrorSourceTotal s 1 1 Ψ Z 1 (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      (56/(P.card : ℝ)) * ‖geometryAffineErrorRetainedSum s 1 1 Ψ Z 1 (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  obtain ⟨C, hC, hparent⟩ := uniform_actual_affine_error_parent_remainder (α := α) Cs μ hCs hμ hcap
  refine ⟨C, hC, ?_⟩
  filter_upwards [hparent] with Z hZpar
  intro hZ T s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  refine (hZpar hZ T s p caps 1 1 1 squarefree_one zero_le_one le_rfl beta hb hcone P hne hp hbad hpcap hcop
    Ψ t reflected key υ).trans_eq ?_
  rw [sub_self, add_zero, show ((1 : Ideal O).absNorm : ℝ) = 1 by simp, div_one]
  rfl

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
