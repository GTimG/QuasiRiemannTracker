import OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl

namespace ZetaZeroFree.Analytic.Rows

noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open scoped Classical SchwartzMap ContDiff
open Set

/-- The source profiles have uniform seminorms even outside the transition ratio:
there they vanish. In particular no restriction on the chosen dyadic exponent is needed. -/
theorem inverse_source_seminorms (S : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ scaled reverse : Bool, ∀ n : ℕ, n ≤ 2 →
      ∀ U : ℝ, 0 < U → ∀ tstar r : ℝ, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (inverseSourceSchwartz scaled reverse n U tstar r σ t) ≤ C * (1 + ‖t‖) ^ J :=
  inverseSourceSchwartz_uniform S

/-- The unconditional reference moment controls both the detector test and its
scale derivative, with the profile and height orders chosen before the row data. -/
theorem inverse_raw_pair_uniform (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ A : ℕ, ∀ data : RowData, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Bool, ∀ n : ℕ, n ≤ 2 → ∀ U : ℝ, 0 < U →
      ∀ tstar r : ℝ, ∀ σ ∈ Icc (0 : ℝ) 1,
      ∀ height t : ℝ, 0 ≤ height → t ∈ Icc (-height) height →
      let W := twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (C * (1 + height) ^ A) ∧
      RawMoment data (scaleProfile W) c κ (C * (1 + height) ^ A) := by
  obtain ⟨J, hJ⟩ := DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1 / 18) (13 / 4) c κ (by norm_num) (by norm_num)
    (fun x hx => referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨A, C₀, hC₀, hfamily⟩ :=
    DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨A, ?_⟩
  intro data
  obtain ⟨C₁, hC₁, href⟩ := hJ data
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, ?_⟩
  intro reverse n hn U hU tstar r σ hσ height t hh ht
  exact hfamily data c κ C₁ hC₁.le href reverse n hn U hU tstar r σ hσ height t hh ht

/-- Bounded real powers and both logarithmic profiles have common seminorm
control. The real-part shift costs a constant, and the norm twist costs a power of height. -/
theorem plain_profile_control (S : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ reverse : Bool, ∀ j k : ℕ, j + k ≤ 2 →
      ∀ σ ∈ Icc (0 : ℝ) 1, ∀ height t : ℝ, 0 ≤ height → t ∈ Icc (-height) height →
      (CenteredMomentDetectorEnergyInitialState.detectorProfiles reverse j k σ t).control S ^ 2 ≤
        C * (1 + height) ^ J := by
  obtain ⟨J, C, hC, he⟩ := CenteredMomentDetectorPlainProfileControl.paired_control S
  refine ⟨J, C, hC, ?_⟩
  intro reverse j k hjk σ hσ height t hh ht
  apply (he reverse j k hjk σ hσ t).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  simpa only [Real.norm_eq_abs] using add_le_add le_rfl (abs_le.mpr ht)

end
end ZetaZeroFree.Analytic.Rows
