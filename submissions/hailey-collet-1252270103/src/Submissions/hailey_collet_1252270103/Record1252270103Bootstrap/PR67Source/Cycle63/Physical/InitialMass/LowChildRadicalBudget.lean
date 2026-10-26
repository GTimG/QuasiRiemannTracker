import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowLabelBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadicalHarmonicMass
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The reciprocal norms of the common radicals of the second labels of a LOW child sum to `Z^ε`, and a pointwise comparison
of the label weights with them bounds the weighted label sum. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentDivisorBoundary
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadicalHarmonicMass Cycle63Moment Cycle63FinalCapacity

/-- Equal-support labels divisible by a squarefree seed have reciprocal common-radical norm sum at most
`C Z^ε` over the seed norm. -/
theorem actual_low_radical_reciprocal_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ seed : Ideal O, Squarefree seed → seed ≠ 0 →
      ∀ labels : Finset FirstSourceLabel,
      (∀ l ∈ labels, Supported l.1.1 ∧ Supported l.1.2) →
      (∀ l ∈ labels, primeSupport l.1.1 = primeSupport l.1.2) →
      (∀ l ∈ labels, seed ∣ l.1.1 ∧ seed ∣ l.1.2) →
      (∀ l ∈ labels, (l.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (l.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∑ l ∈ labels, 1 / ((commonRadical l.1.1 l.1.2).absNorm : ℝ)) ≤ C * Z ^ ε / (seed.absNorm : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := common_radical_harmonic_mass B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ seed hs hs0 labels hsup heq hseed hnorm
  have hh := hbound Z hZ seed hs hs0 (labels.image firstPartitionCode) ?_ ?_
  · rw [Finset.sum_image] at hh
    · exact hh
    · exact first_partition_code_injective.injOn
  · intro v hv
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨(hsup l hl).1.1, (hsup l hl).2.1, heq l hl, (hseed l hl).1, (hseed l hl).2, ?_⟩
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    rw [commonRadical_support]
    exact Q.property
  · intro v hv
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
    exact hnorm l hl

/-- The reciprocal common-radical norm sum over a dyad of first-projector ideals is at most `C Z^ε`. -/
theorem actual_low_radical_projector_shell (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 2 ≤ Z → 1 ≤ T → ∀ Ds : Finset (Ideal O),
      (∀ D ∈ Ds, Squarefree D) →
      (∀ D ∈ Ds, T ≤ (D.absNorm : ℝ) ∧ (D.absNorm : ℝ) < 2 * T) →
      ∀ labels : Ideal O → Finset FirstSourceLabel,
      (∀ D ∈ Ds, ∀ l ∈ labels D, Supported l.1.1 ∧ Supported l.1.2) →
      (∀ D ∈ Ds, ∀ l ∈ labels D, primeSupport l.1.1 = primeSupport l.1.2) →
      (∀ D ∈ Ds, ∀ l ∈ labels D, D ∣ l.1.1 ∧ D ∣ l.1.2) →
      (∀ D ∈ Ds, ∀ l ∈ labels D, (l.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (l.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∑ D ∈ Ds, ∑ l ∈ labels D, 1 / ((commonRadical l.1.1 l.1.2).absNorm : ℝ)) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hbound⟩ := actual_low_radical_reciprocal_mass B ε hB hε
  refine ⟨256 * C, by positivity, ?_⟩
  intro Z T hZ hT Ds hDs hdyad labels hsup heq hseed hnorm
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hcard := divisor_dyad_card Ds T hT (fun D hD => (hDs D hD).ne_zero)
    (fun D hD => (hdyad D hD).2)
  calc
    _ ≤ ∑ _D ∈ Ds, C * Z ^ ε / T := by
      refine Finset.sum_le_sum fun D hD => ?_
      exact (hbound Z hZ D (hDs D hD) (hDs D hD).ne_zero (labels D)
        (hsup D hD) (heq D hD) (hseed D hD) (hnorm D hD)).trans
        (div_le_div_of_nonneg_left (by positivity) hT0 (hdyad D hD).1)
    _ = (Ds.card : ℝ) * (C * Z ^ ε / T) := by simp
    _ ≤ (256 * T) * (C * Z ^ ε / T) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (256 * C) * Z ^ ε := by field_simp

/-- Second-label contributions that are pointwise at most `Z^errbar` over the common-radical norm sum, over the first
labels and their projector dyads, to at most `K Z^(p + exponent + errbar + ε)` over the seed norm; the geometry
exponent of the first label and the exponent of the second label are arbitrary functions. -/
theorem actual_low_pointwise_label_budget (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (second : Bool) (Z T p exponent errbar : ℝ),
      2 ≤ Z → 1 ≤ T → p ≤ B → ∀ seed : Ideal O, Squarefree seed → seed ≠ 0 →
      ∀ labels : Finset FirstSourceLabel,
      (∀ l ∈ labels, Supported l.1.1 ∧ Supported l.1.2) →
      (∀ l ∈ labels, primeSupport l.1.1 = primeSupport l.1.2) →
      (∀ l ∈ labels, seed ∣ l.1.1 ∧ seed ∣ l.1.2) →
      (∀ l ∈ labels, (l.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (l.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ l ∈ labels, ((commonRadical l.1.1 l.1.2).absNorm : ℝ) ≤ Z ^ p) →
      ∀ (geom : FirstSourceLabel → ℝ) (err : FirstSourceLabel → FirstSourceLabel → ℝ),
      (∀ l ∈ labels, geom l ≤ exponent) →
      ∀ (Ds : FirstSourceLabel → Finset (Ideal O))
        (children : FirstSourceLabel → Ideal O → Finset FirstSourceLabel),
      (∀ l ∈ labels, ∀ D ∈ Ds l, Squarefree D) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, T ≤ (D.absNorm : ℝ) ∧ (D.absNorm : ℝ) < 2 * T) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, ∀ v ∈ children l D, Supported v.1.1 ∧ Supported v.1.2) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, ∀ v ∈ children l D, primeSupport v.1.1 = primeSupport v.1.2) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, ∀ v ∈ children l D, D ∣ v.1.1 ∧ D ∣ v.1.2) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, ∀ v ∈ children l D,
        (v.1.1.absNorm : ℝ) ≤ Z ^ B ∧ (v.1.2.absNorm : ℝ) ≤ Z ^ B) →
      (∀ l ∈ labels, ∀ D ∈ Ds l, ∀ v ∈ children l D,
        Z ^ (err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ) ≤
          Z ^ errbar / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) →
      (∑ l ∈ labels, ∑ D ∈ Ds l, ∑ v ∈ children l D,
        Z ^ (geom l + err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ)) ≤
          K * Z ^ (p + exponent + errbar + ε) / (seed.absNorm : ℝ) := by
  obtain ⟨Kf, hKf, hfirst⟩ := actual_first_low_label_count B (ε / 2) hB (half_pos hε)
  obtain ⟨Ks, hKs, hsecond⟩ := actual_low_radical_projector_shell B (ε / 2) hB (half_pos hε)
  refine ⟨Kf * Ks, mul_pos hKf hKs, ?_⟩
  intro second Z T p exponent errbar hZ hT hp seed hs hs0 labels hsup heq hseed hnorm hrad geom err hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ hpoint
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hc := hfirst Z hZ1 p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpoint' (l : FirstSourceLabel) (hl : l ∈ labels) :
      (∑ D ∈ Ds l, ∑ v ∈ children l D,
        Z ^ (geom l + err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ)) ≤
        Z ^ (exponent + errbar) * (Ks * Z ^ (ε / 2)) := by
    have hh := hsecond Z T hZ hT (Ds l) (hDs l hl) (hdyad l hl) (children l)
      (hsup₂ l hl) (heq₂ l hl) (hseed₂ l hl) (hnorm₂ l hl)
    have hterm (D : Ideal O) (hD : D ∈ Ds l) (v : FirstSourceLabel) (hv : v ∈ children l D) :
        Z ^ (geom l + err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ) ≤
          Z ^ (geom l + errbar) * (1 / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) := by
      rw [Real.rpow_add hZ0, Real.rpow_add hZ0, mul_div_assoc]
      calc Z ^ (geom l) * (Z ^ (err l v) / ((if second then v.1.2 else v.1.1).absNorm : ℝ))
          ≤ Z ^ (geom l) * (Z ^ errbar / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) :=
            mul_le_mul_of_nonneg_left (hpoint l hl D hD v hv) (Real.rpow_nonneg hZ0.le _)
        _ = Z ^ (geom l) * Z ^ errbar * (1 / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) := by ring
    calc
      _ ≤ ∑ D ∈ Ds l, ∑ v ∈ children l D,
          Z ^ (geom l + errbar) * (1 / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) :=
        Finset.sum_le_sum fun D hD => Finset.sum_le_sum fun v hv => hterm D hD v hv
      _ = Z ^ (geom l + errbar) *
          (∑ D ∈ Ds l, ∑ v ∈ children l D, 1 / ((commonRadical v.1.1 v.1.2).absNorm : ℝ)) := by
        simp only [Finset.mul_sum]
      _ ≤ Z ^ (exponent + errbar) * (Ks * Z ^ (ε / 2)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [hgeom l hl])) hh
        (by positivity) (by positivity)
  calc
    _ ≤ ∑ _l ∈ labels, Z ^ (exponent + errbar) * (Ks * Z ^ (ε / 2)) := Finset.sum_le_sum hpoint'
    _ = (labels.card : ℝ) * (Z ^ (exponent + errbar) * (Ks * Z ^ (ε / 2))) := by simp
    _ ≤ (Kf * Z ^ (p + ε / 2) / (seed.absNorm : ℝ)) * (Z ^ (exponent + errbar) * (Ks * Z ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      have hsplit : Z ^ ε = Z ^ (ε / 2) * Z ^ (ε / 2) := by
        rw [← Real.rpow_add hZ0, add_halves]
      simp only [Real.rpow_add hZ0]
      rw [hsplit]
      ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
