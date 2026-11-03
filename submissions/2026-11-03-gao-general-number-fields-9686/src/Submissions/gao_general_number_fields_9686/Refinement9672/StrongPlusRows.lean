/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Actual masked numerator transport for both successor row incidences.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
The primitive input is proved from the independently frozen original Hecke
endpoint; no successor endpoint is used to prove its own numerator estimate.
The row/mask identifications adapt the original AxiomMath PoissonRows proofs.
-/
module
public import Submissions.gao_general_number_fields_9686.Refinement9672.FrozenBaseline
public import Submissions.gao_general_number_fields_9686.Refinement9672.Inputs.NativePrimitiveLine12
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Convexity
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyConvexity
@[expose] public section

namespace Refinement9672
open _root_.DedekindZetaZeroFree
namespace DedekindZetaZeroFree.Quantitative.StrongPlusRows

noncomputable section
open _root_.DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

/-- The independently registered old theorem supplies the31/32 input,
without changing any definition in its proof closure. -/
private theorem baseline31 (_D : FixedData S η) :
    _root_.DedekindZetaZeroFree.Quantitative.BaselinePrimitive97.OldHeckeZeroFree31 F :=
  _root_.Refinement9672Baseline.hecke31 F

/-- Allowed-row plus continuation, including the actual finite Euler mask. -/
theorem allowed_line :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) →
        ∀ t : ℝ, ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A, hA, H⟩ :=
    _root_.DedekindZetaZeroFree.Quantitative.BaselinePrimitive97.primitive_line_12_scaled hF (baseline31 D)
  obtain ⟨Cc, hCc, hcb⟩ := ConvexBridge.conductor_bound' D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C1, hC1, H1⟩ := H (ε / 2) (by positivity) (2 * Cc) (by positivity)
  obtain ⟨Ce, hCe, HE⟩ := EulerDeletion.euler_product_bound_with_S D
    (3 / 25) (by norm_num) (ε / 2) (by positivity)
  refine ⟨Ce * 2 ^ (ε / 2) * C1, by positivity, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
  have hU0 : 0 < U := by linarith
  have hq1 : 1 ≤ D.q u := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).1
  let ν := (D.inducers u).plus
  obtain ⟨gp, hgp, hgpL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A ν hnp
  have hgpI : ∀ s : ℂ, 1 < s.re → gp s = Detector.idealLSeries F ν.character s := by
    intro s hs
    exact (hgpL s (by linarith)).trans (RowHeckeBridge.hecke_eq_idealLSeries _ _ _ s hs)
  have hcond : 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ (2 * Cc) * U :=
    ((hcb u hq1).1).trans (by nlinarith)
  have hp := H1 ν hnp U (by linarith) hcond gp hgp hgpI t
  let s : ℂ := ((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hs0 : 0 < s.re := by simp [s]; norm_num
  have hsline : (3 / 25 : ℝ) ≤ s.re := by simp [s]
  have heq : g s = Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
      (fun v => ν.character v.asIdeal) s * gp s := by
    rw [ConvexBridge.entire_eq_mask_mul D u hnp hg hgs s hs0, hgpL s hs0]
  have hm := (RowHeckeBridge.mask_norm_le D u ν (3 / 25) (by norm_num) s hsline).1
  have hmask := hm.trans ((HE u hq1).1)
  have hqpow : D.q u ^ (ε / 2) ≤ 2 ^ (ε / 2) * U ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num) hU0.le]
    exact Real.rpow_le_rpow hq0.le hUq2.le (by positivity)
  have hpowers : U ^ (ε / 2) * U ^ ((17 / 40 : ℝ) + ε / 2) = U ^ ((17 / 40 : ℝ) + ε) := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  change ‖g s‖ ≤ _
  rw [heq, norm_mul]
  calc _ ≤ (Ce * (2 ^ (ε / 2) * U ^ (ε / 2))) *
        (C1 * U ^ ((17 / 40 : ℝ) + ε / 2) * (2 + |t|) ^ A) :=
      mul_le_mul (hmask.trans (mul_le_mul_of_nonneg_left hqpow hCe.le)) hp
        (norm_nonneg _) (by positivity)
    _ = (Ce * 2 ^ (ε / 2) * C1) * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by
      rw [← hpowers]; ring

/-- All raw frequencies, including the omitted incidence, with their actual
masked native plus function; constants precede the row and the dyadic scale. -/
theorem raw_line :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : PrincipalMellinComparison.Frequency D.recipe,
        u ≠ PrincipalMellinComparison.principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ PrincipalMellinComparison.frequencyNorm D.recipe u →
          PrincipalMellinComparison.frequencyNorm D.recipe u < 2 * U →
        ∀ t : ℝ, ‖(RawFixed.FixedData.pkg D).plus u
          (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A, hA, H⟩ :=
    _root_.DedekindZetaZeroFree.Quantitative.BaselinePrimitive97.primitive_line_12_scaled hF (baseline31 D)
  obtain ⟨Cc, hCc, hcb⟩ := RawHeckeIdentification31.plus_conductor_bound D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C1, hC1, H1⟩ := H (ε / 2) (by positivity) (2 * Cc) (by positivity)
  obtain ⟨C2, hC2, H2⟩ := RawDeletionMask31.plus_mask_subpower D (3 / 25) (ε / 2)
    (by norm_num) (by positivity)
  refine ⟨C1 * C2 * 2 ^ (ε / 2), by positivity, fun u hu U hU2 hUq hUq2 t => ?_⟩
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < PrincipalMellinComparison.frequencyNorm D.recipe u := by linarith
  have hnp := ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
  let ν := RawFixed.FixedData.primPlus D u
  obtain ⟨gp, hgp, hgpL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A ν hnp
  have hgpI : ∀ s : ℂ, 1 < s.re → gp s = Detector.idealLSeries F ν.character s := by
    intro s hs
    exact (hgpL s (by linarith)).trans (RowHeckeBridge.hecke_eq_idealLSeries _ _ _ s hs)
  have hcond : 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ (2 * Cc) * U :=
    (hcb u).trans (by nlinarith)
  have hp := H1 ν hnp U (by linarith) hcond gp hgp hgpI t
  let s : ℂ := ((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hs0 : 0 < s.re := by simp [s]; norm_num
  have hmask := (H2 u s (by simp [s])).2.1
  have hqpow : PrincipalMellinComparison.frequencyNorm D.recipe u ^ (ε / 2) ≤
      2 ^ (ε / 2) * U ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num) hU0.le]
    exact Real.rpow_le_rpow hq0.le hUq2.le (by positivity)
  have hpowers : U ^ ((17 / 40 : ℝ) + ε / 2) * U ^ (ε / 2) = U ^ ((17 / 40 : ℝ) + ε) := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  change ‖(RawFixed.FixedData.pkg D).plus u s‖ ≤ _
  rw [RawHeckeIdentification31.plus_eq_hecke_mul_mask D u hu s hs0, ← hgpL s hs0, norm_mul]
  calc _ ≤ (C1 * U ^ ((17 / 40 : ℝ) + ε / 2) * (2 + |t|) ^ A) *
        (C2 * (2 ^ (ε / 2) * U ^ (ε / 2))) :=
      mul_le_mul hp (hmask.trans (mul_le_mul_of_nonneg_left hqpow hC2.le))
        (norm_nonneg _) (by positivity)
    _ = (C1 * C2 * 2 ^ (ε / 2)) * U ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ A := by
      rw [← hpowers]; ring

end
end DedekindZetaZeroFree.Quantitative.StrongPlusRows
end Refinement9672
