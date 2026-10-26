import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.MaskDescent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.FiniteDeletionBins
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Exact raw-row sixth decomposition, with all Euler punctures retained. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeRowClosure HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalProfile HeckeFiniteDeletion HeckeDetectorZeros
local notation "O" => HeckeFamily.O

lemma rowData_character_zero (data : RowData) (u : NonzeroElement) :
    elementCoeff (data.character u) 0 = 0 := by
  rw [data.character_spec]
  exact rowTwist_zero_of_not_supported (elementHom data.η) data.m data.f u.val 0
    data.lambda_dvd data.two_dvd (by
      intro hs
      exact hs.1 (by simp))

/-- Multiplication of the integer row by an arbitrary ideal generator's
sixth power adds exactly its original coprimality holes. -/
theorem amplified_ideal_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    idealCoeff (data.character (amplifiedElement u B)) I =
      if IsCoprime I B.val then idealCoeff (data.character u) I else 0 := by
  by_cases hs : Supported I
  · rw [idealCoeff_eq_row data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) I]
    change idealCoeff data.η I *
      idealRowHom (data.m ^ 6 * data.f ^ 4 *
        (u.val * (idealGenerator B.val) ^ 6)) I = _
    rw [show data.m ^ 6 * data.f ^ 4 * (u.val * (idealGenerator B.val) ^ 6) =
      (data.m ^ 6 * data.f ^ 4 * u.val) * (idealGenerator B.val) ^ 6 by ring,
      idealRowHom_argument_mul, idealRowHom_sixth_mask _ I hs,
      span_idealGenerator]
    by_cases hc : IsCoprime I B.val
    · rw [ite_eq_left hc, mul_one, ite_eq_left hc]
      exact (idealCoeff_eq_row data.η (data.character u) data.m data.f u.val
        (data.character_spec u) I).symm
    · simp only [hc, ite_false, mul_zero]
  · rw [row_coeff_zero_unsupported data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) data.lambda_dvd data.two_dvd I hs,
      row_coeff_zero_unsupported data.η (data.character u) data.m data.f u.val
        (data.character_spec u) data.lambda_dvd data.two_dvd I hs]
    split_ifs <;> rfl

theorem amplified_element_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (n : O) :
    elementCoeff (data.character (amplifiedElement u B)) n =
      if IsCoprime n (idealGenerator B.val) then elementCoeff (data.character u) n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [rowData_character_zero]
    split_ifs <;> rfl
  · have h := amplified_ideal_mask data u B (Ideal.span {n})
    rw [idealCoeff_span _ hn, idealCoeff_span _ hn,
      ← span_idealGenerator B.val, Ideal.isCoprime_span_singleton_iff] at h
    exact h

theorem inducedBy_self (χ : Character) : InducedBy χ χ := by
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc]
  · have hz : idealCoeff χ I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn).2
    rw [ite_eq_right hc, hz]

/-- The exact modulus-mask relation expected by finite Euler deletion. -/
theorem amplified_modulus_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) :
    InducedBy (data.character (amplifiedElement u B)) (data.character u) :=
  HeckeMaskDescent.inducedBy_mask (data.character u)
    (data.character (amplifiedElement u B)) (data.character u)
    (idealGenerator B.val) (amplified_element_mask data u B)
    (inducedBy_self (data.character u))

theorem amplified_nonprincipal (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) :
    (data.character (amplifiedElement u B)).residue ≠ 1 := by
  intro hp
  exact hu ((principal_iff_of_mask _ _ (amplified_modulus_mask data u B)).mp hp)

theorem amplified_positive_zeros (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (amplifiedElement u B)) s = 0 ↔
      LFunction (data.character u) s = 0 :=
  positive_zeros_eq_of_mask _ _ (amplified_nonprincipal data u B hu)
    (amplified_modulus_mask data u B) hs

theorem sixthFrequency_positive_zeros (data : RowData)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character ⟨p.1.val, p.1.property.1⟩).residue ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (ProbePhysical.sixthFrequencyEquiv p)) s = 0 ↔
      LFunction (data.character ⟨p.1.val, p.1.property.1⟩) s = 0 :=
  amplified_positive_zeros data ⟨p.1.val, p.1.property.1⟩ p.2 hu hs

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
