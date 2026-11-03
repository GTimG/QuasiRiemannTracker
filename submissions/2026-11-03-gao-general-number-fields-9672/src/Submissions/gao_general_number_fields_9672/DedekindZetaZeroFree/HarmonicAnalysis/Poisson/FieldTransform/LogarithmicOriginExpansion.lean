/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/FieldTransform/LogarithmicOriginExpansion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.SquareScalingAndOriginExpansion
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.PositiveQuadraticMass
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.UniformEulerDecay

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem transformed_field_origin_uniform
    (D : ℝ) (r : ℕ) (b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) :
    (∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        Vendor.PositiveSideSupport b h → ∀ n : ℕ, n < r →
          ‖(originPolynomial D r h).coeff n‖ ≤ C * Vendor.S b N h) ∧
    (∀ (j : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∃ (N : ℕ) (C : ℝ), 0 < C ∧
        ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
          Vendor.PositiveSideSupport b h → ∀ x : ℝ, 0 < x → x ≤ 1 →
            ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h y -
              Polynomial.eval (Real.log y : ℂ) (originPolynomial D r h)) x‖ ≤
                C * Vendor.S b N h * x ^ δ) ∧
    (∀ (j : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∃ (N : ℕ) (C : ℝ), 0 < N ∧ 0 < C ∧
        ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
          Vendor.PositiveSideSupport b h → ∀ x : ℝ, 0 < x → x ≤ 1 →
            ‖Vendor.EulerIter j (fun y : ℝ => fieldTransform D r h (y ^ 2) -
              Polynomial.eval ((2 * Real.log y : ℝ) : ℂ) (originPolynomial D r h)) x‖ ≤
                C * Vendor.S b N h * x ^ (2 * δ)) ∧
    (∀ j n : ℕ, ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        Vendor.PositiveSideSupport b h → ∀ x : ℝ, 1 ≤ x →
          ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
            C * Vendor.S b N h * Real.rpow x (-(n : ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨N, C, hC, hb'⟩ := originPolynomial_coeff_uniform_bound D r b hD hr hb
    exact ⟨N, C, hC, fun h hh hhc hsupp n hn =>
      hb' h hh hhc (fun x hx => hsupp x hx) n hn⟩
  · intro j δ hδ hδ1
    obtain ⟨N, C, hC, hb'⟩ :=
      fieldTransform_origin_remainder_uniform_bound D r b δ j hD hr hb hδ hδ1
    exact ⟨N, C, hC, fun h hh hhc hsupp x hx hx1 =>
      hb' h hh hhc (fun y hy => hsupp y hy) x hx hx1⟩
  · intro j δ hδ hδ1
    obtain ⟨N, C, hN, hC, hb'⟩ :=
      fieldTransform_comp_sq_origin_remainder_uniform_bound D r b δ j hD hr hb hδ hδ1
    exact ⟨N, C, hN, hC, fun h hh hhc hsupp x hx hx1 =>
      hb' h hh hhc (fun y hy => hsupp y hy) x hx hx1⟩
  · intro j n
    obtain ⟨N, C, hC, hb'⟩ :=
      fieldTransform_uniform_euler_two_ended_bound D r b j n 1 hD hr hb (by norm_num)
    exact ⟨N, C, hC, fun h hh hhc hsupp x hx1 => (hb' h hh hhc hsupp).2 x hx1⟩

end DedekindZetaZeroFree.LargeSieve

end
