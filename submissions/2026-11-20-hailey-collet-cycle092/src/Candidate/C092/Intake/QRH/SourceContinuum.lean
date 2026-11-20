/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate
import Candidate.C092.Intake.QRH.SourceCertificate.LowResponse
import Candidate.C092.Intake.QRH.SourceCertificate.ZeroBandBridge

/-!
# Complete real two-parameter scalar source cover

This assembles the recovered, kernel-checked finite source data with the real
length and response reductions. Every real `y ∈ [0.369, 0.3888]` and
`e ∈ [0, 0.5002]` has a paid low-response route or one of the eight actual
simultaneous inverse/ordinary cutoffs of its length cell.

The first theorem uses the common diagonal `ν = e`; the second proves the
literal general prices for every `ν ≥ e`, with the certified conservative
quota. The genuine curved radical comparison is proved in `QuotaBridge` and
`ZeroBandBridge`. Lifting these scalar bounds to the original source energy,
larger witnesses and radial parameters remains separate work.
-/

set_option autoImplicit false
namespace QRH.SourceCertificate

/-- Every real length and response has a paid route in the actual recovered
source certificate, including all cell and response-bin boundaries. -/
theorem source_scalar_continuum {y e : ℝ}
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ (243/625 : ℝ))
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ)) :
    ∃ c ∈ sourceCells, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) ∧
      ((e ≤ (c.threshold : ℝ) ∧ e*max 0 (lowBracketAt y) < (u-rho : ℚ)) ∨
       ((c.threshold : ℝ) ≤ e ∧ ∃ p ∈ c.cutoffs.zipIdx,
          CutoffGuard c.upper p.1 ∧ PaidAt y e p.1 ∧
          2*y/(H : ℝ) ≤ (p.1.inverse : ℝ) ∧ y/(H : ℝ) ≤ (p.1.ordinary : ℝ) ∧
          y < (H : ℝ)*((p.1.inverse : ℝ)+(p.1.ordinary : ℝ))/2)) := by
  obtain ⟨c,hc,hyl,hyu,hcheck⟩ := sourceCells_cover y hy₀ hy₁
  refine ⟨c,hc,hyl,hyu,?_⟩
  rcases le_total e (c.threshold : ℝ) with hel | hel
  · exact Or.inl ⟨hel,cellCheck_low_positive_part c hcheck hyl hyu he₀ hel⟩
  · exact Or.inr ⟨hel,cellCheck_real_length_response c hcheck hyl hyu hel he₁⟩

/-- The complete real scalar cover also pays every larger common zero band,
using the literal general short, long, and ordinary prices at the tested radius. -/
theorem source_scalar_continuum_with_band {y e ν : ℝ}
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ (243/625 : ℝ))
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ)) (hν : e ≤ ν) :
    ∃ c ∈ sourceCells, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) ∧
      ((e ≤ (c.threshold : ℝ) ∧ e*max 0 (lowBracketAt y) < (u-rho : ℚ)) ∨
       ((c.threshold : ℝ) ≤ e ∧ ∃ p ∈ c.cutoffs.zipIdx,
          CutoffGuard c.upper p.1 ∧ PaidWithBand y e ν p.1 ∧
          2*y/(H : ℝ) ≤ (p.1.inverse : ℝ) ∧ y/(H : ℝ) ≤ (p.1.ordinary : ℝ) ∧
          y < (H : ℝ)*((p.1.inverse : ℝ)+(p.1.ordinary : ℝ))/2)) := by
  obtain ⟨c,hc,hyl,hyu,hcheck⟩ := sourceCells_cover y hy₀ hy₁
  refine ⟨c,hc,hyl,hyu,?_⟩
  rcases le_total e (c.threshold : ℝ) with hel | hel
  · exact Or.inl ⟨hel,cellCheck_low_positive_part c hcheck hyl hyu he₀ hel⟩
  · exact Or.inr ⟨hel,cellCheck_real_band_response c hcheck hyl hyu hel he₁ hν⟩

end QRH.SourceCertificate
