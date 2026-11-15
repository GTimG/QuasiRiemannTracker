/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The genuine physical source approaching the limiting return. The budget,
marked multiplier and cap move together; no limiting analytic estimate is used. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Reserve.Source
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveSource
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths

/-- The physical half-width face, with the full coupled cap debit retained. -/
def face (s : ℝ) : SourceFace :=
  ⟨1-s, 2+10*s, 0, 1/2, 0, 3/20-1000*s/1143⟩

/-- The smaller cap used by the physical return, inside the coupled source. -/
def physicalFace (s : ℝ) : SourceFace := ⟨1-s,2+10*s,0,1/2,0,3/40⟩

/-- Actual uniform initial energies at every sufficiently small positive cost.
The early mesh, physical coefficients and natural zeros are inherited from the
reserve source, rather than postulated as an additional arithmetic input. -/
theorem source {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource (face s) := by
  have hG := Qrh.MarkedAnchor.Reserve.source s hs hsmax hβ
  rw [Qrh.MarkedAnchor.Reserve.rCap_end] at hG
  have hr : (QRH.Record1252270103Source.globalFace
      (1-s) (2+10*s) (3/20-1000/1143*s)).Restricts (face s) := by
    constructor <;> dsimp [QRH.Record1252270103Source.globalFace, face] <;> linarith
  intro ε hε
  obtain ⟨mesh, hm, hsrc⟩ := hG ε hε
  exact ⟨mesh, hm, QRH.Record1252270103Return.unit_source_restrict hr hsrc⟩

theorem physical_source {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource (physicalFace s) := by
  have hr : (face s).Restricts (physicalFace s) := by
    constructor <;> dsimp [face,physicalFace] <;> linarith
  intro ε hε
  obtain ⟨mesh,hm,hsrc⟩ := source hs hsmax hβ ε hε
  exact ⟨mesh,hm,QRH.Record1252270103Return.unit_source_restrict hr hsrc⟩

/-- A nonpositive dual plain length is paid by the native cone. -/
theorem small_plain_shortening {s n₁ n₂ n z : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000)
    (h₁ : n₁ ≤ 0) (h₂ : n₂ ≤ n)
    (hcone : 2*n+(2+10*s)*z ≤ 1-s) (hz : z ≤ (3/40:ℝ)) :
    n₁+n₂+(9/2)*z ≤ 1 := by
  have hm := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ (9/2:ℝ)-(2+10*s)/2 by linarith)
  nlinarith

/-- A source may be fixed before the arithmetic data, within any requested
positive parameter budget. Constants need not be uniform as that budget shrinks. -/
theorem arbitrarily_small (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < η ∧ s ≤ 1/1000000000 ∧
      UniformUnitFaceSource (face s) := by
  let s := min (η/2) (1/1000000000)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsmax : s ≤ 1/1000000000 := min_le_right _ _
  have hsη : s < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨s, hs, hsη, hsmax, source hs hsmax hβ⟩

end
end Qrh.TwoSlot.AnchorContinuum.PositiveSource
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveSource.source
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveSource.physical_source
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveSource.arbitrarily_small
