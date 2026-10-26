/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The global ordinary source uses the existing literal initial-energy contract.
This file establishes only exact domain and interface transport. -/
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source
noncomputable section

open QRH.Record12518109Source QRH.Record12518109Existence

/-- The apparent individual upper edge is implied by the nonnegative total cap. -/
def globalFace (B lam cap : ℝ) : SourceFace := ⟨B, lam, 0, B, 0, cap⟩

/-- One mesh precedes every finite slot type and all moving arithmetic data.
The energy, profiles, initialKeep, relative slots and natural zeros are literal. -/
abbrev GlobalSource (B lam cap : ℝ) : Prop :=
  UniformUnitFaceSource (globalFace B lam cap)

theorem globalFace_admissible_iff {B lam cap m₁ m₂ s M : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hs : 0 ≤ s) (hlam : 0 ≤ lam) :
    (globalFace B lam cap).Admissible m₁ m₂ s M ↔
      s ≤ cap*M ∧ m₁+m₂+lam*s ≤ B*M := by
  constructor
  · rintro ⟨_,_,_,_,_,hcap,hbudget⟩
    exact ⟨hcap,hbudget⟩
  · rintro ⟨hcap,hbudget⟩
    have hmarked : 0 ≤ lam*s := mul_nonneg hlam hs
    change 0*M ≤ m₁ ∧ m₁ ≤ B*M ∧ 0*M ≤ m₂ ∧ m₂ ≤ B*M ∧
      0*M ≤ s ∧ s ≤ cap*M ∧ m₁+m₂+lam*s ≤ B*M
    refine ⟨by simpa using hm₁,by linarith,by simpa using hm₂,
      by linarith,by simpa using hs,hcap,hbudget⟩

/-- Every nonnegative coordinatewise shortening remains in the same global face.
No natural fallback or positive lower edge is needed. -/
theorem globalFace_downward {B lam cap m₁ m₂ s n₁ n₂ z M : ℝ}
    (hlam : 0 ≤ lam) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hs : 0 ≤ s)
    (h : (globalFace B lam cap).Admissible m₁ m₂ s M)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hz : 0 ≤ z)
    (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂) (hslot : z ≤ s) :
    (globalFace B lam cap).Admissible n₁ n₂ z M := by
  obtain ⟨hcap,hbudget⟩ := (globalFace_admissible_iff hm₁ hm₂ hs hlam).mp h
  apply (globalFace_admissible_iff hn₁ hn₂ hz hlam).mpr
  have hmarked := mul_le_mul_of_nonneg_left hslot hlam
  exact ⟨hslot.trans hcap,by linarith⟩

/-- Literal parent inclusion below the crossing, also for distinct width caps. -/
theorem globalFace_inherit {B lam cap B₀ lam₀ cap₀ m₁ m₂ s M : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hs : 0 ≤ s)
    (hlam : 0 ≤ lam) (hlam₀ : 0 ≤ lam₀)
    (h : (globalFace B lam cap).Admissible m₁ m₂ s M)
    (hcap : s ≤ cap₀*M) (hcross : (B-B₀)*M+(lam₀-lam)*s ≤ 0) :
    (globalFace B₀ lam₀ cap₀).Admissible m₁ m₂ s M := by
  obtain ⟨_,hbudget⟩ := (globalFace_admissible_iff hm₁ hm₂ hs hlam).mp h
  apply (globalFace_admissible_iff hm₁ hm₂ hs hlam₀).mpr
  exact ⟨hcap,by nlinarith⟩

end
end QRH.Record1252270103Source

#print axioms QRH.Record1252270103Source.globalFace_admissible_iff
#print axioms QRH.Record1252270103Source.globalFace_downward
#print axioms QRH.Record1252270103Source.globalFace_inherit
