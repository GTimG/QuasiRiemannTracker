/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Logical sufficient-count/middle split of the authentic count, with outside exits explicit. -/
import Candidate.C092.transport.MixedOffsetCountRoutes
import Candidate.C092.transport.MixedOffsetCountPhaseUnion
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49

/-- This is exactly the proven E49 rectangle domain. Its complement is
retained for the original native outside-anchor routes, not discarded. -/
def centralLengths (x z : ℝ) : Prop :=
  anchorLeft ≤ x ∧ x ≤ anchorTop ∧ anchorLeft ≤ 2*z ∧ 2*z ≤ anchorTop

theorem outside_length_cases {x z : ℝ} (hout : ¬centralLengths x z) :
    x<anchorLeft ∨ anchorTop<x ∨ 2*z<anchorLeft ∨ anchorTop<2*z := by
  by_cases h1 : anchorLeft ≤ x
  · by_cases h2 : x ≤ anchorTop
    · by_cases h3 : anchorLeft ≤ 2*z
      · by_cases h4 : 2*z ≤ anchorTop
        · exact False.elim (hout ⟨h1,h2,h3,h4⟩)
        · exact Or.inr (Or.inr (Or.inr (lt_of_not_ge h4)))
      · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge h3)))
    · exact Or.inr (Or.inl (lt_of_not_ge h2))
  · exact Or.inl (lt_of_not_ge h1)

namespace MiddleBank
variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {η : Character} {Z : ℝ}

def BranchConclusion (B : MiddleBank D S η Z) (K : CountConstants) (q₀ : ℝ) : Prop :=
  (4*q₀/3 ≤ B.delta*B.centered ∧
    (B.common.card:ℝ) ≤ B.coefficient K*B.baseScale^(B.R-4*q₀/3+B.loss)) ∨
  (B.delta*B.centered<4*q₀/3 ∧ B.CountConclusion K)

/-- This split reads only the proved deficit after the entire genuine bank
has been fixed. It never changes the zero, cutoff list or witness selection. -/
theorem branch_of_count (B : MiddleBank D S η Z) (K : CountConstants)
    (hc : B.CountConclusion K) (hU : 1 ≤ B.baseScale) (hC : 0 ≤ B.coefficient K) (q₀ : ℝ) :
    B.BranchConclusion K q₀ := by
  by_cases hlarge : 4*q₀/3 ≤ B.delta*B.centered
  · refine Or.inl ⟨hlarge,?_⟩
    apply hc.1.trans
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU ?_) hC
    linarith only [hlarge]
  · exact Or.inr ⟨lt_of_not_ge hlarge,hc⟩

theorem coefficient_nonneg (B : MiddleBank D S η Z) (K : CountConstants) : 0 ≤ B.coefficient K := by
  dsimp [coefficient,countCoefficient,OAI.SevenEighths.HeckeDetectorRawFiber.fiberConstant]
  have hh:=B.height_nonneg
  have h0:=K.C₀_pos
  have hr:=K.Cr_pos
  have hi:=K.Ci_pos
  have hKi:=K.Ki_nonneg
  positivity
end MiddleBank

/-- An actual supplier, including the sufficient-count or remaining-middle
classification, with no count/moment estimate field or premise. -/
theorem actual_middle_branches (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0< mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
      (∀s,D.ell s ≤ mesh D.t/200) → (∀s,D.ell s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κplain : ℝ,7/10 ≤ κplain → κplain ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∀η : Character,∃K : CountConstants,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀B : MiddleBank D S η Z,∀q₀ : ℝ,B.BranchConclusion K q₀ := by
  obtain ⟨mesh,hm,hsrc⟩:=actual_middle_bank_count hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfine hstandard he ht κ hk hk' hkβ η
  obtain ⟨K,hsrc⟩:=hsrc D S hfine hstandard he ht κ hk hk' hkβ η
  refine ⟨K,?_⟩
  filter_upwards [hsrc] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro B q₀
  exact B.branch_of_count K (hZ.2 B) (B.baseScale_gt_one hZ.1).le (B.coefficient_nonneg K) q₀

#print axioms outside_length_cases
#print axioms actual_middle_branches
end
end QRH.Cycle092.MixedOffsetCount
