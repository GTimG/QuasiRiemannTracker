/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Source-backed P12 supplier: invoke the native count and upgrade its remaining
middle branch to the actual inner ordinary width. -/
import Candidate.C092.transport.MixedInnerActualWidthBank
set_option autoImplicit false
namespace QRH.Cycle092.MixedInnerActualWidth
noncomputable section
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.MixedOffsetCount

/-- The source mesh and native count constants keep their original early
quantifier order. No analytic count or width admission is an input. -/
theorem actual_inner_width_branches (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0< t → 0< mesh t) ∧
    ∀(D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
      (∀s,D.ell s≤ mesh D.t/200) → (∀s,D.ell s≤ Cycle25.sourceMesh D.t/200) →
      D.ε≤1/10000000 → D.t≤1/10000000 →
    ∀kplain : ℝ,7/10≤ kplain → kplain≤3/4 → 2*HeckeZeroSupremum.beta-1≤ kplain →
    ∀eta : Character,∃K : CountConstants,∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀row : Row,row∈rows → ∀B : MiddleBank D S eta Z,
      row.box.Contains (B.delta,B.p) → B.γ≤(rowGamma row.box row.B:ℝ) → B.εa≤1/10^(13:ℕ) →
      (4*(rowBudget row.B:ℝ)/3≤ B.delta*B.centered ∧
        (B.common.card:ℝ)≤ B.coefficient K*B.baseScale^(B.R-4*(rowBudget row.B:ℝ)/3+B.loss)) ∨
      (widthLo≤ B.currentSlice.fiber.m ∧ B.currentSlice.fiber.m≤ widthHi ∧ B.CountConclusion K) := by
  obtain ⟨mesh,hm,hsource⟩:=actual_middle_branches hbeta
  refine ⟨mesh,hm,?_⟩
  intro D S hfine hstandard he ht kplain hk hk' hkb eta
  obtain ⟨K,hsource⟩:=hsource D S hfine hstandard he ht kplain hk hk' hkb eta
  refine ⟨K,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro row hr B hp hgamma hann
  exact bank_branch_width hr B K hZ.1 hp hgamma hann (hZ.2 B (rowBudget row.B:ℝ))

end
end QRH.Cycle092.MixedInnerActualWidth
#print axioms QRH.Cycle092.MixedInnerActualWidth.actual_inner_width_branches
