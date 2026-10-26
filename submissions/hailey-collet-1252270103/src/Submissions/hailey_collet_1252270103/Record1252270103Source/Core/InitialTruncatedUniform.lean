/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite width and slot uniformization of the bounded first-budget supplier.
All height extensions and normalization are discharged before this join. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedSubset
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.FixedWidthPhysicalMargins
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.HeightAnchorUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open QRH.Record1252270103Low
open QRH.Record1252270103Source.FixedWidthPhysical

theorem physical_supplier_of_truncated_widths
    (B lam cap cross K ε δ:ℝ)(hB:B≤1)(hlam:1≤lam)(hcap:cap≤1)(hε:0<ε)(hδ:0<δ)
    (hr:∀b∈activeWidthGrid cross cap δ,0≤49/100-K*b)
    (hfixed:∀b∈activeWidthGrid cross cap δ,∃m x:ℝ,0<m ∧ 0<x ∧
      ∀mesh ξ:ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        FixedSubsetTruncatedSupplier B lam cap cross K mesh ξ ε b δ) :
    ∃mesh ξ:ℝ,0<mesh ∧ 0<ξ ∧
      HeightAnchor.InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε
        (upperWidthCell cross cap δ) := by
  apply HeightAnchor.physical_supplier_of_fixed_width_ceilings
    B lam cap cross K ε δ (upperWidthCell cross cap δ) (activeWidthGrid cross cap δ)
    (fun s hs=>upperWidthCell_active_grid cross cap δ s hδ hs)
  intro b hb
  obtain ⟨m,x,hm,hx,h⟩:=hfixed b hb
  refine ⟨m,x,hm,hx,?_⟩
  intro mesh ξ hmesh hmesh' hξ hξ'
  apply HeightAnchor.fixed_width_supplier_of_fixed_subsets
  exact fixed_subset_physical_of_truncated B lam cap cross K mesh ξ ε b δ
    hB hlam hcap hξ.le hε (hr b hb) (h mesh ξ hmesh hmesh' hξ hξ')

end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.physical_supplier_of_truncated_widths
