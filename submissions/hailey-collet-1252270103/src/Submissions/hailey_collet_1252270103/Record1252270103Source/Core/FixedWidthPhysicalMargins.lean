/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The certified width margins at the actual finite-grid endpoints. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.FixedWidthPhysicalCells

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FixedWidthPhysical
noncomputable section
open QRH.Record1252270103Low Record1252270103Finite QRH.Record1252270103Graph

theorem upperWidthCell_fixed_on_grid (cross cap δ b : ℝ) (hδ : 0<δ)
    (hb : b∈activeWidthGrid cross cap δ) : upperWidthCell cross cap δ b=b := by
  have hbI:=activeWidthGrid_bounds cross cap δ b hb
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hb).1
  by_cases ht : cap≤cross+(i:ℝ)*δ
  · simp only [min_eq_left ht] at hbI ⊢
    have h:=upperWidthCell_bounds cross cap δ cap hδ hbI.1 le_rfl
    exact le_antisymm h.2.1 h.1
  · have ht' : cross+(i:ℝ)*δ≤cap:=le_of_lt (lt_of_not_ge ht)
    simp only [min_eq_right ht'] at hbI ⊢
    simp [upperWidthCell,max_eq_right hbI.1,min_eq_right hbI.2,
      mul_div_cancel_right₀ _ hδ.ne']

theorem nf_fixed_width_margins (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss b : ℝ)
    (hb : b∈activeWidthGrid (crossing n low) n.cap (nfWidthDelta n low high hv ha loss)) :
    ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,nfWidthMargin n low high hv ha loss/2≤
        sourceScalarReal (11243277/2500000) n low b j-|loss| *nfWidthDelta n low high hv ha loss) ∧
      0≤sourceWeakReal n low b ∧
      ∀j,nfWidthMargin n low high hv ha loss/2≤
        sourceDensityWidthReal n low high b ν j-|loss| *nfWidthDelta n low high hv ha loss := by
  have hc:=nf_width_certificate n low high hv ha loss
  have he:=upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hc.2.1 hb
  intro ν hν
  have hh:=hc.2.2.2.2.2.2 b (activeWidthGrid_bounds _ _ _ b hb) ν hν
  simpa only [nfWidthCell,he] using hh

theorem seed_fixed_width_margins (n low : Source)
    (hv : SeedSourceValid n low) (loss b : ℝ)
    (hb : b∈activeWidthGrid (crossing n low) n.cap (seedWidthDelta n low hv loss)) :
    ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,seedWidthMargin n low hv loss/2≤
        sourceScalarReal (112445673/25000000) n low b j-|loss| *seedWidthDelta n low hv loss) ∧
      0≤sourceWeakReal n low b ∧
      ∀j : Fin 6,seedWidthMargin n low hv loss/2≤
        sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j)-|loss| *seedWidthDelta n low hv loss := by
  have hc:=seed_width_certificate n low hv loss
  have he:=upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hc.2.1 hb
  intro ν hν
  have hh:=hc.2.2.2.2.2.2 b (activeWidthGrid_bounds _ _ _ b hb) ν hν
  simpa only [seedWidthCell,he] using hh

end
end QRH.Record1252270103Source.FixedWidthPhysical
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.upperWidthCell_fixed_on_grid
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.nf_fixed_width_margins
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.seed_fixed_width_margins
