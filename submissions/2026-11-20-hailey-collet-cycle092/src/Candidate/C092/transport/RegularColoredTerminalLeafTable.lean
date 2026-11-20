/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual recorded response table supplies the genuine early physical bank.
-/
import Candidate.C092.transport.TerminalActualInverseApplyComplete
import Candidate.C092.transport.RegularColoredTerminalLeafTicketGuards
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths OAI.SevenEighths.CenteredMomentEnergyBands
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.StrongPair
open Qrh.MarkedAnchor.Interface

/-- Choose the actual certificate cell before its positive table mesh. -/
theorem terminal_actual_checked_cell {y : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) :
    ∃ cell : Cell,cell ∈ sourceCells ∧ (cell.lower:ℝ) ≤ y ∧ y ≤ (cell.upper:ℝ) ∧
      0 < (cell.threshold:ℝ) ∧ (cell.threshold:ℝ) ≤ (responseUpper:ℝ) ∧
      (cell.threshold:ℝ)*max 0 (lowBracketAt y) < (u-rho:ℚ) ∧
      ∀step : ℝ,0 < step  →  Nonempty (TerminalResponseTable y step cell) := by
  obtain ⟨cells,hcells,htables⟩:=terminal_finite_checked_tables (fun _ : Unit=>y)
    (fun _=>by simpa only [sourceY0] using hy0) (fun _=>by simpa only [sourceY] using hy1)
  refine ⟨cells (), (hcells ()).1,(hcells ()).2.1,(hcells ()).2.2.1,
    (hcells ()).2.2.2.1,(hcells ()).2.2.2.2.1,(hcells ()).2.2.2.2.2,?_⟩
  intro step hs
  obtain ⟨tables⟩:=htables step hs
  exact ⟨tables ()⟩

/-- All window indices are the actual finite table. Its checked guard and
paid certificate are passed directly to the new genuine class constructors;
no old existential fee or source function is identified with the new one. -/
theorem terminal_actual_table_physical_bank
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y loss : ℝ} {cell : Cell} (table : TerminalResponseTable y (loss/10) cell)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (ht : 0 ≤ (cell.threshold:ℝ))
    (hloss : 0 < loss) (heightLoss : ℝ) (hheightLoss : 0 ≤ heightLoss)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (dBank : Finset ℝ) (hdb : ∀d ∈ dBank,(98/100:ℝ) ≤ d ∧ dmin ≤ d ∧ d ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4) :
    let Key := Fin table.Je×Fin table.Jν;
    ∃ feeM feeU commonFee : Key → ℝ,
      (∀ k,0  <  feeM k ∧ 0  <  feeU k ∧ 0  <  commonFee k ∧ commonFee k  ≤  feeM k ∧ commonFee k  ≤  feeU k) ∧
    ∃ ζ : ℝ,0  <  ζ ∧ (∀ k,ζ  ≤  commonFee k/2) ∧
    ∃ δ : ℝ,0  <  δ ∧ δ  ≤  1/1000 ∧ 3*δ  ≤  ζ ∧
    ∃ J : ℕ,∃ bank : Fin J  →  Contract.AnchorRect,
      (∀ j,Contract.UniformInverseRectSource Contract.canonicalFamily (bank j)) ∧
      (∀ r : ℝ,367/500  ≤  r  →  r  ≤  1  → 
        inverseQuota r  ≤  ζ ∨ (0  ≤  inverseQuota r-ζ  →  ∃ j,(bank j).Admissible r (inverseQuota r-ζ) 1)) ∧
    ∃ quota : Key → dBank → ℝ,
      (∀ k d,0  ≤  terminalNativeCap n d.val ∧ terminalNativeCap n d.val  <  1/2 ∧
        0  <  quota k d ∧ quota k d  <  3/20 ∧ quota k d  <  (1-2*terminalNativeCap n d.val)/2 ∧
        2*NativeFourthEffective.credit n d.val-d.val*quota k d  ≤  commonFee k/4 ∧
        ∀ {U X : ℝ},0  <  U  →  length U X  ≤  n  →  length (U^d.val) X  ≤  terminalNativeCap n d.val) ∧
    ∃ im nm : Key → dBank → Fin J → ℝ,∃ nu : Key → dBank → ℝ,
      (∀ k d j,0  <  im k d j ∧ 0  <  nm k d j) ∧ (∀ k d,0  <  nu k d) ∧
    ∃ mesh : ℝ,0  <  mesh ∧
      (∀ k d j,mesh  ≤  im k d j ∧ mesh  ≤  nm k d j) ∧ (∀ k d,mesh  ≤  nu k d) ∧
      (∀ k d j,TerminalActualClassMarkedPhysical n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k) (loss/10) (loss/10) (feeM k)
        (bank j) εm nativeError (terminalNativeCap n d.val) (quota k d) dmin dmax price (im k d j) (nm k d j)) ∧
      (∀ k d,TerminalActualClassUnmarkedPhysical n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k) (loss/10) (loss/10) (feeU k)
        εm nativeError (terminalNativeCap n d.val) (quota k d) dmin dmax price (nu k d)) := by
  dsimp only
  exact terminal_finite_actual_class_physical_bank hβ
    (fun _ : Fin table.Je×Fin table.Jν=>n) (fun _=>y)
    (fun k=>table.egrid k.1) (fun k=>max (table.egrid k.1) (table.νgrid k.2))
    table.cutoff (fun _=>cell.upper) (fun _=>hy0) (fun _=>hy1) (fun _=>hyn) (fun _=>hn)
    (fun k=>ht.trans (table.eBounds k.1).1) (fun _=>le_max_left _ _)
    (fun k=>max_le ((table.eBounds k.1).2.trans (by norm_num [responseUpper])) (table.νBounds k.2).2)
    table.guard table.paid hloss heightLoss hheightLoss εm nativeError hεm hnativeError
    dmin dmax hdmin hdmax dBank hdb price hprice0 hpriceBudget

#print axioms terminal_actual_checked_cell
#print axioms terminal_actual_table_physical_bank
end
end QRH.Cycle092.RegularColoredForward
