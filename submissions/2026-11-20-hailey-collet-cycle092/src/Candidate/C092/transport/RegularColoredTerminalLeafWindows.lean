/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual medium windows select a recorded cutoff after the genuine common
zero, then retain that SAME zero in the supported witness and finite key.
-/
import Candidate.C092.transport.TerminalActualRowTickets
import Candidate.C092.transport.StrongPairRegularTerminalBanks
import Candidate.C092.transport.RegularColoredTerminalLeafRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness HeckeDetectorZeros
open QRH.Cycle092.TerminalActualRow QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O

/-- The response window fixes its recorded cutoff only after one genuine
zero has been chosen. Every cutoff witness retains that zero and label. -/
theorem terminal_window_witnesses {Row Label : Type} [Fintype Row] [Fintype Label]
    [DecidableEq Label] {I K : ℕ}
    (χ : Row→Label→Character) (hn : ∀u j,(χ u j).residue≠1)
    (U d dmax tau epsilon ez price y step : ℝ) (cell : Cell)
    (table : TerminalResponseTable y step cell)
    (level : Row→Fin (I+1)) (band : Row→Fin (K+1)) (response : Row→ℝ)
    (hprice : 0≤ price)
    (hmedium : ∀u,(cell.threshold:ℝ)≤ response u ∧ response u≤(responseUpper:ℝ))
    (hband : ∀u,(51/100:ℝ)+ez*(band u).val≤7/8)
    (hceiling : ∀u,response u≤(2*((51/100:ℝ)+ez*(band u).val)-1)+price)
    (same : ∀u,SameZero (χ u) (hn u) U d dmax tau ((51/100:ℝ)+ez*(band u).val) epsilon (level u).val) :
    ∃ window : Row→Fin table.Je×Fin table.Jν,
    ∃ ws : ∀u,SupportedWitness (χ u) (U^d) ((51/100:ℝ)+ez*(band u).val) epsilon
      (totalCutoff (table.cutoff (window u))) (U^tau) ((U^d)^(tau/(2*dmax))) (level u).val,
      (∀u,table.egrid (window u).1≤ response u ∧ response u< table.egrid (window u).1+step ∧
        max (table.egrid (window u).1) (table.νgrid (window u).2)≤
          (2*((51/100:ℝ)+ez*(band u).val)-1)+price ∧
        (2*((51/100:ℝ)+ez*(band u).val)-1)<
          max (table.egrid (window u).1) (table.νgrid (window u).2)+step) ∧
      (∀u,(ws u).label=(same u).label ∧ (ws u).zero=(same u).zero) := by
  have hc (u : Row) := terminal_table_approx_cover table hprice (hmedium u).1 (hmedium u).2
    (hceiling u) (show 2*((51/100:ℝ)+ez*(band u).val)-1≤3/4 by linarith [hband u])
  choose window hw using hc
  have hd (u : Row) := cutoff_detector_domain (table.cutoff (window u)) (table.guard (window u))
  let ws := fun u=> (same u).witness (totalCutoff (table.cutoff (window u))) (hd u).1 (hd u).2
  refine ⟨window,ws,?_,?_⟩
  · intro u
    exact ⟨(hw u).1,(hw u).2.1,(hw u).2.2.1,(hw u).2.2.2.1⟩
  · intro u
    exact ⟨(same u).same_label _ _ _,(same u).same_zero _ _ _⟩

/-- Consume the actual native RowTickets; no new zero or family is
selected when the response window chooses its recorded cutoff. -/
theorem terminal_windows_from_row_tickets {Row Label : Type} [Fintype Row] [Fintype Label]
    [DecidableEq Label] {I : ℕ}
    (χ : Row→Label→Character) (hn : ∀u j,(χ u j).residue≠1)
    (U d dmax tau epsilon ez price y step : ℝ) (cell : Cell)
    (table : TerminalResponseTable y step cell) (response : Row→ℝ) (hprice : 0≤ price)
    (hmedium : ∀u,(cell.threshold:ℝ)≤ response u ∧ response u≤(responseUpper:ℝ))
    (ticket : ∀u,RowTicket (χ u) (hn u) U d dmax tau epsilon ez price (response u) I) :
    ∃ window : Row→Fin table.Je×Fin table.Jν,
    ∃ ws : ∀u,SupportedWitness (χ u) (U^d) ((51/100:ℝ)+ez*(ticket u).level.val) epsilon
      (totalCutoff (table.cutoff (window u))) (U^tau) ((U^d)^(tau/(2*dmax))) (ticket u).band.val,
      (∀u,table.egrid (window u).1≤ response u ∧ response u< table.egrid (window u).1+step ∧
        max (table.egrid (window u).1) (table.νgrid (window u).2)≤
          (2*((51/100:ℝ)+ez*(ticket u).level.val)-1)+price ∧
        (2*((51/100:ℝ)+ez*(ticket u).level.val)-1)<
          max (table.egrid (window u).1) (table.νgrid (window u).2)+step) ∧
      (∀u,(ws u).label=(ticket u).shared.label ∧ (ws u).zero=(ticket u).shared.zero) := by
  exact terminal_window_witnesses χ hn U d dmax tau epsilon ez price y step cell table
    (fun u=>(ticket u).band) (fun u=>(ticket u).level) response hprice hmedium
    (fun u=>(ticket u).upper) (fun u=>(ticket u).ceiling) (fun u=>(ticket u).shared)

/-- The finite key retains the actual band, level, recorded window, label
and BOTH native integer dyads of the same supported witness. -/
def terminalWitnessKey {Row Label : Type} [Fintype Label] {I K Je Jν : ℕ}
    {χ : Row→Label→Character} {U d dmax tau epsilon ez : ℝ}
    (level : Row→Fin (I+1)) (band : Row→Fin (K+1)) (window : Row→Fin Je×Fin Jν)
    (cutoff : Fin Je×Fin Jν→ℝ)
    (ws : ∀u,SupportedWitness (χ u) (U^d) ((51/100:ℝ)+ez*(band u).val) epsilon
      (cutoff (window u)) (U^tau) ((U^d)^(tau/(2*dmax))) (level u).val) :
    Row→Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×Label×Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d)) :=
  fun u=>(level u,band u,window u,(ws u).label,(ws u).left,(ws u).right)

/-- The original finite source is partitioned by the genuine ticket key,
with no additional rows and no row-count factor. -/
theorem terminal_class_energy_partition {Slot Key : Type} [Fintype Slot] [DecidableEq Slot]
    [Fintype Key] [DecidableEq Key] (T : Finset Slot) (rows : Finset FreeRow)
    (key : rows→Key) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) :
    StrongPair.finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark=
      ∑tag:Key,StrongPair.finiteEnergyOn T (classRows rows key tag) η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  unfold StrongPair.finiteEnergyOn
  rw [original_sum_partition rows key]
  apply Finset.sum_congr rfl
  intro tag htag
  unfold classRows
  rw [Finset.sum_image (fun a _ b _ h=> Subtype.ext h)]
  simp only [Finset.sum_filter,Finset.mem_univ,ite_true]

#print axioms terminal_window_witnesses
#print axioms terminal_windows_from_row_tickets
#print axioms terminal_class_energy_partition
end
end QRH.Cycle092.RegularColoredForward
