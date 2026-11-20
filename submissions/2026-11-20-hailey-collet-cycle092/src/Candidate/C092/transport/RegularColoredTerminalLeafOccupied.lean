/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine row ticket and recorded response window supply every frozen
fiber band and response endpoint; both native dyads remain unchanged. -/
import Candidate.C092.transport.RegularColoredTerminalLeafTicketGuards
import Candidate.C092.transport.RegularColoredTerminalLeafWindowFee
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open QRH.Cycle092.TerminalActualRow QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate

/-- All scalar guards and both actual response endpoints come from the
original ticket fiber and its chosen table entry. No new window is chosen. -/
theorem terminal_actual_occupied_class {Label : Type} [Fintype Label] [DecidableEq Label]
    {I : ℕ} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (hn : ∀u : rows,∀j,(χ u.val j).residue≠1)
    (U d dmax τ ε ez price y step : ℝ) (cell : Cell) (table : TerminalResponseTable y step cell)
    (hUd : 1 < U^d) (hε : ε ≤ 1/7500) (response : FreeRow→ℝ)
    (ticket : ∀u : rows,RowTicket (χ u.val) (hn u) U d dmax τ ε ez price (response u.val) I)
    (window : rows→Fin table.Je×Fin table.Jν)
    (ws : ∀u : rows,SupportedWitness (χ u.val) (U^d) ((51/100:ℝ)+ez*(ticket u).level.val) ε
      (totalCutoff (table.cutoff (window u))) (U^τ) ((U^d)^(τ/(2*dmax))) (ticket u).band.val)
    (hwindow : ∀u : rows,table.egrid (window u).1 ≤ response u.val ∧ response u.val < table.egrid (window u).1+step ∧
      max (table.egrid (window u).1) (table.νgrid (window u).2) ≤ 2*((51/100:ℝ)+ez*(ticket u).level.val)-1+price ∧
      2*((51/100:ℝ)+ez*(ticket u).level.val)-1 < max (table.egrid (window u).1) (table.νgrid (window u).2)+step)
    (tag : Fin (I+1)×Fin (⌊(73/200:ℝ)/ez⌋₊+1)×(Fin table.Je×Fin table.Jν)×Label×
      Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))) :
    let key := terminalWitnessKey (fun u=>(ticket u).band) (fun u=>(ticket u).level) window
      (fun k=>totalCutoff (table.cutoff k)) ws;
    let fiber := classRows rows key tag;
    let a := (51/100:ℝ)+ez*tag.2.1.val;
    let m := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val);
    let r := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.1.val);
    fiber.Nonempty →
      1 ≤ tag.1.val ∧ (51/100:ℝ) < a ∧ a ≤ 7/8 ∧
      (∀u∈fiber,table.egrid tag.2.2.1.1 ≤ response u ∧ response u ≤ table.egrid tag.2.2.1.1+step) ∧
      max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2) ≤ 2*a-1+price ∧
      2*a-1 ≤ max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2)+step ∧
      0 ≤ m ∧ m ≤ 51/100 ∧ 0 ≤ r ∧
      1 ≤ totalCutoff (table.cutoff tag.2.2.1) ∧ totalCutoff (table.cutoff tag.2.2.1) ≤ 3/2 ∧
      (((table.cutoff tag.2.2.1).inverse:ℝ) ≤ r → (367/500:ℝ) ≤ r) := by
  classical
  intro key fiber a m r hclass
  obtain ⟨z,hz⟩ := hclass
  let zc : fiber := ⟨z,hz⟩
  have hguards := terminal_actual_ticket_class_guards rows χ hn U d dmax τ ε ez price response
    ticket window (fun k=>totalCutoff (table.cutoff k)) ws tag zc
  have hfields (u : fiber) := terminal_key_fields rows χ U d dmax τ ε ez
    (fun u=>(ticket u).band) (fun u=>(ticket u).level) window (fun k=>totalCutoff (table.cutoff k)) ws tag u
  have hresponse (u : fiber) : table.egrid tag.2.2.1.1 ≤ response u.val ∧
      response u.val < table.egrid tag.2.2.1.1+step ∧
      max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2) ≤ 2*a-1+price ∧
      2*a-1 < max (table.egrid tag.2.2.1.1) (table.νgrid tag.2.2.1.2)+step := by
    let parent : rows := ⟨u.val,classRows_subset rows key tag u.property⟩
    have hf := hfields u
    have hw := hwindow parent
    have hlevel : (ticket parent).level=tag.2.1 := hf.2.1
    have hwin : window parent=tag.2.2.1 := hf.2.2.1
    simpa only [hwin,hlevel] using hw
  obtain ⟨wc,hc⟩ := terminal_witness_class rows χ U d dmax τ ε ez hUd
    (fun u=>(ticket u).band) (fun u=>(ticket u).level) window (fun k=>totalCutoff (table.cutoff k)) ws tag
  have hmu : (wc zc).m=m := (hc zc).2.2.2.2
  have hmu1 := actual_ordinary_cap_upper (table.cutoff tag.2.2.1) (wc zc) (table.guard tag.2.2.1) hε
  rw [hmu] at hmu1
  have hm1 : m ≤ 51/100 := (le_max_left _ _).trans hmu1
  have hm0 : 0 ≤ m := Real.logb_nonneg hUd (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hr0 : 0 ≤ r := Real.logb_nonneg hUd (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hcut := cutoff_detector_domain (table.cutoff tag.2.2.1) (table.guard tag.2.2.1)
  have hinv : (367/500:ℝ) < ((table.cutoff tag.2.2.1).inverse:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr (table.guard tag.2.2.1).2.2.2.2.2.1
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  exact ⟨hguards.1,hguards.2.1,hguards.2.2.1,
    (fun u hu=>⟨(hresponse ⟨u,hu⟩).1,(hresponse ⟨u,hu⟩).2.1.le⟩),
    (hresponse zc).2.2.1,(hresponse zc).2.2.2.le,hm0,hm1,hr0,hcut.1,hcut.2,
    (fun h=>hinv.le.trans h)⟩

#print axioms terminal_actual_occupied_class
end
end QRH.Cycle092.RegularColoredForward
