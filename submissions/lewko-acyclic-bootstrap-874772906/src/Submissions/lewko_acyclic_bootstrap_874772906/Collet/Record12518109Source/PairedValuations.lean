/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.PairedSteps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.MixedValuations
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.AdditionalCones0
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.AdditionalCones1
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

theorem raw_paired_base (k : Fin 15) {l r : ℝ}
    (hl : l ∈ Set.Icc (rawCells k).q (3/4))
    (hr : r ∈ Set.Icc (rawCells k).q (3/4)) (i j : Fin 6) :
    0 ≤ pairedGap (rawCells k) (i.val+1) (j.val+1) l r := by
  fin_cases k
  · exact additional0_paired_base (by simpa [rawCells,cell0] using hl) (by simpa [rawCells,cell0] using hr) i j
  · exact additional1_paired_base (by simpa [rawCells,cell1] using hl) (by simpa [rawCells,cell1] using hr) i j
  · exact cell2_paired_all (by simpa [rawCells,cell2] using hl) (by simpa [rawCells,cell2] using hr) i j
  · exact cell3_paired_all (by simpa [rawCells,cell3] using hl) (by simpa [rawCells,cell3] using hr) i j
  · exact cell4_paired_all (by simpa [rawCells,cell4] using hl) (by simpa [rawCells,cell4] using hr) i j
  · exact cell5_paired_all (by simpa [rawCells,cell5] using hl) (by simpa [rawCells,cell5] using hr) i j
  · exact cell6_paired_all (by simpa [rawCells,cell6] using hl) (by simpa [rawCells,cell6] using hr) i j
  · exact cell7_paired_all (by simpa [rawCells,cell7] using hl) (by simpa [rawCells,cell7] using hr) i j
  · exact cell8_paired_all (by simpa [rawCells,cell8] using hl) (by simpa [rawCells,cell8] using hr) i j
  · exact cell9_paired_all (by simpa [rawCells,cell9] using hl) (by simpa [rawCells,cell9] using hr) i j
  · exact cell10_paired_all (by simpa [rawCells,cell10] using hl) (by simpa [rawCells,cell10] using hr) i j
  · exact cell11_paired_all (by simpa [rawCells,cell11] using hl) (by simpa [rawCells,cell11] using hr) i j
  · exact cell12_paired_all (by simpa [rawCells,cell12] using hl) (by simpa [rawCells,cell12] using hr) i j
  · exact cell13_paired_all (by simpa [rawCells,cell13] using hl) (by simpa [rawCells,cell13] using hr) i j
  · exact cell14_paired_all (by simpa [rawCells,cell14] using hl) (by simpa [rawCells,cell14] using hr) i j

theorem raw_paired_all (k : Fin 15) {l r : ℝ}
    (hl : l ∈ Set.Icc (rawCells k).q (3/4))
    (hr : r ∈ Set.Icc (rawCells k).q (3/4)) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    0 ≤ pairedGap (rawCells k) i j l r := by
  have hq := (raw_mixed_parameters k).2.2.2.2
  have hqrange : (rawCells k).q ∈ Set.Icc (31/50:ℝ) (3/4) := hq
  have hlrange : l ∈ Set.Icc (31/50:ℝ) (3/4) := ⟨hq.1.trans hl.1,hl.2⟩
  have hrrange : r ∈ Set.Icc (31/50:ℝ) (3/4) := ⟨hq.1.trans hr.1,hr.2⟩
  have hρq := rho_bounds hqrange
  have hρl := rho_bounds hlrange
  have hρr := rho_bounds hrrange
  have hgamma : gamma (rawCells k) ≤ 5/7 := by
    unfold gamma
    linarith [hq.2,hρq.1]
  have hleft : 0 ≤ l+rho l-gamma (rawCells k) := by
    linarith [hlrange.1,hρl.1]
  have hright : 0 ≤ r+rho r-gamma (rawCells k) := by
    linarith [hrrange.1,hρr.1]
  have h := six_reduction (fun a b => -pairedGap (rawCells k) a b l r) ?_ ?_ ?_ i j hi hj
  · linarith
  · intro a b ha ha6 hb hb6
    let ai : Fin 6 := ⟨a-1,by omega⟩
    let bj : Fin 6 := ⟨b-1,by omega⟩
    have ha' : ai.val+1 = a := by dsimp [ai]; omega
    have hb' : bj.val+1 = b := by dsimp [bj]; omega
    have h := raw_paired_base k hl hr ai bj
    rw [ha',hb'] at h
    exact neg_nonpos.mpr h
  · intro a b _ _
    have hs := pairedGap_step_left (rawCells k) a b l r hρl.2 hρr.2
    linarith only [hs,hleft]
  · intro a b _ _
    have hs := pairedGap_step_right (rawCells k) a b l r hρl.2 hρr.2
    linarith only [hs,hright]
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.raw_paired_all
