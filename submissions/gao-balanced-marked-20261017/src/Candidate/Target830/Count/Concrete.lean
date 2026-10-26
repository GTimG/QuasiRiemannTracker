import Candidate.Target830.Count.Guards.Window0
import Candidate.Target830.Count.Guards.Window1
import Candidate.Target830.Count.Guards.Window2
import Candidate.Target830.Count.Guards.Window3
import Candidate.Target830.Count.Guards.Window4
import Candidate.Target830.Count.Guards.Window5
import Candidate.Target830.Count.Guards.Window6
import Candidate.Target830.Count.Guards.Window7
import Candidate.Target830.Count.Guards.Window8
import Candidate.Target830.Count.Guards.Window9
set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def branches : List Branch := [
  window0.toBranch window0_admissible,
  window1.toBranch window1_admissible,
  window2.toBranch window2_admissible,
  window3.toBranch window3_admissible,
  window4.toBranch window4_admissible,
  window5.toBranch window5_admissible,
  window6.toBranch window6_admissible,
  window7.toBranch window7_admissible,
  window8.toBranch window8_admissible,
  window9.toBranch window9_admissible]

def count (κ δ p : ℝ) : ℝ := finiteEnvelope oldCount branches κ δ p

def rowAt (κ d cap δ p : ℝ) : ℝ := rowBase d cap δ p+3*d*count κ δ p/4

theorem count_le_old (κ δ p : ℝ) : count κ δ p ≤ oldCount κ δ p :=
  finiteEnvelope_le_base oldCount branches κ δ p

theorem count_gap {a κ δ p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hδ : 0 ≤ δ ∧ δ ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    count κ δ p-count a δ p ≤ 5*(κ-a)/216 := by
  apply finiteEnvelope_gap oldCount branches (by linarith)
  have h := Cycle63.Arithmetic.Bernstein.row_gap ha hak hδ hp
  dsimp only [oldCount]
  linarith

theorem count_antitone {κ δ p q : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ 3/4)
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 3/4) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1/2) :
    count κ δ q ≤ count κ δ p := by
  apply finiteEnvelope_antitone oldCount branches hpq hq
  exact OAI.SevenEighths.Cycle25DetectorRowCount.countingR0_antitone
    hk hkhi hδ hδhi hp hpq hq

theorem count_bound {κ δ p : ℝ} {P : ℝ → Prop}
    (hold : P (oldCount κ δ p))
    (hfixed : ∀ b ∈ branches, b.available δ p → P (b.value δ p)) :
    P (count κ δ p) := finiteEnvelope_bound oldCount branches hold hfixed

theorem count_attained (κ δ p : ℝ) :
    count κ δ p=oldCount κ δ p ∨
      ∃ b ∈ branches,b.available δ p ∧ count κ δ p=b.value δ p :=
  finiteEnvelope_attained oldCount branches κ δ p

theorem count_le_window0 {κ δ p : ℝ} (ha : window0.Available δ p) :
    count κ δ p ≤ affineR window0.plane.lambda window0.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window0.toBranch window0_admissible ∈ branches by simp [branches]) ha

theorem count_le_window1 {κ δ p : ℝ} (ha : window1.Available δ p) :
    count κ δ p ≤ affineR window1.plane.lambda window1.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window1.toBranch window1_admissible ∈ branches by simp [branches]) ha

theorem count_le_window2 {κ δ p : ℝ} (ha : window2.Available δ p) :
    count κ δ p ≤ affineR window2.plane.lambda window2.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window2.toBranch window2_admissible ∈ branches by simp [branches]) ha

theorem count_le_window3 {κ δ p : ℝ} (ha : window3.Available δ p) :
    count κ δ p ≤ affineR window3.plane.lambda window3.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window3.toBranch window3_admissible ∈ branches by simp [branches]) ha

theorem count_le_window4 {κ δ p : ℝ} (ha : window4.Available δ p) :
    count κ δ p ≤ affineR window4.plane.lambda window4.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window4.toBranch window4_admissible ∈ branches by simp [branches]) ha

theorem count_le_window5 {κ δ p : ℝ} (ha : window5.Available δ p) :
    count κ δ p ≤ affineR window5.plane.lambda window5.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window5.toBranch window5_admissible ∈ branches by simp [branches]) ha

theorem count_le_window6 {κ δ p : ℝ} (ha : window6.Available δ p) :
    count κ δ p ≤ affineR window6.plane.lambda window6.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window6.toBranch window6_admissible ∈ branches by simp [branches]) ha

theorem count_le_window7 {κ δ p : ℝ} (ha : window7.Available δ p) :
    count κ δ p ≤ affineR window7.plane.lambda window7.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window7.toBranch window7_admissible ∈ branches by simp [branches]) ha

theorem count_le_window8 {κ δ p : ℝ} (ha : window8.Available δ p) :
    count κ δ p ≤ affineR window8.plane.lambda window8.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window8.toBranch window8_admissible ∈ branches by simp [branches]) ha

theorem count_le_window9 {κ δ p : ℝ} (ha : window9.Available δ p) :
    count κ δ p ≤ affineR window9.plane.lambda window9.plane.B δ p := by
  exact finiteEnvelope_le_branch oldCount
    (show window9.toBranch window9_admissible ∈ branches by simp [branches]) ha

end
end OAI.SevenEighths.Target830.Count
#print axioms OAI.SevenEighths.Target830.Count.count_gap
#print axioms OAI.SevenEighths.Target830.Count.count_antitone
#print axioms OAI.SevenEighths.Target830.Count.count_bound
