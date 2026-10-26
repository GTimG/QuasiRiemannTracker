/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.Count.Concrete
import Candidate.Uneven.MainCountAdmission10
import Candidate.Uneven.MainCountAdmission11
import Candidate.Uneven.MainCountAdmission12
import Candidate.Uneven.MainCountAdmission13
import Candidate.Uneven.MainCountAdmission14

set_option autoImplicit false
namespace OAI.SevenEighths.MainCount
noncomputable section
open Target830.Count

def branches (S : Stage) : List Branch := [
  (window10 S).toBranch (window10_admissible S),
  (window11 S).toBranch (window11_admissible S),
  (window12 S).toBranch (window12_admissible S),
  (window13 S).toBranch (window13_admissible S),
  (window14 S).toBranch (window14_admissible S)]

def count (S : Stage) (κ d p : ℝ) : ℝ :=
  finiteEnvelope Target830.Count.count (branches S) κ d p

theorem count_le_previous (S : Stage) (κ d p : ℝ) :
    count S κ d p ≤ Target830.Count.count κ d p :=
  finiteEnvelope_le_base Target830.Count.count (branches S) κ d p

theorem count_le_old (S : Stage) (κ d p : ℝ) :
    count S κ d p ≤ oldCount κ d p :=
  (count_le_previous S κ d p).trans (Target830.Count.count_le_old κ d p)


theorem count_antitone (S : Stage) {κ d p q : ℝ}
    (hk : 7/10 ≤ κ) (hkhi : κ ≤ 3/4) (hd : 0 ≤ d) (hdhi : d ≤ 3/4)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1/2) : count S κ d q ≤ count S κ d p :=
  finiteEnvelope_antitone Target830.Count.count (branches S) hpq hq
    (Target830.Count.count_antitone hk hkhi hd hdhi hp hpq hq)


theorem count_attained (S : Stage) (κ d p : ℝ) :
    count S κ d p=Target830.Count.count κ d p ∨
      ∃ b ∈ branches S,b.available d p ∧ count S κ d p=b.value d p :=
  finiteEnvelope_attained Target830.Count.count (branches S) κ d p

theorem count_le_window10 (S : Stage) {κ d p : ℝ}
    (ha : (window10 S).Available d p) :
    count S κ d p ≤ affineR (window10 S).plane.lambda (window10 S).plane.B d p := by
  exact finiteEnvelope_le_branch Target830.Count.count
    (show (window10 S).toBranch (window10_admissible S) ∈ branches S by simp [branches]) ha

theorem count_le_window11 (S : Stage) {κ d p : ℝ}
    (ha : (window11 S).Available d p) :
    count S κ d p ≤ affineR (window11 S).plane.lambda (window11 S).plane.B d p := by
  exact finiteEnvelope_le_branch Target830.Count.count
    (show (window11 S).toBranch (window11_admissible S) ∈ branches S by simp [branches]) ha

theorem count_le_window12 (S : Stage) {κ d p : ℝ}
    (ha : (window12 S).Available d p) :
    count S κ d p ≤ affineR (window12 S).plane.lambda (window12 S).plane.B d p := by
  exact finiteEnvelope_le_branch Target830.Count.count
    (show (window12 S).toBranch (window12_admissible S) ∈ branches S by simp [branches]) ha

theorem count_le_window13 (S : Stage) {κ d p : ℝ}
    (ha : (window13 S).Available d p) :
    count S κ d p ≤ affineR (window13 S).plane.lambda (window13 S).plane.B d p := by
  exact finiteEnvelope_le_branch Target830.Count.count
    (show (window13 S).toBranch (window13_admissible S) ∈ branches S by simp [branches]) ha

theorem count_le_window14 (S : Stage) {κ d p : ℝ}
    (ha : (window14 S).Available d p) :
    count S κ d p ≤ affineR (window14 S).plane.lambda (window14 S).plane.B d p := by
  exact finiteEnvelope_le_branch Target830.Count.count
    (show (window14 S).toBranch (window14_admissible S) ∈ branches S by simp [branches]) ha

end
end OAI.SevenEighths.MainCount
