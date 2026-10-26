import Candidate.Target830.Physical.CountGeometry
import Candidate.Cycle25.Assembly.Count.Optimization

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.DetectorCount
open scoped Classical

def window : Fin 10 → Count.Window :=
  ![Count.window0,Count.window1,Count.window2,Count.window3,Count.window4,
    Count.window5,Count.window6,Count.window7,Count.window8,Count.window9]

theorem window_admissible (i : Fin 10) {δ p : ℝ} (ha : (window i).Available δ p) :
    Count.Admissible (window i).plane δ p := by
  fin_cases i
  · exact Count.window0_admissible δ p ha
  · exact Count.window1_admissible δ p ha
  · exact Count.window2_admissible δ p ha
  · exact Count.window3_admissible δ p ha
  · exact Count.window4_admissible δ p ha
  · exact Count.window5_admissible δ p ha
  · exact Count.window6_admissible δ p ha
  · exact Count.window7_admissible δ p ha
  · exact Count.window8_admissible δ p ha
  · exact Count.window9_admissible δ p ha

theorem attained (κ δ p : ℝ) :
    Count.count κ δ p=Count.oldCount κ δ p ∨
      ∃i : Fin 10,(window i).Available δ p ∧
        Count.count κ δ p=Count.affineR (window i).plane.lambda (window i).plane.B δ p := by
  rcases Count.count_attained κ δ p with hh | ⟨b,hb,ha,he⟩
  · exact Or.inl hh
  · right
    simp [Count.branches] at hb
    rcases hb with hb|hb|hb|hb|hb|hb|hb|hb|hb|hb <;> subst b
    · exact ⟨0,ha,he⟩
    · exact ⟨1,ha,he⟩
    · exact ⟨2,ha,he⟩
    · exact ⟨3,ha,he⟩
    · exact ⟨4,ha,he⟩
    · exact ⟨5,ha,he⟩
    · exact ⟨6,ha,he⟩
    · exact ⟨7,ha,he⟩
    · exact ⟨8,ha,he⟩
    · exact ⟨9,ha,he⟩

def choice (κ δ p : ℝ) : Option (Fin 10) :=
  if hh : Count.count κ δ p=Count.oldCount κ δ p then none
  else some (Classical.choose ((attained κ δ p).resolve_left hh))

theorem choice_none {κ δ p : ℝ} (hh : choice κ δ p=none) :
    Count.count κ δ p=Count.oldCount κ δ p := by
  by_cases he : Count.count κ δ p=Count.oldCount κ δ p
  · exact he
  · simpa [choice,he] using hh

theorem choice_some {κ δ p : ℝ} {i : Fin 10} (hh : choice κ δ p=some i) :
    (window i).Available δ p ∧
      Count.count κ δ p=Count.affineR (window i).plane.lambda (window i).plane.B δ p := by
  by_cases he : Count.count κ δ p=Count.oldCount κ δ p
  · simp [choice,he] at hh
  · have hi : Classical.choose ((attained κ δ p).resolve_left he)=i := by
      simpa [choice,he] using hh
    rw [←hi]
    exact Classical.choose_spec ((attained κ δ p).resolve_left he)

def cutoff (δ p κ : ℝ) : ℝ :=
  match choice κ δ p with
  | none => Cycle25DetectorRowCount.cutoff δ p κ
  | some i => CountArithmetic.tN (window i).plane δ p

theorem cutoff_bounds {δ p κ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 3/4)
    (hp : 0 ≤ p) (hphi : p ≤ 1/2) (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ cutoff δ p κ ∧ cutoff δ p κ ≤ 3/2 := by
  unfold cutoff
  split <;> rename_i hh
  · exact Cycle25DetectorRowCount.cutoff_bounds hδ hδhi hp hphi hk
      (hkhi.trans (by norm_num [kappa0]))
  · have hg := CountArithmetic.admissible_geometry _ (window_admissible _ (choice_some hh).1)
      hδ hp hk hkhi
    exact ⟨hg.1,hg.2.1⟩

end OAI.SevenEighths.Target830.Physical.DetectorCount
end
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.attained
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.cutoff_bounds
