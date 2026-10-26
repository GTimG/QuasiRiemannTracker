/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Seed
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell00
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell01
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell02
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell03
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell04
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell05
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell06
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell07
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell08
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell09
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell10
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell11
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell12
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell13
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Cell14
set_option autoImplicit false
namespace Record12518109Admission
def OnFace (c : Cell) (m₁ m₂ s : ℝ) : Prop :=
 m₁ ∈ Set.Icc c.plainLo c.plainHi ∧ m₂ ∈ Set.Icc c.plainLo c.plainHi ∧
 s ∈ Set.Icc c.lo c.hi ∧ m₁+m₂+c.L*s ≤ c.B

def PriorMatches (earlier later : Cell) : Prop :=
 later.priorB=earlier.B ∧ later.priorL=earlier.L ∧
 later.priorLo=earlier.lo ∧ later.priorHi=earlier.hi ∧
 later.priorPlainLo=earlier.plainLo ∧ later.priorPlainHi=earlier.plainHi
theorem first_prior_matches_seed : cell0.priorB=seedB ∧ cell0.priorL=seedL ∧ cell0.priorLo=2/125 ∧ cell0.priorHi=1/50 ∧ cell0.priorPlainLo=1/4 ∧ cell0.priorPlainHi=11/20 := by norm_num [cell0, seedB, seedL]
theorem prior1_matches : PriorMatches cell0 cell1 := by norm_num [PriorMatches, cell0, cell1]
theorem prior2_matches : PriorMatches cell1 cell2 := by norm_num [PriorMatches, cell1, cell2]
theorem prior3_matches : PriorMatches cell1 cell3 := by norm_num [PriorMatches, cell1, cell3]
theorem prior4_matches : PriorMatches cell1 cell4 := by norm_num [PriorMatches, cell1, cell4]
theorem prior5_matches : PriorMatches cell1 cell5 := by norm_num [PriorMatches, cell1, cell5]
theorem prior6_matches : PriorMatches cell1 cell6 := by norm_num [PriorMatches, cell1, cell6]
theorem prior7_matches : PriorMatches cell1 cell7 := by norm_num [PriorMatches, cell1, cell7]
theorem prior8_matches : PriorMatches cell1 cell8 := by norm_num [PriorMatches, cell1, cell8]
theorem prior9_matches : PriorMatches cell1 cell9 := by norm_num [PriorMatches, cell1, cell9]
theorem prior10_matches : PriorMatches cell1 cell10 := by norm_num [PriorMatches, cell1, cell10]
theorem prior11_matches : PriorMatches cell1 cell11 := by norm_num [PriorMatches, cell1, cell11]
theorem prior12_matches : PriorMatches cell1 cell12 := by norm_num [PriorMatches, cell1, cell12]
theorem prior13_matches : PriorMatches cell1 cell13 := by norm_num [PriorMatches, cell1, cell13]
theorem prior14_matches : PriorMatches cell1 cell14 := by norm_num [PriorMatches, cell1, cell14]
theorem physical_closed_width_cover {s : ℝ} (hs : s ∈ Set.Icc (17/500) (1/25)) : s ∈ Set.Icc cell2.lo cell2.hi ∨ s ∈ Set.Icc cell3.lo cell3.hi ∨ s ∈ Set.Icc cell4.lo cell4.hi ∨ s ∈ Set.Icc cell5.lo cell5.hi := by
 by_cases h0 : s ≤ (9/250:ℝ)
 · left; norm_num [cell2]; constructor <;> linarith [hs.1, hs.2]
 ·
   by_cases h1 : s ≤ (3/80:ℝ)
   · right; left; norm_num [cell3]; constructor <;> linarith [hs.1, hs.2]
   ·
     by_cases h2 : s ≤ (39/1000:ℝ)
     · right; right; left; norm_num [cell4]; constructor <;> linarith [hs.1, hs.2]
     ·
       right; right; right; norm_num [cell5]; constructor <;> linarith [hs.1, hs.2]
theorem physical_face_cover {m₁ m₂ s : ℝ} (h₁ : m₁ ∈ Set.Icc (2/5) (11/25)) (h₂ : m₂ ∈ Set.Icc (2/5) (11/25)) (hs : s ∈ Set.Icc (17/500) (1/25)) (hc : m₁+m₂*1+(74001/20000)*s ≤ (306003/312500)) : OnFace cell2 m₁ m₂ s ∨ OnFace cell3 m₁ m₂ s ∨ OnFace cell4 m₁ m₂ s ∨ OnFace cell5 m₁ m₂ s := by
 have hw := physical_closed_width_cover hs
 rcases hw with w2 | w3 | w4 | w5
 · left; exact ⟨by simpa [cell2] using h₁, by simpa [cell2] using h₂, w2, by simpa [cell2] using hc⟩
 · right; left; exact ⟨by simpa [cell3] using h₁, by simpa [cell3] using h₂, w3, by simpa [cell3] using hc⟩
 · right; right; left; exact ⟨by simpa [cell4] using h₁, by simpa [cell4] using h₂, w4, by simpa [cell4] using hc⟩
 · right; right; right; exact ⟨by simpa [cell5] using h₁, by simpa [cell5] using h₂, w5, by simpa [cell5] using hc⟩
theorem count_closed_width_cover {s : ℝ} (hs : s ∈ Set.Icc (17/500) (43/1000)) : s ∈ Set.Icc cell6.lo cell6.hi ∨ s ∈ Set.Icc cell7.lo cell7.hi ∨ s ∈ Set.Icc cell8.lo cell8.hi ∨ s ∈ Set.Icc cell9.lo cell9.hi ∨ s ∈ Set.Icc cell10.lo cell10.hi ∨ s ∈ Set.Icc cell11.lo cell11.hi ∨ s ∈ Set.Icc cell12.lo cell12.hi ∨ s ∈ Set.Icc cell13.lo cell13.hi ∨ s ∈ Set.Icc cell14.lo cell14.hi := by
 by_cases h0 : s ≤ (9/250:ℝ)
 · left; norm_num [cell6]; constructor <;> linarith [hs.1, hs.2]
 ·
   by_cases h1 : s ≤ (3/80:ℝ)
   · right; left; norm_num [cell7]; constructor <;> linarith [hs.1, hs.2]
   ·
     by_cases h2 : s ≤ (39/1000:ℝ)
     · right; right; left; norm_num [cell8]; constructor <;> linarith [hs.1, hs.2]
     ·
       by_cases h3 : s ≤ (1/25:ℝ)
       · right; right; right; left; norm_num [cell9]; constructor <;> linarith [hs.1, hs.2]
       ·
         by_cases h4 : s ≤ (81/2000:ℝ)
         · right; right; right; right; left; norm_num [cell10]; constructor <;> linarith [hs.1, hs.2]
         ·
           by_cases h5 : s ≤ (41/1000:ℝ)
           · right; right; right; right; right; left; norm_num [cell11]; constructor <;> linarith [hs.1, hs.2]
           ·
             by_cases h6 : s ≤ (83/2000:ℝ)
             · right; right; right; right; right; right; left; norm_num [cell12]; constructor <;> linarith [hs.1, hs.2]
             ·
               by_cases h7 : s ≤ (21/500:ℝ)
               · right; right; right; right; right; right; right; left; norm_num [cell13]; constructor <;> linarith [hs.1, hs.2]
               ·
                 right; right; right; right; right; right; right; right; norm_num [cell14]; constructor <;> linarith [hs.1, hs.2]
theorem count_face_cover {m₁ m₂ s : ℝ} (h₁ : m₁ ∈ Set.Icc (2/5) (11/25)) (h₂ : m₂ ∈ Set.Icc (2/5) (11/25)) (hs : s ∈ Set.Icc (17/500) (43/1000)) (hc : m₁+m₂*1+(906637/250000)*s ≤ (9763743/10000000)) : OnFace cell6 m₁ m₂ s ∨ OnFace cell7 m₁ m₂ s ∨ OnFace cell8 m₁ m₂ s ∨ OnFace cell9 m₁ m₂ s ∨ OnFace cell10 m₁ m₂ s ∨ OnFace cell11 m₁ m₂ s ∨ OnFace cell12 m₁ m₂ s ∨ OnFace cell13 m₁ m₂ s ∨ OnFace cell14 m₁ m₂ s := by
 have hw := count_closed_width_cover hs
 rcases hw with w6 | w7 | w8 | w9 | w10 | w11 | w12 | w13 | w14
 · left; exact ⟨by simpa [cell6] using h₁, by simpa [cell6] using h₂, w6, by simpa [cell6] using hc⟩
 · right; left; exact ⟨by simpa [cell7] using h₁, by simpa [cell7] using h₂, w7, by simpa [cell7] using hc⟩
 · right; right; left; exact ⟨by simpa [cell8] using h₁, by simpa [cell8] using h₂, w8, by simpa [cell8] using hc⟩
 · right; right; right; left; exact ⟨by simpa [cell9] using h₁, by simpa [cell9] using h₂, w9, by simpa [cell9] using hc⟩
 · right; right; right; right; left; exact ⟨by simpa [cell10] using h₁, by simpa [cell10] using h₂, w10, by simpa [cell10] using hc⟩
 · right; right; right; right; right; left; exact ⟨by simpa [cell11] using h₁, by simpa [cell11] using h₂, w11, by simpa [cell11] using hc⟩
 · right; right; right; right; right; right; left; exact ⟨by simpa [cell12] using h₁, by simpa [cell12] using h₂, w12, by simpa [cell12] using hc⟩
 · right; right; right; right; right; right; right; left; exact ⟨by simpa [cell13] using h₁, by simpa [cell13] using h₂, w13, by simpa [cell13] using hc⟩
 · right; right; right; right; right; right; right; right; exact ⟨by simpa [cell14] using h₁, by simpa [cell14] using h₂, w14, by simpa [cell14] using hc⟩
end Record12518109Admission
