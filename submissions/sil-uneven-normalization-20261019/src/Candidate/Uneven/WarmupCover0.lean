/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.WarmupRows0Part0
import Candidate.Uneven.WarmupRows0Part1
import Candidate.Uneven.WarmupRows0Part2
import Candidate.Uneven.WarmupRows0Part3

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

theorem full_row_0 {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    : ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row 0 i d p ≤ theta-reserve := by
  by_cases hD7 : d ≤ (117/256:ℝ)
  · by_cases hD3 : d ≤ (459/1024:ℝ)
    · by_cases hD1 : d ≤ (111/256:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_0 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_1 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_2 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_3 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
      · by_cases hD2 : d ≤ (57/128:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_4 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_5 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_6 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_7 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_8 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_9 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_10 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD1,hD2,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_11 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
    · by_cases hD5 : d ≤ (465/1024:ℝ)
      · by_cases hD4 : d ≤ (231/512:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_12 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_13 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_14 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_15 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_16 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_17 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_18 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD4,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_19 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
      · by_cases hD6 : d ≤ (4543/10000:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (4543/10000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_20 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (4543/10000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_21 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (4543/10000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_22 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (4543/10000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_23 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_24 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_25 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_26 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (4543/10000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD3,hD5,hD6,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_27 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
  · by_cases hD10 : d ≤ (477/1024:ℝ)
    · by_cases hD8 : d ≤ (237/512:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_28 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_29 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_30 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_0_31 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
      · by_cases hD9 : d ≤ (951/2048:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (951/2048:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_32 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (951/2048:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_33 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (951/2048:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_34 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (951/2048:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_35 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (951/2048:ℝ) ≤ d ∧ d ≤ (477/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_32 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (951/2048:ℝ) ≤ d ∧ d ≤ (477/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_33 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (951/2048:ℝ) ≤ d ∧ d ≤ (477/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_34 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (951/2048:ℝ) ≤ d ∧ d ≤ (477/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD8,hD9,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_35 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
    · by_cases hD12 : d ≤ (123/256:ℝ)
      · by_cases hD11 : d ≤ (15/32:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (477/1024:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_32 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (477/1024:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_33 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (477/1024:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_34 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (477/1024:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_35 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_36 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_37 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_38 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_39 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
      · by_cases hD13 : d ≤ (63/128:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_40 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_41 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_42 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_43 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_44 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_45 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_46 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD7,hD10,hD12,hD13,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_0_47 (by constructor <;> linarith only [hdcell.1,hdcell.2]) (by constructor <;> linarith only [hpcell.1,hpcell.2]))⟩

end Sil.Uneven.WarmupRows
