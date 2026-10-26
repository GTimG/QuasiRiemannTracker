/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.RoundedRows3Part0
import Candidate.Uneven.RoundedRows3Part1
import Candidate.Uneven.RoundedRows3Part2

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem complement_row_3 {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hc : ¬ ((117/256:ℝ) ≤ d ∧ d ≤ 63/128 ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2))
    : ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row 3 i d p ≤ theta-reserve := by
  by_cases hD6 : d ≤ (9087/20000:ℝ)
  · by_cases hD3 : d ≤ (459/1024:ℝ)
    · by_cases hD1 : d ≤ (111/256:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_0 hdcell hpcell)⟩
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_1 hdcell hpcell)⟩
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_2 hdcell hpcell)⟩
          · have hdcell : (0/1:ℝ) ≤ d ∧ d ≤ (111/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hP2,hP3]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_3 hdcell hpcell)⟩
      · by_cases hD2 : d ≤ (57/128:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_4 hdcell hpcell)⟩
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_5 hdcell hpcell)⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_6 hdcell hpcell)⟩
            · have hdcell : (111/256:ℝ) ≤ d ∧ d ≤ (57/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hav : available 5 d p := by
                unfold available
                refine Or.inr (Or.inl (?_))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨5,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_7 hdcell hpcell)⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_8 hdcell hpcell)⟩
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_9 hdcell hpcell)⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hav : available 5 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inl (?_)))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨5,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_10 hdcell hpcell)⟩
            · have hdcell : (57/128:ℝ) ≤ d ∧ d ≤ (459/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD1,hD2,hP2,hP3]
              have hav : available 2 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inr (Or.inl (?_))))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨2,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_11 hdcell hpcell)⟩
    · by_cases hD4 : d ≤ (231/512:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_12 hdcell hpcell)⟩
          · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_13 hdcell hpcell)⟩
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP3]
            have hav : available 2 d p := by
              unfold available
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))
              refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            exact ⟨2,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_14 hdcell hpcell)⟩
          · have hdcell : (459/1024:ℝ) ≤ d ∧ d ≤ (231/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hP2,hP3]
            have hav : available 2 d p := by
              unfold available
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))
              refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            exact ⟨2,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_15 hdcell hpcell)⟩
      · by_cases hD5 : d ≤ (465/1024:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_16 hdcell hpcell)⟩
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_17 hdcell hpcell)⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hav : available 1 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_))))))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨1,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_18 hdcell hpcell)⟩
            · have hdcell : (231/512:ℝ) ≤ d ∧ d ≤ (465/1024:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hav : available 1 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_))))))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨1,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_19 hdcell hpcell)⟩
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (9087/20000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_20 hdcell hpcell)⟩
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (9087/20000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_21 hdcell hpcell)⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (9087/20000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hav : available 3 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨3,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_22 hdcell hpcell)⟩
            · have hdcell : (465/1024:ℝ) ≤ d ∧ d ≤ (9087/20000:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD3,hD4,hD5,hP2,hP3]
              have hav : available 3 d p := by
                unfold available
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))))
                refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
              exact ⟨3,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_23 hdcell hpcell)⟩
  · by_cases hD9 : d ≤ (15/32:ℝ)
    · by_cases hD7 : d ≤ (117/256:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_24 hdcell hpcell)⟩
          · have hdcell : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_25 hdcell hpcell)⟩
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP3]
            have hav : available 3 d p := by
              unfold available
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))))
              refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            exact ⟨3,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_26 hdcell hpcell)⟩
          · have hdcell : (9087/20000:ℝ) ≤ d ∧ d ≤ (117/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hP2,hP3]
            have hav : available 3 d p := by
              unfold available
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (?_)))))))
              refine ⟨rfl,?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            exact ⟨3,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_27 hdcell hpcell)⟩
      · by_cases hD8 : d ≤ (237/512:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_28 hdcell hpcell)⟩
            · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            · have hdcell : (117/256:ℝ) ≤ d ∧ d ≤ (237/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_29 hdcell hpcell)⟩
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP1]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            · have hdcell : (237/512:ℝ) ≤ d ∧ d ≤ (15/32:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD7,hD8,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
    · by_cases hD10 : d ≤ (123/256:ℝ)
      · by_cases hP2 : p ≤ (127/256:ℝ)
        · by_cases hP1 : p ≤ (63/128:ℝ)
          · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP1]
            have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP1]
            have hav : available 0 d p := by
              unfold available
              exact Or.inl rfl
            exact ⟨0,by norm_num,hav,row_bound_of_gap
              (denominator_pos (by norm_num) hd hp) (gap_3_30 hdcell hpcell)⟩
          · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP1]
            have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP1]
            exfalso
            apply hc
            refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
        · by_cases hP3 : p ≤ (255/512:ℝ)
          · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP3]
            have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP3]
            exfalso
            apply hc
            refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
          · have hdcell : (15/32:ℝ) ≤ d ∧ d ≤ (123/256:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP3]
            have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
              constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hP2,hP3]
            exfalso
            apply hc
            refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
      · by_cases hD11 : d ≤ (63/128:ℝ)
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_31 hdcell hpcell)⟩
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
            · have hdcell : (123/256:ℝ) ≤ d ∧ d ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              exfalso
              apply hc
              refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hdcell.1,hdcell.2,hpcell.1,hpcell.2]
        · by_cases hP2 : p ≤ (127/256:ℝ)
          · by_cases hP1 : p ≤ (63/128:ℝ)
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hpcell : (0/1:ℝ) ≤ p ∧ p ≤ (63/128:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_32 hdcell hpcell)⟩
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hpcell : (63/128:ℝ) ≤ p ∧ p ≤ (127/256:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP1]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_33 hdcell hpcell)⟩
          · by_cases hP3 : p ≤ (255/512:ℝ)
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hpcell : (127/256:ℝ) ≤ p ∧ p ≤ (255/512:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_34 hdcell hpcell)⟩
            · have hdcell : (63/128:ℝ) ≤ d ∧ d ≤ (3/4:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hpcell : (255/512:ℝ) ≤ p ∧ p ≤ (1/2:ℝ) := by
                constructor <;> linarith only [hd.1,hd.2,hp.1,hp.2,hD6,hD9,hD10,hD11,hP2,hP3]
              have hav : available 0 d p := by
                unfold available
                exact Or.inl rfl
              exact ⟨0,by norm_num,hav,row_bound_of_gap
                (denominator_pos (by norm_num) hd hp) (gap_3_35 hdcell hpcell)⟩

end Sil.Uneven.RoundedRows
