import Cycle25.Assembly.Parameters
import OAI.NumberTheory.DirichletL.ParametersSlotLengths
namespace Cycle25.HighParameters
noncomputable section
open scoped BigOperators

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0 < L) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0 < ell j ∧ ell j < L) ∧ (∑j,ell j)=Cycle25.ell := by
  have hscale : 0 < 6*Cycle25.ell := mul_pos (by norm_num) ell_pos
  obtain ⟨N,hN,old,hi,hb,hs⟩ := OAI.SevenEighths.Parameters.exists_distinct_slot_lengths
    (L/(6*Cycle25.ell)) (by positivity)
  refine ⟨N,hN,(fun j=>(6*Cycle25.ell:ℝ)*old j),?_,?_,?_⟩
  · intro j k he
    apply hi
    exact (mul_left_cancel₀ hscale.ne' he)
  · intro j
    constructor
    · exact mul_pos hscale (hb j).1
    · have hh := (hb j).2
      have hc := (lt_div_iff₀ hscale).mp hh
      nlinarith only [hc]
  · rw [←Finset.mul_sum,hs]
    ring

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0 < rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=Cycle25.ell ∧
      (∀j,0 < ell j ∧ dmax*rmin ≤ ell j ∧ ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀j,rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k ≤ dmin*mesh ∧ ell k ≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d ≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end
end Cycle25.HighParameters

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
