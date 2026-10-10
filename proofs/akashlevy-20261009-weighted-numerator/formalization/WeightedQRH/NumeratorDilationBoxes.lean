import WeightedQRH.NumeratorPacketFourth
import WeightedQRH.NumeratorAmplitudeHolder

/-! Finitely many exponent boxes for the actual compactly truncated dilation.
The box count depends on the chosen small width, not on the row scale. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedQRH.Numerator

theorem exponent_boxes_cover (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi) := by
  induction n with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · simpa using ht
    · have hpow : 1 ≤ U^xi := Real.one_le_rpow hU hxi
      have ht1 : t ≤ 1 := by simpa using hupper
      simpa using ht1.trans hpow
  | succ n ih =>
    by_cases hsmall : t ≤ U^((n : ℝ)*xi)
    · obtain ⟨j,hj,hlo,hhi⟩ := ih hsmall
      refine ⟨j,?_,hlo,hhi⟩
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (by omega))
    · refine ⟨n,Finset.mem_range.mpr (by omega),(le_of_lt (lt_of_not_ge hsmall)),?_⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hupper

/-- Compact support bounds every active coefficient dilation by a fixed power of U. -/
theorem active_dilation_upper (U xi L N b Y : ℝ) (n : ℕ)
    (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hL : L ≤ 1) (hN : 0 ≤ N)
    (hcut : N ≤ b*Y) (hY : b*Y ≤ U^((n : ℝ)*xi)) :
    max 1 (L*N) ≤ U^((n : ℝ)*xi) := by
  apply max_le
  · exact Real.one_le_rpow hU (mul_nonneg (Nat.cast_nonneg _) hxi)
  · exact (mul_le_mul_of_nonneg_right hL hN).trans
      (by simpa only [one_mul] using hcut.trans hY)

def dilationBox (U xi : ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  if h : ∃ j ∈ Finset.range (n+1), U^((j : ℝ)*xi) ≤ t ∧ t ≤ U^(((j : ℝ)+1)*xi)
  then Classical.choose h else 0

theorem dilationBox_mem (U xi : ℝ) (n : ℕ) (t : ℝ) :
    dilationBox U xi n t ∈ Finset.range (n+1) := by
  unfold dilationBox
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem dilationBox_spec (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) :
    U^((dilationBox U xi n t : ℝ)*xi) ≤ t ∧
      t ≤ U^(((dilationBox U xi n t : ℝ)+1)*xi) := by
  have he := exponent_boxes_cover U xi hU hxi n t ht hupper
  rw [dilationBox,dif_pos he]
  exact (Classical.choose_spec he).2

theorem dilation_weight_bound (U xi : ℝ) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (n : ℕ) (t rho : ℝ) (ht : 1 ≤ t) (hupper : t ≤ U^((n : ℝ)*xi)) (hrho : 0 ≤ rho) :
    t^(-rho) ≤ U^(-rho*(dilationBox U xi n t : ℝ)*xi) := by
  have hlo := (dilationBox_spec U xi hU hxi n t ht hupper).1
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (U^((dilationBox U xi n t : ℝ)*xi))^(-rho) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU0 _) hlo (neg_nonpos.mpr hrho)
    _ = _ := by rw [←Real.rpow_mul hU0.le]; congr 1; ring

theorem finite_box_partition {κ : Type*} (U xi : ℝ) (n : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) :
    (∑ j ∈ Finset.range (n+1), if dilationBox U xi n (t e) = j then f e else 0) = f e := by
  rw [Finset.sum_eq_single (dilationBox U xi n (t e))]
  · simp
  · intro j hj hne
    simp only [ite_eq_right (Ne.symm hne)]
  · intro hn
    exact False.elim (hn (dilationBox_mem U xi n (t e)))

def boxSeriesTerm {κ : Type*} (U xi : ℝ) (n j : ℕ) (t : κ → ℝ) (f : κ → ℂ)
    (e : κ) : ℂ := if dilationBox U xi n (t e) = j then f e else 0

theorem boxSeries_summable_norm {κ : Type*} (U xi : ℝ) (n j : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    Summable (fun e => ‖boxSeriesTerm U xi n j t f e‖) := by
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro e
  unfold boxSeriesTerm
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f e)

theorem tsum_box_decomposition {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1), ∑' e, boxSeriesTerm U xi n j t f e := by
  rw [←Summable.tsum_finsetSum (fun j hj => (boxSeries_summable_norm U xi n j t f hf).of_norm)]
  apply tsum_congr
  intro e
  exact (finite_box_partition U xi n t f e).symm

theorem norm_tsum_le_boxes {κ : Type*} (U xi : ℝ) (n : ℕ)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    ‖∑' e, f e‖ ≤ ∑ j ∈ Finset.range (n+1), ‖∑' e, boxSeriesTerm U xi n j t f e‖ := by
  rw [tsum_box_decomposition U xi n t f hf]
  exact norm_sum_le _ _

end WeightedQRH.Numerator
