import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionRawLift
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators

/-- A small sixth root leaves a polynomially large core window. -/
theorem small_root_window (U N κ : ℝ) (hU : 1<U) (hN : 1≤N)
    (hcap : N≤U^κ) : U^(1-6*κ)≤U/N^6 ∧ U/N^6≤U := by
  have hUp : 0<U := zero_lt_one.trans hU
  have hNp : 0<N := zero_lt_one.trans_le hN
  constructor
  · have hpow : N^6≤U^(6*κ) := by
      calc
        _≤(U^κ)^6 := pow_le_pow_left₀ hNp.le hcap 6
        _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le];congr 1;ring
    calc
      _ = U/U^(6*κ) := by rw [Real.rpow_sub hUp,Real.rpow_one]
      _ ≤ U/N^6 := div_le_div_of_nonneg_left hUp.le (pow_pos hNp _) hpow
  · exact (div_le_self hUp.le (one_le_pow₀ hN))

/-- Logarithmic rescaling preserves every literal slot length. -/
theorem core_window_scale (U N κ : ℝ) (hU : 1<U) (hN : 1≤N)
    (hκ : κ<1/6) (hcap : N≤U^κ) :
    ∃d : ℝ,0<d ∧ 1-6*κ≤d ∧ d≤1 ∧ U^d=U/N^6 ∧
      ∀w : ℝ,(U/N^6)^(w/d)=U^w := by
  have hUp : 0<U := zero_lt_one.trans hU
  have hNp : 0<N := zero_lt_one.trans_le hN
  let Y := U/N^6
  let d := Real.log Y/Real.log U
  have hwindow := small_root_window U N κ hU hN hcap
  have hY : 1<Y := (Real.one_lt_rpow hU (by linarith)).trans_le hwindow.1
  have hYp : 0<Y := zero_lt_one.trans hY
  have hlogU : 0<Real.log U := Real.log_pos hU
  have hd : 0<d := div_pos (Real.log_pos hY) hlogU
  have hbase : U^d=Y := by
    dsimp [d]
    rw [Real.rpow_def_of_pos hUp]
    rw [mul_div_cancel₀ _ hlogU.ne']
    exact Real.exp_log hYp
  refine ⟨d,hd,?_,?_,hbase,?_⟩
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    rw [hbase]
    exact hwindow.1
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    rw [hbase,Real.rpow_one]
    exact hwindow.2
  · intro w
    change Y^(w/d)=U^w
    rw [←hbase,←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hd.ne']

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
