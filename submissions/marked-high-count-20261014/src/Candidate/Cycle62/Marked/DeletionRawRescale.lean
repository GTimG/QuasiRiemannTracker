import Candidate.Cycle62.Marked.DeletionRawLift

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

/-- Rescaling to a core window shrinks only the fixed capacity cutoff;
the full physical slot width and its marked saving are retained. -/
theorem rescaled_marked_power (U d d₀ ρ δ S g cap loss : ℝ)
    (hU : 1≤U) (hd : 0<d) (hd₀ : d₀≤d) (hd1 : d≤1)
    (hg : 0≤g) (hcap : 0≤cap) (hloss : 0≤loss) :
    (U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss) ≤
      U^(δ*S-g*min S (cap*d₀)+loss)*(U^d)^ρ := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hmin : d*min (S/d) cap = min S (cap*d) := by
    rw [mul_min_of_nonneg _ _ hd.le,mul_div_cancel₀ _ hd.ne',mul_comm d cap]
  have hminmono : min S (cap*d₀)≤min S (cap*d) :=
    min_le_min_left S (mul_le_mul_of_nonneg_left hd₀ hcap)
  have hgm := mul_le_mul_of_nonneg_left hminmono hg
  have hdl := mul_le_of_le_one_left hloss hd1
  rw [←Real.rpow_mul hUp.le,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have he : d*(δ*(S/d))=δ*S := by field_simp
  calc
    _ = d*ρ+δ*S-g*(d*min (S/d) cap)+d*loss := by rw [←he];ring
    _ ≤ _ := by rw [hmin];nlinarith

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.core_window_scale
#print axioms OAI.SevenEighths.Deletion26.rescaled_marked_power
