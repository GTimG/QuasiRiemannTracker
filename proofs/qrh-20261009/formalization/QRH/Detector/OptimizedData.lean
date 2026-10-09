import QRH.Detector.FineSmallData
import QRH.Detector.DynamicMomentInput

/-! Constructive parameter and slot choice; no analytic estimate is a field.
The old data's unused slot presentation is retained for upstream compatibility,
while the actual physical slots below have total ell. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.QRHParameters
open Parameters QRHDynamicMomentInput

def optimizedLengths {gap:ℝ} (D:HighData gap) (j:Fin D.N):ℝ:=(6*QRH.ell)*D.ell j

lemma optimizedLengths_sum {gap:ℝ} (D:HighData gap):∑j,optimizedLengths D j=QRH.ell:=by
  simp only [optimizedLengths,←Finset.mul_sum,D.slots_sum]
  ring

lemma optimizedLengths_pos {gap:ℝ} (D:HighData gap) (j:Fin D.N):0<optimizedLengths D j:=by
  have he:0<QRH.ell:=by norm_num [QRH.ell,QRH.theta]
  exact mul_pos (by positivity) (D.slots_bounds j).1

lemma optimizedLengths_injective {gap:ℝ} (D:HighData gap):Function.Injective (optimizedLengths D):=by
  have he:6*QRH.ell≠0:=by norm_num [QRH.ell,QRH.theta]
  intro j k h
  exact D.slots_injective (mul_left_cancel₀ he h)

lemma optimizedLengths_lower {gap:ℝ} (D:HighData gap) (j:Fin D.N):
    (7/8:ℝ)*D.rmin≤optimizedLengths D j:=by
  have he:1≤6*QRH.ell:=by norm_num [QRH.ell,QRH.theta]
  have hp:=mul_le_mul_of_nonneg_right he (D.slots_bounds j).1.le
  dsimp [optimizedLengths]
  linarith [(D.slots_bounds j).2.1]

/-- The actual optimized slots and every analytic small parameter are chosen
before any height degree. A height may subsequently be chosen by D.height_choice. -/
theorem exists_optimized_data (gap:ℝ) (hgap:0<gap):
    ∃D:HighData gap,
      D.t<(1/10000000000000000:ℝ) ∧
      (∀j,optimizedLengths D j≤D.t/200) ∧
      (∀j,optimizedLengths D j≤dynamicMesh D.t/200) ∧
      2000*D.ε≤D.t ∧ 2000*D.e≤D.t ∧ ((D.N:ℝ)+8)*D.eps≤D.t:=by
  have he:0<6*QRH.ell:=by norm_num [QRH.ell,QRH.theta]
  obtain ⟨D,hfine,ht,hε,he',heps⟩:=exists_high_data_fine_small gap (1/10000000000000000) hgap
    (by norm_num) (fun t=>min t (dynamicMesh t)/(6*QRH.ell))
    (fun t ht=>div_pos (lt_min ht (dynamicMesh_pos t ht)) he)
  have hsmall (j:Fin D.N):optimizedLengths D j≤min D.t (dynamicMesh D.t)/200:=by
    have hj:=mul_le_mul_of_nonneg_left (hfine j) he.le
    have hid:(6*QRH.ell)*(min D.t (dynamicMesh D.t)/(6*QRH.ell)/200)=
        min D.t (dynamicMesh D.t)/200:=by
      have hellne:QRH.ell≠0:=by norm_num [QRH.ell,QRH.theta]
      field_simp
    exact hj.trans_eq hid
  refine ⟨D,ht,?_,?_,hε,he',heps⟩
  · intro j
    exact (hsmall j).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  · intro j
    exact (hsmall j).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

lemma optimized_count_budget {gap:ℝ} (D:HighData gap):159*D.ε+D.t+D.t+7*D.t≤1/32:=D.count_budget

lemma optimized_central_budget {gap:ℝ} (D:HighData gap)
    (ht:D.t<(1/10000000000000000:ℝ)) (hε:2000*D.ε≤D.t)
    (he:2000*D.e≤D.t) (heps:((D.N:ℝ)+8)*D.eps≤D.t)
    (J:ℕ)(τ:ℝ)(hτ:0<τ)(hheight:2*τ*(1+(J:ℝ))≤D.t):
    QRH.h*(159*D.ε+D.t+D.t+7*D.t)+2*QRH.zeta+(3/2)*(2*D.t)+
      (26*D.e+(D.N+8)*D.eps+D.t+D.t*QRH.ell)+
      (D.t+2*τ+2*τ*(J:ℝ))+D.sigma≤(1/1000000000000:ℝ):=by
  have hh:QRH.h≤1:=by norm_num [QRH.h,QRH.lx,QRH.M,QRH.ell,QRH.b,QRH.theta]
  have hel:QRH.ell≤1:=by norm_num [QRH.ell,QRH.theta]
  have hε0:=D.epsilon_pos
  have ht0:=D.t_pos
  have h1:=mul_le_mul_of_nonneg_right hh
    (show 0≤159*D.ε+D.t+D.t+7*D.t by positivity)
  have h2:=mul_le_mul_of_nonneg_left hel D.t_pos.le
  have hs:=D.high_saving
  norm_num [QRH.zeta] at *
  nlinarith [D.epsilon_pos,D.e_pos,D.t_pos]

end SevenEighths.QRHParameters
end
end OAI
