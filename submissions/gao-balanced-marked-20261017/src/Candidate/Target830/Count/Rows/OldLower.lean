import Candidate.Target830.Count.Concrete
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count.Certificates
noncomputable section

def old_lower_leaf0_power (δ p : ℝ) : ℝ := (82232563/60000000)*δ^0*p^0 +
  (-17470225776787/20240820000000)*δ^0*p^1 +
  (-268795063/150000000)*δ^1*p^0 +
  (-3025643971787/16867350000000)*δ^1*p^1 +
  (284026781142457/379343328030000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (3697454891/5622450000)*δ^2*p^1 +
  (-767050867/2811225000)*δ^2*p^2 +
  (-1875546532/12644777601)*δ^2*p^3

def old_lower_leaf0_minimum : ℝ := 1297900842158389283/15173733121200000000
def old_lower_leaf0_table : Fin 3 → Fin 4 → ℝ := ![
  ![(82232563/60000000:ℝ), (148975224805379/121444920000000:ℝ), (8219062439287/7590307500000:ℝ), (7602318216787/8096328000000:ℝ)],
  ![(838266071/1200000000:ℝ), (1320083954239999/2428898400000000:ℝ), (9373371585642434627/22760599681800000000:ℝ), (9212155562310007333/30347466242400000000:ℝ)],
  ![(184690441/600000000:ℝ), (246769005228959/1214449200000000:ℝ), (3017526800420867699/22760599681800000000:ℝ), (1297900842158389283/15173733121200000000:ℝ)]]
theorem old_lower_leaf0_lower (i : Fin 3) (j : Fin 4) :
    old_lower_leaf0_minimum ≤ old_lower_leaf0_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_leaf0_minimum,old_lower_leaf0_table]
theorem old_lower_leaf0_identity (δ p : ℝ) :
    old_lower_leaf0_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_lower_leaf0_table
      ((δ-(0))/((3/4)-(0)))
      ((p-(0))/((1/2)-(0))) := by
  norm_num [old_lower_leaf0_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_lower_leaf0_table,Fin.sum_univ_succ]
  ring
theorem old_lower_leaf0_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) : 0 < old_lower_leaf0_power δ p := by
  rw [old_lower_leaf0_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_lower_leaf0_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_lower_leaf0_lower

theorem old_lower_leaf0_binding (δ p : ℝ) :
    old_lower_leaf0_power δ p=(oldJ δ p)*(theta-reserve-rowBase d0 (oldCapacityAt kappaStar d0) δ p)-3*(d0)*(oldN δ p)/4 := by
  norm_num [old_lower_leaf0_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_lower_leaf0_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar d0 (oldCapacityAt kappaStar d0) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_lower_leaf0_binding δ p) (old_lower_leaf0_positive hδ hp)
    have hd : 0 ≤ 3*(d0)/4 := by norm_num [d0,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

theorem old_lower_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar d0 (oldCapacityAt kappaStar d0) δ p ≤ theta-reserve := by
  apply old_lower_leaf0_bound
  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]

end
end OAI.SevenEighths.Target830.Count.Certificates

#print axioms OAI.SevenEighths.Target830.Count.Certificates.old_lower_bound
