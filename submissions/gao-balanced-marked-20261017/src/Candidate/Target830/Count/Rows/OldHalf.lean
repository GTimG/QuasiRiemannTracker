import Candidate.Target830.Count.Concrete
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count.Certificates
noncomputable section

def old_half_leaf0_power (δ p : ℝ) : ℝ := (1478281/2400000)*δ^0*p^0 +
  (-314059320169/809632800000)*δ^0*p^1 +
  (-172213/187500)*δ^1*p^0 +
  (82621800031/674694000000)*δ^1*p^1 +
  (310886375431151/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-78169687111/337347000000)*δ^2*p^1 +
  (1128812399/8433675000)*δ^2*p^2 +
  (-3911657096/37934332803)*δ^2*p^3

def old_half_leaf0_minimum : ℝ := 70333791338843051/1213898649696000000
def old_half_leaf0_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1478281/2400000:ℝ), (2678102642873/4857796800000:ℝ), (147752707669/303612300000:ℝ), (136665600169/323853120000:ℝ)],
  ![(3258293/12000000:ℝ), (20842618645003/97155936000000:ℝ), (302383509315463883/1820847974544000000:ℝ), (51042088903813687/404632883232000000:ℝ)],
  ![(2500181/12000000:ℝ), (13337709880549/97155936000000:ℝ), (10871951253316499/121389864969600000:ℝ), (70333791338843051/1213898649696000000:ℝ)]]
theorem old_half_leaf0_lower (i : Fin 3) (j : Fin 4) :
    old_half_leaf0_minimum ≤ old_half_leaf0_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_leaf0_minimum,old_half_leaf0_table]
theorem old_half_leaf0_identity (δ p : ℝ) :
    old_half_leaf0_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_half_leaf0_table
      ((δ-(0))/((3/4)-(0)))
      ((p-(0))/((1/2)-(0))) := by
  norm_num [old_half_leaf0_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_half_leaf0_table,Fin.sum_univ_succ]
  ring
theorem old_half_leaf0_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) : 0 < old_half_leaf0_power δ p := by
  rw [old_half_leaf0_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_half_leaf0_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_half_leaf0_lower

theorem old_half_leaf0_binding (δ p : ℝ) :
    old_half_leaf0_power δ p=(oldJ δ p)*(theta-reserve-rowBase y (oldCapacityAt kappaStar y) δ p)-3*(y)*(oldN δ p)/4 := by
  norm_num [old_half_leaf0_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_half_leaf0_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar y (oldCapacityAt kappaStar y) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_half_leaf0_binding δ p) (old_half_leaf0_positive hδ hp)
    have hd : 0 ≤ 3*(y)/4 := by norm_num [y,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

theorem old_half_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar y (oldCapacityAt kappaStar y) δ p ≤ theta-reserve := by
  apply old_half_leaf0_bound
  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]

end
end OAI.SevenEighths.Target830.Count.Certificates

#print axioms OAI.SevenEighths.Target830.Count.Certificates.old_half_bound
