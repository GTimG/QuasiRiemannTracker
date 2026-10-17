import Candidate.Target830.Count.Concrete
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count.Certificates
noncomputable section

def old_junction_leaf0_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf0_minimum : ℝ := 51072338113322323/24277972993920000000
def old_junction_leaf0_table : Fin 3 → Fin 4 → ℝ := ![
  ![(794177/12000000:ℝ), (1438757261041/24288984000000:ℝ), (79377196973/1518061500000:ℝ), (73420869473/1619265600000:ℝ)],
  ![(3190387/240000000:ℝ), (10938334144291/971559360000000:ℝ), (180280333244242781/18208479745440000000:ℝ), (37308674687504119/4046328832320000000:ℝ)],
  ![(3686117/120000000:ℝ), (28590441721349/1943118720000000:ℝ), (72504754402400303/12138986496960000000:ℝ), (51072338113322323/24277972993920000000:ℝ)]]
theorem old_junction_leaf0_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf0_minimum ≤ old_junction_leaf0_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf0_minimum,old_junction_leaf0_table]
theorem old_junction_leaf0_identity (δ p : ℝ) :
    old_junction_leaf0_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf0_table
      ((δ-(0))/((3/8)-(0)))
      ((p-(0))/((1/2)-(0))) := by
  norm_num [old_junction_leaf0_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf0_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf0_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) : 0 < old_junction_leaf0_power δ p := by
  rw [old_junction_leaf0_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf0_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf0_lower

theorem old_junction_leaf0_binding (δ p : ℝ) :
    old_junction_leaf0_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf0_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf0_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf0_binding δ p) (old_junction_leaf0_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def old_junction_leaf1_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf1_minimum : ℝ := 38391974439821563/3237063065856000000
def old_junction_leaf1_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3686117/120000000:ℝ), (88278466278101/3886237440000000:ℝ), (601953225619723271/36416959490880000000:ℝ), (38391974439821563/3237063065856000000:ℝ)],
  ![(11554081/240000000:ℝ), (32212461167171/971559360000000:ℝ), (393870146511865307/18208479745440000000:ℝ), (31491581520083749/2427797299392000000:ℝ)],
  ![(2038183/15000000:ℝ), (101496111021683/971559360000000:ℝ), (241692150520001791/3034746624240000000:ℝ), (146168624096634503/2427797299392000000:ℝ)]]
theorem old_junction_leaf1_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf1_minimum ≤ old_junction_leaf1_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf1_minimum,old_junction_leaf1_table]
theorem old_junction_leaf1_identity (δ p : ℝ) :
    old_junction_leaf1_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf1_table
      ((δ-(3/8))/((3/4)-(3/8)))
      ((p-(0))/((1/4)-(0))) := by
  norm_num [old_junction_leaf1_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf1_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf1_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) : 0 < old_junction_leaf1_power δ p := by
  rw [old_junction_leaf1_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf1_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf1_lower

theorem old_junction_leaf1_binding (δ p : ℝ) :
    old_junction_leaf1_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf1_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf1_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf1_binding δ p) (old_junction_leaf1_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def old_junction_leaf2_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf2_minimum : ℝ := 810415034312531/202316441616000000
def old_junction_leaf2_table : Fin 3 → Fin 4 → ℝ := ![
  ![(38391974439821563/3237063065856000000:ℝ), (2775103646897017921/291335675927040000000:ℝ), (2205406992378217147/291335675927040000000:ℝ), (48202804805903843/8092657664640000000:ℝ)],
  ![(48228449879959937/3884475679027200000:ℝ), (39204645543830891/4316084087808000000:ℝ), (734017970074840639/116534270370816000000:ℝ), (810415034312531/202316441616000000:ℝ)],
  ![(951783071866672693/38844756790272000000:ℝ), (22519279762371447221/1165342703708160000000:ℝ), (17405388998432734927/1165342703708160000000:ℝ), (364273305473584553/32370630658560000000:ℝ)]]
theorem old_junction_leaf2_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf2_minimum ≤ old_junction_leaf2_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf2_minimum,old_junction_leaf2_table]
theorem old_junction_leaf2_identity (δ p : ℝ) :
    old_junction_leaf2_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf2_table
      ((δ-(3/8))/((9/16)-(3/8)))
      ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [old_junction_leaf2_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf2_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf2_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) : 0 < old_junction_leaf2_power δ p := by
  rw [old_junction_leaf2_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf2_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf2_lower

theorem old_junction_leaf2_binding (δ p : ℝ) :
    old_junction_leaf2_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf2_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf2_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf2_binding δ p) (old_junction_leaf2_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def old_junction_leaf3_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf3_minimum : ℝ := 31509642441586901/97111891975680000000
def old_junction_leaf3_table : Fin 3 → Fin 4 → ℝ := ![
  ![(48202804805903843/8092657664640000000:ℝ), (1265194953646859549/291335675927040000000:ℝ), (11929060925790703/3884475679027200000:ℝ), (51072338113322323/24277972993920000000:ℝ)],
  ![(80619406178405083/16185315329280000000:ℝ), (3528290654559694463/1165342703708160000000:ℝ), (69504323242772803/46613708148326400000:ℝ), (31509642441586901/97111891975680000000:ℝ)],
  ![(163283467135441969/25896504526848000000:ℝ), (3574934359863338509/932274162966528000000:ℝ), (1744958760675350509/932274162966528000000:ℝ), (9273450117692969/25896504526848000000:ℝ)]]
theorem old_junction_leaf3_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf3_minimum ≤ old_junction_leaf3_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf3_minimum,old_junction_leaf3_table]
theorem old_junction_leaf3_identity (δ p : ℝ) :
    old_junction_leaf3_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf3_table
      ((δ-(3/8))/((15/32)-(3/8)))
      ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [old_junction_leaf3_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf3_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf3_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) : 0 < old_junction_leaf3_power δ p := by
  rw [old_junction_leaf3_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf3_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf3_lower

theorem old_junction_leaf3_binding (δ p : ℝ) :
    old_junction_leaf3_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf3_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf3_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf3_binding δ p) (old_junction_leaf3_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def old_junction_leaf4_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf4_minimum : ℝ := 9273450117692969/25896504526848000000
def old_junction_leaf4_table : Fin 3 → Fin 4 → ℝ := ![
  ![(163283467135441969/25896504526848000000:ℝ), (3574934359863338509/932274162966528000000:ℝ), (1744958760675350509/932274162966528000000:ℝ), (9273450117692969/25896504526848000000:ℝ)],
  ![(493939710963589513/64741261317120000000:ℝ), (10818090490197303619/2330685407416320000000:ℝ), (349971842749207493/155379027161088000000:ℝ), (76082466882220733/194223783951360000000:ℝ)],
  ![(364273305473584553/32370630658560000000:ℝ), (8822288995665352889/1165342703708160000000:ℝ), (1070615951367336629/233068540741632000000:ℝ), (217352534452336223/97111891975680000000:ℝ)]]
theorem old_junction_leaf4_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf4_minimum ≤ old_junction_leaf4_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf4_minimum,old_junction_leaf4_table]
theorem old_junction_leaf4_identity (δ p : ℝ) :
    old_junction_leaf4_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf4_table
      ((δ-(15/32))/((9/16)-(15/32)))
      ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [old_junction_leaf4_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf4_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf4_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) : 0 < old_junction_leaf4_power δ p := by
  rw [old_junction_leaf4_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf4_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf4_lower

theorem old_junction_leaf4_binding (δ p : ℝ) :
    old_junction_leaf4_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf4_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf4_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf4_binding δ p) (old_junction_leaf4_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def old_junction_leaf5_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (530223191527/3373470000000)*δ^1*p^1 +
  (49316635882051/1138029984090000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-271761844241/337347000000)*δ^2*p^1 +
  (4252499899/8433675000)*δ^2*p^2 +
  (-5161132096/37934332803)*δ^2*p^3

def old_junction_leaf5_minimum : ℝ := 217352534452336223/97111891975680000000
def old_junction_leaf5_table : Fin 3 → Fin 4 → ℝ := ![
  ![(951783071866672693/38844756790272000000:ℝ), (4121266842185678413/291335675927040000000:ℝ), (4048964550122665807/582671351854080000000:ℝ), (217352534452336223/97111891975680000000:ℝ)],
  ![(4935005711575507/134877627744000000:ℝ), (820880034618897727/36416959490880000000:ℝ), (153204391883816863/12138986496960000000:ℝ), (17999223014837123/3034746624240000000:ℝ)],
  ![(146168624096634503/2427797299392000000:ℝ), (247458819443168933/6069493248480000000:ℝ), (973272950263728101/36416959490880000000:ℝ), (11380415003771501/674388138720000000:ℝ)]]
theorem old_junction_leaf5_lower (i : Fin 3) (j : Fin 4) :
    old_junction_leaf5_minimum ≤ old_junction_leaf5_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_leaf5_minimum,old_junction_leaf5_table]
theorem old_junction_leaf5_identity (δ p : ℝ) :
    old_junction_leaf5_power δ p=Cycle63.Arithmetic.Bernstein.tensor old_junction_leaf5_table
      ((δ-(9/16))/((3/4)-(9/16)))
      ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [old_junction_leaf5_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    old_junction_leaf5_table,Fin.sum_univ_succ]
  ring
theorem old_junction_leaf5_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) : 0 < old_junction_leaf5_power δ p := by
  rw [old_junction_leaf5_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [old_junction_leaf5_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) old_junction_leaf5_lower

theorem old_junction_leaf5_binding (δ p : ℝ) :
    old_junction_leaf5_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (oldCapacityAt kappaStar dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [old_junction_leaf5_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem old_junction_leaf5_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (old_junction_leaf5_binding δ p) (old_junction_leaf5_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

theorem old_junction_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dMinus (oldCapacityAt kappaStar dMinus) δ p ≤ theta-reserve := by
  by_cases h1 : δ ≤ (3/8:ℝ)
  ·
    apply old_junction_leaf0_bound
    all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  ·
    by_cases h2 : p ≤ (1/4:ℝ)
    ·
      apply old_junction_leaf1_bound
      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
    ·
      by_cases h3 : δ ≤ (9/16:ℝ)
      ·
        by_cases h4 : p ≤ (3/8:ℝ)
        ·
          apply old_junction_leaf2_bound
          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
        ·
          by_cases h5 : δ ≤ (15/32:ℝ)
          ·
            apply old_junction_leaf3_bound
            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
          ·
            apply old_junction_leaf4_bound
            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
      ·
        apply old_junction_leaf5_bound
        all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]

end
end OAI.SevenEighths.Target830.Count.Certificates

#print axioms OAI.SevenEighths.Target830.Count.Certificates.old_junction_bound
