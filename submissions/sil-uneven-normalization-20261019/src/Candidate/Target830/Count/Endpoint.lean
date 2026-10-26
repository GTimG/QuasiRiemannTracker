import Candidate.Target830.Count.Concrete
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
import Candidate.Target830.Count.Rows.OldLower
import Candidate.Target830.Count.Rows.OldHalf
import Candidate.Target830.Count.Rows.OldJunction
import Candidate.Target830.Count.Rows.Top

/- Original module: Candidate.Target830.Count.Rows.NewJunction. -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count.Certificates
noncomputable section

def new_junction_leaf0_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf0_minimum : ℝ := 111723546499358065117/49175478301812480000000
def new_junction_leaf0_table : Fin 3 → Fin 4 → ℝ := ![
  ![(794177/12000000:ℝ), (1438757261041/24288984000000:ℝ), (79377196973/1518061500000:ℝ), (73420869473/1619265600000:ℝ)],
  ![(3190387/240000000:ℝ), (208664569167041079533/18440804363179680000000:ℝ), (737387217226881290653/73763217452718720000000:ℝ), (229580621168893248833/24587739150906240000000:ℝ)],
  ![(3686117/120000000:ℝ), (273114080402914459271/18440804363179680000000:ℝ), (903129337962869378117/147526434905437440000000:ℝ), (111723546499358065117/49175478301812480000000:ℝ)]]
theorem new_junction_leaf0_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf0_minimum ≤ new_junction_leaf0_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf0_minimum,new_junction_leaf0_table]
theorem new_junction_leaf0_identity (δ p : ℝ) :
    new_junction_leaf0_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf0_table
      ((δ-(0))/((3/8)-(0)))
      ((p-(0))/((1/2)-(0))) := by
  norm_num [new_junction_leaf0_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf0_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf0_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) : 0 < new_junction_leaf0_power δ p := by
  rw [new_junction_leaf0_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf0_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf0_lower

theorem new_junction_leaf0_binding (δ p : ℝ) :
    new_junction_leaf0_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf0_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf0_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf0_binding δ p) (new_junction_leaf0_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def new_junction_leaf1_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf1_minimum : ℝ := 471032024894756072857/39340382641449984000000
def new_junction_leaf1_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3686117/120000000:ℝ), (839572100876171063459/36881608726359360000000:ℝ), (9804618788195553559957/590105739621749760000000:ℝ), (471032024894756072857/39340382641449984000000:ℝ)],
  ![(11554081/240000000:ℝ), (1225340872127668840151/36881608726359360000000:ℝ), (802169996975226850513/36881608726359360000000:ℝ), (32273030665918069933/2458773915090624000000:ℝ)],
  ![(2038183/15000000:ℝ), (963963538130767153217/9220402181589840000000:ℝ), (11768825245720063614811/147526434905437440000000:ℝ), (593758592063644053319/9835095660362496000000:ℝ)]]
theorem new_junction_leaf1_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf1_minimum ≤ new_junction_leaf1_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf1_minimum,new_junction_leaf1_table]
theorem new_junction_leaf1_identity (δ p : ℝ) :
    new_junction_leaf1_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf1_table
      ((δ-(3/8))/((3/4)-(3/8)))
      ((p-(0))/((1/4)-(0))) := by
  norm_num [new_junction_leaf1_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf1_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf1_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) : 0 < new_junction_leaf1_power δ p := by
  rw [new_junction_leaf1_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf1_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf1_lower

theorem new_junction_leaf1_binding (δ p : ℝ) :
    new_junction_leaf1_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf1_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf1_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf1_binding δ p) (new_junction_leaf1_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def new_junction_leaf2_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf2_minimum : ℝ := 17532000579871955503/4196307481754664960000
def new_junction_leaf2_table : Fin 3 → Fin 4 → ℝ := ![
  ![(471032024894756072857/39340382641449984000000:ℝ), (711988895754279357413/73763217452718720000000:ℝ), (18194764245637485491297/2360422958486999040000000:ℝ), (1600832704006704732907/262269217609666560000000:ℝ)],
  ![(197480103109889038357/15736153056579993600000:ℝ), (272421055749073130777/29505286981087488000000:ℝ), (6100328945688288067949/944169183394799616000000:ℝ), (17532000579871955503/4196307481754664960000:ℝ)],
  ![(3878803374458710523989/157361530565799936000000:ℝ), (5749799511022431646493/295052869810874880000000:ℝ), (142680025468700755030877/9441691833947996160000000:ℝ), (11999716966259057670127/1049076870438666240000000:ℝ)]]
theorem new_junction_leaf2_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf2_minimum ≤ new_junction_leaf2_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf2_minimum,new_junction_leaf2_table]
theorem new_junction_leaf2_identity (δ p : ℝ) :
    new_junction_leaf2_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf2_table
      ((δ-(3/8))/((9/16)-(3/8)))
      ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [new_junction_leaf2_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf2_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf2_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) : 0 < new_junction_leaf2_power δ p := by
  rw [new_junction_leaf2_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf2_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf2_lower

theorem new_junction_leaf2_binding (δ p : ℝ) :
    new_junction_leaf2_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf2_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf2_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf2_binding δ p) (new_junction_leaf2_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def new_junction_leaf3_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf3_minimum : ℝ := 99456490159003827919/196701913207249920000000
def new_junction_leaf3_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1600832704006704732907/262269217609666560000000:ℝ), (10620224426483199701029/2360422958486999040000000:ℝ), (190864125645709196417/59010573962174976000000:ℝ), (111723546499358065117/49175478301812480000000:ℝ)],
  ![(5393165480497403903689/1049076870438666240000000:ℝ), (30185805429236858944063/9441691833947996160000000:ℝ), (78719613335832375211/47208459169739980800000:ℝ), (99456490159003827919/196701913207249920000000:ℝ)],
  ![(5433809614444370870651/839261496350932992000000:ℝ), (30315440786995384000709/7553353467158396928000000:ℝ), (1942518095714832435773/944169183394799616000000:ℝ), (86238936573663845933/157361530565799936000000:ℝ)]]
theorem new_junction_leaf3_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf3_minimum ≤ new_junction_leaf3_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf3_minimum,new_junction_leaf3_table]
theorem new_junction_leaf3_identity (δ p : ℝ) :
    new_junction_leaf3_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf3_table
      ((δ-(3/8))/((15/32)-(3/8)))
      ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [new_junction_leaf3_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf3_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf3_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) : 0 < new_junction_leaf3_power δ p := by
  rw [new_junction_leaf3_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf3_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf3_lower

theorem new_junction_leaf3_binding (δ p : ℝ) :
    new_junction_leaf3_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf3_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf3_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf3_binding δ p) (new_junction_leaf3_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def new_junction_leaf4_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf4_minimum : ℝ := 86238936573663845933/157361530565799936000000
def new_junction_leaf4_table : Fin 3 → Fin 4 → ℝ := ![
  ![(5433809614444370870651/839261496350932992000000:ℝ), (30315440786995384000709/7553353467158396928000000:ℝ), (1942518095714832435773/944169183394799616000000:ℝ), (86238936573663845933/157361530565799936000000:ℝ)],
  ![(16382717111227046545877/2098153740877332480000000:ℝ), (91205593076503202115419/18883383667895992320000000:ℝ), (1155321962356508683663/472084591697399808000000:ℝ), (232281702550311573827/393403826414499840000000:ℝ)],
  ![(11999716966259057670127/1049076870438666240000000:ℝ), (73314879923962283031409/9441691833947996160000000:ℝ), (1131582331581021717221/236042295848699904000000:ℝ), (480262908229736178457/196701913207249920000000:ℝ)]]
theorem new_junction_leaf4_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf4_minimum ≤ new_junction_leaf4_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf4_minimum,new_junction_leaf4_table]
theorem new_junction_leaf4_identity (δ p : ℝ) :
    new_junction_leaf4_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf4_table
      ((δ-(15/32))/((9/16)-(15/32)))
      ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [new_junction_leaf4_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf4_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf4_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) : 0 < new_junction_leaf4_power δ p := by
  rw [new_junction_leaf4_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf4_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf4_lower

theorem new_junction_leaf4_binding (δ p : ℝ) :
    new_junction_leaf4_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf4_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf4_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf4_binding δ p) (new_junction_leaf4_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def new_junction_leaf5_power (δ p : ℝ) : ℝ := (794177/12000000)*δ^0*p^0 +
  (-168722109473/4048164000000)*δ^0*p^1 +
  (-4231051/15000000)*δ^1*p^0 +
  (10180428405387720751/64030570705485000000)*δ^1*p^1 +
  (216114247649251037/5122445656438800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-57365202375019013/71145078561650000)*δ^2*p^1 +
  (2149297265229543037/4268704713699000000)*δ^2*p^2 +
  (-1926713901271/14229015712330)*δ^2*p^3

def new_junction_leaf5_minimum : ℝ := 480262908229736178457/196701913207249920000000
def new_junction_leaf5_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3878803374458710523989/157361530565799936000000:ℝ), (33814741559478248484053/2360422958486999040000000:ℝ), (2108561466607950025367/295052869810874880000000:ℝ), (480262908229736178457/196701913207249920000000:ℝ)],
  ![(722850714727316333051/19670191320724992000000:ℝ), (6708016208198518974667/295052869810874880000000:ℝ), (946450511939511431921/73763217452718720000000:ℝ), (151063377767362120193/24587739150906240000000:ℝ)],
  ![(593758592063644053319/9835095660362496000000:ℝ), (6043932516189257984759/147526434905437440000000:ℝ), (496703893878832898921/18440804363179680000000:ℝ), (209991915102129712051/12293869575453120000000:ℝ)]]
theorem new_junction_leaf5_lower (i : Fin 3) (j : Fin 4) :
    new_junction_leaf5_minimum ≤ new_junction_leaf5_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [new_junction_leaf5_minimum,new_junction_leaf5_table]
theorem new_junction_leaf5_identity (δ p : ℝ) :
    new_junction_leaf5_power δ p=Cycle63.Arithmetic.Bernstein.tensor new_junction_leaf5_table
      ((δ-(9/16))/((3/4)-(9/16)))
      ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [new_junction_leaf5_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    new_junction_leaf5_table,Fin.sum_univ_succ]
  ring
theorem new_junction_leaf5_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) : 0 < new_junction_leaf5_power δ p := by
  rw [new_junction_leaf5_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [new_junction_leaf5_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) new_junction_leaf5_lower

theorem new_junction_leaf5_binding (δ p : ℝ) :
    new_junction_leaf5_power δ p=(oldJ δ p)*(theta-reserve-rowBase dMinus (newCapacity dMinus) δ p)-3*(dMinus)*(oldN δ p)/4 := by
  norm_num [new_junction_leaf5_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem new_junction_leaf5_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (new_junction_leaf5_binding δ p) (new_junction_leaf5_positive hδ hp)
    have hd : 0 ≤ 3*(dMinus)/4 := by norm_num [dMinus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

theorem new_junction_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dMinus (newCapacity dMinus) δ p ≤ theta-reserve := by
  by_cases h1 : δ ≤ (3/8:ℝ)
  ·
    apply new_junction_leaf0_bound
    all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  ·
    by_cases h2 : p ≤ (1/4:ℝ)
    ·
      apply new_junction_leaf1_bound
      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
    ·
      by_cases h3 : δ ≤ (9/16:ℝ)
      ·
        by_cases h4 : p ≤ (3/8:ℝ)
        ·
          apply new_junction_leaf2_bound
          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
        ·
          by_cases h5 : δ ≤ (15/32:ℝ)
          ·
            apply new_junction_leaf3_bound
            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
          ·
            apply new_junction_leaf4_bound
            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
      ·
        apply new_junction_leaf5_bound
        all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]

end
end OAI.SevenEighths.Target830.Count.Certificates

#print axioms OAI.SevenEighths.Target830.Count.Certificates.new_junction_bound
end

/- Original module: Candidate.Target830.Count.Endpoint. -/
section

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def oldExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (oldCapacityAt kappaStar d) δ p
def newExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (newCapacity d) δ p
def rowCommon (δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p
def rowSlope (δ p : ℝ) : ℝ := 1/4-17/50+3*count kappaStar δ p/4

theorem affine_interval_le {f : ℝ → ℝ} {a b A S M d : ℝ}
    (hf : ∀ z, f z=A+z*S) (hd : d ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f d ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with hS | hS
  · have hm := mul_le_mul_of_nonneg_right hd.2 hS
    linarith
  · have hm := mul_le_mul_of_nonpos_right hd.1 hS
    linarith

theorem rowAt_capacity_antitone {κ d C₁ C₂ δ p : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hC : C₁ ≤ C₂) :
    rowAt κ d C₂ δ p ≤ rowAt κ d C₁ δ p := by
  have hm := mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.mpr hC)
  unfold rowAt rowBase
  nlinarith

def newClipLine (d δ p : ℝ) : ℝ := rowAt kappaStar d (slotClip*d) δ p
def newAffineLine (d δ p : ℝ) : ℝ :=
  rowAt kappaStar d ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda) δ p

theorem newClipLine_affine (d δ p : ℝ) :
    newClipLine d δ p=rowCommon δ p+d*(rowSlope δ p-δ*p*slotClip/2) := by
  unfold newClipLine rowAt rowBase rowCommon rowSlope
  ring

theorem newAffineLine_affine (d δ p : ℝ) :
    newAffineLine d δ p=rowCommon δ p-δ*p*y/SourcePlane.A.lambda+
      d*(rowSlope δ p+δ*p*(2-SourcePlane.A.B)/(2*SourcePlane.A.lambda)) := by
  unfold newAffineLine rowAt rowBase rowCommon rowSlope
  ring

theorem newClipLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newClipLine d δ p ≤ newExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact min_le_left _ _

theorem newAffineLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newAffineLine d δ p ≤ newExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact min_le_right _ _

theorem new_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : newExponent d δ p ≤ theta-reserve := by
  have hlo := Certificates.new_junction_bound hδ hp
  have hhi := Certificates.top_bound hδ hp
  have hc : newClipLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => newClipLine_affine z δ p) hd
    · exact (newClipLine_le hδ.1 hp.1).trans hlo
    · exact (newClipLine_le hδ.1 hp.1).trans hhi
  have ha : newAffineLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => newAffineLine_affine z δ p) hd
    · exact (newAffineLine_le hδ.1 hp.1).trans hlo
    · exact (newAffineLine_le hδ.1 hp.1).trans hhi
  rcases le_total (slotClip*d)
    ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda) with hm | hm
  · simpa only [newExponent,newCapacity,min_eq_left hm,newClipLine] using hc
  · simpa only [newExponent,newCapacity,min_eq_right hm,newAffineLine] using ha

def oldLeftLine (d δ p : ℝ) : ℝ := rowAt kappaStar d (d/(6*kappaStar)) δ p
def oldRightLine (d δ p : ℝ) : ℝ := rowAt kappaStar d ((2*y-d)/(6*kappaStar)) δ p

theorem oldLeftLine_affine (d δ p : ℝ) :
    oldLeftLine d δ p=rowCommon δ p+d*(rowSlope δ p-δ*p/(12*kappaStar)) := by
  unfold oldLeftLine rowAt rowBase rowCommon rowSlope
  ring
theorem oldRightLine_affine (d δ p : ℝ) :
    oldRightLine d δ p=rowCommon δ p-δ*p*y/(6*kappaStar)+
      d*(rowSlope δ p+δ*p/(12*kappaStar)) := by
  unfold oldRightLine rowAt rowBase rowCommon rowSlope
  ring
theorem oldLeftLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_left _ _)
    (by norm_num [kappaStar,theta])
theorem oldRightLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_right _ _)
    (by norm_num [kappaStar,theta])

theorem old_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p ≤ theta-reserve := by
  have hlo := Certificates.old_lower_bound hδ hp
  have hhi := Certificates.old_junction_bound hδ hp
  have hl : oldLeftLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => oldLeftLine_affine z δ p) hd
    · exact (oldLeftLine_le hδ.1 hp.1).trans hlo
    · exact (oldLeftLine_le hδ.1 hp.1).trans hhi
  have hr : oldRightLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => oldRightLine_affine z δ p) hd
    · exact (oldRightLine_le hδ.1 hp.1).trans hlo
    · exact (oldRightLine_le hδ.1 hp.1).trans hhi
  rcases le_total d (2*y-d) with hm | hm
  · simpa only [oldExponent,oldCapacityAt,min_eq_left hm,oldLeftLine] using hl
  · simpa only [oldExponent,oldCapacityAt,min_eq_right hm,oldRightLine] using hr

end
end OAI.SevenEighths.Target830.Count
#print axioms OAI.SevenEighths.Target830.Count.new_interval_bound
#print axioms OAI.SevenEighths.Target830.Count.old_interval_bound
end
