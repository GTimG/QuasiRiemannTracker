import Candidate.Target830.Count.Concrete
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count.Certificates
noncomputable section

def top_leaf0_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf0_minimum : ℝ := 7127166218983115615134657/4917547830181248000000000000
def top_leaf0_table : Fin 3 → Fin 4 → ℝ := ![
  ![(38223849901/600000000000:ℝ), (69247587867698333/1214449200000000000:ℝ), (3820435573755049/75903075000000000:ℝ), (3533756699497549/80963280000000000:ℝ)],
  ![(545062393799/48000000000000:ℝ), (35552134799065625368887841/3688160872635936000000000000:ℝ), (63196529776391123794682953/7376321745271872000000000000:ℝ), (20012785094298095712337283/2458773915090624000000000000:ℝ)],
  ![(703608397759/24000000000000:ℝ), (3138188375209930616287987/230510054539746000000000000:ℝ), (75523644673036743180189857/14752643490543744000000000000:ℝ), (7127166218983115615134657/4917547830181248000000000000:ℝ)]]
theorem top_leaf0_lower (i : Fin 3) (j : Fin 4) :
    top_leaf0_minimum ≤ top_leaf0_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf0_minimum,top_leaf0_table]
theorem top_leaf0_identity (δ p : ℝ) :
    top_leaf0_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf0_table
      ((δ-(0))/((3/8)-(0)))
      ((p-(0))/((1/2)-(0))) := by
  norm_num [top_leaf0_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf0_table,Fin.sum_univ_succ]
  ring
theorem top_leaf0_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) : 0 < top_leaf0_power δ p := by
  rw [top_leaf0_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf0_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf0_lower

theorem top_leaf0_binding (δ p : ℝ) :
    top_leaf0_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf0_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf0_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (3/8))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf0_binding δ p) (top_leaf0_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf1_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf1_minimum : ℝ := 8553253962856670804627633/786807652828999680000000000
def top_leaf1_table : Fin 3 → Fin 4 → ℝ := ![
  ![(703608397759/24000000000000:ℝ), (39584221857848120338956817/1844080436317968000000000000:ℝ), (909715250412042228045930097/59010573962174976000000000000:ℝ), (8553253962856670804627633/786807652828999680000000000:ℝ)],
  ![(2269371197237/48000000000000:ℝ), (239240852689662003359621677/7376321745271872000000000000:ℝ), (38784287918204620925587859/1844080436317968000000000000:ℝ), (6135714718949371183278893/491754783018124800000000000:ℝ)],
  ![(1626631399739/12000000000000:ℝ), (192218344711398377847453709/1844080436317968000000000000:ℝ), (1172573983511386029187147951/14752643490543744000000000000:ℝ), (59110714967760277341710227/983509566036249600000000000:ℝ)]]
theorem top_leaf1_lower (i : Fin 3) (j : Fin 4) :
    top_leaf1_minimum ≤ top_leaf1_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf1_minimum,top_leaf1_table]
theorem top_leaf1_identity (δ p : ℝ) :
    top_leaf1_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf1_table
      ((δ-(3/8))/((3/4)-(3/8)))
      ((p-(0))/((1/4)-(0))) := by
  norm_num [top_leaf1_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf1_table,Fin.sum_univ_succ]
  ring
theorem top_leaf1_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) : 0 < top_leaf1_power δ p := by
  rw [top_leaf1_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf1_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf1_lower

theorem top_leaf1_binding (δ p : ℝ) :
    top_leaf1_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf1_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf1_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/4)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf1_binding δ p) (top_leaf1_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf2_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf2_minimum : ℝ := 35930737820911291419096187/10490768704386662400000000000
def top_leaf2_table : Fin 3 → Fin 4 → ℝ := ![
  ![(8553253962856670804627633/786807652828999680000000000:ℝ), (31711465350959646968602729/3688160872635936000000000000:ℝ), (1581850021907139275694689837/236042295848699904000000000000:ℝ), (134903857437296634212605327/26226921760966656000000000000:ℝ)],
  ![(91851987565878323489369309/7868076528289996800000000000:ℝ), (49563174416748361483921933/5901057396217497600000000000:ℝ), (535153091918893792559999753/94416918339479961600000000000:ℝ), (35930737820911291419096187/10490768704386662400000000000:ℝ)],
  ![(377380565188514402322441361/15736153056579993600000000000:ℝ), (556244988891279126279857273/29505286981087488000000000000:ℝ), (13698678406363831805055798137/944169183394799616000000000000:ℝ), (1140026498279232127595876707/104907687043866624000000000000:ℝ)]]
theorem top_leaf2_lower (i : Fin 3) (j : Fin 4) :
    top_leaf2_minimum ≤ top_leaf2_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf2_minimum,top_leaf2_table]
theorem top_leaf2_identity (δ p : ℝ) :
    top_leaf2_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf2_table
      ((δ-(3/8))/((9/16)-(3/8)))
      ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [top_leaf2_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf2_table,Fin.sum_univ_succ]
  ring
theorem top_leaf2_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) : 0 < top_leaf2_power δ p := by
  rw [top_leaf2_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf2_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf2_lower

theorem top_leaf2_binding (δ p : ℝ) :
    top_leaf2_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf2_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf2_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16))
    (hp : p ∈ Set.Icc (1/4:ℝ) (3/8)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf2_binding δ p) (top_leaf2_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf3_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf3_minimum : ℝ := 2187929101265805350421705917/1258892244526399488000000000000
def top_leaf3_table : Fin 3 → Fin 4 → ℝ := ![
  ![(134903857437296634212605327/26226921760966656000000000000:ℝ), (257569266112483731005706749/59010573962174976000000000000:ℝ), (3465646103439609123043467121/944169183394799616000000000000:ℝ), (961919103177679513738891811/314723061131599872000000000000:ℝ)],
  ![(449461403979149725520691589/104907687043866624000000000000:ℝ), (49187440656471055272416363/14752643490543744000000000000:ℝ), (9393702220121346412734652027/3776676733579198464000000000000:ℝ), (2187929101265805350421705917/1258892244526399488000000000000:ℝ)],
  ![(479651336889328898565644351/83926149635093299200000000000:ℝ), (850594753692228413683185871/188833836678959923200000000000:ℝ), (10332428006736538540930279361/3021341386863358771200000000000:ℝ), (2471402831784083085964381387/1007113795621119590400000000000:ℝ)]]
theorem top_leaf3_lower (i : Fin 3) (j : Fin 4) :
    top_leaf3_minimum ≤ top_leaf3_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf3_minimum,top_leaf3_table]
theorem top_leaf3_identity (δ p : ℝ) :
    top_leaf3_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf3_table
      ((δ-(3/8))/((15/32)-(3/8)))
      ((p-(3/8))/((7/16)-(3/8))) := by
  norm_num [top_leaf3_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf3_table,Fin.sum_univ_succ]
  ring
theorem top_leaf3_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16)) : 0 < top_leaf3_power δ p := by
  rw [top_leaf3_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf3_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf3_lower

theorem top_leaf3_binding (δ p : ℝ) :
    top_leaf3_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf3_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf3_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf3_binding δ p) (top_leaf3_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf4_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf4_minimum : ℝ := 71473520410993769539843429/314723061131599872000000000000
def top_leaf4_table : Fin 3 → Fin 4 → ℝ := ![
  ![(961919103177679513738891811/314723061131599872000000000000:ℝ), (461173703125293591877976749/188833836678959923200000000000:ℝ), (112597067635841085549008827/59010573962174976000000000000:ℝ), (7127166218983115615134657/4917547830181248000000000000:ℝ)],
  ![(6035605513976523405377273161/2517784489052798976000000000000:ℝ), (2591469289995871505471023691/1510670693431679385600000000000:ℝ), (529908591965918636187313547/472084591697399808000000000000:ℝ), (24118925782251849111537347/39340382641449984000000000000:ℝ)],
  ![(45251152619889730453017823247/20142275912422391808000000000000:ℝ), (3569792810786046909715314101/2417073109490687016960000000000:ℝ), (3042915032784672185333877499/3776676733579198464000000000000:ℝ), (71473520410993769539843429/314723061131599872000000000000:ℝ)]]
theorem top_leaf4_lower (i : Fin 3) (j : Fin 4) :
    top_leaf4_minimum ≤ top_leaf4_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf4_minimum,top_leaf4_table]
theorem top_leaf4_identity (δ p : ℝ) :
    top_leaf4_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf4_table
      ((δ-(3/8))/((27/64)-(3/8)))
      ((p-(7/16))/((1/2)-(7/16))) := by
  norm_num [top_leaf4_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf4_table,Fin.sum_univ_succ]
  ring
theorem top_leaf4_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2)) : 0 < top_leaf4_power δ p := by
  rw [top_leaf4_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf4_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf4_lower

theorem top_leaf4_binding (δ p : ℝ) :
    top_leaf4_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf4_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf4_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf4_binding δ p) (top_leaf4_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf5_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf5_minimum : ℝ := 5974709664875039132693458409/6714091970807463936000000000000
def top_leaf5_table : Fin 3 → Fin 4 → ℝ := ![
  ![(45251152619889730453017823247/20142275912422391808000000000000:ℝ), (112499139064660182050968161133/60426827737267175424000000000000:ℝ), (14517189556941051672406448591/9668292437962748067840000000000:ℝ), (15646409893366604950982724601/13428183941614927872000000000000:ℝ)],
  ![(21108730563983636831508730603/10071137956211195904000000000000:ℝ), (50370813080842326563994285257/30213413868633587712000000000000:ℝ), (30585910254030871602160984439/24170731094906870169600000000000:ℝ), (5974709664875039132693458409/6714091970807463936000000000000:ℝ)],
  ![(2471402831784083085964381387/1007113795621119590400000000000:ℝ), (5955098739660104616374576561/3021341386863358771200000000000:ℝ), (18342824476826666694387595219/12085365547453435084800000000000:ℝ), (734063044341367793889247733/671409197080746393600000000000:ℝ)]]
theorem top_leaf5_lower (i : Fin 3) (j : Fin 4) :
    top_leaf5_minimum ≤ top_leaf5_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf5_minimum,top_leaf5_table]
theorem top_leaf5_identity (δ p : ℝ) :
    top_leaf5_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf5_table
      ((δ-(27/64))/((15/32)-(27/64)))
      ((p-(7/16))/((15/32)-(7/16))) := by
  norm_num [top_leaf5_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf5_table,Fin.sum_univ_succ]
  ring
theorem top_leaf5_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32)) : 0 < top_leaf5_power δ p := by
  rw [top_leaf5_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf5_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf5_lower

theorem top_leaf5_binding (δ p : ℝ) :
    top_leaf5_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf5_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf5_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf5_binding δ p) (top_leaf5_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf6_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf6_minimum : ℝ := 9533683963944869617563282599/20625690534320529211392000000000
def top_leaf6_table : Fin 3 → Fin 4 → ℝ := ![
  ![(15646409893366604950982724601/13428183941614927872000000000000:ℝ), (481976395318270375542905913679/483414621898137403392000000000000:ℝ), (201784131360718244850526685311/241707310949068701696000000000000:ℝ), (87467162142003327713459418599/128910565839503307571200000000000:ℝ)],
  ![(27595829223116683216369641419/26856367883229855744000000000000:ℝ), (821385936584465885852189577461/966829243796274806784000000000000:ℝ), (327688586566817993694270620369/483414621898137403392000000000000:ℝ), (132087897739019523249856403869/257821131679006615142400000000000:ℝ)],
  ![(54226509439694117359541512897/53712735766459711488000000000000:ℝ), (1586727076202805279674108888503/1933658487592549613568000000000000:ℝ), (617001348177827747084168893807/966829243796274806784000000000000:ℝ), (9533683963944869617563282599/20625690534320529211392000000000:ℝ)]]
theorem top_leaf6_lower (i : Fin 3) (j : Fin 4) :
    top_leaf6_minimum ≤ top_leaf6_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf6_minimum,top_leaf6_table]
theorem top_leaf6_identity (δ p : ℝ) :
    top_leaf6_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf6_table
      ((δ-(27/64))/((57/128)-(27/64)))
      ((p-(15/32))/((31/64)-(15/32))) := by
  norm_num [top_leaf6_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf6_table,Fin.sum_univ_succ]
  ring
theorem top_leaf6_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) : 0 < top_leaf6_power δ p := by
  rw [top_leaf6_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf6_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf6_lower

theorem top_leaf6_binding (δ p : ℝ) :
    top_leaf6_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf6_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf6_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf6_binding δ p) (top_leaf6_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf7_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf7_minimum : ℝ := 313462585709615708941716013/5035568978105597952000000000000
def top_leaf7_table : Fin 3 → Fin 4 → ℝ := ![
  ![(87467162142003327713459418599/128910565839503307571200000000000:ℝ), (504870906687176936299784537741/966829243796274806784000000000000:ℝ), (5615961767580447888768240943/15106706934316793856000000000000:ℝ), (71473520410993769539843429/314723061131599872000000000000:ℝ)],
  ![(307022222023026178676775241067/515642263358013230284800000000000:ℝ), (1680305933192374746570332652041/3867316975185099227136000000000000:ℝ), (16894289476886357810219940403/60426827737267175424000000000000:ℝ), (164416195796954054806918369/1258892244526399488000000000000:ℝ)],
  ![(1116562338622713144292345354847/2062569053432052921139200000000000:ℝ), (5808866199788806359331747856597/15469267900740396908544000000000000:ℝ), (52171053876583308735400195111/241707310949068701696000000000000:ℝ), (313462585709615708941716013/5035568978105597952000000000000:ℝ)]]
theorem top_leaf7_lower (i : Fin 3) (j : Fin 4) :
    top_leaf7_minimum ≤ top_leaf7_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf7_minimum,top_leaf7_table]
theorem top_leaf7_identity (δ p : ℝ) :
    top_leaf7_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf7_table
      ((δ-(27/64))/((111/256)-(27/64)))
      ((p-(31/64))/((1/2)-(31/64))) := by
  norm_num [top_leaf7_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf7_table,Fin.sum_univ_succ]
  ring
theorem top_leaf7_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2)) : 0 < top_leaf7_power δ p := by
  rw [top_leaf7_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf7_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf7_lower

theorem top_leaf7_binding (δ p : ℝ) :
    top_leaf7_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf7_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf7_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf7_binding δ p) (top_leaf7_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf8_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf8_minimum : ℝ := 465548752315409210227470273389/2291743392702281023488000000000000
def top_leaf8_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1116562338622713144292345354847/2062569053432052921139200000000000:ℝ), (28366167478918309883048676035899/61877071602961587634176000000000000:ℝ), (46661794774698586119843396723301/123754143205923175268352000000000000:ℝ), (2724490040491903881129897984029/9166973570809124093952000000000000:ℝ)],
  ![(502517894576660786938794872713/1031284526716026460569600000000000:ℝ), (497371083418321021458563527829/1237541432059231752683520000000000:ℝ), (3936748508477179037512234706359/12375414320592317526835200000000000:ℝ), (216235057052447616649212365663/916697357080912409395200000000000:ℝ)],
  ![(9533683963944869617563282599/20625690534320529211392000000000:ℝ), (5789383674015356343085341773419/15469267900740396908544000000000000:ℝ), (8907026970589424217932407422901/30938535801480793817088000000000000:ℝ), (465548752315409210227470273389/2291743392702281023488000000000000:ℝ)]]
theorem top_leaf8_lower (i : Fin 3) (j : Fin 4) :
    top_leaf8_minimum ≤ top_leaf8_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf8_minimum,top_leaf8_table]
theorem top_leaf8_identity (δ p : ℝ) :
    top_leaf8_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf8_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(31/64))/((63/128)-(31/64))) := by
  norm_num [top_leaf8_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf8_table,Fin.sum_univ_succ]
  ring
theorem top_leaf8_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) : 0 < top_leaf8_power δ p := by
  rw [top_leaf8_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf8_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf8_lower

theorem top_leaf8_binding (δ p : ℝ) :
    top_leaf8_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf8_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf8_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf8_binding δ p) (top_leaf8_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf9_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-1082996339245033/26999400000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (656800490668781293838551447/4099724000997600000000000000)*δ^1*p^1 +
  (164150063250319179821890153/4099724000997600000000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-2767982359700612079966809847/3416436667498000000000000000)*δ^2*p^1 +
  (1730422182246966040071509847/3416436667498000000000000000)*δ^2*p^2 +
  (-115755591881443853/854109166874500000)*δ^2*p^3

def top_leaf9_minimum : ℝ := 3448204300375423274276944857/223899593441148928000000000000000
def top_leaf9_table : Fin 3 → Fin 4 → ℝ := ![
  ![(790424002384951674332812307615761/2201022563363870421811200000000000000:ℝ), (9220361572023495764671792390050853/33015338450458056327168000000000000000:ℝ), (202475433530098274517859042879/1007548170485170176000000000000000:ℝ), (111193012471908614897289880073/895598373764595712000000000000000:ℝ)],
  ![(327649380943217114889022297224167/1100511281681935210905600000000000000:ℝ), (3557442530812010561244158758864691/16507669225229028163584000000000000000:ℝ), (67929746561138495496572983613/503774085242585088000000000000000:ℝ), (24955863286675155106789162031/447799186882297856000000000000000:ℝ)],
  ![(145743845915575785083578550526049/550255640840967605452800000000000000:ℝ), (1486648573099505374531518883293877/8253834612614514081792000000000000000:ℝ), (24424320568678414576615629511/251887042621292544000000000000000:ℝ), (3448204300375423274276944857/223899593441148928000000000000000:ℝ)]]
theorem top_leaf9_lower (i : Fin 3) (j : Fin 4) :
    top_leaf9_minimum ≤ top_leaf9_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf9_minimum,top_leaf9_table]
theorem top_leaf9_identity (δ p : ℝ) :
    top_leaf9_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf9_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [top_leaf9_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf9_table,Fin.sum_univ_succ]
  ring
theorem top_leaf9_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) : 0 < top_leaf9_power δ p := by
  rw [top_leaf9_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf9_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf9_lower

theorem top_leaf9_binding (δ p : ℝ) :
    top_leaf9_power δ p=(affineJ Plane.oldWeak.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.oldWeak.lambda Plane.oldWeak.B δ p)/4 := by
  norm_num [top_leaf9_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf9_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window0.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (63/128:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window0_admissible δ p ha).j
    change 0 < affineJ Plane.oldWeak.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.oldWeak.B) hj.ne'
    have hc := count_le_window0 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.oldWeak.lambda Plane.oldWeak.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf9_binding δ p) (top_leaf9_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf10_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf10_minimum : ℝ := 53127100679801108594612830553/128910565839503307571200000000000
def top_leaf10_table : Fin 3 → Fin 4 → ℝ := ![
  ![(54226509439694117359541512897/53712735766459711488000000000000:ℝ), (1586727076202805279674108888503/1933658487592549613568000000000000:ℝ), (617001348177827747084168893807/966829243796274806784000000000000:ℝ), (9533683963944869617563282599/20625690534320529211392000000000:ℝ)],
  ![(13315340108288717071585935739/13428183941614927872000000000000:ℝ), (382670569809169696910959655521/483414621898137403392000000000000:ℝ), (144656380805504876694949136719/241707310949068701696000000000000:ℝ), (53127100679801108594612830553/128910565839503307571200000000000:ℝ)],
  ![(734063044341367793889247733/671409197080746393600000000000:ℝ), (21296579917607194175631782363/24170731094906870169600000000000:ℝ), (8170415320245500227307716919/12085365547453435084800000000000:ℝ), (15408366440646505413207168959/32227641459875826892800000000000:ℝ)]]
theorem top_leaf10_lower (i : Fin 3) (j : Fin 4) :
    top_leaf10_minimum ≤ top_leaf10_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf10_minimum,top_leaf10_table]
theorem top_leaf10_identity (δ p : ℝ) :
    top_leaf10_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf10_table
      ((δ-(57/128))/((15/32)-(57/128)))
      ((p-(15/32))/((31/64)-(15/32))) := by
  norm_num [top_leaf10_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf10_table,Fin.sum_univ_succ]
  ring
theorem top_leaf10_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) : 0 < top_leaf10_power δ p := by
  rw [top_leaf10_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf10_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf10_lower

theorem top_leaf10_binding (δ p : ℝ) :
    top_leaf10_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf10_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf10_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf10_binding δ p) (top_leaf10_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf11_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf11_minimum : ℝ := 1523867795440546578800927731733/9166973570809124093952000000000000
def top_leaf11_table : Fin 3 → Fin 4 → ℝ := ![
  ![(9533683963944869617563282599/20625690534320529211392000000000:ℝ), (5789383674015356343085341773419/15469267900740396908544000000000000:ℝ), (8907026970589424217932407422901/30938535801480793817088000000000000:ℝ), (465548752315409210227470273389/2291743392702281023488000000000000:ℝ)],
  ![(450850501817826174817533387187/1031284526716026460569600000000000:ℝ), (10723257610603399835877278897951/30938535801480793817088000000000000:ℝ), (15944365339971801684168456159809/61877071602961587634176000000000000:ℝ), (781019723999398757663819265241/4583486785404562046976000000000000:ℝ)],
  ![(909892767587374695807299412743/2062569053432052921139200000000000:ℝ), (21522089579499807080701438844803/61877071602961587634176000000000000:ℝ), (31704285965042212106272527235357/123754143205923175268352000000000000:ℝ), (1523867795440546578800927731733/9166973570809124093952000000000000:ℝ)]]
theorem top_leaf11_lower (i : Fin 3) (j : Fin 4) :
    top_leaf11_minimum ≤ top_leaf11_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf11_minimum,top_leaf11_table]
theorem top_leaf11_identity (δ p : ℝ) :
    top_leaf11_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf11_table
      ((δ-(57/128))/((117/256)-(57/128)))
      ((p-(31/64))/((63/128)-(31/64))) := by
  norm_num [top_leaf11_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf11_table,Fin.sum_univ_succ]
  ring
theorem top_leaf11_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) : 0 < top_leaf11_power δ p := by
  rw [top_leaf11_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf11_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf11_lower

theorem top_leaf11_binding (δ p : ℝ) :
    top_leaf11_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf11_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf11_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf11_binding δ p) (top_leaf11_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf12_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf12_minimum : ℝ := 126192369304449407860063811675689/2640088388393027739058176000000000000
def top_leaf12_table : Fin 3 → Fin 4 → ℝ := ![
  ![(465548752315409210227470273389/2291743392702281023488000000000000:ℝ), (19895394996369297592560277298707/123754143205923175268352000000000000:ℝ), (29401557861632772842427754452391/247508286411846350536704000000000000:ℝ), (12740781466274208661952761503337/165005524274564233691136000000000000:ℝ)],
  ![(1712117228630217178118759812019/9166973570809124093952000000000000:ℝ), (71164656956746291187553002762317/495016572823692701073408000000000000:ℝ), (100151555017871422930651232032441/990033145647385402146816000000000000:ℝ), (38915850999437636159007404871607/660022097098256934764544000000000000:ℝ)],
  ![(6510141700699778450366085886253/36667894283236496375808000000000000:ℝ), (265101767342107823050300993654099/1980066291294770804293632000000000000:ℝ), (358936789654500102049054777686247/3960132582589541608587264000000000000:ℝ), (126192369304449407860063811675689/2640088388393027739058176000000000000:ℝ)]]
theorem top_leaf12_lower (i : Fin 3) (j : Fin 4) :
    top_leaf12_minimum ≤ top_leaf12_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf12_minimum,top_leaf12_table]
theorem top_leaf12_identity (δ p : ℝ) :
    top_leaf12_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf12_table
      ((δ-(57/128))/((231/512)-(57/128)))
      ((p-(63/128))/((127/256)-(63/128))) := by
  norm_num [top_leaf12_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf12_table,Fin.sum_univ_succ]
  ring
theorem top_leaf12_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256)) : 0 < top_leaf12_power δ p := by
  rw [top_leaf12_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf12_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf12_lower

theorem top_leaf12_binding (δ p : ℝ) :
    top_leaf12_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf12_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf12_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf12_binding δ p) (top_leaf12_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf13_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-1082996339245033/26999400000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (656800490668781293838551447/4099724000997600000000000000)*δ^1*p^1 +
  (164150063250319179821890153/4099724000997600000000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-2767982359700612079966809847/3416436667498000000000000000)*δ^2*p^1 +
  (1730422182246966040071509847/3416436667498000000000000000)*δ^2*p^2 +
  (-115755591881443853/854109166874500000)*δ^2*p^3

def top_leaf13_minimum : ℝ := 1968577661970814584261106118901989/33144810365950048704921600000000000000
def top_leaf13_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1529037736757425894995133841071693/11005112816819352109056000000000000000:ℝ), (78015486594897312407929475973503/660306769009161126543360000000000000:ℝ), (12870885588154172581459466157535313/132061353801832225308672000000000000000:ℝ), (39810945901140706120228898793341/517887661967969511014400000000000000:ℝ)],
  ![(11426242858119185618914738913190311/88040902534554816872448000000000000000:ℝ), (574938237208893164948554359988861/5282454152073289012346880000000000000:ℝ), (92966143902860195704979621726416051/1056490830414657802469376000000000000000:ℝ), (278628198973787856782368398145207/4143101295743756088115200000000000000:ℝ)],
  ![(86207851650199786606578872702399797/704327220276438534979584000000000000000:ℝ), (4280707237551056524642542926431607/42259633216586312098775040000000000000:ℝ), (678639713759052956941083846450578777/8451926643317262419755008000000000000000:ℝ), (1968577661970814584261106118901989/33144810365950048704921600000000000000:ℝ)]]
theorem top_leaf13_lower (i : Fin 3) (j : Fin 4) :
    top_leaf13_minimum ≤ top_leaf13_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf13_minimum,top_leaf13_table]
theorem top_leaf13_identity (δ p : ℝ) :
    top_leaf13_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf13_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(127/256))/((255/512)-(127/256))) := by
  norm_num [top_leaf13_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf13_table,Fin.sum_univ_succ]
  ring
theorem top_leaf13_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (255/512)) : 0 < top_leaf13_power δ p := by
  rw [top_leaf13_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf13_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf13_lower

theorem top_leaf13_binding (δ p : ℝ) :
    top_leaf13_power δ p=(affineJ Plane.oldWeak.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.oldWeak.lambda Plane.oldWeak.B δ p)/4 := by
  norm_num [top_leaf13_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf13_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (255/512)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window1.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (127/256:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window1_admissible δ p ha).j
    change 0 < affineJ Plane.oldWeak.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.oldWeak.B) hj.ne'
    have hc := count_le_window1 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.oldWeak.lambda Plane.oldWeak.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf13_binding δ p) (top_leaf13_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf14_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-24501487786541/579360000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (10181327196329579455207119/58648614344960000000000000)*δ^1*p^1 +
  (5971209877966238307276403/175945843034880000000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-122619264343509593591619277/146621535862400000000000000)*δ^2*p^1 +
  (79561529916031896707199277/146621535862400000000000000)*δ^2*p^2 +
  (-554122018336471724311/3665538396560000000000)*δ^2*p^3

def top_leaf14_minimum : ℝ := 46748798415569994686594367569/1844925883061423308800000000000000
def top_leaf14_table : Fin 3 → Fin 4 → ℝ := ![
  ![(18541468309351682912032029699113/177807445106343291125760000000000000:ℝ), (477014413901314172001211256758327/5667612312764692404633600000000000000:ℝ), (44382462252114502310992660789/691847206148033740800000000000000:ℝ), (1275167781060953600831149961/28826966922834739200000000000000:ℝ)],
  ![(134313081836602365700823514569371/1422459560850746329006080000000000000:ℝ), (3362515355478981932213244776838629/45340898502117539237068800000000000000:ℝ), (298867280521102340295005368703/5534777649184269926400000000000000:ℝ), (7825904895226236044610560347/230615735382677913600000000000000:ℝ)],
  ![(981832120041510430046733898167857/11379676486805970632048640000000000000:ℝ), (23891318098634976092124630125270383/362727188016940313896550400000000000000:ℝ), (2016981010472763911535547300381/44278221193474159411200000000000000:ℝ), (46748798415569994686594367569/1844925883061423308800000000000000:ℝ)]]
theorem top_leaf14_lower (i : Fin 3) (j : Fin 4) :
    top_leaf14_minimum ≤ top_leaf14_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf14_minimum,top_leaf14_table]
theorem top_leaf14_identity (δ p : ℝ) :
    top_leaf14_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf14_table
      ((δ-(57/128))/((459/1024)-(57/128)))
      ((p-(255/512))/((1/2)-(255/512))) := by
  norm_num [top_leaf14_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf14_table,Fin.sum_univ_succ]
  ring
theorem top_leaf14_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) : 0 < top_leaf14_power δ p := by
  rw [top_leaf14_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf14_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf14_lower

theorem top_leaf14_binding (δ p : ℝ) :
    top_leaf14_power δ p=(affineJ Plane.PR60.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.PR60.lambda Plane.PR60.B δ p)/4 := by
  norm_num [top_leaf14_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf14_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024))
    (hp : p ∈ Set.Icc (255/512:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window2.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (255/512:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window2_admissible δ p ha).j
    change 0 < affineJ Plane.PR60.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.PR60.B) hj.ne'
    have hc := count_le_window2 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.PR60.lambda Plane.PR60.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf14_binding δ p) (top_leaf14_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf15_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-24501487786541/579360000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (10181327196329579455207119/58648614344960000000000000)*δ^1*p^1 +
  (5971209877966238307276403/175945843034880000000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-122619264343509593591619277/146621535862400000000000000)*δ^2*p^1 +
  (79561529916031896707199277/146621535862400000000000000)*δ^2*p^2 +
  (-554122018336471724311/3665538396560000000000)*δ^2*p^3

def top_leaf15_minimum : ℝ := 267308455925609643706369657/27131262986197401600000000000000
def top_leaf15_table : Fin 3 → Fin 4 → ℝ := ![
  ![(5957648477203816980097206446542211/40303020890771145988505600000000000000:ℝ), (9666006600564190507660912995300719/90681797004235078474137600000000000000:ℝ), (1455995429485923975296414889553/22139110596737079705600000000000000:ℝ), (46748798415569994686594367569/1844925883061423308800000000000000:ℝ)],
  ![(2823897070484526988509486567914239/20151510445385572994252800000000000000:ℝ), (4470592717123104449335876760903131/45340898502117539237068800000000000000:ℝ), (636169742372373944257700311397/11069555298368539852800000000000000:ℝ), (15445178834665050508152126181/922462941530711654400000000000000:ℝ)],
  ![(1351799085251475451306358731495211/10075755222692786497126400000000000000:ℝ), (2092944112189220958332633525832119/22670449251058769618534400000000000000:ℝ), (281631237328952858835287513353/5534777649184269926400000000000000:ℝ), (267308455925609643706369657/27131262986197401600000000000000:ℝ)]]
theorem top_leaf15_lower (i : Fin 3) (j : Fin 4) :
    top_leaf15_minimum ≤ top_leaf15_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf15_minimum,top_leaf15_table]
theorem top_leaf15_identity (δ p : ℝ) :
    top_leaf15_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf15_table
      ((δ-(459/1024))/((231/512)-(459/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [top_leaf15_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf15_table,Fin.sum_univ_succ]
  ring
theorem top_leaf15_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) : 0 < top_leaf15_power δ p := by
  rw [top_leaf15_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf15_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf15_lower

theorem top_leaf15_binding (δ p : ℝ) :
    top_leaf15_power δ p=(affineJ Plane.PR60.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.PR60.lambda Plane.PR60.B δ p)/4 := by
  norm_num [top_leaf15_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf15_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window3.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (127/256:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window3_admissible δ p ha).j
    change 0 < affineJ Plane.PR60.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.PR60.B) hj.ne'
    have hc := count_le_window3 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.PR60.lambda Plane.PR60.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf15_binding δ p) (top_leaf15_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf16_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf16_minimum : ℝ := 21492091171795697871845238202609/660022097098256934764544000000000000
def top_leaf16_table : Fin 3 → Fin 4 → ℝ := ![
  ![(6510141700699778450366085886253/36667894283236496375808000000000000:ℝ), (265101767342107823050300993654099/1980066291294770804293632000000000000:ℝ), (358936789654500102049054777686247/3960132582589541608587264000000000000:ℝ), (126192369304449407860063811675689/2640088388393027739058176000000000000:ℝ)],
  ![(617181448687868818825713252443/3666789428323649637580800000000000:ℝ), (24554490685723048135038997625893/198006629129477080429363200000000000:ℝ), (31726735923751451237550462724273/396013258258954160858726400000000000:ℝ), (1934426692222965421681960077299/52801767767860554781163520000000000:ℝ)],
  ![(1523867795440546578800927731733/9166973570809124093952000000000000:ℝ), (60024719500599848670330091799659/495016572823692701073408000000000000:ℝ), (75936801029545501696160867366047/990033145647385402146816000000000000:ℝ), (21492091171795697871845238202609/660022097098256934764544000000000000:ℝ)]]
theorem top_leaf16_lower (i : Fin 3) (j : Fin 4) :
    top_leaf16_minimum ≤ top_leaf16_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf16_minimum,top_leaf16_table]
theorem top_leaf16_identity (δ p : ℝ) :
    top_leaf16_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf16_table
      ((δ-(231/512))/((117/256)-(231/512)))
      ((p-(63/128))/((127/256)-(63/128))) := by
  norm_num [top_leaf16_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf16_table,Fin.sum_univ_succ]
  ring
theorem top_leaf16_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256)) : 0 < top_leaf16_power δ p := by
  rw [top_leaf16_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf16_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf16_lower

theorem top_leaf16_binding (δ p : ℝ) :
    top_leaf16_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf16_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf16_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf16_binding δ p) (top_leaf16_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf17_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-1521041659110493/35627400000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (3175768432072126270762067/18032808985032000000000000)*δ^1*p^1 +
  (118196658320663649382409/3606561797006400000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-2528093608544779576907391/3005468164172000000000000)*δ^2*p^1 +
  (1651058583405770455253191/3005468164172000000000000)*δ^2*p^2 +
  (-115755591881443853/751367041043000000)*δ^2*p^3

def top_leaf17_minimum : ℝ := 107646662840434965194899261/22690524857146697318400000000000
def top_leaf17_table : Fin 3 → Fin 4 → ℝ := ![
  ![(16347132610455736079215443793399/116175487268591090270208000000000000:ℝ), (138088610596881906755550644048911/1394105847223093083242496000000000000:ℝ), (39344946813546426857222956111/680715745714400919552000000000000:ℝ), (480804583849085038590317057/28363156071433371648000000000000:ℝ)],
  ![(31291758424571072236383057947297/232350974537182180540416000000000000:ℝ), (51697972871232854190539478998293/557642338889237233296998400000000000:ℝ), (69638159438858210444352172457/1361431491428801839104000000000000:ℝ), (567283408053957942276313351/56726312142866743296000000000000:ℝ)],
  ![(2422904161698150760604832602527/18588077962974574443233280000000000:ℝ), (98221736390066558035478299054739/1115284677778474466593996800000000000:ℝ), (25160175794832892548488151251/544572596571520735641600000000000:ℝ), (107646662840434965194899261/22690524857146697318400000000000:ℝ)]]
theorem top_leaf17_lower (i : Fin 3) (j : Fin 4) :
    top_leaf17_minimum ≤ top_leaf17_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf17_minimum,top_leaf17_table]
theorem top_leaf17_identity (δ p : ℝ) :
    top_leaf17_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf17_table
      ((δ-(231/512))/((465/1024)-(231/512)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [top_leaf17_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf17_table,Fin.sum_univ_succ]
  ring
theorem top_leaf17_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) : 0 < top_leaf17_power δ p := by
  rw [top_leaf17_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf17_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf17_lower

theorem top_leaf17_binding (δ p : ℝ) :
    top_leaf17_power δ p=(affineJ Plane.PR62.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.PR62.lambda Plane.PR62.B δ p)/4 := by
  norm_num [top_leaf17_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf17_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window4.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (127/256:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window4_admissible δ p ha).j
    change 0 < affineJ Plane.PR62.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.PR62.B) hj.ne'
    have hc := count_le_window4 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.PR62.lambda Plane.PR62.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf17_binding δ p) (top_leaf17_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf18_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-2979979156318186151/68330251800000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (5175833912115184487/28470938250000000000)*δ^1*p^1 +
  (260800155947732385100103/8646339464910006000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-647021017524568341/759225020000000000)*δ^2*p^1 +
  (214339672698956147/379612510000000000)*δ^2*p^2 +
  (-115755591881443853/720528288742500500)*δ^2*p^3

def top_leaf18_minimum : ℝ := 3800956108018411171038661541/424984877379256614912000000000000
def top_leaf18_table : Fin 3 → Fin 4 → ℝ := ![
  ![(634638947064671702021555605296937/4456289427828313842379653120000000000:ℝ), (13444442080341363591022337097789733/133688682834849415271389593600000000000:ℝ), (61755266317261524749081556405577/1044442834647261056807731200000000000:ℝ), (24613448652580620309587128201/1359951607613621167718400000000000:ℝ)],
  ![(3841184812778285930634541517268901/27851808923926961514872832000000000000:ℝ), (3200464231308257344654107532553497/33422170708712353817847398400000000000:ℝ), (70520601706580520635149803469313/1305553543309076321009664000000000000:ℝ), (21562951232880365933479700417/1699939509517026459648000000000000:ℝ)],
  ![(940716638432982014813371745441113/6962952230981740378718208000000000000:ℝ), (774013246775135652060203419241053/8355542677178088454461849600000000000:ℝ), (16509457349005024537089387633509/326388385827269080252416000000000000:ℝ), (3800956108018411171038661541/424984877379256614912000000000000:ℝ)]]
theorem top_leaf18_lower (i : Fin 3) (j : Fin 4) :
    top_leaf18_minimum ≤ top_leaf18_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf18_minimum,top_leaf18_table]
theorem top_leaf18_identity (δ p : ℝ) :
    top_leaf18_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf18_table
      ((δ-(465/1024))/((117/256)-(465/1024)))
      ((p-(127/256))/((1/2)-(127/256))) := by
  norm_num [top_leaf18_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf18_table,Fin.sum_univ_succ]
  ring
theorem top_leaf18_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) : 0 < top_leaf18_power δ p := by
  rw [top_leaf18_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf18_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf18_lower

theorem top_leaf18_binding (δ p : ℝ) :
    top_leaf18_power δ p=(affineJ Plane.A.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.A.lambda Plane.A.B δ p)/4 := by
  norm_num [top_leaf18_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf18_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window5.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (127/256:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window5_admissible δ p ha).j
    change 0 < affineJ Plane.A.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.A.B) hj.ne'
    have hc := count_le_window5 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.A.lambda Plane.A.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf18_binding δ p) (top_leaf18_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf19_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf19_minimum : ℝ := 185712017860286955284277116623/1145871696351140511744000000000000
def top_leaf19_table : Fin 3 → Fin 4 → ℝ := ![
  ![(909892767587374695807299412743/2062569053432052921139200000000000:ℝ), (21522089579499807080701438844803/61877071602961587634176000000000000:ℝ), (31704285965042212106272527235357/123754143205923175268352000000000000:ℝ), (1523867795440546578800927731733/9166973570809124093952000000000000:ℝ)],
  ![(114760566442387130247441506389/257821131679006615142400000000000:ℝ), (2699707992224101811206039986713/7734633950370198454272000000000000:ℝ), (3939980156267602605526017768887/15469267900740396908544000000000000:ℝ), (185712017860286955284277116623/1145871696351140511744000000000000:ℝ)],
  ![(15408366440646505413207168959/32227641459875826892800000000000:ℝ), (73311975403854546900402785279/193365848759254961356800000000000:ℝ), (109032278196100411948350279233/386731697518509922713600000000000:ℝ), (5342213746964478421259493433/28646792408778512793600000000000:ℝ)]]
theorem top_leaf19_lower (i : Fin 3) (j : Fin 4) :
    top_leaf19_minimum ≤ top_leaf19_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf19_minimum,top_leaf19_table]
theorem top_leaf19_identity (δ p : ℝ) :
    top_leaf19_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf19_table
      ((δ-(117/256))/((15/32)-(117/256)))
      ((p-(31/64))/((63/128)-(31/64))) := by
  norm_num [top_leaf19_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf19_table,Fin.sum_univ_succ]
  ring
theorem top_leaf19_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) : 0 < top_leaf19_power δ p := by
  rw [top_leaf19_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf19_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf19_lower

theorem top_leaf19_binding (δ p : ℝ) :
    top_leaf19_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf19_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf19_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf19_binding δ p) (top_leaf19_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf20_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-3282005976578734879/74553002200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (3910849747934499310909929589/21225939219883141500000000000)*δ^1*p^1 +
  (4938611284035474347392679/169807513759065132000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-9702244974601811056145637/11320500917271008800000000)*δ^2*p^1 +
  (5053173542568487237202169/8844141341617975625000000)*δ^2*p^2 +
  (-115755591881443853/707531307329438050)*δ^2*p^3

def top_leaf20_minimum : ℝ := 17678797435263724247692525273/11128505221714092490752000000000000
def top_leaf20_table : Fin 3 → Fin 4 → ℝ := ![
  ![(751661099956420200039153753988723/2848897336758807677632512000000000000:ℝ), (42170915127161530142059602992867/237408111396567306469376000000000000:ℝ), (3315048932538983917341190423657/35611216709485095970406400000000000:ℝ), (28392066402010319387309730409/2782126305428523122688000000000000:ℝ)],
  ![(1481008956617868738022397434701227/5697794673517615355265024000000000000:ℝ), (245652875740566563555269646141909/1424448668379403838816256000000000000:ℝ), (2057718352605239881486751686123/23740811139656730646937600000000000:ℝ), (14294555550755021946276411521/5564252610857046245376000000000000:ℝ)],
  ![(2994494011113992491696347343869091/11395589347035230710530048000000000000:ℝ), (495730839559005774885047989133057/2848897336758807677632512000000000000:ℝ), (12385706820048117715659721507673/142444866837940383881625600000000000:ℝ), (17678797435263724247692525273/11128505221714092490752000000000000:ℝ)]]
theorem top_leaf20_lower (i : Fin 3) (j : Fin 4) :
    top_leaf20_minimum ≤ top_leaf20_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf20_minimum,top_leaf20_table]
theorem top_leaf20_identity (δ p : ℝ) :
    top_leaf20_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf20_table
      ((δ-(117/256))/((237/512)-(117/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [top_leaf20_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf20_table,Fin.sum_univ_succ]
  ring
theorem top_leaf20_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) : 0 < top_leaf20_power δ p := by
  rw [top_leaf20_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf20_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf20_lower

theorem top_leaf20_binding (δ p : ℝ) :
    top_leaf20_power δ p=(affineJ Plane.C.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.C.lambda Plane.C.B δ p)/4 := by
  norm_num [top_leaf20_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf20_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window6.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (63/128:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window6_admissible δ p ha).j
    change 0 < affineJ Plane.C.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.C.B) hj.ne'
    have hc := count_le_window6 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.C.lambda Plane.C.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf20_binding δ p) (top_leaf20_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf21_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-3282005976578734879/74553002200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (3910849747934499310909929589/21225939219883141500000000000)*δ^1*p^1 +
  (4938611284035474347392679/169807513759065132000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-9702244974601811056145637/11320500917271008800000000)*δ^2*p^1 +
  (5053173542568487237202169/8844141341617975625000000)*δ^2*p^2 +
  (-115755591881443853/707531307329438050)*δ^2*p^3

def top_leaf21_minimum : ℝ := 423030235563587787677014219/695531576357130780672000000000000
def top_leaf21_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2994494011113992491696347343869091/11395589347035230710530048000000000000:ℝ), (495730839559005774885047989133057/2848897336758807677632512000000000000:ℝ), (12385706820048117715659721507673/142444866837940383881625600000000000:ℝ), (17678797435263724247692525273/11128505221714092490752000000000000:ℝ)],
  ![(189185631812015469209243738645983/712224334189701919408128000000000000:ℝ), (20839830318203267610814861915929/118704055698283653234688000000000000:ℝ), (776568970279049758899933306163/8902804177371273992601600000000000:ℝ), (423030235563587787677014219/695531576357130780672000000000000:ℝ)],
  ![(2450428743233360049033456963923/8902804177371273992601600000000000:ℝ), (12786897798765355293035889241/69553157635713078067200000000000:ℝ), (17471071025810741375418759451/185475087028568208179200000000000:ℝ), (54630477299262499195154477/8694144704464134758400000000000:ℝ)]]
theorem top_leaf21_lower (i : Fin 3) (j : Fin 4) :
    top_leaf21_minimum ≤ top_leaf21_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf21_minimum,top_leaf21_table]
theorem top_leaf21_identity (δ p : ℝ) :
    top_leaf21_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf21_table
      ((δ-(237/512))/((15/32)-(237/512)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [top_leaf21_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf21_table,Fin.sum_univ_succ]
  ring
theorem top_leaf21_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) : 0 < top_leaf21_power δ p := by
  rw [top_leaf21_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf21_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf21_lower

theorem top_leaf21_binding (δ p : ℝ) :
    top_leaf21_power δ p=(affineJ Plane.C.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.C.lambda Plane.C.B δ p)/4 := by
  norm_num [top_leaf21_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf21_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window7.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (63/128:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window7_admissible δ p ha).j
    change 0 < affineJ Plane.C.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.C.B) hj.ne'
    have hc := count_le_window7 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.C.lambda Plane.C.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf21_binding δ p) (top_leaf21_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf22_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf22_minimum : ℝ := 2471402831784083085964381387/1007113795621119590400000000000
def top_leaf22_table : Fin 3 → Fin 4 → ℝ := ![
  ![(479651336889328898565644351/83926149635093299200000000000:ℝ), (850594753692228413683185871/188833836678959923200000000000:ℝ), (10332428006736538540930279361/3021341386863358771200000000000:ℝ), (2471402831784083085964381387/1007113795621119590400000000000:ℝ)],
  ![(1499333876488345041786838577/209815374087733248000000000000:ℝ), (2678975667454068299698605739/472084591697399808000000000000:ℝ), (32874735593439999879182092751/7553353467158396928000000000000:ℝ), (7981155956388804728978495101/2517784489052798976000000000000:ℝ)],
  ![(1140026498279232127595876707/104907687043866624000000000000:ℝ), (2135254630896929455004109119/236042295848699904000000000000:ℝ), (27949915566955743545886657181/3776676733579198464000000000000:ℝ), (7452974166567912083090650511/1258892244526399488000000000000:ℝ)]]
theorem top_leaf22_lower (i : Fin 3) (j : Fin 4) :
    top_leaf22_minimum ≤ top_leaf22_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf22_minimum,top_leaf22_table]
theorem top_leaf22_identity (δ p : ℝ) :
    top_leaf22_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf22_table
      ((δ-(15/32))/((9/16)-(15/32)))
      ((p-(3/8))/((7/16)-(3/8))) := by
  norm_num [top_leaf22_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf22_table,Fin.sum_univ_succ]
  ring
theorem top_leaf22_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16)) : 0 < top_leaf22_power δ p := by
  rw [top_leaf22_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf22_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf22_lower

theorem top_leaf22_binding (δ p : ℝ) :
    top_leaf22_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf22_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf22_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf22_binding δ p) (top_leaf22_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf23_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf23_minimum : ℝ := 734063044341367793889247733/671409197080746393600000000000
def top_leaf23_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2471402831784083085964381387/1007113795621119590400000000000:ℝ), (5955098739660104616374576561/3021341386863358771200000000000:ℝ), (18342824476826666694387595219/12085365547453435084800000000000:ℝ), (734063044341367793889247733/671409197080746393600000000000:ℝ)],
  ![(28319326071698024887778897137/10071137956211195904000000000000:ℝ), (68731161712359765763497245963/30213413868633587712000000000000:ℝ), (42785387653275795175389396437/24170731094906870169600000000000:ℝ), (8706551221952316745091496251/6714091970807463936000000000000:ℝ)],
  ![(74093534650747282678098489383/20142275912422391808000000000000:ℝ), (185940533590729938848980003957/60426827737267175424000000000000:ℝ), (121383857381684952654945890947/48341462189813740339200000000000:ℝ), (26573776121675715400574875969/13428183941614927872000000000000:ℝ)]]
theorem top_leaf23_lower (i : Fin 3) (j : Fin 4) :
    top_leaf23_minimum ≤ top_leaf23_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf23_minimum,top_leaf23_table]
theorem top_leaf23_identity (δ p : ℝ) :
    top_leaf23_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf23_table
      ((δ-(15/32))/((33/64)-(15/32)))
      ((p-(7/16))/((15/32)-(7/16))) := by
  norm_num [top_leaf23_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf23_table,Fin.sum_univ_succ]
  ring
theorem top_leaf23_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32)) : 0 < top_leaf23_power δ p := by
  rw [top_leaf23_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf23_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf23_lower

theorem top_leaf23_binding (δ p : ℝ) :
    top_leaf23_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf23_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf23_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf23_binding δ p) (top_leaf23_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf24_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf24_minimum : ℝ := 15408366440646505413207168959/32227641459875826892800000000000
def top_leaf24_table : Fin 3 → Fin 4 → ℝ := ![
  ![(734063044341367793889247733/671409197080746393600000000000:ℝ), (21296579917607194175631782363/24170731094906870169600000000000:ℝ), (8170415320245500227307716919/12085365547453435084800000000000:ℝ), (15408366440646505413207168959/32227641459875826892800000000000:ℝ)],
  ![(16047181665365994683983973581/13428183941614927872000000000000:ℝ), (469192626895118070114311638999/483414621898137403392000000000000:ℝ), (182160232004315132397359540041/241707310949068701696000000000000:ℝ), (70139830845370934711044521119/128910565839503307571200000000000:ℝ)],
  ![(76081241896312338258725815633/53712735766459711488000000000000:ℝ), (2278903532890392265300924756327/1933658487592549613568000000000000:ℝ), (917032157768309792703452120383/966829243796274806784000000000000:ℝ), (374443940423180349370535589503/515642263358013230284800000000000:ℝ)]]
theorem top_leaf24_lower (i : Fin 3) (j : Fin 4) :
    top_leaf24_minimum ≤ top_leaf24_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf24_minimum,top_leaf24_table]
theorem top_leaf24_identity (δ p : ℝ) :
    top_leaf24_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf24_table
      ((δ-(15/32))/((63/128)-(15/32)))
      ((p-(15/32))/((31/64)-(15/32))) := by
  norm_num [top_leaf24_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf24_table,Fin.sum_univ_succ]
  ring
theorem top_leaf24_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) : 0 < top_leaf24_power δ p := by
  rw [top_leaf24_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf24_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf24_lower

theorem top_leaf24_binding (δ p : ℝ) :
    top_leaf24_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf24_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf24_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf24_binding δ p) (top_leaf24_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf25_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf25_minimum : ℝ := 5342213746964478421259493433/28646792408778512793600000000000
def top_leaf25_table : Fin 3 → Fin 4 → ℝ := ![
  ![(15408366440646505413207168959/32227641459875826892800000000000:ℝ), (73311975403854546900402785279/193365848759254961356800000000000:ℝ), (109032278196100411948350279233/386731697518509922713600000000000:ℝ), (5342213746964478421259493433/28646792408778512793600000000000:ℝ)],
  ![(26354659321591391272774639391/51564226335801323028480000000000:ℝ), (3165250040084261940826182835607/7734633950370198454272000000000000:ℝ), (4782602099420430350342004569753/15469267900740396908544000000000000:ℝ), (241665081896871318416482358017/1145871696351140511744000000000000:ℝ)],
  ![(1182096450236491913670206461799/2062569053432052921139200000000000:ℝ), (28970762345262369154623724427107/61877071602961587634176000000000000:ℝ), (45186237055487456023328316049213/123754143205923175268352000000000000:ℝ), (2419116820025896388916211594037/9166973570809124093952000000000000:ℝ)]]
theorem top_leaf25_lower (i : Fin 3) (j : Fin 4) :
    top_leaf25_minimum ≤ top_leaf25_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf25_minimum,top_leaf25_table]
theorem top_leaf25_identity (δ p : ℝ) :
    top_leaf25_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf25_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(31/64))/((63/128)-(31/64))) := by
  norm_num [top_leaf25_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf25_table,Fin.sum_univ_succ]
  ring
theorem top_leaf25_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) : 0 < top_leaf25_power δ p := by
  rw [top_leaf25_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf25_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf25_lower

theorem top_leaf25_binding (δ p : ℝ) :
    top_leaf25_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf25_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf25_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf25_binding δ p) (top_leaf25_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf26_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-3282005976578734879/74553002200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (3910849747934499310909929589/21225939219883141500000000000)*δ^1*p^1 +
  (4938611284035474347392679/169807513759065132000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-9702244974601811056145637/11320500917271008800000000)*δ^2*p^1 +
  (5053173542568487237202169/8844141341617975625000000)*δ^2*p^2 +
  (-115755591881443853/707531307329438050)*δ^2*p^3

def top_leaf26_minimum : ℝ := 54630477299262499195154477/8694144704464134758400000000000
def top_leaf26_table : Fin 3 → Fin 4 → ℝ := ![
  ![(2450428743233360049033456963923/8902804177371273992601600000000000:ℝ), (12786897798765355293035889241/69553157635713078067200000000000:ℝ), (17471071025810741375418759451/185475087028568208179200000000000:ℝ), (54630477299262499195154477/8694144704464134758400000000000:ℝ)],
  ![(104865817375987736674771097024777/356112167094850959704064000000000000:ℝ), (11894628046636041939357014541031/59352027849141826617344000000000000:ℝ), (481348143579323620130217374309/4451402088685636996300800000000000:ℝ), (6132627040347912115741523021/347765788178565390336000000000000:ℝ)],
  ![(970818464649326910869003944960147/2848897336758807677632512000000000000:ℝ), (173703557782585650712565483636729/712224334189701919408128000000000000:ℝ), (5300406979254690385186539143177/35611216709485095970406400000000000:ℝ), (154709120750087508121240736521/2782126305428523122688000000000000:ℝ)]]
theorem top_leaf26_lower (i : Fin 3) (j : Fin 4) :
    top_leaf26_minimum ≤ top_leaf26_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf26_minimum,top_leaf26_table]
theorem top_leaf26_identity (δ p : ℝ) :
    top_leaf26_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf26_table
      ((δ-(15/32))/((123/256)-(15/32)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [top_leaf26_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf26_table,Fin.sum_univ_succ]
  ring
theorem top_leaf26_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) : 0 < top_leaf26_power δ p := by
  rw [top_leaf26_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf26_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf26_lower

theorem top_leaf26_binding (δ p : ℝ) :
    top_leaf26_power δ p=(affineJ Plane.C.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.C.lambda Plane.C.B δ p)/4 := by
  norm_num [top_leaf26_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf26_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window8.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (63/128:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window8_admissible δ p ha).j
    change 0 < affineJ Plane.C.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.C.B) hj.ne'
    have hc := count_le_window8 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.C.lambda Plane.C.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf26_binding δ p) (top_leaf26_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf27_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf27_minimum : ℝ := 2419116820025896388916211594037/9166973570809124093952000000000000
def top_leaf27_table : Fin 3 → Fin 4 → ℝ := ![
  ![(1182096450236491913670206461799/2062569053432052921139200000000000:ℝ), (28970762345262369154623724427107/61877071602961587634176000000000000:ℝ), (45186237055487456023328316049213/123754143205923175268352000000000000:ℝ), (2419116820025896388916211594037/9166973570809124093952000000000000:ℝ)],
  ![(655003263804664088214713673979/1031284526716026460569600000000000:ℝ), (16309762184925321391318993084679/30938535801480793817088000000000000:ℝ), (26055828657805734621960297770201/61877071602961587634176000000000000:ℝ), (1452456492438411115250282161969/4583486785404562046976000000000000:ℝ)],
  ![(374443940423180349370535589503/515642263358013230284800000000000:ℝ), (9513720056896637380046484564571/15469267900740396908544000000000000:ℝ), (15648002515812046176460301829829/30938535801480793817088000000000000:ℝ), (913173264608084115285112204541/2291743392702281023488000000000000:ℝ)]]
theorem top_leaf27_lower (i : Fin 3) (j : Fin 4) :
    top_leaf27_minimum ≤ top_leaf27_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf27_minimum,top_leaf27_table]
theorem top_leaf27_identity (δ p : ℝ) :
    top_leaf27_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf27_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(31/64))/((63/128)-(31/64))) := by
  norm_num [top_leaf27_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf27_table,Fin.sum_univ_succ]
  ring
theorem top_leaf27_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) : 0 < top_leaf27_power δ p := by
  rw [top_leaf27_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf27_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf27_lower

theorem top_leaf27_binding (δ p : ℝ) :
    top_leaf27_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf27_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf27_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf27_binding δ p) (top_leaf27_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf28_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-3282005976578734879/74553002200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (3910849747934499310909929589/21225939219883141500000000000)*δ^1*p^1 +
  (4938611284035474347392679/169807513759065132000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-9702244974601811056145637/11320500917271008800000000)*δ^2*p^1 +
  (5053173542568487237202169/8844141341617975625000000)*δ^2*p^2 +
  (-115755591881443853/707531307329438050)*δ^2*p^3

def top_leaf28_minimum : ℝ := 154709120750087508121240736521/2782126305428523122688000000000000
def top_leaf28_table : Fin 3 → Fin 4 → ℝ := ![
  ![(970818464649326910869003944960147/2848897336758807677632512000000000000:ℝ), (173703557782585650712565483636729/712224334189701919408128000000000000:ℝ), (5300406979254690385186539143177/35611216709485095970406400000000000:ℝ), (154709120750087508121240736521/2782126305428523122688000000000000:ℝ)],
  ![(551355195145375964169919556861039/1424448668379403838816256000000000000:ℝ), (102335789502769399076423396390543/356112167094850959704064000000000000:ℝ), (1125004801645798634888556548647/5935202784914182661734400000000000:ℝ), (130178612588695859658274644437/1391063152714261561344000000000000:ℝ)],
  ![(327926225100093821393511725875771/712224334189701919408128000000000000:ℝ), (21234159862597485663484395200439/59352027849141826617344000000000000:ℝ), (2288233239859017010164900602353/8902804177371273992601600000000000:ℝ), (110018542611245211130920910513/695531576357130780672000000000000:ℝ)]]
theorem top_leaf28_lower (i : Fin 3) (j : Fin 4) :
    top_leaf28_minimum ≤ top_leaf28_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf28_minimum,top_leaf28_table]
theorem top_leaf28_identity (δ p : ℝ) :
    top_leaf28_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf28_table
      ((δ-(123/256))/((63/128)-(123/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [top_leaf28_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf28_table,Fin.sum_univ_succ]
  ring
theorem top_leaf28_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) : 0 < top_leaf28_power δ p := by
  rw [top_leaf28_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf28_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf28_lower

theorem top_leaf28_binding (δ p : ℝ) :
    top_leaf28_power δ p=(affineJ Plane.C.lambda δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(affineN Plane.C.lambda Plane.C.B δ p)/4 := by
  norm_num [top_leaf28_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf28_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have ha : window9.Available δ p := by
      constructor
      · exact hδ
      · change p ∈ Set.Icc (63/128:ℝ) (1/2)
        constructor <;> linarith [hp.1,hp.2]
    have hj := (window9_admissible δ p ha).j
    change 0 < affineJ Plane.C.lambda δ p at hj
    have hn := affine_count_mul (B:=Plane.C.B) hj.ne'
    have hc := count_le_window9 (κ:=kappaStar) ha
    change count kappaStar δ p ≤ affineR Plane.C.lambda Plane.C.B δ p at hc
    have hr := positive_polynomial_to_row hj hn (top_leaf28_binding δ p) (top_leaf28_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf29_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf29_minimum : ℝ := 103543564668675046044684877/1258892244526399488000000000000
def top_leaf29_table : Fin 3 → Fin 4 → ℝ := ![
  ![(76081241896312338258725815633/53712735766459711488000000000000:ℝ), (909441178756770176643860074933/966829243796274806784000000000000:ℝ), (14993247482064897777156989071/30213413868633587712000000000000:ℝ), (103543564668675046044684877/1258892244526399488000000000000:ℝ)],
  ![(43986878565580348890757868471/26856367883229855744000000000000:ℝ), (548754464919709845038659845851/483414621898137403392000000000000:ℝ), (10049188469339129422624088657/15106706934316793856000000000000:ℝ), (142857915352141874355682979/629446122263199744000000000000:ℝ)],
  ![(26573776121675715400574875969/13428183941614927872000000000000:ℝ), (349736653471900991145966080149/241707310949068701696000000000000:ℝ), (7168652109058506598074789583/7553353467158396928000000000000:ℝ), (152399360662444008625477741/314723061131599872000000000000:ℝ)]]
theorem top_leaf29_lower (i : Fin 3) (j : Fin 4) :
    top_leaf29_minimum ≤ top_leaf29_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf29_minimum,top_leaf29_table]
theorem top_leaf29_identity (δ p : ℝ) :
    top_leaf29_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf29_table
      ((δ-(63/128))/((33/64)-(63/128)))
      ((p-(15/32))/((1/2)-(15/32))) := by
  norm_num [top_leaf29_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf29_table,Fin.sum_univ_succ]
  ring
theorem top_leaf29_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2)) : 0 < top_leaf29_power δ p := by
  rw [top_leaf29_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf29_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf29_lower

theorem top_leaf29_binding (δ p : ℝ) :
    top_leaf29_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf29_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf29_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf29_binding δ p) (top_leaf29_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf30_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf30_minimum : ℝ := 152399360662444008625477741/314723061131599872000000000000
def top_leaf30_table : Fin 3 → Fin 4 → ℝ := ![
  ![(74093534650747282678098489383/20142275912422391808000000000000:ℝ), (29920092645843605932732907953/12085365547453435084800000000000:ℝ), (5339859781109178494569056691/3776676733579198464000000000000:ℝ), (152399360662444008625477741/314723061131599872000000000000:ℝ)],
  ![(22887104289524628895159796123/5035568978105597952000000000000:ℝ), (388384472078370291200026957/120853655474534350848000000000:ℝ), (1921171464553527138337819291/944169183394799616000000000000:ℝ), (78585041658797537880187561/78680765282899968000000000000:ℝ)],
  ![(7452974166567912083090650511/1258892244526399488000000000000:ℝ), (3353585886490345790531449177/755335346715839692800000000000:ℝ), (737506364083927630850432707/236042295848699904000000000000:ℝ), (38624394907363742346242917/19670191320724992000000000000:ℝ)]]
theorem top_leaf30_lower (i : Fin 3) (j : Fin 4) :
    top_leaf30_minimum ≤ top_leaf30_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf30_minimum,top_leaf30_table]
theorem top_leaf30_identity (δ p : ℝ) :
    top_leaf30_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf30_table
      ((δ-(33/64))/((9/16)-(33/64)))
      ((p-(7/16))/((1/2)-(7/16))) := by
  norm_num [top_leaf30_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf30_table,Fin.sum_univ_succ]
  ring
theorem top_leaf30_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2)) : 0 < top_leaf30_power δ p := by
  rw [top_leaf30_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf30_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf30_lower

theorem top_leaf30_binding (δ p : ℝ) :
    top_leaf30_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf30_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf30_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf30_binding δ p) (top_leaf30_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

def top_leaf31_power (δ p : ℝ) : ℝ := (38223849901/600000000000)*δ^0*p^0 +
  (-8120618687617549/202408200000000000)*δ^0*p^1 +
  (-837615199427/3000000000000)*δ^1*p^0 +
  (2036983885231502328138527/12806114141097000000000000)*δ^1*p^1 +
  (1407278615775789714199/34149637709592000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-230186211742441198267/284580314246600000000)*δ^2*p^1 +
  (43131241997692261300997/85374094273980000000000)*δ^2*p^2 +
  (-115755591881443853/853740942739800000)*δ^2*p^3

def top_leaf31_minimum : ℝ := 38624394907363742346242917/19670191320724992000000000000
def top_leaf31_table : Fin 3 → Fin 4 → ℝ := ![
  ![(377380565188514402322441361/15736153056579993600000000000:ℝ), (3239211344432749985641095953/236042295848699904000000000000:ℝ), (194943404958826974867123227/29505286981087488000000000000:ℝ), (38624394907363742346242917/19670191320724992000000000000:ℝ)],
  ![(71382144405659019708268013/1967019132072499200000000000:ℝ), (658616045312747594656189567/29505286981087488000000000000:ℝ), (183881989990980112813775257/14752643490543744000000000000:ℝ), (7158558304876323365689189/1229386957545312000000000000:ℝ)],
  ![(59110714967760277341710227/983509566036249600000000000:ℝ), (600747465521422291064158859/14752643490543744000000000000:ℝ), (12315428803476860829176609/461020109079492000000000000:ℝ), (20759926047410136779979691/1229386957545312000000000000:ℝ)]]
theorem top_leaf31_lower (i : Fin 3) (j : Fin 4) :
    top_leaf31_minimum ≤ top_leaf31_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_leaf31_minimum,top_leaf31_table]
theorem top_leaf31_identity (δ p : ℝ) :
    top_leaf31_power δ p=Cycle63.Arithmetic.Bernstein.tensor top_leaf31_table
      ((δ-(9/16))/((3/4)-(9/16)))
      ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [top_leaf31_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    top_leaf31_table,Fin.sum_univ_succ]
  ring
theorem top_leaf31_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) : 0 < top_leaf31_power δ p := by
  rw [top_leaf31_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [top_leaf31_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) top_leaf31_lower

theorem top_leaf31_binding (δ p : ℝ) :
    top_leaf31_power δ p=(oldJ δ p)*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*(dPlus)*(oldN δ p)/4 := by
  norm_num [top_leaf31_power,rowBase,reserve,d0,oldCapacityAt,newCapacity,oldJ,oldD,oldP,oldN,affineJ,affineD,affineA,affineC,affineU,affineN,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,theta,h,x,y,ell,kappaStar,dMinus,dPlus,slotClip]
  <;> ring
theorem top_leaf31_bound {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4))
    (hp : p ∈ Set.Icc (1/4:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
    have hdg : δ ∈ Set.Icc (0:ℝ) (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
    have hpg : p ∈ Set.Icc (0:ℝ) (1/2) := by constructor <;> linarith [hp.1,hp.2]
    have hj := oldJ_pos hdg hpg
    have hn := old_count_mul hdg hpg
    have hc := count_le_old kappaStar δ p
    have hr := positive_polynomial_to_row hj hn (top_leaf31_binding δ p) (top_leaf31_positive hδ hp)
    have hd : 0 ≤ 3*(dPlus)/4 := by norm_num [dPlus,d0,y,dMinus,dPlus,h,ell,theta]
    have hm := mul_le_mul_of_nonneg_left hc hd
    unfold rowAt
    nlinarith

theorem top_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    rowAt kappaStar dPlus (newCapacity dPlus) δ p ≤ theta-reserve := by
  by_cases h1 : δ ≤ (3/8:ℝ)
  ·
    apply top_leaf0_bound
    all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  ·
    by_cases h2 : p ≤ (1/4:ℝ)
    ·
      apply top_leaf1_bound
      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
    ·
      by_cases h3 : δ ≤ (9/16:ℝ)
      ·
        by_cases h4 : p ≤ (3/8:ℝ)
        ·
          apply top_leaf2_bound
          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
        ·
          by_cases h5 : δ ≤ (15/32:ℝ)
          ·
            by_cases h6 : p ≤ (7/16:ℝ)
            ·
              apply top_leaf3_bound
              all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
            ·
              by_cases h7 : δ ≤ (27/64:ℝ)
              ·
                apply top_leaf4_bound
                all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
              ·
                by_cases h8 : p ≤ (15/32:ℝ)
                ·
                  apply top_leaf5_bound
                  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                ·
                  by_cases h9 : δ ≤ (57/128:ℝ)
                  ·
                    by_cases h10 : p ≤ (31/64:ℝ)
                    ·
                      apply top_leaf6_bound
                      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                    ·
                      by_cases h11 : δ ≤ (111/256:ℝ)
                      ·
                        apply top_leaf7_bound
                        all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                      ·
                        by_cases h12 : p ≤ (63/128:ℝ)
                        ·
                          apply top_leaf8_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                        ·
                          apply top_leaf9_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                  ·
                    by_cases h10 : p ≤ (31/64:ℝ)
                    ·
                      apply top_leaf10_bound
                      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                    ·
                      by_cases h11 : δ ≤ (117/256:ℝ)
                      ·
                        by_cases h12 : p ≤ (63/128:ℝ)
                        ·
                          apply top_leaf11_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                        ·
                          by_cases h13 : δ ≤ (231/512:ℝ)
                          ·
                            by_cases h14 : p ≤ (127/256:ℝ)
                            ·
                              apply top_leaf12_bound
                              all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                            ·
                              by_cases h15 : δ ≤ (459/1024:ℝ)
                              ·
                                by_cases h16 : p ≤ (255/512:ℝ)
                                ·
                                  apply top_leaf13_bound
                                  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                                ·
                                  apply top_leaf14_bound
                                  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                              ·
                                apply top_leaf15_bound
                                all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                          ·
                            by_cases h14 : p ≤ (127/256:ℝ)
                            ·
                              apply top_leaf16_bound
                              all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                            ·
                              by_cases h15 : δ ≤ (465/1024:ℝ)
                              ·
                                apply top_leaf17_bound
                                all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                              ·
                                apply top_leaf18_bound
                                all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                      ·
                        by_cases h12 : p ≤ (63/128:ℝ)
                        ·
                          apply top_leaf19_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                        ·
                          by_cases h13 : δ ≤ (237/512:ℝ)
                          ·
                            apply top_leaf20_bound
                            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                          ·
                            apply top_leaf21_bound
                            all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
          ·
            by_cases h6 : p ≤ (7/16:ℝ)
            ·
              apply top_leaf22_bound
              all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
            ·
              by_cases h7 : δ ≤ (33/64:ℝ)
              ·
                by_cases h8 : p ≤ (15/32:ℝ)
                ·
                  apply top_leaf23_bound
                  all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                ·
                  by_cases h9 : δ ≤ (63/128:ℝ)
                  ·
                    by_cases h10 : p ≤ (31/64:ℝ)
                    ·
                      apply top_leaf24_bound
                      all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                    ·
                      by_cases h11 : δ ≤ (123/256:ℝ)
                      ·
                        by_cases h12 : p ≤ (63/128:ℝ)
                        ·
                          apply top_leaf25_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                        ·
                          apply top_leaf26_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                      ·
                        by_cases h12 : p ≤ (63/128:ℝ)
                        ·
                          apply top_leaf27_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                        ·
                          apply top_leaf28_bound
                          all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
                  ·
                    apply top_leaf29_bound
                    all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
              ·
                apply top_leaf30_bound
                all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
      ·
        apply top_leaf31_bound
        all_goals constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]

end
end OAI.SevenEighths.Target830.Count.Certificates

#print axioms OAI.SevenEighths.Target830.Count.Certificates.top_bound
