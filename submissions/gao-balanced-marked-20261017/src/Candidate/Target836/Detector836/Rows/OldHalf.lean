import Candidate.Target836.Detector836.EndpointArithmetic
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Target836.EndpointCertificates
noncomputable section
open Target836.Arithmetic Target836.EndpointArithmetic
open Cycle63.Arithmetic.Bernstein (tensor basis2 basis3 tensor_pos normalize_mem)

def old_half_old_power (δ p : ℝ) : ℝ := (37043573/60000000)*δ^0*p^0 +
  (-2810691685253/7228980000000)*δ^0*p^1 +
  (-23030033/25000000)*δ^1*p^0 +
  (5141894211229/42169050000000)*δ^1*p^1 +
  (697152112952231/2540326825575000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-27516761233/120483000000)*δ^2*p^1 +
  (6973141121/52711312500)*δ^2*p^2 +
  (-3497681087/33871024341)*δ^2*p^3
def old_half_old_minimum0 : ℝ := 1228360428013022472367/8129045841840000000000
theorem old_half_old_minimum0_pos : 0 < old_half_old_minimum0 := by norm_num [old_half_old_minimum0]
def old_half_old_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(37043573/60000000:ℝ), (23968033149301/43373880000000:ℝ), (1322333841503/2710867500000:ℝ), (1223109985253/2891592000000:ℝ)],
  ![(12372767689/30000000000:ℝ), (106917530193425251/303617160000000000:ℝ), (1810468305766581877217/6096784381380000000000:ℝ), (1003334943673641520819/4064522920920000000000:ℝ)],
  ![(4597061939/15000000000:ℝ), (147664279212228551/607234320000000000:ℝ), (2344084622522835021947/12193568762760000000000:ℝ), (1228360428013022472367/8129045841840000000000:ℝ)]]
theorem old_half_old_table0_lower (i : Fin 3) (j : Fin 4) : old_half_old_minimum0 ≤ old_half_old_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_old_minimum0,old_half_old_table0]
theorem old_half_old_identity0 (δ p : ℝ) :
    old_half_old_power δ p = tensor old_half_old_table0 ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_half_old_power,tensor,basis2,basis3,old_half_old_table0,Fin.sum_univ_succ]
  ring
theorem old_half_old_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (89/200)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_half_old_power δ p := by
  rw [old_half_old_identity0]
  exact tensor_pos old_half_old_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_old_table0_lower
def old_half_old_minimum1 : ℝ := 15773103432196633/273705247200000000
theorem old_half_old_minimum1_pos : 0 < old_half_old_minimum1 := by norm_num [old_half_old_minimum1]
def old_half_old_table1 : Fin 3 → Fin 4 → ℝ := ![
  ![(1072703387/3750000000:ℝ), (4816051547528027/21686940000000000:ℝ), (74877975483793730399/435484598670000000000:ℝ), (38486869237398230947/290323065780000000000:ℝ)],
  ![(1724985487/7500000000:ℝ), (24867437340312041/151808580000000000:ℝ), (353150407947442543897/3048392190690000000000:ℝ), (165375384718959371729/2032261460460000000000:ℝ)],
  ![(7790321/37500000:ℝ), (830520636378569/6072343200000000:ℝ), (3623658489770056351/40645229209200000000:ℝ), (15773103432196633/273705247200000000:ℝ)]]
theorem old_half_old_table1_lower (i : Fin 3) (j : Fin 4) : old_half_old_minimum1 ≤ old_half_old_table1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_old_minimum1,old_half_old_table1]
theorem old_half_old_identity1 (δ p : ℝ) :
    old_half_old_power δ p = tensor old_half_old_table1 ((δ-(49/100))/((3/4)-(49/100))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_half_old_power,tensor,basis2,basis3,old_half_old_table1,Fin.sum_univ_succ]
  ring
theorem old_half_old_leaf1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (49/100:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_half_old_power δ p := by
  rw [old_half_old_identity1]
  exact tensor_pos old_half_old_minimum1_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_old_table1_lower
def old_half_old_minimum2 : ℝ := 7873267789652236584040561/52786011960000000000000000
theorem old_half_old_minimum2_pos : 0 < old_half_old_minimum2 := by norm_num [old_half_old_minimum2]
def old_half_old_table2 : Fin 3 → Fin 4 → ℝ := ![
  ![(4597061939/15000000000:ℝ), (29571291148601918081/121446864000000000000:ℝ), (3357570385272207158871479/17419383946800000000000000:ℝ), (3523948136037703860441491/23225845262400000000000000:ℝ)],
  ![(11439082199/37500000000:ℝ), (20994912699972288889/86747760000000000000:ℝ), (116653816062375529253008927/609678438138000000000000000:ℝ), (17469615390968722502239969/116129226312000000000000000:ℝ)],
  ![(22772369101/75000000000:ℝ), (730412121640185332753/3036171600000000000000:ℝ), (52637372655760052696614963/277126562790000000000000000:ℝ), (7873267789652236584040561/52786011960000000000000000:ℝ)]]
theorem old_half_old_table2_lower (i : Fin 3) (j : Fin 4) : old_half_old_minimum2 ≤ old_half_old_table2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_old_minimum2,old_half_old_table2]
theorem old_half_old_identity2 (δ p : ℝ) :
    old_half_old_power δ p = tensor old_half_old_table2 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [old_half_old_power,tensor,basis2,basis3,old_half_old_table2,Fin.sum_univ_succ]
  ring
theorem old_half_old_leaf2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (0:ℝ) (199/400)) :
    0 < old_half_old_power δ p := by
  rw [old_half_old_identity2]
  exact tensor_pos old_half_old_minimum2_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_old_table2_lower
def old_half_old_minimum3 : ℝ := 48970662201905850621971/362903832225000000000000
theorem old_half_old_minimum3_pos : 0 < old_half_old_minimum3 := by norm_num [old_half_old_minimum3]
def old_half_old_table3 : Fin 3 → Fin 4 → ℝ := ![
  ![(22772369101/75000000000:ℝ), (26189233426892188529/108434700000000000000:ℝ), (947521439861875842683393/4948688621250000000000000:ℝ), (498186864739721773539811/3299125747500000000000000:ℝ)],
  ![(44169399341/150000000000:ℝ), (11439076799310851/49288500000000000:ℝ), (62049501361654514189197/340222342710937500000000:ℝ), (16179089719767414803947/113407447570312500000000:ℝ)],
  ![(1072703387/3750000000:ℝ), (242190166893317531/1084347000000000000:ℝ), (94692023107398350065873/544355748337500000000000:ℝ), (48970662201905850621971/362903832225000000000000:ℝ)]]
theorem old_half_old_table3_lower (i : Fin 3) (j : Fin 4) : old_half_old_minimum3 ≤ old_half_old_table3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_old_minimum3,old_half_old_table3]
theorem old_half_old_identity3 (δ p : ℝ) :
    old_half_old_power δ p = tensor old_half_old_table3 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(0))/((49/100)-(0))) := by
  norm_num [old_half_old_power,tensor,basis2,basis3,old_half_old_table3,Fin.sum_univ_succ]
  ring
theorem old_half_old_leaf3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (0:ℝ) (49/100)) :
    0 < old_half_old_power δ p := by
  rw [old_half_old_identity3]
  exact tensor_pos old_half_old_minimum3_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_old_table3_lower
theorem old_half_old_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hn : ¬Detector836.InRegion δ p) (ha : ¬Detector836.InAcceptedRegion δ p) :
    0 < old_half_old_power δ p := by
  rcases old_region_cover hδ hp hn ha with hb|hb|hb|hb
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_half_old_leaf0_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_half_old_leaf1_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_half_old_leaf2_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_half_old_leaf3_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_half_old_binding (δ p : ℝ) :
    old_half_old_power δ p = oldJ δ p*(theta-reserve-rowBase y (oldCapacity y) δ p)-3*y*oldN δ p/4 := by
  norm_num [old_half_old_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_half_affine_power (δ p : ℝ) : ℝ := (37043573/60000000)*δ^0*p^0 +
  (-1474074900389/3562740000000)*δ^0*p^1 +
  (-23030033/25000000)*δ^1*p^0 +
  (146040814513846313/953888007600000000)*δ^1*p^1 +
  (172002137224573993/572332804560000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-117832574885160607/476944003800000000)*δ^2*p^1 +
  (63067084921699607/476944003800000000)*δ^2*p^2 +
  (-6995362174/59618000475)*δ^2*p^3
def old_half_affine_minimum0 : ℝ := 7340809848527364839329/57233280456000000000000
theorem old_half_affine_minimum0_pos : 0 < old_half_affine_minimum0 := by norm_num [old_half_affine_minimum0]
def old_half_affine_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(190298390652290621329814111/1300756374000000000000000000:ℝ), (567604827250954482739699111/3902269122000000000000000000:ℝ), (225732419109075261174007/1560907648800000000000000:ℝ), (74809832051890488504389/520302549600000000000000:ℝ)],
  ![(3089380848489555205504561/22356750178125000000000000:ℝ), (9212746884332125715493311/67070250534375000000000000:ℝ), (7326117965516140529347/53656200427500000000000:ℝ), (1213712336535279035839/8942700071250000000000:ℝ)],
  ![(18697626042236451680585971/143083201140000000000000000:ℝ), (55745311996507496998290971/429249603420000000000000000:ℝ), (4431977168527756524943/34339968273600000000000:ℝ), (7340809848527364839329/57233280456000000000000:ℝ)]]
theorem old_half_affine_table0_lower (i : Fin 3) (j : Fin 4) : old_half_affine_minimum0 ≤ old_half_affine_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_affine_minimum0,old_half_affine_table0]
theorem old_half_affine_identity0 (δ p : ℝ) :
    old_half_affine_power δ p = tensor old_half_affine_table0 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [old_half_affine_power,tensor,basis2,basis3,old_half_affine_table0,Fin.sum_univ_succ]
  ring
theorem old_half_affine_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < old_half_affine_power δ p := by
  rw [old_half_affine_identity0]
  exact tensor_pos old_half_affine_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_affine_table0_lower
theorem old_half_affine_pos {δ p : ℝ} (h : Detector836.InRegion δ p) :
    0 < old_half_affine_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_half_affine_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_half_affine_binding (δ p : ℝ) :
    old_half_affine_power δ p = Detector836.JN δ p*(theta-reserve-rowBase y (oldCapacity y) δ p)-3*y*newN δ p/4 := by
  norm_num [old_half_affine_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_half_accepted_power (δ p : ℝ) : ℝ := (37043573/60000000)*δ^0*p^0 +
  (-23744930293/57936000000)*δ^0*p^1 +
  (-23030033/25000000)*δ^1*p^0 +
  (1380388939593333863/9307070784000000000)*δ^1*p^1 +
  (2758227636319006777/9307070784000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-5683010369694606229/23267676960000000000)*δ^2*p^1 +
  (3079424469738346229/23267676960000000000)*δ^2*p^2 +
  (-16743399363469/145422981000000)*δ^2*p^3
def old_half_accepted_minimum0 : ℝ := 407622143212600248665687/2820324480000000000000000
theorem old_half_accepted_minimum0_pos : 0 < old_half_accepted_minimum0 := by norm_num [old_half_accepted_minimum0]
def old_half_accepted_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(2443247815951346937404124001/16545903616000000000000000000:ℝ), (65873933240599862299653216409/446739397632000000000000000000:ℝ), (23162074265155574641963/157302604800000000000000:ℝ), (182463233024619213141197/1240942771200000000000000:ℝ)],
  ![(12111832837739857182567903359/82729518080000000000000000000:ℝ), (326552188263159163082571773831/2233696988160000000000000000000:ℝ), (8152136771665844622835507/55842424704000000000000000:ℝ), (301499382984188926816241/2068237952000000000000000:ℝ)],
  ![(5458458712824367590349817171/37604326400000000000000000000:ℝ), (147166648413225726909567122939/1015316812800000000000000000000:ℝ), (3673879432678983187206583/25382920320000000000000000:ℝ), (407622143212600248665687/2820324480000000000000000:ℝ)]]
theorem old_half_accepted_table0_lower (i : Fin 3) (j : Fin 4) : old_half_accepted_minimum0 ≤ old_half_accepted_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_half_accepted_minimum0,old_half_accepted_table0]
theorem old_half_accepted_identity0 (δ p : ℝ) :
    old_half_accepted_power δ p = tensor old_half_accepted_table0 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [old_half_accepted_power,tensor,basis2,basis3,old_half_accepted_table0,Fin.sum_univ_succ]
  ring
theorem old_half_accepted_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (199/400:ℝ) (1/2)) :
    0 < old_half_accepted_power δ p := by
  rw [old_half_accepted_identity0]
  exact tensor_pos old_half_accepted_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_half_accepted_table0_lower
theorem old_half_accepted_pos {δ p : ℝ} (h : Detector836.InAcceptedRegion δ p) :
    0 < old_half_accepted_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_half_accepted_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_half_accepted_binding (δ p : ℝ) :
    old_half_accepted_power δ p = DetectorAffine.JN δ p*(theta-reserve-rowBase y (oldCapacity y) δ p)-3*y*acceptedN δ p/4 := by
  norm_num [old_half_accepted_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring
theorem old_half_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent y δ p ≤ theta-reserve := by
  have hk : Detector836.kStar ≤ kappaStar := by rw [kappaStar_eq_detector]
  by_cases hn : Detector836.InRegion δ p
  · unfold oldExponent rowAt
    have hc : Detector836.count kappaStar δ p=Detector836.RNew δ p := by simp only [Detector836.count,hn,hk,and_self,ite_true]
    rw [hc]
    exact positive_polynomial_to_row (Detector836.region_JN_pos hn) (new_count_mul hn)
      (old_half_affine_binding δ p) (old_half_affine_pos hn)
  · by_cases ha : Detector836.InAcceptedRegion δ p
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=DetectorAffine.RNew δ p := by simp only [Detector836.count,hn,ha,hk,false_and,and_self,ite_false,ite_true]
      rw [hc]
      exact positive_polynomial_to_row (DetectorAffine.region_JN_pos (Detector836.accepted_region_subset ha)) (accepted_count_mul ha)
        (old_half_accepted_binding δ p) (old_half_accepted_pos ha)
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=Cycle63.Arithmetic.Bernstein.countingR0 kappaStar δ p := by simp only [Detector836.count,hn,ha,false_and,ite_false]
      rw [hc]
      exact positive_polynomial_to_row (oldJ_pos hδ hp) (old_count_mul hδ hp)
        (old_half_old_binding δ p) (old_half_old_pos hδ hp hn ha)
end
end Target836.EndpointCertificates
#print axioms Target836.EndpointCertificates.old_half_bound
