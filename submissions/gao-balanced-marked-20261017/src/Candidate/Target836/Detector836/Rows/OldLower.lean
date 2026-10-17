import Candidate.Target836.Detector836.EndpointArithmetic
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Target836.EndpointCertificates
noncomputable section
open Target836.Arithmetic Target836.EndpointArithmetic
open Cycle63.Arithmetic.Bernstein (tensor basis2 basis3 tensor_pos normalize_mem)

def old_lower_old_power (δ p : ℝ) : ℝ := (16429687/12000000)*δ^0*p^0 +
  (-8726250367249/10120572000000)*δ^0*p^1 +
  (-53742187/30000000)*δ^1*p^0 +
  (-1507660065649/8433810000000)*δ^1*p^1 +
  (1108705615545541/1481857314918750)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (46217241703/70281750000)*δ^2*p^1 +
  (-435858413/1597312500)*δ^2*p^2 +
  (-11720667328/79032390129)*δ^2*p^3
def old_lower_old_minimum0 : ℝ := 196348753961014126589/592742925967500000000
theorem old_lower_old_minimum0_pos : 0 < old_lower_old_minimum0 := by norm_num [old_lower_old_minimum0]
def old_lower_old_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(16429687/12000000:ℝ), (74412664743233/60723432000000:ℝ), (4105400898499/3795214500000:ℝ), (3797344267249/4048228800000:ℝ)],
  ![(11646632357/12000000000:ℝ), (49806495058496819/60723432000000000:ℝ), (243175398620965407389/355645755580500000000:ℝ), (118267990750409523851/210753040344000000000:ℝ)],
  ![(1341954619/2000000000:ℝ), (5809038671815483/10843470000000000:ℝ), (25114541080536957031/59274292596750000000:ℝ), (196348753961014126589/592742925967500000000:ℝ)]]
theorem old_lower_old_table0_lower (i : Fin 3) (j : Fin 4) : old_lower_old_minimum0 ≤ old_lower_old_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_old_minimum0,old_lower_old_table0]
theorem old_lower_old_identity0 (δ p : ℝ) :
    old_lower_old_power δ p = tensor old_lower_old_table0 ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_lower_old_power,tensor,basis2,basis3,old_lower_old_table0,Fin.sum_univ_succ]
  ring
theorem old_lower_old_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (89/200)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_lower_old_power δ p := by
  rw [old_lower_old_identity0]
  exact tensor_pos old_lower_old_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_old_table0_lower
def old_lower_old_minimum1 : ℝ := 146776078152150943/1724343057360000000
theorem old_lower_old_minimum1_pos : 0 < old_lower_old_minimum1 := by norm_num [old_lower_old_minimum1]
def old_lower_old_table1 : Fin 3 → Fin 4 → ℝ := ![
  ![(611401529/1000000000:ℝ), (36389472608266399/75904290000000000:ℝ), (1577182814360367407/4233878042625000000:ℝ), (96958395513398068157/338710243410000000000:ℝ)],
  ![(331664039/750000000:ℝ), (2431363158364171/7590429000000000:ℝ), (5083959145268283653/22227859723781250000:ℝ), (12693211621109486927/79032390129000000000:ℝ)],
  ![(36820309/120000000:ℝ), (122925815664473/607234320000000:ℝ), (469474020613693813/3556457555805000000:ℝ), (146776078152150943/1724343057360000000:ℝ)]]
theorem old_lower_old_table1_lower (i : Fin 3) (j : Fin 4) : old_lower_old_minimum1 ≤ old_lower_old_table1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_old_minimum1,old_lower_old_table1]
theorem old_lower_old_identity1 (δ p : ℝ) :
    old_lower_old_power δ p = tensor old_lower_old_table1 ((δ-(49/100))/((3/4)-(49/100))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_lower_old_power,tensor,basis2,basis3,old_lower_old_table1,Fin.sum_univ_succ]
  ring
theorem old_lower_old_leaf1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (49/100:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_lower_old_power δ p := by
  rw [old_lower_old_identity1]
  exact tensor_pos old_lower_old_minimum1_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_old_table1_lower
def old_lower_old_minimum2 : ℝ := 23455176734845723974660949/71847627390000000000000000
theorem old_lower_old_minimum2_pos : 0 < old_lower_old_minimum2 := by norm_num [old_lower_old_minimum2]
def old_lower_old_table2 : Fin 3 → Fin 4 → ℝ := ![
  ![(1341954619/2000000000:ℝ), (581637209008762541/1084347000000000000:ℝ), (120868670309129053886870357/284516604464400000000000000:ℝ), (166917734726612001252313/501792953200000000000000:ℝ)],
  ![(1667345227/2500000000:ℝ), (80846722002843721927/151808580000000000000:ℝ), (85621506055514072151704809/203226146046000000000000000:ℝ), (52088128342117095037333121/158064780258000000000000000:ℝ)],
  ![(6629168721/10000000000:ℝ), (200668908198689741599/379521450000000000000:ℝ), (24561708948386849491786277/58784422410000000000000000:ℝ), (23455176734845723974660949/71847627390000000000000000:ℝ)]]
theorem old_lower_old_table2_lower (i : Fin 3) (j : Fin 4) : old_lower_old_minimum2 ≤ old_lower_old_table2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_old_minimum2,old_lower_old_table2]
theorem old_lower_old_identity2 (δ p : ℝ) :
    old_lower_old_power δ p = tensor old_lower_old_table2 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [old_lower_old_power,tensor,basis2,basis3,old_lower_old_table2,Fin.sum_univ_succ]
  ring
theorem old_lower_old_leaf2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (0:ℝ) (199/400)) :
    0 < old_lower_old_power δ p := by
  rw [old_lower_old_identity2]
  exact tensor_pos old_lower_old_minimum2_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_old_table2_lower
def old_lower_old_minimum3 : ℝ := 5876176825849539296797/20161324012500000000000
theorem old_lower_old_minimum3_pos : 0 < old_lower_old_minimum3 := by norm_num [old_lower_old_minimum3]
def old_lower_old_table3 : Fin 3 → Fin 4 → ℝ := ![
  ![(6629168721/10000000000:ℝ), (7194163590188398957/13554337500000000000:ℝ), (347378387051756195956303/824781436875000000000000:ℝ), (30297232930335808048451/91642381875000000000000:ℝ)],
  ![(12735579011/20000000000:ℝ), (498746972328438409/985770000000000000:ℝ), (723016166210196102524209/1814519161125000000000000:ℝ), (41729661277232848118677/134408826750000000000000:ℝ)],
  ![(611401529/1000000000:ℝ), (261356022395530423/542173500000000000:ℝ), (4273202607456326459401/11340744757031250000000:ℝ), (5876176825849539296797/20161324012500000000000:ℝ)]]
theorem old_lower_old_table3_lower (i : Fin 3) (j : Fin 4) : old_lower_old_minimum3 ≤ old_lower_old_table3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_old_minimum3,old_lower_old_table3]
theorem old_lower_old_identity3 (δ p : ℝ) :
    old_lower_old_power δ p = tensor old_lower_old_table3 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(0))/((49/100)-(0))) := by
  norm_num [old_lower_old_power,tensor,basis2,basis3,old_lower_old_table3,Fin.sum_univ_succ]
  ring
theorem old_lower_old_leaf3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (0:ℝ) (49/100)) :
    0 < old_lower_old_power δ p := by
  rw [old_lower_old_identity3]
  exact tensor_pos old_lower_old_minimum3_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_old_table3_lower
theorem old_lower_old_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hn : ¬Detector836.InRegion δ p) (ha : ¬Detector836.InAcceptedRegion δ p) :
    0 < old_lower_old_power δ p := by
  rcases old_region_cover hδ hp hn ha with hb|hb|hb|hb
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_lower_old_leaf0_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_lower_old_leaf1_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_lower_old_leaf2_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_lower_old_leaf3_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_lower_old_binding (δ p : ℝ) :
    old_lower_old_power δ p = oldJ δ p*(theta-reserve-rowBase d0 (oldCapacity d0) δ p)-3*d0*oldN δ p/4 := by
  norm_num [old_lower_old_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_lower_affine_power (δ p : ℝ) : ℝ := (16429687/12000000)*δ^0*p^0 +
  (-653786534791/712548000000)*δ^0*p^1 +
  (-53742187/30000000)*δ^1*p^0 +
  (-14298341247529813/111286934220000000)*δ^1*p^1 +
  (11100518490315557/13354432106400000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (7315967440572157/11128693422000000)*δ^2*p^1 +
  (-3703662185467493/11128693422000000)*δ^2*p^2 +
  (-23441334656/139108667775)*δ^2*p^3
def old_lower_affine_minimum0 : ℝ := 52820265159309746179/190777601520000000000
theorem old_lower_affine_minimum0_pos : 0 < old_lower_affine_minimum0 := by norm_num [old_lower_affine_minimum0]
def old_lower_affine_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(462746252334131969135191/1445284860000000000000000:ℝ), (28981407517370074612306411/91052946180000000000000000:ℝ), (32011756183456190104867/101169940200000000000000:ℝ), (3818737322587336774433/12140392824000000000000:ℝ)],
  ![(19913363463174587970001/66242222750000000000000:ℝ), (467592777841363692674861/1564972512468750000000000:ℝ), (49572912338611398790177/166930401330000000000000:ℝ), (985414356348742432873/3338608026600000000000:ℝ)],
  ![(44856739229526424577851/158981334600000000000000:ℝ), (401178339378653651981753/1430832011400000000000000:ℝ), (1328862679617518108383/4769440038000000000000:ℝ), (52820265159309746179/190777601520000000000:ℝ)]]
theorem old_lower_affine_table0_lower (i : Fin 3) (j : Fin 4) : old_lower_affine_minimum0 ≤ old_lower_affine_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_affine_minimum0,old_lower_affine_table0]
theorem old_lower_affine_identity0 (δ p : ℝ) :
    old_lower_affine_power δ p = tensor old_lower_affine_table0 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [old_lower_affine_power,tensor,basis2,basis3,old_lower_affine_table0,Fin.sum_univ_succ]
  ring
theorem old_lower_affine_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < old_lower_affine_power δ p := by
  rw [old_lower_affine_identity0]
  exact tensor_pos old_lower_affine_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_affine_table0_lower
theorem old_lower_affine_pos {δ p : ℝ} (h : Detector836.InRegion δ p) :
    0 < old_lower_affine_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_lower_affine_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_lower_affine_binding (δ p : ℝ) :
    old_lower_affine_power δ p = Detector836.JN δ p*(theta-reserve-rowBase d0 (oldCapacity d0) δ p)-3*d0*newN δ p/4 := by
  norm_num [old_lower_affine_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_lower_accepted_power (δ p : ℝ) : ℝ := (16429687/12000000)*δ^0*p^0 +
  (-10531429367/11587200000)*δ^0*p^1 +
  (-53742187/30000000)*δ^1*p^0 +
  (-29609136667801909/217164984960000000)*δ^1*p^1 +
  (177692453418313061/217164984960000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (14277019653439447/21716498496000000)*δ^2*p^1 +
  (-1404750712238539/4343299699200000)*δ^2*p^2 +
  (-876669289049/5301879515625)*δ^2*p^3
def old_lower_accepted_minimum0 : ℝ := 832321868318921287859/2632302848000000000000
theorem old_lower_accepted_minimum0_pos : 0 < old_lower_accepted_minimum0 := by norm_num [old_lower_accepted_minimum0]
def old_lower_accepted_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(374829431354105984487252583/1158213253120000000000000000:ℝ), (134742238042618387902259709/416956771123200000000000000:ℝ), (84091311877476099122809/260597981952000000000000:ℝ), (373194938772737758849/1158213253120000000000:ℝ)],
  ![(1856600363505235520054666297/5791066265600000000000000000:ℝ), (667398864599087134951046371/2084783855616000000000000000:ℝ), (59502026197882902874673/186141415680000000000000:ℝ), (1848465600645817357151/5791066265600000000000:ℝ)],
  ![(836002301330112366005954693/2632302848000000000000000000:ℝ), (300518677119936500221837159/947629025280000000000000000:ℝ), (187548140827868129449979/592268140800000000000000:ℝ), (832321868318921287859/2632302848000000000000:ℝ)]]
theorem old_lower_accepted_table0_lower (i : Fin 3) (j : Fin 4) : old_lower_accepted_minimum0 ≤ old_lower_accepted_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_lower_accepted_minimum0,old_lower_accepted_table0]
theorem old_lower_accepted_identity0 (δ p : ℝ) :
    old_lower_accepted_power δ p = tensor old_lower_accepted_table0 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [old_lower_accepted_power,tensor,basis2,basis3,old_lower_accepted_table0,Fin.sum_univ_succ]
  ring
theorem old_lower_accepted_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (199/400:ℝ) (1/2)) :
    0 < old_lower_accepted_power δ p := by
  rw [old_lower_accepted_identity0]
  exact tensor_pos old_lower_accepted_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_lower_accepted_table0_lower
theorem old_lower_accepted_pos {δ p : ℝ} (h : Detector836.InAcceptedRegion δ p) :
    0 < old_lower_accepted_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_lower_accepted_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_lower_accepted_binding (δ p : ℝ) :
    old_lower_accepted_power δ p = DetectorAffine.JN δ p*(theta-reserve-rowBase d0 (oldCapacity d0) δ p)-3*d0*acceptedN δ p/4 := by
  norm_num [old_lower_accepted_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring
theorem old_lower_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent d0 δ p ≤ theta-reserve := by
  have hk : Detector836.kStar ≤ kappaStar := by rw [kappaStar_eq_detector]
  by_cases hn : Detector836.InRegion δ p
  · unfold oldExponent rowAt
    have hc : Detector836.count kappaStar δ p=Detector836.RNew δ p := by simp only [Detector836.count,hn,hk,and_self,ite_true]
    rw [hc]
    exact positive_polynomial_to_row (Detector836.region_JN_pos hn) (new_count_mul hn)
      (old_lower_affine_binding δ p) (old_lower_affine_pos hn)
  · by_cases ha : Detector836.InAcceptedRegion δ p
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=DetectorAffine.RNew δ p := by simp only [Detector836.count,hn,ha,hk,false_and,and_self,ite_false,ite_true]
      rw [hc]
      exact positive_polynomial_to_row (DetectorAffine.region_JN_pos (Detector836.accepted_region_subset ha)) (accepted_count_mul ha)
        (old_lower_accepted_binding δ p) (old_lower_accepted_pos ha)
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=Cycle63.Arithmetic.Bernstein.countingR0 kappaStar δ p := by simp only [Detector836.count,hn,ha,false_and,ite_false]
      rw [hc]
      exact positive_polynomial_to_row (oldJ_pos hδ hp) (old_count_mul hδ hp)
        (old_lower_old_binding δ p) (old_lower_old_pos hδ hp hn ha)
end
end Target836.EndpointCertificates
#print axioms Target836.EndpointCertificates.old_lower_bound
