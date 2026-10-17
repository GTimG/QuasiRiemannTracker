import Candidate.Target836.Detector836.EndpointArithmetic
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Target836.EndpointCertificates
noncomputable section
open Target836.Arithmetic Target836.EndpointArithmetic
open Cycle63.Arithmetic.Bernstein (tensor basis2 basis3 tensor_pos normalize_mem)

def old_junction_old_power (δ p : ℝ) : ℝ := (794617/12000000)*δ^0*p^0 +
  (-422042543359/10120572000000)*δ^0*p^1 +
  (-4247621/15000000)*δ^1*p^0 +
  (188848965463/1204830000000)*δ^1*p^1 +
  (782513357268367/17782287779025000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-677842059539/843381000000)*δ^2*p^1 +
  (26546109871/52711312500)*δ^2*p^2 +
  (-32312955109/237097170387)*δ^2*p^3
def old_junction_old_minimum0 : ℝ := 6728358006622850669/56903320892880000000000
theorem old_junction_old_minimum0_pos : 0 < old_junction_old_minimum0 := by norm_num [old_junction_old_minimum0]
def old_junction_old_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(794617/12000000:ℝ), (3598946737103/60723432000000:ℝ), (198556512109/3795214500000:ℝ), (183657443359/4048228800000:ℝ)],
  ![(19270231/6000000000:ℝ), (125941933383479/60723432000000000:ℝ), (14956543329162670751/8535498133932000000000:ℝ), (12783077723243438257/5690332089288000000000:ℝ)],
  ![(39217827/1000000000:ℝ), (10545598544814323/607234320000000000:ℝ), (93171943367597741093/17070996267864000000000:ℝ), (6728358006622850669/56903320892880000000000:ℝ)]]
theorem old_junction_old_table0_lower (i : Fin 3) (j : Fin 4) : old_junction_old_minimum0 ≤ old_junction_old_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_old_minimum0,old_junction_old_table0]
theorem old_junction_old_identity0 (δ p : ℝ) :
    old_junction_old_power δ p = tensor old_junction_old_table0 ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_junction_old_power,tensor,basis2,basis3,old_junction_old_table0,Fin.sum_univ_succ]
  ring
theorem old_junction_old_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (89/200)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_junction_old_power δ p := by
  rw [old_junction_old_identity0]
  exact tensor_pos old_junction_old_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_old_table0_lower
def old_junction_old_minimum1 : ℝ := 217466575641122417/2032261460460000000000
theorem old_junction_old_minimum1_pos : 0 < old_junction_old_minimum1 := by norm_num [old_junction_old_minimum1]
def old_junction_old_table1 : Fin 3 → Fin 4 → ℝ := ![
  ![(2969529/62500000:ℝ), (3218452833498473/151808580000000000:ℝ), (4122850904487037313/609678438138000000000:ℝ), (217466575641122417/2032261460460000000000:ℝ)],
  ![(111599623/1500000000:ℝ), (1045003732591369/30361716000000000:ℝ), (51784616993664696391/4267749066966000000000:ℝ), (3657591787727062727/2845166044644000000000:ℝ)],
  ![(4052611/30000000:ℝ), (87904406397361/1214468640000000:ℝ), (683448321885654251/18967773630960000000:ℝ), (56757791339691151/3448686114720000000:ℝ)]]
theorem old_junction_old_table1_lower (i : Fin 3) (j : Fin 4) : old_junction_old_minimum1 ≤ old_junction_old_table1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_old_minimum1,old_junction_old_table1]
theorem old_junction_old_identity1 (δ p : ℝ) :
    old_junction_old_power δ p = tensor old_junction_old_table1 ((δ-(49/100))/((3/4)-(49/100))) ((p-(0))/((1/2)-(0))) := by
  norm_num [old_junction_old_power,tensor,basis2,basis3,old_junction_old_table1,Fin.sum_univ_succ]
  ring
theorem old_junction_old_leaf1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (49/100:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < old_junction_old_power δ p := by
  rw [old_junction_old_identity1]
  exact tensor_pos old_junction_old_minimum1_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_old_table1_lower
def old_junction_old_minimum2 : ℝ := 391339537759087698794789/2586514586040000000000000000
theorem old_junction_old_minimum2_pos : 0 < old_junction_old_minimum2 := by norm_num [old_junction_old_minimum2]
def old_junction_old_table2 : Fin 3 → Fin 4 → ℝ := ![
  ![(39217827/1000000000:ℝ), (2122388520928272917/121446864000000000000:ℝ), (4760455981833109906349821/853549813393200000000000000:ℝ), (32325967907203717672537/162580916836800000000000000:ℝ)],
  ![(99258257/2500000000:ℝ), (1533999638376299869/86747760000000000000:ℝ), (3431741797062532671120677/609678438138000000000000000:ℝ), (974871757663883812532981/5690332089288000000000000000:ℝ)],
  ![(201033893/5000000000:ℝ), (54360344570390555717/3036171600000000000000:ℝ), (11038342366881288695908391/1939885939530000000000000000:ℝ), (391339537759087698794789/2586514586040000000000000000:ℝ)]]
theorem old_junction_old_table2_lower (i : Fin 3) (j : Fin 4) : old_junction_old_minimum2 ≤ old_junction_old_table2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_old_minimum2,old_junction_old_table2]
theorem old_junction_old_identity2 (δ p : ℝ) :
    old_junction_old_power δ p = tensor old_junction_old_table2 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [old_junction_old_power,tensor,basis2,basis3,old_junction_old_table2,Fin.sum_univ_succ]
  ring
theorem old_junction_old_leaf2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (0:ℝ) (199/400)) :
    0 < old_junction_old_power δ p := by
  rw [old_junction_old_identity2]
  exact tensor_pos old_junction_old_minimum2_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_old_table2_lower
def old_junction_old_minimum3 : ℝ := 272650363964796450601/907259580562500000000000
theorem old_junction_old_minimum3_pos : 0 < old_junction_old_minimum3 := by norm_num [old_junction_old_minimum3]
def old_junction_old_table3 : Fin 3 → Fin 4 → ℝ := ![
  ![(201033893/5000000000:ℝ), (1977898703111086181/108434700000000000000:ℝ), (2726618103923158716563/449880783750000000000000:ℝ), (1340652069170858201111/3299125747500000000000000:ℝ)],
  ![(434793713/10000000000:ℝ), (26706512787723553/1355433750000000000:ℝ), (8834152041688237277063/1360889370843750000000000:ℝ), (272650363964796450601/907259580562500000000000:ℝ)],
  ![(2969529/62500000:ℝ), (23559569790509471/1084347000000000000:ℝ), (3998087118617528516873/544355748337500000000000:ℝ), (187149272931250495471/362903832225000000000000:ℝ)]]
theorem old_junction_old_table3_lower (i : Fin 3) (j : Fin 4) : old_junction_old_minimum3 ≤ old_junction_old_table3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_old_minimum3,old_junction_old_table3]
theorem old_junction_old_identity3 (δ p : ℝ) :
    old_junction_old_power δ p = tensor old_junction_old_table3 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(0))/((49/100)-(0))) := by
  norm_num [old_junction_old_power,tensor,basis2,basis3,old_junction_old_table3,Fin.sum_univ_succ]
  ring
theorem old_junction_old_leaf3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (0:ℝ) (49/100)) :
    0 < old_junction_old_power δ p := by
  rw [old_junction_old_identity3]
  exact tensor_pos old_junction_old_minimum3_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_old_table3_lower
theorem old_junction_old_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hn : ¬Detector836.InRegion δ p) (ha : ¬Detector836.InAcceptedRegion δ p) :
    0 < old_junction_old_power δ p := by
  rcases old_region_cover hδ hp hn ha with hb|hb|hb|hb
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_junction_old_leaf0_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_junction_old_leaf1_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_junction_old_leaf2_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact old_junction_old_leaf3_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_junction_old_binding (δ p : ℝ) :
    old_junction_old_power δ p = oldJ δ p*(theta-reserve-rowBase dMinus (oldCapacity dMinus) δ p)-3*dMinus*oldN δ p/4 := by
  norm_num [old_junction_old_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_junction_affine_power (δ p : ℝ) : ℝ := (794617/12000000)*δ^0*p^0 +
  (-31620194281/712548000000)*δ^0*p^1 +
  (-4247621/15000000)*δ^1*p^0 +
  (232223359876411679/1335443210640000000)*δ^1*p^1 +
  (5744894430010931/160253185276800000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-111633783640503269/133544321064000000)*δ^2*p^1 +
  (73109597980477837/133544321064000000)*δ^2*p^2 +
  (-64625910218/417326003325)*δ^2*p^3
def old_junction_affine_minimum0 : ℝ := 22318221657441271/1251978009975000000000
theorem old_junction_affine_minimum0_pos : 0 < old_junction_affine_minimum0 := by norm_num [old_junction_affine_minimum0]
def old_junction_affine_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(25425613003809442365043/52030254960000000000000000:ℝ), (411207519298479115239101/1092635354160000000000000000:ℝ), (2914352451623242354661/10926353541600000000000000:ℝ), (23278217965014057127/145684713888000000000000:ℝ)],
  ![(337682528035738317143/894270007125000000000000:ℝ), (4784559795403463382301/18779670149625000000000000:ℝ), (12662937163194938273/93898350748125000000000:ℝ), (22318221657441271/1251978009975000000000:ℝ)],
  ![(3298062262766452015223/5723328045600000000000000:ℝ), (7568931418166477258623/17169984136800000000000000:ℝ), (52976777606246522263/171699841368000000000000:ℝ), (410638322010984461/2289331218240000000000:ℝ)]]
theorem old_junction_affine_table0_lower (i : Fin 3) (j : Fin 4) : old_junction_affine_minimum0 ≤ old_junction_affine_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_affine_minimum0,old_junction_affine_table0]
theorem old_junction_affine_identity0 (δ p : ℝ) :
    old_junction_affine_power δ p = tensor old_junction_affine_table0 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [old_junction_affine_power,tensor,basis2,basis3,old_junction_affine_table0,Fin.sum_univ_succ]
  ring
theorem old_junction_affine_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < old_junction_affine_power δ p := by
  rw [old_junction_affine_identity0]
  exact tensor_pos old_junction_affine_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_affine_table0_lower
theorem old_junction_affine_pos {δ p : ℝ} (h : Detector836.InRegion δ p) :
    0 < old_junction_affine_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_junction_affine_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_junction_affine_binding (δ p : ℝ) :
    old_junction_affine_power δ p = Detector836.JN δ p*(theta-reserve-rowBase dMinus (oldCapacity dMinus) δ p)-3*dMinus*newN δ p/4 := by
  norm_num [old_junction_affine_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def old_junction_accepted_power (δ p : ℝ) : ℝ := (794617/12000000)*δ^0*p^0 +
  (-509349497/11587200000)*δ^0*p^1 +
  (-4247621/15000000)*δ^1*p^0 +
  (446572471800476669/2605979819520000000)*δ^1*p^1 +
  (19268821948424903/521195963904000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-5414432501867347991/6514949548800000000)*δ^2*p^1 +
  (3523182348046753591/6514949548800000000)*δ^2*p^2 +
  (-154682116106783/1017960867000000)*δ^2*p^3
def old_junction_accepted_minimum0 : ℝ := 363519209362966450919/2369072563200000000000000
theorem old_junction_accepted_minimum0_pos : 0 < old_junction_accepted_minimum0 := by norm_num [old_junction_accepted_minimum0]
def old_junction_accepted_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(3932255782623783334356433/13898559037440000000000000000:ℝ), (32086461273595746373259011/125087031336960000000000000000:ℝ), (28803111479617700791/125087031336960000000000:ℝ), (212834948752515937789/1042391927808000000000000:ℝ)],
  ![(17726741748739096824146447/69492795187200000000000000000:ℝ), (142782188493538951779193949/625435156684800000000000000000:ℝ), (90090995018984130571/446739397632000000000000:ℝ), (913133260967219673251/5211959639040000000000000:ℝ)],
  ![(7407611040797723666587043/31587634176000000000000000000:ℝ), (58938778835280147010809881/284288707584000000000000000000:ℝ), (256283799255188884681/1421443537920000000000000:ℝ), (363519209362966450919/2369072563200000000000000:ℝ)]]
theorem old_junction_accepted_table0_lower (i : Fin 3) (j : Fin 4) : old_junction_accepted_minimum0 ≤ old_junction_accepted_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [old_junction_accepted_minimum0,old_junction_accepted_table0]
theorem old_junction_accepted_identity0 (δ p : ℝ) :
    old_junction_accepted_power δ p = tensor old_junction_accepted_table0 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [old_junction_accepted_power,tensor,basis2,basis3,old_junction_accepted_table0,Fin.sum_univ_succ]
  ring
theorem old_junction_accepted_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (199/400:ℝ) (1/2)) :
    0 < old_junction_accepted_power δ p := by
  rw [old_junction_accepted_identity0]
  exact tensor_pos old_junction_accepted_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) old_junction_accepted_table0_lower
theorem old_junction_accepted_pos {δ p : ℝ} (h : Detector836.InAcceptedRegion δ p) :
    0 < old_junction_accepted_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact old_junction_accepted_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem old_junction_accepted_binding (δ p : ℝ) :
    old_junction_accepted_power δ p = DetectorAffine.JN δ p*(theta-reserve-rowBase dMinus (oldCapacity dMinus) δ p)-3*dMinus*acceptedN δ p/4 := by
  norm_num [old_junction_accepted_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring
theorem old_junction_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent dMinus δ p ≤ theta-reserve := by
  have hk : Detector836.kStar ≤ kappaStar := by rw [kappaStar_eq_detector]
  by_cases hn : Detector836.InRegion δ p
  · unfold oldExponent rowAt
    have hc : Detector836.count kappaStar δ p=Detector836.RNew δ p := by simp only [Detector836.count,hn,hk,and_self,ite_true]
    rw [hc]
    exact positive_polynomial_to_row (Detector836.region_JN_pos hn) (new_count_mul hn)
      (old_junction_affine_binding δ p) (old_junction_affine_pos hn)
  · by_cases ha : Detector836.InAcceptedRegion δ p
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=DetectorAffine.RNew δ p := by simp only [Detector836.count,hn,ha,hk,false_and,and_self,ite_false,ite_true]
      rw [hc]
      exact positive_polynomial_to_row (DetectorAffine.region_JN_pos (Detector836.accepted_region_subset ha)) (accepted_count_mul ha)
        (old_junction_accepted_binding δ p) (old_junction_accepted_pos ha)
    · unfold oldExponent rowAt
      have hc : Detector836.count kappaStar δ p=Cycle63.Arithmetic.Bernstein.countingR0 kappaStar δ p := by simp only [Detector836.count,hn,ha,false_and,ite_false]
      rw [hc]
      exact positive_polynomial_to_row (oldJ_pos hδ hp) (old_count_mul hδ hp)
        (old_junction_old_binding δ p) (old_junction_old_pos hδ hp hn ha)
end
end Target836.EndpointCertificates
#print axioms Target836.EndpointCertificates.old_junction_bound
