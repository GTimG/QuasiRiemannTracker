import Candidate.Target836.Detector836.EndpointArithmetic
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Target836.EndpointCertificates
noncomputable section
open Target836.Arithmetic Target836.EndpointArithmetic
open Cycle63.Arithmetic.Bernstein (tensor basis2 basis3 tensor_pos normalize_mem)

def top_old_power (δ p : ℝ) : ℝ := (39136849901/600000000000)*δ^0*p^0 +
  (-20786637677368427/506028600000000000)*δ^0*p^1 +
  (-846086199427/3000000000000)*δ^1*p^0 +
  (21143140065490933019759/133544321064000000000000)*δ^1*p^1 +
  (1138754368934355088031/26708864212800000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-5975070823797128529523/7419128948000000000000)*δ^2*p^1 +
  (11210449319452672438031/22257386844000000000000)*δ^2*p^2 +
  (-575746931691093/4239502256000000)*δ^2*p^3
def top_old_minimum0 : ℝ := 49753258348188521268377/32050637055360000000000000000
theorem top_old_minimum0_pos : 0 < top_old_minimum0 := by norm_num [top_old_minimum0]
def top_old_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(39136849901/600000000000:ℝ), (177257015960763259/3036171600000000000:ℝ), (9779398642712177/189760725000000000:ℝ), (9045582707068427/202411440000000000:ℝ)],
  ![(2972028052997/1200000000000000:ℝ), (1443724495839503759072501/961519111660800000000000000:ℝ), (361766491948232139095099/274719746188800000000000000:ℝ), (1232506326041202157235923/641012741107200000000000000:ℝ)],
  ![(7747559383999/200000000000000:ℝ), (819864036347568140374154659/48075955583040000000000000000:ℝ), (101189673391292771653155899/19230382233216000000000000000:ℝ), (49753258348188521268377/32050637055360000000000000000:ℝ)]]
theorem top_old_table0_lower (i : Fin 3) (j : Fin 4) : top_old_minimum0 ≤ top_old_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_old_minimum0,top_old_table0]
theorem top_old_identity0 (δ p : ℝ) :
    top_old_power δ p = tensor top_old_table0 ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [top_old_power,tensor,basis2,basis3,top_old_table0,Fin.sum_univ_succ]
  ring
theorem top_old_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0:ℝ) (89/200)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < top_old_power δ p := by
  rw [top_old_identity0]
  exact tensor_pos top_old_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_old_table0_lower
def top_old_minimum1 : ℝ := 245808166202293134893987/8012659263840000000000000000
theorem top_old_minimum1_pos : 0 < top_old_minimum1 := by norm_num [top_old_minimum1]
def top_old_table1 : Fin 3 → Fin 4 → ℝ := ![
  ![(4708400392859/100000000000000:ℝ), (251672299663074677383419529/12018988895760000000000000000:ℝ), (31796156056680441148934489/4807595558304000000000000000:ℝ), (245808166202293134893987/8012659263840000000000000000:ℝ)],
  ![(11118040293013/150000000000000:ℝ), (2356111438307056962143647/68679936547200000000000000:ℝ), (11652573008805779058834853/961519111660800000000000000:ℝ), (423534026992144313262107/320506370553600000000000000:ℝ)],
  ![(1619478399739/12000000000000:ℝ), (278448491438444182222721/3846076446643200000000000:ℝ), (1388972675945651274602617/38460764466432000000000000:ℝ), (8489868687122176066751/512810192885760000000000:ℝ)]]
theorem top_old_table1_lower (i : Fin 3) (j : Fin 4) : top_old_minimum1 ≤ top_old_table1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_old_minimum1,top_old_table1]
theorem top_old_identity1 (δ p : ℝ) :
    top_old_power δ p = tensor top_old_table1 ((δ-(49/100))/((3/4)-(49/100))) ((p-(0))/((1/2)-(0))) := by
  norm_num [top_old_power,tensor,basis2,basis3,top_old_table1,Fin.sum_univ_succ]
  ring
theorem top_old_leaf1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (49/100:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < top_old_power δ p := by
  rw [top_old_identity1]
  exact tensor_pos top_old_minimum1_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_old_table1_lower
def top_old_minimum2 : ℝ := 312394726852463754941693398951/8012659263840000000000000000000000
theorem top_old_minimum2_pos : 0 < top_old_minimum2 := by norm_num [top_old_minimum2]
def top_old_table2 : Fin 3 → Fin 4 → ℝ := ![
  ![(7747559383999/200000000000000:ℝ), (165015299837276563270915661941/9615191116608000000000000000000:ℝ), (20692397765983810497593878659659/3846076446643200000000000000000000:ℝ), (25944617769205175607244254721/320506370553600000000000000000000:ℝ)],
  ![(4903338840071/125000000000000:ℝ), (835224668076031174130905206419/48075955583040000000000000000000:ℝ), (14930722216754666630202729833083/2747197461888000000000000000000000:ℝ), (2816315632382032267319814577/50079120399000000000000000000000:ℝ)],
  ![(39733624521141/1000000000000000:ℝ), (604290753547366546936993134403/34339968273600000000000000000000:ℝ), (528790586805910381963692044813579/96151911166080000000000000000000000:ℝ), (312394726852463754941693398951/8012659263840000000000000000000000:ℝ)]]
theorem top_old_table2_lower (i : Fin 3) (j : Fin 4) : top_old_minimum2 ≤ top_old_table2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_old_minimum2,top_old_table2]
theorem top_old_identity2 (δ p : ℝ) :
    top_old_power δ p = tensor top_old_table2 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [top_old_power,tensor,basis2,basis3,top_old_table2,Fin.sum_univ_succ]
  ring
theorem top_old_leaf2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (0:ℝ) (199/400)) :
    0 < top_old_power δ p := by
  rw [top_old_identity2]
  exact tensor_pos top_old_minimum2_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_old_table2_lower
def top_old_minimum3 : ℝ := 2901438419693983662420440789/14308320114000000000000000000000
theorem top_old_minimum3_pos : 0 < top_old_minimum3 := by norm_num [top_old_minimum3]
def top_old_table3 : Fin 3 → Fin 4 → ℝ := ![
  ![(39733624521141/1000000000000000:ℝ), (153937615466880896981240184853/8584992068400000000000000000000:ℝ), (5036446579504212994704684464597/858499206840000000000000000000000:ℝ), (83126730392993842516190381797/286166402280000000000000000000000:ℝ)],
  ![(86057128449731/2000000000000000:ℝ), (8334532560079257492269960561/429249603420000000000000000000:ℝ), (271208564226204643053764823139/42924960342000000000000000000000:ℝ), (2901438419693983662420440789/14308320114000000000000000000000:ℝ)],
  ![(4708400392859/100000000000000:ℝ), (1842549257696614659683047903/85849920684000000000000000000:ℝ), (61738918347883231373156617847/8584992068400000000000000000000:ℝ), (1244780262437773414345730047/2861664022800000000000000000000:ℝ)]]
theorem top_old_table3_lower (i : Fin 3) (j : Fin 4) : top_old_minimum3 ≤ top_old_table3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_old_minimum3,top_old_table3]
theorem top_old_identity3 (δ p : ℝ) :
    top_old_power δ p = tensor top_old_table3 ((δ-(451/1000))/((49/100)-(451/1000))) ((p-(0))/((49/100)-(0))) := by
  norm_num [top_old_power,tensor,basis2,basis3,top_old_table3,Fin.sum_univ_succ]
  ring
theorem top_old_leaf3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (49/100)) (hp : p ∈ Set.Icc (0:ℝ) (49/100)) :
    0 < top_old_power δ p := by
  rw [top_old_identity3]
  exact tensor_pos top_old_minimum3_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_old_table3_lower
theorem top_old_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hn : ¬Detector836.InRegion δ p) (ha : ¬Detector836.InAcceptedRegion δ p) :
    0 < top_old_power δ p := by
  rcases old_region_cover hδ hp hn ha with hb|hb|hb|hb
  · obtain ⟨hδb,hpb⟩ := hb
    exact top_old_leaf0_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact top_old_leaf1_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact top_old_leaf2_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  · obtain ⟨hδb,hpb⟩ := hb
    exact top_old_leaf3_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem top_old_binding (δ p : ℝ) :
    top_old_power δ p = oldJ δ p*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*dPlus*oldN δ p/4 := by
  norm_num [top_old_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def top_affine_power (δ p : ℝ) : ℝ := (39136849901/600000000000)*δ^0*p^0 +
  (-1557372668110493/35627400000000000)*δ^0*p^1 +
  (-846086199427/3000000000000)*δ^1*p^0 +
  (13890485798860587/79172000000000000)*δ^1*p^1 +
  (16151597890689031729/470115418800000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-16578521937955997/19793000000000000)*δ^2*p^1 +
  (21677079688487047/39586000000000000)*δ^2*p^2 +
  (-12090685565512953/78352569800000000)*δ^2*p^3
def top_affine_minimum0 : ℝ := 4036456366476427094209867/451310802048000000000000000000
theorem top_affine_minimum0_pos : 0 < top_affine_minimum0 := by norm_num [top_affine_minimum0]
def top_affine_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(26550787486556808652020793139/70517312820000000000000000000000:ℝ), (56224118681939725521479804339/211551938460000000000000000000000:ℝ), (83413029020730058601743891/528879846150000000000000000000:ℝ), (1475866832451146704440283/28206925128000000000000000000:ℝ)],
  ![(99611293342992346997073435527/282069251280000000000000000000000:ℝ), (202885007614181100288853132127/846207753840000000000000000000000:ℝ), (546289953903912726931441901/4231038769200000000000000000000:ℝ), (2390092714282904890944019/112827700512000000000000000000:ℝ)],
  ![(393840291640330071466103038811/1128277005120000000000000000000000:ℝ), (788339787506428617391945737611/3384831015360000000000000000000000:ℝ), (505784497269776857833790517/4231038769200000000000000000000:ℝ), (4036456366476427094209867/451310802048000000000000000000:ℝ)]]
theorem top_affine_table0_lower (i : Fin 3) (j : Fin 4) : top_affine_minimum0 ≤ top_affine_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_affine_minimum0,top_affine_table0]
theorem top_affine_identity0 (δ p : ℝ) :
    top_affine_power δ p = tensor top_affine_table0 ((δ-(451/1000))/((1843/4000)-(451/1000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [top_affine_power,tensor,basis2,basis3,top_affine_table0,Fin.sum_univ_succ]
  ring
theorem top_affine_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000:ℝ) (1843/4000)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < top_affine_power δ p := by
  rw [top_affine_identity0]
  exact tensor_pos top_affine_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_affine_table0_lower
def top_affine_minimum1 : ℝ := 4127602359546357978043/2888389133107200000000000000
theorem top_affine_minimum1_pos : 0 < top_affine_minimum1 := by norm_num [top_affine_minimum1]
def top_affine_table1 : Fin 3 → Fin 4 → ℝ := ![
  ![(393840291640330071466103038811/1128277005120000000000000000000000:ℝ), (788339787506428617391945737611/3384831015360000000000000000000000:ℝ), (505784497269776857833790517/4231038769200000000000000000000:ℝ), (4036456366476427094209867/451310802048000000000000000000:ℝ)],
  ![(31323028061960833056400614973/90262160409600000000000000000000:ℝ), (62139173282502458040816987373/270786481228800000000000000000000:ℝ), (19421270758108356931398593/169241550768000000000000000000:ℝ), (101959929691906468754141/36104864163840000000000000000:ℝ)],
  ![(2525926694905701205915996139/7220972832768000000000000000000:ℝ), (5000646085965674812701941339/21662918498304000000000000000000:ℝ), (3106599974672569324367063/27078648122880000000000000000:ℝ), (4127602359546357978043/2888389133107200000000000000:ℝ)]]
theorem top_affine_table1_lower (i : Fin 3) (j : Fin 4) : top_affine_minimum1 ≤ top_affine_table1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_affine_minimum1,top_affine_table1]
theorem top_affine_identity1 (δ p : ℝ) :
    top_affine_power δ p = tensor top_affine_table1 ((δ-(1843/4000))/((149/320)-(1843/4000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [top_affine_power,tensor,basis2,basis3,top_affine_table1,Fin.sum_univ_succ]
  ring
theorem top_affine_leaf1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1843/4000:ℝ) (149/320)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < top_affine_power δ p := by
  rw [top_affine_identity1]
  exact tensor_pos top_affine_minimum1_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_affine_table1_lower
def top_affine_minimum2 : ℝ := 615064648376240348467/18052432081920000000000000000
theorem top_affine_minimum2_pos : 0 < top_affine_minimum2 := by norm_num [top_affine_minimum2]
def top_affine_table2 : Fin 3 → Fin 4 → ℝ := ![
  ![(2525926694905701205915996139/7220972832768000000000000000000:ℝ), (5000646085965674812701941339/21662918498304000000000000000000:ℝ), (3106599974672569324367063/27078648122880000000000000000:ℝ), (4127602359546357978043/2888389133107200000000000000:ℝ)],
  ![(15912569655340848545749644251/45131080204800000000000000000000:ℝ), (31438489433319706138365773051/135393240614400000000000000000000:ℝ), (38822457850597519246379389/338483101536000000000000000000:ℝ), (615064648376240348467/18052432081920000000000000000:ℝ)],
  ![(101598268214587918085892469259/282069251280000000000000000000000:ℝ), (201696231777463118322452426459/846207753840000000000000000000000:ℝ), (63160300703662124052918199/528879846150000000000000000000:ℝ), (379552839149394348194923/112827700512000000000000000000:ℝ)]]
theorem top_affine_table2_lower (i : Fin 3) (j : Fin 4) : top_affine_minimum2 ≤ top_affine_table2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_affine_minimum2,top_affine_table2]
theorem top_affine_identity2 (δ p : ℝ) :
    top_affine_power δ p = tensor top_affine_table2 ((δ-(149/320))/((941/2000)-(149/320))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [top_affine_power,tensor,basis2,basis3,top_affine_table2,Fin.sum_univ_succ]
  ring
theorem top_affine_leaf2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (149/320:ℝ) (941/2000)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < top_affine_power δ p := by
  rw [top_affine_identity2]
  exact tensor_pos top_affine_minimum2_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_affine_table2_lower
def top_affine_minimum3 : ℝ := 379552839149394348194923/112827700512000000000000000000
theorem top_affine_minimum3_pos : 0 < top_affine_minimum3 := by norm_num [top_affine_minimum3]
def top_affine_table3 : Fin 3 → Fin 4 → ℝ := ![
  ![(101598268214587918085892469259/282069251280000000000000000000000:ℝ), (201696231777463118322452426459/846207753840000000000000000000000:ℝ), (63160300703662124052918199/528879846150000000000000000000:ℝ), (379552839149394348194923/112827700512000000000000000000:ℝ)],
  ![(5508854984470918839286062001/14103462564000000000000000000000:ℝ), (11125946152716146907655890301/42310387692000000000000000000000:ℝ), (58528913561660899979775851/423103876920000000000000000000:ℝ), (94119378976878286613147/5641385025600000000000000000:ℝ)],
  ![(351296189613872673518495639/705173128200000000000000000000:ℝ), (770468099587995453521451839/2115519384600000000000000000000:ℝ), (2468327880287721245779007/10577596923000000000000000000:ℝ), (29787015728393180885083/282069251280000000000000000:ℝ)]]
theorem top_affine_table3_lower (i : Fin 3) (j : Fin 4) : top_affine_minimum3 ≤ top_affine_table3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_affine_minimum3,top_affine_table3]
theorem top_affine_identity3 (δ p : ℝ) :
    top_affine_power δ p = tensor top_affine_table3 ((δ-(941/2000))/((49/100)-(941/2000))) ((p-(49/100))/((1/2)-(49/100))) := by
  norm_num [top_affine_power,tensor,basis2,basis3,top_affine_table3,Fin.sum_univ_succ]
  ring
theorem top_affine_leaf3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (941/2000:ℝ) (49/100)) (hp : p ∈ Set.Icc (49/100:ℝ) (1/2)) :
    0 < top_affine_power δ p := by
  rw [top_affine_identity3]
  exact tensor_pos top_affine_minimum3_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_affine_table3_lower
theorem top_affine_pos {δ p : ℝ} (h : Detector836.InRegion δ p) :
    0 < top_affine_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  by_cases split0 : δ ≤ (1843/4000:ℝ)
  ·
    exact top_affine_leaf0_pos
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
  ·
    by_cases split1 : δ ≤ (149/320:ℝ)
    ·
      exact top_affine_leaf1_pos
        (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
        (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    ·
      by_cases split2 : δ ≤ (941/2000:ℝ)
      ·
        exact top_affine_leaf2_pos
          (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
          (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
      ·
        exact top_affine_leaf3_pos
          (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
          (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem top_affine_binding (δ p : ℝ) :
    top_affine_power δ p = Detector836.JN δ p*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*dPlus*newN δ p/4 := by
  norm_num [top_affine_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring

def top_accepted_power (δ p : ℝ) : ℝ := (39136849901/600000000000)*δ^0*p^0 +
  (-25086720786541/579360000000000)*δ^0*p^1 +
  (-846086199427/3000000000000)*δ^1*p^0 +
  (5287885526881146463317/30579393280000000000000)*δ^1*p^1 +
  (3256456599341926982329/91738179840000000000000)*δ^1*p^2 +
  (1/2)*δ^2*p^0 +
  (-63661644379490288294111/76448483200000000000000)*δ^2*p^1 +
  (41351825911276576107711/76448483200000000000000)*δ^2*p^2 +
  (-57878111802110506011/382242416000000000000)*δ^2*p^3
def top_accepted_minimum0 : ℝ := 41661454487559461737575467/917381798400000000000000000000
theorem top_accepted_minimum0_pos : 0 < top_accepted_minimum0 := by norm_num [top_accepted_minimum0]
def top_accepted_table0 : Fin 3 → Fin 4 → ℝ := ![
  ![(164695075535550460251651779193/978540584960000000000000000000000:ℝ), (626559885105971812851633919093/4403432632320000000000000000000000:ℝ), (569676602027663333712473/4892702924800000000000000000:ℝ), (3329774558586637527277307/36695271936000000000000000000:ℝ)],
  ![(700600409217443449404929585787/4892702924800000000000000000000000:ℝ), (2571387992325554014350768995387/22017163161600000000000000000000000:ℝ), (6645675513192813931196881/73390543872000000000000000000:ℝ), (11830294767604022543632213/183476359680000000000000000000:ℝ)],
  ![(3065598043280010024142425672033/24463514624000000000000000000000000:ℝ), (10844907548139450806579795812933/110085815808000000000000000000000000:ℝ), (26376621071401807438292419/366952719360000000000000000000:ℝ), (41661454487559461737575467/917381798400000000000000000000:ℝ)]]
theorem top_accepted_table0_lower (i : Fin 3) (j : Fin 4) : top_accepted_minimum0 ≤ top_accepted_table0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [top_accepted_minimum0,top_accepted_table0]
theorem top_accepted_identity0 (δ p : ℝ) :
    top_accepted_power δ p = tensor top_accepted_table0 ((δ-(89/200))/((451/1000)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [top_accepted_power,tensor,basis2,basis3,top_accepted_table0,Fin.sum_univ_succ]
  ring
theorem top_accepted_leaf0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200:ℝ) (451/1000)) (hp : p ∈ Set.Icc (199/400:ℝ) (1/2)) :
    0 < top_accepted_power δ p := by
  rw [top_accepted_identity0]
  exact tensor_pos top_accepted_minimum0_pos (normalize_mem (by norm_num) hδ)
    (normalize_mem (by norm_num) hp) top_accepted_table0_lower
theorem top_accepted_pos {δ p : ℝ} (h : Detector836.InAcceptedRegion δ p) :
    0 < top_accepted_power δ p := by
  have hδb := And.intro h.1 h.2.1
  have hpb := And.intro h.2.2.1 h.2.2.2
  exact top_accepted_leaf0_pos
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
    (by constructor <;> linarith [hδb.1,hδb.2,hpb.1,hpb.2])
theorem top_accepted_binding (δ p : ℝ) :
    top_accepted_power δ p = DetectorAffine.JN δ p*(theta-reserve-rowBase dPlus (newCapacity dPlus) δ p)-3*dPlus*acceptedN δ p/4 := by
  norm_num [top_accepted_power,rowBase,oldCapacity,newCapacity,reserve,oldJ,oldD,oldP,oldN,newN,acceptedN,
    Detector836.JN,Detector836.DN,Detector836.aN,Detector836.cN,Detector836.lam,Detector836.Bc,
    DetectorAffine.JN,DetectorAffine.DN,DetectorAffine.aN,DetectorAffine.cN,DetectorAffine.lam,DetectorAffine.Bc,
    theta,h,x,y,ell,kappaStar,d0,dMinus,dPlus,lambda,B]
  ring
theorem top_bound {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dPlus δ p ≤ theta-reserve := by
  have hk : Detector836.kStar ≤ kappaStar := by rw [kappaStar_eq_detector]
  by_cases hn : Detector836.InRegion δ p
  · unfold newExponent rowAt
    have hc : Detector836.count kappaStar δ p=Detector836.RNew δ p := by simp only [Detector836.count,hn,hk,and_self,ite_true]
    rw [hc]
    exact positive_polynomial_to_row (Detector836.region_JN_pos hn) (new_count_mul hn)
      (top_affine_binding δ p) (top_affine_pos hn)
  · by_cases ha : Detector836.InAcceptedRegion δ p
    · unfold newExponent rowAt
      have hc : Detector836.count kappaStar δ p=DetectorAffine.RNew δ p := by simp only [Detector836.count,hn,ha,hk,false_and,and_self,ite_false,ite_true]
      rw [hc]
      exact positive_polynomial_to_row (DetectorAffine.region_JN_pos (Detector836.accepted_region_subset ha)) (accepted_count_mul ha)
        (top_accepted_binding δ p) (top_accepted_pos ha)
    · unfold newExponent rowAt
      have hc : Detector836.count kappaStar δ p=Cycle63.Arithmetic.Bernstein.countingR0 kappaStar δ p := by simp only [Detector836.count,hn,ha,false_and,ite_false]
      rw [hc]
      exact positive_polynomial_to_row (oldJ_pos hδ hp) (old_count_mul hδ hp)
        (top_old_binding δ p) (top_old_pos hδ hp hn ha)
end
end Target836.EndpointCertificates
#print axioms Target836.EndpointCertificates.top_bound
