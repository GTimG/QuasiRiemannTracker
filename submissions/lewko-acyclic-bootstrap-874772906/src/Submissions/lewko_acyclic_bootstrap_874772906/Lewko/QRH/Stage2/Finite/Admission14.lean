/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(75490965307346089/157396201727529:ℝ),(75133569105618560/157396201727529:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission14_00_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission14_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]
def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(55186855284494848/157396201727529:ℝ),(54986855284494848/157396201727529:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission14_01_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission14_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]
def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9357568789830570/52465400575843:ℝ),(9325493405912576/52465400575843:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission14_02_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission14_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]
def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(65769559714328511328256/1416565815547761:ℝ),(43699988753699842297856/472188605182587:ℝ),(65330680146771015565312/1416565815547761:ℝ)],
![(65330313652299643392512/1416565815547761:ℝ),(43407222285114743522816/472188605182587:ℝ),(64891628603044587175936/1416565815547761:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (990167672775948901/1934084526827876352:ℝ) admission14_03_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission14_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]
def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(366961542203640098032/52465400575843:ℝ),(729830266156154720256/52465400575843:ℝ),(362873599410870157312/52465400575843:ℝ)],
![(371763089187946086554/52465400575843:ℝ),(739406433688904029696/52465400575843:ℝ),(367648252034697396224/52465400575843:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1038189695580111/13431142547415808:ℝ) admission14_04_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission14_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]
def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(457850399180452646150903/98372626079705625:ℝ),(2747261085959334555167146/295117878239116875:ℝ),(1373696708264726731844437/295117878239116875:ℝ)],
![(441224749216752938703929/98372626079705625:ℝ),(2647668680775484574640586/295117878239116875:ℝ),(1323981166260441334942549/295117878239116875:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (441224749216752938703929/8802233579874423930880000:ℝ) admission14_05_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission14_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]
def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1157967463844195391295564374734952644608/222962078864277026675608012569:ℝ),(42578064354202724869037857748902733103104/2749865639326083328999165488351:ℝ),(126935995325599719339521643630776188665856/8249596917978249986997496465053:ℝ),(42046597056256363113216870649261237207040/8249596917978249986997496465053:ℝ)],
![(43357931361587646164079725068520409278464/8249596917978249986997496465053:ℝ),(43090105444669694372682952714752258062336/2749865639326083328999165488351:ℝ),(128468844965311764937259887146836235649024/8249596917978249986997496465053:ℝ),(42556458614913532602629941671099870740480/8249596917978249986997496465053:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (156635780097009104166987801526715/1407931207334954664447572730035712:ℝ) admission14_06_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission14_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]
def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1696684143907236307741781130515553808/74320692954759008891869337523:ℝ),(3379650042295350643189726709504782336/74320692954759008891869337523:ℝ),(1682979563023608777489113282751365120/74320692954759008891869337523:ℝ)],
![(1671356996005455856395093316277142022/74320692954759008891869337523:ℝ),(3329099323848897205052260913212301824/74320692954759008891869337523:ℝ),(1657755889306352359508427155282984960/74320692954759008891869337523:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12647673716021365047519128076805/50736259723782150070182801082368:ℝ) admission14_07_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission14_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]
def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(393453388205462330959114311443415469213754223432277637/12096466952271974103494358320800781250000000000:ℝ),(1273643843090927091453948389222638449780595525536486139/12096466952271974103494358320800781250000000000:ℝ),(2460341865288998670210107366855475988994690081389621861/21773640514089553386289844977441406250000000000:ℝ),(4379991925877925978030396144517382085027199781760232787/108868202570447766931449224887207031250000000000:ℝ)],
![(3282798270522080354758549190306246313020402244262169051/48385867809087896413977433283203125000000000000:ℝ),(10205609565605735748125948206026931427876479464353921011/48385867809087896413977433283203125000000000000:ℝ),(23765788863309077953350319664733317523136332763153390457/108868202570447766931449224887207031250000000000:ℝ),(8189460121019035338861204771261186354636238803103198547/108868202570447766931449224887207031250000000000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (393453388205462330959114311443415469213754223432277637/554175252876297831166583341955678208000000000000000000000:ℝ) admission14_08_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission14_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]
def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1107195192019207263107847773517510504143295968/2177364051408955338628984497744140625:ℝ),(219462355017149135062595628482483033918992336/145157603427263689241932299849609375:ℝ),(3262320423300815053241576966100162280131878912/2177364051408955338628984497744140625:ℝ),(215516069010374583643242531633432826004307968/435472810281791067725796899548828125:ℝ)],
![(1022751517057965178760519717097798529371750452/2177364051408955338628984497744140625:ℝ),(202622793037446271304247292812686794289609902/145157603427263689241932299849609375:ℝ),(3010463161605399885446530033914637425016398848/2177364051408955338628984497744140625:ℝ),(198774567690505787157977965060967253723643904/435472810281791067725796899548828125:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3033059199379055590179107132888294276789/304417558342692900421096806494208000000000:ℝ) admission14_09_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission14_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]
def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(216553573319627785576962355314688/4611216847486201171875:ℝ),(14286829677453483604786548719616/102471485499693359375:ℝ),(1908479946220007836544574796464128/13833650542458603515625:ℝ),(629418687339170906629277785260032/13833650542458603515625:ℝ)],
![(416204714245929691854574039625728/4611216847486201171875:ℝ),(137247392201852087929661135679488/512357427498466796875:ℝ),(146622090180248204281531683602432/553346021698344140625:ℝ),(1208486863390362808501163545591808/13833650542458603515625:ℝ)],
![(66507406246920327942651704051456/1537072282495400390625:ℝ),(13154077866656726668605973426432/102471485499693359375:ℝ),(195102051188026372182164150638592/1537072282495400390625:ℝ),(64298292544103612595726253293568/1537072282495400390625:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (735835562257045127056803741/275069799371075747840000000000:ℝ) admission14_10_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission14_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]
def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1392802740027475352502661402409171440/74320692954759008891869337523:ℝ),(2774366009259814235720095907576963072/74320692954759008891869337523:ℝ),(153508488016613214447675379431178240/8257854772751000987985481947:ℝ)],
![(1371509800704720557193775672524000250/74320692954759008891869337523:ℝ),(2731868926593389776840219513360360448/74320692954759008891869337523:ℝ),(151152460229925506261355099551498240/8257854772751000987985481947:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2306403506926353550130540459465/11274724383062700015596178018304:ℝ) admission14_11_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission14_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_11_coefficients]
def admission14_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission14_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission14_12_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission14_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_12_coefficients]
def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission14_13_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission14_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_13_coefficients]
def admission14_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission14_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission14_14_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission14_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_14_coefficients]
theorem admission14_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission14_00_pos hδ hp
 · exact admission14_01_pos hδ hp
 · exact admission14_02_pos hδ hp
 · exact admission14_03_pos hδ hp
 · exact admission14_04_pos hδ hp
 · exact admission14_05_pos hδ hp
 · exact admission14_06_pos hδ hp
 · exact admission14_07_pos hδ hp
 · exact admission14_08_pos hδ hp
 · exact admission14_09_pos hδ hp
 · exact admission14_10_pos hδ hp
 · exact admission14_11_pos hδ hp
 · exact admission14_12_pos hδ hp
 · exact admission14_13_pos hδ hp
 · exact admission14_14_pos hδ hp
#print axioms admission14_all
end
end LewkoStage2Finite
