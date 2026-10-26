/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission36_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(75490965307346089/157396201727529:ℝ),(75133569105618560/157396201727529:ℝ)]]
theorem admission36_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission36_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission36_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_00_coefficients]
def admission36_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(55186855284494848/157396201727529:ℝ),(54986855284494848/157396201727529:ℝ)]]
theorem admission36_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission36_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission36_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_01_coefficients]
def admission36_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9357568789830570/52465400575843:ℝ),(9325493405912576/52465400575843:ℝ)]]
theorem admission36_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission36_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission36_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_02_coefficients]
def admission36_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129561831335468578533376/1416565815547761:ℝ),(86082299360747227303936/472188605182587:ℝ),(128685628346773103378432/1416565815547761:ℝ)],
![(129122585273439710597632/1416565815547761:ℝ),(85789532892162128528896/472188605182587:ℝ),(128246576803046674989056/1416565815547761:ℝ)]]
theorem admission36_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1956887463425394821/3868169053655752704:ℝ) admission36_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission36_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_03_coefficients]
def admission36_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(753236849786419148592/52465400575843:ℝ),(1498072651583686004736/52465400575843:ℝ),(744845809317049270272/52465400575843:ℝ)],
![(758038396770725137114/52465400575843:ℝ),(1507648819116435314176/52465400575843:ℝ),(749620461940876509184/52465400575843:ℝ)]]
theorem admission36_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131020954085491/26862285094831616:ℝ) admission36_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission36_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_04_coefficients]
def admission36_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(840885373524256608790423/98372626079705625:ℝ),(5046921579685563122508266/295117878239116875:ℝ),(2524238405114017216666997/295117878239116875:ℝ)],
![(824259723560556901343449/98372626079705625:ℝ),(4947329174501713141981706/295117878239116875:ℝ),(2474522863109731819765109/295117878239116875:ℝ)]]
theorem admission36_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (824259723560556901343449/17604467159748847861760000:ℝ) admission36_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission36_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_05_coefficients]
def admission36_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(87755227684661114487370225269649252990976/8249596917978249986997496465053:ℝ),(87213011197512527809584191137247131746304/2749865639326083328999165488351:ℝ),(260016449065009769587992383127969150795776/8249596917978249986997496465053:ℝ),(86132640347141404184086025385877008547840/8249596917978249986997496465053:ℝ)],
![(88268362884013531173514068472976414418944/8249596917978249986997496465053:ℝ),(87725052287979497313229286103096656705536/2749865639326083328999165488351:ℝ),(261549298704721815185730626644029197778944/8249596917978249986997496465053:ℝ),(86642501905798573673499096407715642081280/8249596917978249986997496465053:ℝ)]]
theorem admission36_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320869089466115102857671772636015/2815862414669909328895145460071424:ℝ) admission36_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission36_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_06_coefficients]
def admission36_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3279033962610626467642461193263143888/74320692954759008891869337523:ℝ),(6531460053039868707144529940948381696/74320692954759008891869337523:ℝ),(3252452594319563674065138991895019520/74320692954759008891869337523:ℝ)],
![(3253706814708846016295773379024732102/74320692954759008891869337523:ℝ),(6480909334593415269007064144655901184/74320692954759008891869337523:ℝ),(3227228920602307256084452864426639360/74320692954759008891869337523:ℝ)]]
theorem admission36_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (24621802677935083435702917972005/101472519447564300140365602164736:ℝ) admission36_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission36_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_07_coefficients]
def admission36_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2495891494111155692840320567419415374592893797397613777/12096466952271974103494358320800781250000000000:ℝ),(7642401919565215854761930243120278848573229723889749679/12096466952271974103494358320800781250000000000:ℝ),(14034693513979285137120570761964496147756911039829177649/21773640514089553386289844977441406250000000000:ℝ),(23854866953582647564408433802191938401438243579466665127/108868202570447766931449224887207031250000000000:ℝ)],
![(11692550694144853802283374214210245934536960540123513611/48385867809087896413977433283203125000000000000:ℝ),(35680641871502890801357875621617493023047016257766975171/48385867809087896413977433283203125000000000000:ℝ),(81637547106760510287902636640278418316947437555351169397/108868202570447766931449224887207031250000000000:ℝ),(27664335148723756925239242428935742671047282600809630887/108868202570447766931449224887207031250000000000:ℝ)]]
theorem admission36_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2495891494111155692840320567419415374592893797397613777/1108350505752595662333166683911356416000000000000000000000:ℝ) admission36_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission36_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_08_coefficients]
def admission36_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1831817257446181789929201010695472725025848928/2177364051408955338628984497744140625:ℝ),(362803468816216147756830554610225653785249424/145157603427263689241932299849609375:ℝ),(5388711572331420579599168219770568264074780672/2177364051408955338628984497744140625:ℝ),(355695382081339583102794513690770576745627648/435472810281791067725796899548828125:ℝ)],
![(1747373582484939705581872954275760750254303412/2177364051408955338628984497744140625:ℝ),(69192781367302656799696443788085882831173398/29031520685452737848386459969921875:ℝ),(5136854310636005411804121287585043408959300608/2177364051408955338628984497744140625:ℝ),(338953880761470786617529947118305004464963584/435472810281791067725796899548828125:ℝ)]]
theorem admission36_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5172025768455059610252837327854995795669/608835116685385800842193612988416000000000:ℝ) admission36_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission36_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_09_coefficients]
def admission36_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2129793055786873601170853382569984/13833650542458603515625:ℝ),(420950978540150750135200192282624/922243369497240234375:ℝ),(693245700365571758615980073418752/1537072282495400390625:ℝ),(2054739797331258176686671159099392/13833650542458603515625:ℝ)],
![(4151983252307827648962087275597824/13833650542458603515625:ℝ),(4102162457785868770195736002834432/4611216847486201171875:ℝ),(2431429153841862357863617462042624/2766730108491720703125:ℝ),(1334213960539469375897655525769216/4611216847486201171875:ℝ)],
![(2021803429964331280442264176557824/13833650542458603515625:ℝ),(399404374950681138091089663375616/922243369497240234375:ℝ),(5916780618325206040920026711595008/13833650542458603515625:ℝ),(1947518541132890562495945937518592/13833650542458603515625:ℝ)]]
theorem admission36_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7429193653613626718505653143/3300837592452908974080000000000:ℝ) admission36_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission36_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_10_coefficients]
def admission36_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2689476840753575150403325781946893360/74320692954759008891869337523:ℝ),(5357185107749558416139358293840945152/74320692954759008891869337523:ℝ),(296414850993131742056909499403796480/8257854772751000987985481947:ℝ)],
![(2668183901430820355094440052061722170/74320692954759008891869337523:ℝ),(5314688025083133957259481899624342528/74320692954759008891869337523:ℝ),(98019607735481344623529739841372160/2752618257583666995995160649:ℝ)]]
theorem admission36_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4486981555274109403542926323305/22549448766125400031192356036608:ℝ) admission36_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission36_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_11_coefficients]
def admission36_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission36_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission36_12_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission36_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_12_coefficients]
def admission36_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission36_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission36_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission36_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_13_coefficients]
def admission36_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission36_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission36_14_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission36_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_14_coefficients]
theorem admission36_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission36_00_pos hδ hp
 · exact admission36_01_pos hδ hp
 · exact admission36_02_pos hδ hp
 · exact admission36_03_pos hδ hp
 · exact admission36_04_pos hδ hp
 · exact admission36_05_pos hδ hp
 · exact admission36_06_pos hδ hp
 · exact admission36_07_pos hδ hp
 · exact admission36_08_pos hδ hp
 · exact admission36_09_pos hδ hp
 · exact admission36_10_pos hδ hp
 · exact admission36_11_pos hδ hp
 · exact admission36_12_pos hδ hp
 · exact admission36_13_pos hδ hp
 · exact admission36_14_pos hδ hp
#print axioms admission36_all
end
end LewkoStage2Finite
