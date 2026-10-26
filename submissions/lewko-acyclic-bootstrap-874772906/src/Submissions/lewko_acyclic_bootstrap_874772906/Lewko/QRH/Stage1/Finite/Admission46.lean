/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission46_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(400951743041438293/104931017973333:ℝ),(1202140436070394880/314793053919999:ℝ)]]
theorem admission46_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission46_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission46_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_00_coefficients]
def admission46_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(293397449618771968/104931017973333:ℝ),(879792348856315904/314793053919999:ℝ)]]
theorem admission46_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission46_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission46_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_01_coefficients]
def admission46_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(492648479581420/346306990011:ℝ),(1477310282627072/1038920970033:ℝ)]]
theorem admission46_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission46_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission46_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_02_coefficients]
def admission46_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43831045658350995956543488/944379161759997:ℝ),(262874195649254134811463680/2833137485279991:ℝ),(131381067685001146941833216/2833137485279991:ℝ)],
![(43812311697553922910748672/944379161759997:ℝ),(262761795018340556829851648/2833137485279991:ℝ),(131324868940078788097605632/2833137485279991:ℝ)]]
theorem admission46_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3913786081674062851/7736354093137895424:ℝ) admission46_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission46_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_03_coefficients]
def admission46_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(59713056285172034468/8180480079:ℝ),(15156461799848156426240/1038920970033:ℝ),(7572905241427069370368/1038920970033:ℝ)],
![(7589613467189938236704/1038920970033:ℝ),(5056189393701243551744/346306990011:ℝ),(2526318768114903285760/346306990011:ℝ)]]
theorem admission46_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1805521307331817/22695574897360896:ℝ) admission46_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission46_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_04_coefficients]
def admission46_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2539281429154338419229896036/590236976099998125:ℝ),(5078780867643237969360402848/590236976099998125:ℝ),(846499668136985883105653104/196745658699999375:ℝ)],
![(2532915240560758896593185712/590236976099998125:ℝ),(5066051071945476706846646432/590236976099998125:ℝ),(168875693142223522690832048/39349131739999875:ℝ)]]
theorem admission46_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (158307202535047431037074107/3380064678985900763381760000:ℝ) admission46_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission46_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_05_coefficients]
def admission46_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(14041396958157329994520514528940646313910272/326718059833277618424131577033:ℝ),(4251220585523848590016673823232351955366305792/32998524043161039460837289280333:ℝ),(4247898933406375559387055756827766327208837120/32998524043161039460837289280333:ℝ),(1414859440566245297313281323169619649547468800/32998524043161039460837289280333:ℝ)],
![(1419226132028898617648609578565601301459173376/32998524043161039460837289280333:ℝ),(4254354866899629237798887018959853848882118656/32998524043161039460837289280333:ℝ),(4251032378670395131282130479348020301350830080/32998524043161039460837289280333:ℝ),(1415903643709456484058262893155367753927884800/32998524043161039460837289280333:ℝ)]]
theorem admission46_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41177829278349099253341594104702225/360431878615433647017572098379317248:ℝ) admission46_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission46_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_06_coefficients]
def admission46_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(65570652137598336194509502656404702524/2943405944443942508325509703:ℝ),(43691403062661263193869819359859757056/981135314814647502775169901:ℝ),(65503565419062949613224564138170122240/2943405944443942508325509703:ℝ)],
![(65506685742803376928508396387575641632/2943405944443942508325509703:ℝ),(43648769719296535941023834843294302208/981135314814647502775169901:ℝ),(65439631779677680494200703268715233280/2943405944443942508325509703:ℝ)]]
theorem admission46_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1950253003230025783008357979915/8037460498961592342734191828992:ℝ) admission46_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission46_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_07_coefficients]
def admission46_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(810764400062547572696077421346485890151139800668887788647759/870949219889174394553349062508789062500000000000:ℝ),(487572811046992911253607816534365642474547312710202107265309/174189843977834878910669812501757812500000000000:ℝ),(2443434576949512309131314500910964420242890196111884181536787/870949219889174394553349062508789062500000000000:ℝ),(816334921341493265643592019421160250710898211067066121358001/870949219889174394553349062508789062500000000000:ℝ)],
![(33055452143705723936880794659225187319727450203027203942377/34837968795566975782133962500351562500000000000:ℝ),(2484711490899916370864219560790660750668213873902933504287779/870949219889174394553349062508789062500000000000:ℝ),(99610549693049713897081702417629689078078559499094514824971/34837968795566975782133962500351562500000000000:ℝ),(831938554583193483083498441962987441472210185551671964895921/870949219889174394553349062508789062500000000000:ℝ)]]
theorem admission46_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (810764400062547572696077421346485890151139800668887788647759/326867215179292498901706102166651643363328000000000000000000000:ℝ) admission46_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission46_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_08_coefficients]
def admission46_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28046348737985906750132971823583226284156739404884/8709492198891743945533490625087890625:ℝ),(84031213341422267543520640158758052693017828595056/8709492198891743945533490625087890625:ℝ),(83923395401058652720827233893789935347021177618432/8709492198891743945533490625087890625:ℝ),(5587706160248867920137567686660623043442509873152/1741898439778348789106698125017578125:ℝ)],
![(27874726837076124260647168578232733002680091540832/8709492198891743945533490625087890625:ℝ),(83516535824737454975691016488344237513372184007808/8709492198891743945533490625087890625:ℝ),(83408906024778598908541038954989564057632226410496/8709492198891743945533490625087890625:ℝ),(5553419408148152589863135794130926949160089288704/1741898439778348789106698125017578125:ℝ)]]
theorem admission46_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (20688099444464417509224771686386044879109/2435350531185362479848460124184576000000000:ℝ) admission46_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission46_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_09_coefficients]
def admission46_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8608210866595103438104207582311159808/1844490550312494140625:ℝ),(386760524743698979752606052665962719232/27667358254687412109375:ℝ),(386151622083189141950006676821843247104/27667358254687412109375:ℝ),(4759787420496074107762545847798071296/1024716972395830078125:ℝ)],
![(257364822294963182968285447596275236864/27667358254687412109375:ℝ),(85653036283031577760570679885297975296/3074150917187490234375:ℝ),(85517812134261957955238810694717538304/3074150917187490234375:ℝ),(2536116881049536103666323018624270336/273934240145419921875:ℝ)],
![(128241266134576972591391843027657555968/27667358254687412109375:ℝ),(384115622731296657074322806289504796672/27667358254687412109375:ℝ),(76701501692977200611588988658503385088/5533471650937482421875:ℝ),(127633151883155575575013980030669684736/27667358254687412109375:ℝ)]]
theorem admission46_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (14858454452263607594069789633/6601688826144337428480000000000:ℝ) admission46_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission46_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_10_coefficients]
def admission46_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53773183489721570897815147460149177028/2943405944443942508325509703:ℝ),(35830500061513366631813839522287042560/981135314814647502775169901:ℝ),(53718324710206879129123804291159556096/2943405944443942508325509703:ℝ)],
![(53719409698408919021679533998701529568/2943405944443942508325509703:ℝ),(35794660225397005841159213677012975616/981135314814647502775169901:ℝ),(53664578988943255723910153805372588032/2943405944443942508325509703:ℝ)]]
theorem admission46_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (799664541914213534055801537713/4018730249480796171367095914496:ℝ) admission46_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission46_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_11_coefficients]
def admission46_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission46_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission46_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission46_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_12_coefficients]
def admission46_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission46_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission46_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission46_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_13_coefficients]
def admission46_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission46_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission46_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission46_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_14_coefficients]
theorem admission46_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission46_00_pos hδ hp
 · exact admission46_01_pos hδ hp
 · exact admission46_02_pos hδ hp
 · exact admission46_03_pos hδ hp
 · exact admission46_04_pos hδ hp
 · exact admission46_05_pos hδ hp
 · exact admission46_06_pos hδ hp
 · exact admission46_07_pos hδ hp
 · exact admission46_08_pos hδ hp
 · exact admission46_09_pos hδ hp
 · exact admission46_10_pos hδ hp
 · exact admission46_11_pos hδ hp
 · exact admission46_12_pos hδ hp
 · exact admission46_13_pos hδ hp
 · exact admission46_14_pos hδ hp
#print axioms admission46_all
end
end LewkoStage1Finite
