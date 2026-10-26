/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8427618923146631/34977005991111:ℝ),(75133777254399680/314793053919999:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission13_00_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission13_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]
def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6154113533724416/34977005991111:ℝ),(54987021803519744/314793053919999:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission13_01_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission13_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]
def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10329672086820/115435663337:ℝ),(92331892664192/1038920970033:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission13_02_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission13_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]
def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3678287428659866675200/314793053919999:ℝ),(65769472694233374599168/2833137485279991:ℝ),(32665433036294574522368/2833137485279991:ℝ)],
![(3653874199309118613248/314793053919999:ℝ),(65330223682723677806336/2833137485279991:ℝ),(32445906688941610287104/2833137485279991:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1980340984432471331/3868177046568947712:ℝ) admission13_03_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission13_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]
def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1836932340190256224/1038920970033:ℝ),(3633245100134963200/1038920970033:ℝ),(1796409303674519552/1038920970033:ℝ)],
![(1860835903636735012/1038920970033:ℝ),(3680784992947357952/1038920970033:ℝ),(1820046268196552704/1038920970033:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (13705515317341/177309178885632:ℝ) admission13_04_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission13_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]
def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5407675923718410539534/4647535244881875:ℝ),(274746949842425290126804/118047395219999625:ℝ),(228977848864462847457734/196745658699999375:ℝ)],
![(5210673279933444789842/4647535244881875:ℝ),(1323857745946361092877204/590236976099998125:ℝ),(44138380377682983826318/39349131739999875:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2605336639966722394921/51981801780664074240000:ℝ) admission13_05_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission13_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]
def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(21823611002469683892819133426961560219648/32998524043161039460837289280333:ℝ),(64666634356908705973585848897290342084608/32998524043161039460837289280333:ℝ),(63866439306739348401596085991672195317760/32998524043161039460837289280333:ℝ),(21023410476413698850501031321343413452800/32998524043161039460837289280333:ℝ)],
![(22081825760517669684710250975910980116992/32998524043161039460837289280333:ℝ),(65437978873022567173114910640099816858112/32998524043161039460837289280333:ℝ),(64634501508841337365713495895334033489920/32998524043161039460837289280333:ℝ),(21278342884424242489412547431145196748800/32998524043161039460837289280333:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (313273228353466076411322225948325/2815874051683075367324782018588416:ℝ) admission13_06_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission13_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]
def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16934909097518877833637210116437856/2943405944443942508325509703:ℝ),(1244356580282880573838702410254336/109015034979405278086129989:ℝ),(16663259744294316828918599005061120/2943405944443942508325509703:ℝ)],
![(16683117274895823819797176833382724/2943405944443942508325509703:ℝ),(3677344350245848941181284873343232/327045104938215834258389967:ℝ),(16413518965445609332731642483752960/2943405944443942508325509703:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1001801694668311116499734038315/4018730249480796171367095914496:ℝ) admission13_07_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission13_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]
def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(387122714817665813530641838785248710473506984371883/107997919262096149116913517578125000000000000:ℝ),(34795230699730816548996862360996158997273099069380463/2743147149257242187569603346484375000000000000:ℝ),(25453208672938952143899858492357447173209730074990486271/1741898439778348789106698125017578125000000000000:ℝ),(9602086540180398126105581502261886049044040691867993173/1741898439778348789106698125017578125000000000000:ℝ)],
![(3473530692898335200817176259008320343894080373082869/431991677048384596467654070312500000000000000:ℝ),(1424813748232019852903673711619780881291955149624774371/54862942985144843751392066929687500000000000000:ℝ),(48452793707694239221956468889926452586364910758777627967/1741898439778348789106698125017578125000000000000:ℝ),(17221048083979332422934889384013444037965903233179440213/1741898439778348789106698125017578125000000000000:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (387122714817665813530641838785248710473506984371883/618463375022335217152910451277824000000000000000000000:ℝ) admission13_08_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission13_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]
def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(568440957494743078247611061352853846999209656/8709492198891743945533490625087890625:ℝ),(1675601953527928223597713101094065706650763544/8709492198891743945533490625087890625:ℝ),(1645951402646735418855126728131913753713031168/8709492198891743945533490625087890625:ℝ),(107758125314020189238558030173302537499795456/1741898439778348789106698125017578125:ℝ)],
![(525849413204864582798687279789074092738608549/8709492198891743945533490625087890625:ℝ),(1548567774621573940585572893700807580245024521/8709492198891743945533490625087890625:ℝ),(1519654821147733542675453094922851396125485312/8709492198891743945533490625087890625:ℝ),(99387336226931485558276806411169701981626368/1741898439778348789106698125017578125:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (12132243191764097358188086720113489011429/1217675265592681239924230062092288000000000:ℝ) admission13_09_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission13_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]
def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(167485420966900269586479808028672/27667358254687412109375:ℝ),(492308107400479624764157661421568/27667358254687412109375:ℝ),(96435592433790778985083083751424/5533471650937482421875:ℝ),(157355330968374539747737565364224/27667358254687412109375:ℝ)],
![(64440888203261016396008625731584/5533471650937482421875:ℝ),(946496429582754278389752889194496/27667358254687412109375:ℝ),(926414873014398511194795752415232/27667358254687412109375:ℝ),(302122995640699314785085991878656/27667358254687412109375:ℝ)],
![(17180168845618109966469148513408/3074150917187490234375:ℝ),(50433048942477397741406882737792/3074150917187490234375:ℝ),(9865503188552327893838849987072/614830183437498046875:ℝ),(16074642063917976694256515710976/3074150917187490234375:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (490559145017028097358902457/183380245170676039680000000000:ℝ) admission13_10_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission13_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]
def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13901614867442701246604155510091936/2943405944443942508325509703:ℝ),(340495624905695515068224003842048/36338344993135092695376663:ℝ),(13679050469859054090163763471679488/2943405944443942508325509703:ℝ)],
![(13689912302699040338565886622055356/2943405944443942508325509703:ℝ),(3017611450680506252362051625053184/327045104938215834258389967:ℝ),(13469106246173025163547941261574144/2943405944443942508325509703:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (411044502141510777696165199633/2009365124740398085683547957248:ℝ) admission13_11_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission13_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]
def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission13_12_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission13_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]
def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission13_13_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission13_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]
def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission13_14_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission13_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]
theorem admission13_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission13_00_pos hδ hp
 · exact admission13_01_pos hδ hp
 · exact admission13_02_pos hδ hp
 · exact admission13_03_pos hδ hp
 · exact admission13_04_pos hδ hp
 · exact admission13_05_pos hδ hp
 · exact admission13_06_pos hδ hp
 · exact admission13_07_pos hδ hp
 · exact admission13_08_pos hδ hp
 · exact admission13_09_pos hδ hp
 · exact admission13_10_pos hδ hp
 · exact admission13_11_pos hδ hp
 · exact admission13_12_pos hδ hp
 · exact admission13_13_pos hδ hp
 · exact admission13_14_pos hδ hp
#print axioms admission13_all
end
end LewkoStage1Finite
