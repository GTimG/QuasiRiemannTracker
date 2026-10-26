/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission36_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1188837382383617/2478685463937:ℝ),(150267554508799360/314793053919999:ℝ)]]
theorem admission36_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission36_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission36_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_00_coefficients]
def admission36_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(869086957535744/2478685463937:ℝ),(109974043607039488/314793053919999:ℝ)]]
theorem admission36_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission36_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission36_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_01_coefficients]
def admission36_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1459046783036/8180480079:ℝ),(184663785328384/1038920970033:ℝ)]]
theorem admission36_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission36_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission36_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_02_coefficients]
def admission36_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(259124398655719849005056/2833137485279991:ℝ),(172165088497907696316416/944379161759997:ℝ),(257371990038003239944192/2833137485279991:ℝ)],
![(258245904232700455419392/2833137485279991:ℝ),(171579554027097279474176/944379161759997:ℝ),(256493884648591383003136/2833137485279991:ℝ)]]
theorem admission36_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3913786081674062851/7736354093137895424:ℝ) admission36_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission36_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_03_coefficients]
def admission36_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4971875140631400352/346306990011:ℝ),(9888297704978108416/346306990011:ℝ),(4916488620582895616/346306990011:ℝ)],
![(5003568614225035916/346306990011:ℝ),(29854520758647247360/1038920970033:ℝ),(14844013719836819456/1038920970033:ℝ)]]
theorem admission36_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9377457848707/118206119257088:ℝ) admission36_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission36_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_04_coefficients]
def admission36_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1681775178160947936485438/196745658699999375:ℝ),(10093869803411039078041396/590236976099998125:ℝ),(5048490160930643109645082/590236976099998125:ℝ)],
![(1648523784842748005503394/196745658699999375:ℝ),(9894684433166933222614036/590236976099998125:ℝ),(4949058797218067969731354/590236976099998125:ℝ)]]
theorem admission36_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (824261892421374002751697/17604503536384899809280000:ℝ) admission36_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission36_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_05_coefficients]
def admission36_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(351022784302920514547428526202658085789696/32998524043161039460837289280333:ℝ),(38761545360707160321836807070752026370048/1222167557154112572623603306679:ℝ),(1040071356355107206476550556562798306918400/32998524043161039460837289280333:ℝ),(344532404678956578053185016655151680716800/32998524043161039460837289280333:ℝ)],
![(353075338187194894141877631507880601928704/32998524043161039460837289280333:ℝ),(38989120630658972917725579654421544963072/1222167557154112572623603306679:ℝ),(1046202794059641685999958389495067059159040/32998524043161039460837289280333:ℝ),(346571863943040927164477145533565947084800/32998524043161039460837289280333:ℝ)]]
theorem admission36_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (641741612328135553846480355887025/5631748103366150734649564037176832:ℝ) admission36_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission36_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_06_coefficients]
def admission36_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129863474987608672994695811525916128/2943405944443942508325509703:ℝ),(258673169262708646252966406794276864/2943405944443942508325509703:ℝ),(128810743935077799699983574656942080/2943405944443942508325509703:ℝ)],
![(128860413870711776461655420504774852/2943405944443942508325509703:ℝ),(2021032670208374379702297466736128/23176424759401122112799289:ℝ),(127811780819682969715235748571709440/2943405944443942508325509703:ℝ)]]
theorem admission36_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1950253003230025783008357979915/8037460498961592342734191828992:ℝ) admission36_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission36_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_07_coefficients]
def admission36_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(19968888941780192197146416592238758719313254835252972007/96772135543241599394816562500976562500000000000:ℝ),(183433435870683273907467080299379903602750545334726734667/290316406629724798184449687502929687500000000000:ℝ),(112287008163869600403416608383543888153618896119301953159/174189843977834878910669812501757812500000000000:ℝ),(190854679385340407984550532646134327173850186547106309857/870949219889174394553349062508789062500000000000:ℝ)],
![(93547478758173427322590974763762827916201444396580305501/387088542172966397579266250003906250000000000000:ℝ),(856398969766659680786774690777637170158771657449625094383/1161265626518899192737798750011718750000000000000:ℝ),(653147980151652181954172110003366799527936017211952731427/870949219889174394553349062508789062500000000000:ℝ),(221330525560536145171867764173140559129537636712352098017/870949219889174394553349062508789062500000000000:ℝ)]]
theorem admission36_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (19968888941780192197146416592238758719313254835252972007/8866840689542439748852704594364465152000000000000000000000:ℝ) admission36_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission36_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_08_coefficients]
def admission36_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7327270351626008464688703481775173635509784208/8709492198891743945533490625087890625:ℝ),(161246008291355894044830879526159333587201296/64514757028827732929877708333984375:ℝ),(21554848305662923800901547757433648955788091392/8709492198891743945533490625087890625:ℝ),(1422781597889129695326804427336058521342640128/1741898439778348789106698125017578125:ℝ)],
![(6989494101495330291646559740798409219665052782/8709492198891743945533490625087890625:ℝ),(30752344833943212614667788260066310052689542/12902951405765546585975541666796875:ℝ),(203439748855857367082831483157123063310373888/86232596028631128173598917080078125:ℝ),(1355815285192420065884554637238995837197287424/1741898439778348789106698125017578125:ℝ)]]
theorem admission36_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (20688099444464417509224771686386044879109/2435350531185362479848460124184576000000000:ℝ) admission36_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission36_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_09_coefficients]
def admission36_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4259604778234612388762204349743104/27667358254687412109375:ℝ),(841905663285488820784106292690944/1844490550312494140625:ℝ),(1386497532467363693201650885722112/3074150917187490234375:ℝ),(4109497853871553315815467930877952/27667358254687412109375:ℝ)],
![(8304003179415141954385464225542144/27667358254687412109375:ℝ),(2734787106750675257774427875160064/3074150917187490234375:ℝ),(4862879988201086741770400759250944/5533471650937482421875:ℝ),(2668439875527416114422539048452096/9222452751562470703125:ℝ)],
![(4043624865584056823139313739302144/27667358254687412109375:ℝ),(798812324136603433825441524810496/1844490550312494140625:ℝ),(11833614446192045208382140066408448/27667358254687412109375:ℝ),(3895054683934191149139830933553152/27667358254687412109375:ℝ)]]
theorem admission36_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (14858454452263607594069789633/6601688826144337428480000000000:ℝ) admission36_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission36_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission36_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission36_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission36_10_coefficients]
def admission36_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(106514526243598826815835471256476192/2943405944443942508325509703:ℝ),(212166928353785176708668521206202368/2943405944443942508325509703:ℝ),(105653407732523912042225307991539712/2943405944443942508325509703:ℝ)],
![(105671236893932356531913700472607036/2943405944443942508325509703:ℝ),(1657353278240688977194250968459264/23176424759401122112799289:ℝ),(104813630837779796335762019151118336/2943405944443942508325509703:ℝ)]]
theorem admission36_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (799664541914213534055801537713/4018730249480796171367095914496:ℝ) admission36_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
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
def admission36_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission36_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission36_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Finite
