/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1188837382383617/2478685463937:ℝ),(150267554508799360/314793053919999:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission14_00_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission14_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]
def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(869086957535744/2478685463937:ℝ),(109974043607039488/314793053919999:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission14_01_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission14_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]
def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1459046783036/8180480079:ℝ),(184663785328384/1038920970033:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission14_02_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission14_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]
def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(131539492588466749198336/2833137485279991:ℝ),(87400225844548349095936/944379161759997:ℝ),(130661732145178298089472/2833137485279991:ℝ)],
![(130660998165447355612672/2833137485279991:ℝ),(86814691373737932253696/944379161759997:ℝ),(129783626755766441148416/2833137485279991:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1980340984432471331/3868177046568947712:ℝ) admission14_03_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission14_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]
def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7266586743999738976/1038920970033:ℝ),(14452127414968004608/1038920970033:ℝ),(7185637214698078208/1038920970033:ℝ)],
![(7361667164780645668/1038920970033:ℝ),(14641755058680926720/1038920970033:ℝ),(7280185072786210816/1038920970033:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (13705515317341/177309178885632:ℝ) admission14_04_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission14_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]
def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(915703224046423812952318/196745658699999375:ℝ),(5494536752840843685418676/590236976099998125:ℝ),(2747400720395072476821722/590236976099998125:ℝ)],
![(882451830728223881970274/196745658699999375:ℝ),(5295351382596737829991316/590236976099998125:ℝ),(2647969356682497336907994/590236976099998125:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (441225915364111940985137/8802251768192449904640000:ℝ) admission14_05_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission14_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]
def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(171380095142531437118502099637267511074816/32998524043161039460837289280333:ℝ),(233625737905467306198702436986433445888/15088488359927315711402509959:ℝ),(507746682943921779812396719822809742704640/32998524043161039460837289280333:ℝ),(168187283811309590804008250570747307622400/32998524043161039460837289280333:ℝ)],
![(173432649026805816712951204942490027213824/32998524043161039460837289280333:ℝ),(6383753346764888132661223326523542569984/407389185718037524207867768893:ℝ),(513878120648456259335804552755078494945280/32998524043161039460837289280333:ℝ),(170226743075393939915300379449161573990400/32998524043161039460837289280333:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (313273228353466076411322225948325/2815874051683075367324782018588416:ℝ) admission14_06_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission14_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]
def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(67195796509450970156200774198366048/2943405944443942508325509703:ℝ),(133848294312452818302964326173978624/2943405944443942508325509703:ℝ),(66653038977177267315674396020244480/2943405944443942508325509703:ℝ)],
![(66192735392554073623160383177224772/2943405944443942508325509703:ℝ),(1038159639103997781670785020907008/23176424759401122112799289:ℝ),(65654075861782437330926569935011840/2943405944443942508325509703:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1001801694668311116499734038315/4018730249480796171367095914496:ℝ) admission14_07_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission14_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]
def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3148482975363766831570554098715482840182414889842277267/96772135543241599394816562500976562500000000000:ℝ),(30575145111152015199851058346207464728873709306703090247/290316406629724798184449687502929687500000000000:ℝ),(19687344691933634293851382389235098274096966417331331251/174189843977834878910669812501757812500000000000:ℝ),(35047608451624218646030227991677304439443205362627880917/870949219889174394553349062508789062500000000000:ℝ)],
![(26265854892507725860287524789669724399678084614937526541/387088542172966397579266250003906250000000000000:ℝ),(244965806728534645956310602964947414663264313337530516703/1161265626518899192737798750011718750000000000000:ℝ),(190149662791972351406345980031822850130326368702099621887/870949219889174394553349062508789062500000000000:ℝ),(65523454626819955833347459518683536395130655527873669077/870949219889174394553349062508789062500000000000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3148482975363766831570554098715482840182414889842277267/4433420344771219874426352297182232576000000000000000000000:ℝ) admission14_08_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission14_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]
def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(4428784940239507666893241041445345994861981648/8709492198891743945533490625087890625:ℝ),(97538913163432620739056844591961944838129744/64514757028827732929877708333984375:ℝ),(13049293129428153029733988722925807264839852032/8709492198891743945533490625087890625:ℝ),(862065002512161513908464241386420299998363648/1741898439778348789106698125017578125:ℝ)],
![(4091008690108829493851097300468581579017250222/8709492198891743945533490625087890625:ℝ),(90054629041792789767564906366134161514376158/64514757028827732929877708333984375:ℝ),(12041859458206823304198420764361587703399523328/8709492198891743945533490625087890625:ℝ),(795098689815451884466214451289357615853010944/1741898439778348789106698125017578125:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (12132243191764097358188086720113489011429/1217675265592681239924230062092288000000000:ℝ) admission14_09_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission14_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]
def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(144369646833856481002643383730176/3074150917187490234375:ℝ),(257164003285801471181093492670464/1844490550312494140625:ℝ),(3816975820296310056674512459399168/27667358254687412109375:ℝ),(1258842647746996317981900522913792/27667358254687412109375:ℝ)],
![(277470971028239687372186418016256/3074150917187490234375:ℝ),(2470463441689099496756401579773952/9222452751562470703125:ℝ),(293245417589839432888008596488192/1106694330187496484375:ℝ),(2416983965125594518280687935029248/27667358254687412109375:ℝ)],
![(133015375794775123871326796897536/3074150917187490234375:ℝ),(26308267602633947568341990632192/204943394479166015625:ℝ),(390205768538062278207855188273152/3074150917187490234375:ℝ),(128597136511343813554052125687808/3074150917187490234375:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (490559145017028097358902457/183380245170676039680000000000:ℝ) admission14_10_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission14_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]
def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(55160810954663092057294063292977312/2943405944443942508325509703:ℝ),(109876493114158889801707342509129728/2943405944443942508325509703:ℝ),(54716201879436216360655053886717952/2943405944443942508325509703:ℝ)],
![(54317521604996621773372292509108156/2943405944443942508325509703:ℝ),(851916780290875694462273183442944/23176424759401122112799289:ℝ),(53876424984692100654191765046296576/2943405944443942508325509703:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (411044502141510777696165199633/2009365124740398085683547957248:ℝ) admission14_11_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
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
def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission14_13_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Finite
