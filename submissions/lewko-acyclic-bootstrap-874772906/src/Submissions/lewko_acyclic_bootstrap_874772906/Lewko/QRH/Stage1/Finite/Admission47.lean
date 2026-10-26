/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission47_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1188837382383617/2478685463937:ℝ),(150267554508799360/314793053919999:ℝ)]]
theorem admission47_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission47_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission47_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_00_coefficients]
def admission47_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(869086957535744/2478685463937:ℝ),(109974043607039488/314793053919999:ℝ)]]
theorem admission47_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission47_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission47_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_01_coefficients]
def admission47_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1459046783036/8180480079:ℝ),(184663785328384/1038920970033:ℝ)]]
theorem admission47_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission47_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission47_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_02_coefficients]
def admission47_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(258684956927406383889920/2833137485279991:ℝ),(171872255823567898454528/944379161759997:ℝ),(256932937343297311473664/2833137485279991:ℝ)],
![(257806462504386990304256/2833137485279991:ℝ),(171286721352757481612288/944379161759997:ℝ),(256054831953885454532608/2833137485279991:ℝ)]]
theorem admission47_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1953543334609111439/3868177046568947712:ℝ) admission47_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission47_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_03_coefficients]
def admission47_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(14963431913631041444/1038920970033:ℝ),(29759972900559114752/1038920970033:ℝ),(14796739790792753152/1038920970033:ℝ)],
![(15058512334411948136/1038920970033:ℝ),(3327733393808004096/115435663337:ℝ),(1654587516542320640/115435663337:ℝ)]]
theorem admission47_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (225780331280407/2836946862170112:ℝ) admission47_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission47_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_04_coefficients]
def admission47_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1665149481501847970994416/196745658699999375:ℝ),(9994438613121533015560168/590236976099998125:ℝ),(999787177439073573240884/118047395219999625:ℝ)],
![(1631898088183648040012372/196745658699999375:ℝ),(9795253242877427160132808/590236976099998125:ℝ),(4899504523482792726290692/590236976099998125:ℝ)]]
theorem admission47_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (407974522045912010003093/8802251768192449904640000:ℝ) admission47_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission47_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_05_coefficients]
def admission47_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(352055608555152719586231567068673468744704/32998524043161039460837289280333:ℝ),(4319535259801093601282520400624528043008/135796395239345841402622589631:ℝ),(10328154506569457052802180160172729303040/326718059833277618424131577033:ℝ),(345552134310998752608831081094358813900800/32998524043161039460837289280333:ℝ)],
![(354108162439427099180680672373895984883712/32998524043161039460837289280333:ℝ),(13034464202720551669143818729763423660032/407389185718037524207867768893:ℝ),(1049275042868049641856428029109714411847680/32998524043161039460837289280333:ℝ),(347591593575083101720123209972773080268800/32998524043161039460837289280333:ℝ)]]
theorem admission47_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5149128054246287831795678751086575/45053984826929205877196512297414656:ℝ) admission47_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission47_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_06_coefficients]
def admission47_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129359895428409191454029333547391172/2943405944443942508325509703:ℝ),(257670112231858376206939604360720896/2943405944443942508325509703:ℝ),(128311262377380384707609661614325760/2943405944443942508325509703:ℝ)],
![(128356834311512294920988942526249896/2943405944443942508325509703:ℝ),(2013134583351285639182401384582144/23176424759401122112799289:ℝ),(127312299261985554722861835529093120/2943405944443942508325509703:ℝ)]]
theorem admission47_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (971315759750256002219099697335/4018730249480796171367095914496:ℝ) admission47_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission47_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_07_coefficients]
def admission47_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(173423034525294196111176641132717862793454463737592193529/774177084345932795158532500007812500000000000000:ℝ),(1589750632613845434767501606002004202967007489399134431509/2322531253037798385475597500023437500000000000000:ℝ),(971208384090959135043046710673424796834376132239054915929/1393518751822679031285358500014062500000000000000:ℝ),(1647596897564815234568894337831854335685765268198701026879/6967593759113395156426792500070312500000000000000:ℝ)],
![(8030675220295980527167490316893337954854052553949161139/30967083373837311806341300000312500000000000000:ℝ),(1835081085181698605081314345162239314462546441620570742939/2322531253037798385475597500023437500000000000000:ℝ),(5589745435113229114711946098052302854250612954118818304701/6967593759113395156426792500070312500000000000000:ℝ),(1891403666966381132067432190047904191331264869520667332159/6967593759113395156426792500070312500000000000000:ℝ)]]
theorem admission47_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (173423034525294196111176641132717862793454463737592193529/70934725516339517990821636754915721216000000000000000000000:ℝ) admission47_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission47_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_08_coefficients]
def admission47_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7156909883237104365252184216041065930028434542/8709492198891743945533490625087890625:ℝ),(52494024958362940088191680250056122016433546/21504919009609244309959236111328125:ℝ),(21049661979666916296182853224597399525437907968/8709492198891743945533490625087890625:ℝ),(1389298441540774880605679532287527179269963776/1741898439778348789106698125017578125:ℝ)],
![(6819133633106426192210040475064301514183703116/8709492198891743945533490625087890625:ℝ),(49999263584482996431027700841446860908515684/21504919009609244309959236111328125:ℝ),(20042228308445586570647285266033179963997579264/8709492198891743945533490625087890625:ℝ),(1322332128844065251163429742190464495124611072/1741898439778348789106698125017578125:ℝ)]]
theorem admission47_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10088593512299081811244428575061527215001/1217675265592681239924230062092288000000000:ℝ) admission47_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission47_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_09_coefficients]
def admission47_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4151613539329241784789450518889728/27667358254687412109375:ℝ),(455783366047578014530816044848896/1024716972395830078125:ℝ),(486303218697104003733302016206848/1106694330187496484375:ℝ),(1334347785893125370263322571046912/9222452751562470703125:ℝ)],
![(323458945216458210458882571633664/1106694330187496484375:ℝ),(7987862509970412826485820429904896/9222452751562470703125:ℝ),(292197406002887122155276261072896/341572324131943359375:ℝ),(7790876456644886176591980148031488/27667358254687412109375:ℝ)],
![(3934086555485740734198667635454976/27667358254687412109375:ℝ),(777008166480129239086586297658368/1844490550312494140625:ℝ),(11508101716199141539589820983386112/27667358254687412109375:ℝ),(3787066010189006187489694153965568/27667358254687412109375:ℝ)]]
theorem admission47_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3611627588452345073213285593/1650422206536084357120000000000:ℝ) admission47_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission47_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_10_coefficients]
def admission47_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(106091125341304414385145344892817724/2943405944443942508325509703:ℝ),(211323643231311615810133161834747904/2943405944443942508325509703:ℝ),(105233519285151854188993663571329024/2943405944443942508325509703:ℝ)],
![(105247835991637944101223574108948568/2943405944443942508325509703:ℝ),(1650713237906251489804208768684032/23176424759401122112799289:ℝ),(104393742390407738482530374730907648/2943405944443942508325509703:ℝ)]]
theorem admission47_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (398230523645049051218148707317/2009365124740398085683547957248:ℝ) admission47_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission47_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_11_coefficients]
def admission47_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission47_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission47_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission47_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_12_coefficients]
def admission47_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission47_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission47_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission47_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_13_coefficients]
def admission47_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission47_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission47_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission47_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_14_coefficients]
theorem admission47_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission47_00_pos hδ hp
 · exact admission47_01_pos hδ hp
 · exact admission47_02_pos hδ hp
 · exact admission47_03_pos hδ hp
 · exact admission47_04_pos hδ hp
 · exact admission47_05_pos hδ hp
 · exact admission47_06_pos hδ hp
 · exact admission47_07_pos hδ hp
 · exact admission47_08_pos hδ hp
 · exact admission47_09_pos hδ hp
 · exact admission47_10_pos hδ hp
 · exact admission47_11_pos hδ hp
 · exact admission47_12_pos hδ hp
 · exact admission47_13_pos hδ hp
 · exact admission47_14_pos hδ hp
#print axioms admission47_all
end
end LewkoStage1Finite
