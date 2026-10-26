/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission45_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(534364059703944391/34977005991111:ℝ),(4808561744281579520/314793053919999:ℝ)]]
theorem admission45_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission45_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission45_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_00_coefficients]
def admission45_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391063266158362624/34977005991111:ℝ),(3519169395425263616/314793053919999:ℝ)]]
theorem admission45_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission45_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission45_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_01_coefficients]
def admission45_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(656652920736164/115435663337:ℝ),(5909241130508288/1038920970033:ℝ)]]
theorem admission45_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission45_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission45_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_02_coefficients]
def admission45_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(934364684999246728754118656/314793053919999:ℝ),(16816771280874936221556752384/2833137485279991:ℝ),(8407489151921315662769684480/2833137485279991:ℝ)],
![(311421591574584717633585152/104931017973333:ℝ),(16814972908473145297368842240/2833137485279991:ℝ),(8406589972002557921262043136/2833137485279991:ℝ)]]
theorem admission45_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (31316988065848342781/61890832745103163392:ℝ) admission45_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission45_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_03_coefficients]
def admission45_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(161595979118920771641572/346306990011:ℝ),(323135152648735247187968/346306990011:ℝ),(161539175649330438602752/346306990011:ℝ)],
![(161628257128586963951056/346306990011:ℝ),(969599108981251410165760/1038920970033:ℝ),(484714343954673563598848/1038920970033:ℝ)]]
theorem admission45_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2407121295471943/30260766529814528:ℝ) admission45_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission45_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_04_coefficients]
def admission45_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32483469176538986724815541292/118047395219999625:ℝ),(324838159171955187006465983408/590236976099998125:ℝ),(54140270517707302949403839816/196745658699999375:ℝ)],
![(32463103568301925406661883912/118047395219999625:ℝ),(324634513414501626541503471536/590236976099998125:ℝ),(54106331278893410634979953992/196745658699999375:ℝ)]]
theorem admission45_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4057887946037740675832735489/86529655782039059542573056000:ℝ) admission45_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission45_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_05_coefficients]
def admission45_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(362383124706123286200875322045520107556182654976/32998524043161039460837289280333:ℝ),(1086936835050453473023211240473233807096379703296/32998524043161039460837289280333:ℝ),(1086724312629066876939141299663037990484175749120/32998524043161039460837289280333:ℝ),(362170602284376038136360608491878690943978700800/32998524043161039460837289280333:ℝ)],
![(362449967081748514621594174136142693846033498112/32998524043161039460837289280333:ℝ),(1087137348801759873508279896155090705322935713792/32998524043161039460837289280333:ℝ),(1086924813005913600980739841301309781101227540480/32998524043161039460837289280333:ℝ),(362237431285541554088039428970966569624325324800/32998524043161039460837289280333:ℝ)]]
theorem admission45_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (164696121957775193612342540514818525/1441727514461734588070288393517268992:ℝ) admission45_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission45_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_06_coefficients]
def admission45_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4192278666671681320637501983475150173196/2943405944443942508325509703:ℝ),(931498209086972195383167429550909997056/327045104938215834258389967:ℝ),(4191205248589864469341990330931609600000/2943405944443942508325509703:ℝ)],
![(4191255597432136394024672268732138018032/2943405944443942508325509703:ℝ),(310423624974708391576214162625647673344/109015034979405278086129989:ℝ),(4190182310359700163437608557020331376640/2943405944443942508325509703:ℝ)]]
theorem admission45_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (15609645509569720042637022424565/64299683991692738741873534631936:ℝ) admission45_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission45_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_07_coefficients]
def admission45_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10379550103942605692734458721213508009365616874323942398380443/43547460994458719727667453125439453125000000000:ℝ),(155782450300028233985113604286431603251526563000070570175506257/217737304972293598638337265627197265625000000000:ℝ),(155871647699029145784388723441920287500546647898107262701088747/217737304972293598638337265627197265625000000000:ℝ),(10397389583655676342205609568478515583232271357545528950371941/43547460994458719727667453125439453125000000000:ℝ)],
![(10429496343764677276987134212407906800298895165265753757935773/43547460994458719727667453125439453125000000000:ℝ),(156531570825479474900361626530358436780631906369699723053516259/217737304972293598638337265627197265625000000000:ℝ),(156620695157237275765408266891545177594790174145014987824803819/217737304972293598638337265627197265625000000000:ℝ),(2089464242005823407602662024122472518733693935179253529938657/8709492198891743945533490625087890625000000000:ℝ)]]
theorem admission45_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (10379550103942605692734458721213508009365616874323942398380443/4183900354294943985941838107733141035050598400000000000000000000:ℝ) admission45_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission45_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_08_coefficients]
def admission45_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1429638953009626895012361772630180481243370074775364/1741898439778348789106698125017578125:ℝ),(21437681415300415035380362061052791971792316635699904/8709492198891743945533490625087890625:ℝ),(21430778774684115848796398754770320854815102320246784/8709492198891743945533490625087890625:ℝ),(285651684977852881283530737332643789817441522024448/348379687955669757821339625003515625:ℝ)],
![(1427443998935410640194242025790719630612761890495824/1741898439778348789106698125017578125:ℝ),(21404760114068568215265981665873891909215892112758528/8709492198891743945533490625087890625:ℝ),(21397860483151119950002228673128133726301536280117248/8709492198891743945533490625087890625:ℝ),(1426064072754818625280090045541318399053132692717568/1741898439778348789106698125017578125:ℝ)]]
theorem admission45_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (166015707975581593960534088027351349481979/19482804249482899838787680993476608000000000:ℝ) admission45_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission45_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_09_coefficients]
def admission45_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(131528830815434065906136896629648583696384/27667358254687412109375:ℝ),(2921707932127658662729740443951726747648/204943394479166015625:ℝ),(43808294797247726942884164184942221197312/3074150917187490234375:ℝ),(131372913153669277650345039360645463539712/27667358254687412109375:ℝ)],
![(87610732756517975616208179342734308868096/9222452751562470703125:ℝ),(788184802002230816188015553424811609358336/27667358254687412109375:ℝ),(787873017086945353310312184378346918903808/27667358254687412109375:ℝ),(17501360890316512619303077932115882409984/1844490550312494140625:ℝ)],
![(131303342311563746915711120554525361045504/27667358254687412109375:ℝ),(393754155743919977470831862272303258271744/27667358254687412109375:ℝ),(393598288497229977120987333293441313406976/27667358254687412109375:ℝ),(131147475065113383160116591575663416180736/27667358254687412109375:ℝ)]]
theorem admission45_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (954223469780942710059146277313/422508084873237595422720000000000:ℝ) admission45_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission45_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_10_coefficients]
def admission45_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3437990606468111691657129052020488244212/2943405944443942508325509703:ℝ),(763900380479483709778028777748100612096/327045104938215834258389967:ℝ),(3437112849913022289780505066861620101120/2943405944443942508325509703:ℝ)],
![(3437130562660379182018178951579491281680/2943405944443942508325509703:ℝ),(9428509532197023452385837966983168000/4037593888126121410597407:ℝ),(3436252918372804315297086659089028612096/2943405944443942508325509703:ℝ)]]
theorem admission45_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6400519829937823704065916424783/32149841995846369370936767315968:ℝ) admission45_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission45_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_11_coefficients]
def admission45_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission45_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission45_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission45_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_12_coefficients]
def admission45_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission45_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission45_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission45_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_13_coefficients]
def admission45_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission45_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission45_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission45_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_14_coefficients]
theorem admission45_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission45_00_pos hδ hp
 · exact admission45_01_pos hδ hp
 · exact admission45_02_pos hδ hp
 · exact admission45_03_pos hδ hp
 · exact admission45_04_pos hδ hp
 · exact admission45_05_pos hδ hp
 · exact admission45_06_pos hδ hp
 · exact admission45_07_pos hδ hp
 · exact admission45_08_pos hδ hp
 · exact admission45_09_pos hδ hp
 · exact admission45_10_pos hδ hp
 · exact admission45_11_pos hδ hp
 · exact admission45_12_pos hδ hp
 · exact admission45_13_pos hδ hp
 · exact admission45_14_pos hδ hp
#print axioms admission45_all
end
end LewkoStage1Finite
