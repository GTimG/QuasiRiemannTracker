/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission42_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2404995665194709759/314793053919999:ℝ),(2404280872140789760/314793053919999:ℝ)]]
theorem admission42_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission42_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission42_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_00_coefficients]
def admission42_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1759984697712631808/314793053919999:ℝ),(1759584697712631808/314793053919999:ℝ)]]
theorem admission42_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission42_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission42_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_01_coefficients]
def admission42_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2955255721371332/1038920970033:ℝ),(2954620565254144/1038920970033:ℝ)]]
theorem admission42_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission42_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission42_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_02_coefficients]
def admission42_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1051609210665536698106937344/2833137485279991:ℝ),(77880375245221873752965120/104931017973333:ℝ),(1051160938969853893223120896/2833137485279991:ℝ)],
![(1051384409407309542143713280/2833137485279991:ℝ),(77863723532573111110737920/104931017973333:ℝ),(1050936143990164457846210560/2833137485279991:ℝ)]]
theorem admission42_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (62640675544152525535/123781665490206326784:ℝ) admission42_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission42_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_03_coefficients]
def admission42_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6733514344929122349488/115435663337:ℝ),(13462295956198542639104/115435663337:ℝ),(6728781964416221446144/115435663337:ℝ)],
![(6736204651945378413396/115435663337:ℝ),(121209080619968594157568/1038920970033:ℝ),(60583241931416554962944/1038920970033:ℝ)]]
theorem admission42_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (300799994070063/3782595816226816:ℝ) admission42_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission42_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_04_coefficients]
def admission42_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2258601294533887557270824338/65581886233333125:ℝ),(8131136655474510819298832852/118047395219999625:ℝ),(20328270758758528417584515218/590236976099998125:ℝ)],
![(451154490205245387140721638/13116377246666625:ℝ),(8120953851373322467129747412/118047395219999625:ℝ),(812112653185924367270664034/23609479043999925:ℝ)]]
theorem admission42_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (225577245102622693570360819/4807203099002169974587392000:ℝ) admission42_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission42_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_05_coefficients]
def admission42_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22655959791610369657038404102439271263113510912/32998524043161039460837289280333:ℝ),(22647104282081532492524281834114637373023780864/10999508014387013153612429760111:ℝ),(67914750478728735035454600030530970413674004480/32998524043161039460837289280333:ℝ),(22629397423914235263052648610827929557716172800/32998524043161039460837289280333:ℝ)],
![(22664316760648389351662711201815371258905968640/32998524043161039460837289280333:ℝ),(22655460136303834727062486734598140142984478720/10999508014387013153612429760111:ℝ),(67939814697503347563974677760440963562806968320/32998524043161039460837289280333:ℝ),(22637751049059924757012501170713914392759500800/32998524043161039460837289280333:ℝ)]]
theorem admission42_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20581317061363947926158879100355925/180215939307716823508786049189658624:ℝ) admission42_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission42_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_06_coefficients]
def admission42_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(524424851781527356351669725907539486896/2943405944443942508325509703:ℝ),(1048581225667274405790290716144643964928/2943405944443942508325509703:ℝ),(524156390631274135143844234844270755840/2943405944443942508325509703:ℝ)],
![(524169051717252946208106805219559172500/2943405944443942508325509703:ℝ),(1048069691049544965797119365567431680000/2943405944443942508325509703:ℝ),(523900656073733058667748791366451200000/2943405944443942508325509703:ℝ)]]
theorem admission42_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (31226912502868953863844203434375/128599367983385477483747069263872:ℝ) admission42_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission42_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_07_coefficients]
def admission42_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(19860510827585524983410316342280470009380977848983257911347/1344057438100577769372452256958007812500000000:ℝ),(536854769197720064353866866209049463236009619214448305865701/12096516942905199924352070312622070312500000000:ℝ),(193491261805766551226176035556957876880393452048167255413551/4354746099445871972766745312543945312500000000:ℝ),(1614289999290253718143290412726919829441592868735052242116573/108868652486146799319168632813598632812500000000:ℝ)],
![(40106522080521291004035933318278783625576491286265280669911/2688114876201155538744904513916015625000000000:ℝ),(1084116019847857547791475724907202800027439283792046493773067/24193033885810399848704140625244140625000000000:ℝ),(4884101577695079375962124552501576611506341158613829495189399/108868652486146799319168632813598632812500000000:ℝ),(1629893632531953935583196835268747020202904843219658085654493/108868652486146799319168632813598632812500000000:ℝ)]]
theorem admission42_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (19860510827585524983410316342280470009380977848983257911347/8070795436525740713622372893003744280576000000000000000000000:ℝ) admission42_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission42_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_08_coefficients]
def admission42_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(448566216546135864455819017701513213869718048064336/8709492198891743945533490625087890625:ℝ),(89655640067598947219042048004898918391639669706368/580632813259449596368899375005859375:ℝ),(1343970612322530882864949639508215452647436980322304/8709492198891743945533490625087890625:ℝ),(89540445572384748043298810556688753072209840308224/1741898439778348789106698125017578125:ℝ)],
![(89438798798351527786969047276860010729558940296572/1741898439778348789106698125017578125:ℝ),(89381245727498193866172915746770918501951688937056/580632813259449596368899375005859375:ℝ),(267971089938273549559867789240246440366587188084736/1741898439778348789106698125017578125:ℝ),(17853230311115805080220671083290236863590095126528/348379687955669757821339625003515625:ℝ)]]
theorem admission42_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (66508465674205888361560818118193137882613/7793121699793159935515072397390643200000000:ℝ) admission42_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission42_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_09_coefficients]
def admission42_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4129239325137855044886528381670933725184/27667358254687412109375:ℝ),(4125987643967866473238919203308171624448/9222452751562470703125:ℝ),(4122736127601604293035826580572929523712/9222452751562470703125:ℝ),(4119484776098929792527250513465207422976/27667358254687412109375:ℝ)],
![(1648878694041205753678692550012219654144/5533471650937482421875:ℝ),(1647578441390858269827551684653665124352/1844490550312494140625:ℝ),(987766952767396596646380838199530356736/1106694330187496484375:ℝ),(182775348192173691978104631894319562752/614830183437498046875:ℝ)],
![(164606040056987578204340121377842745344/1106694330187496484375:ℝ),(2030568602415941757265701562723397632/4554297655092578125:ℝ),(98607648069964234326935197001592602624/221338866037499296875:ℝ),(164216110022130311464075626644020133888/1106694330187496484375:ℝ)]]
theorem admission42_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (152938170379149086274277071137/67601293579718015267635200000000:ℝ) admission42_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission42_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_10_coefficients]
def admission42_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(430073620483206074720105320687731545936/2943405944443942508325509703:ℝ),(859927693568157268481757416796861890560/2943405944443942508325509703:ℝ),(429854089124182279843417735300850384896/2943405944443942508325509703:ℝ)],
![(429858581462280717066792179204674729580/2943405944443942508325509703:ℝ),(859497671666404610116975059782069616640/2943405944443942508325509703:ℝ),(429639106239127786222563133357702512640/2943405944443942508325509703:ℝ)]]
theorem admission42_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12804243154499762839751336972645/64299683991692738741873534631936:ℝ) admission42_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission42_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_11_coefficients]
def admission42_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission42_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission42_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission42_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_12_coefficients]
def admission42_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission42_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission42_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission42_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_13_coefficients]
def admission42_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission42_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission42_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission42_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_14_coefficients]
theorem admission42_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission42_00_pos hδ hp
 · exact admission42_01_pos hδ hp
 · exact admission42_02_pos hδ hp
 · exact admission42_03_pos hδ hp
 · exact admission42_04_pos hδ hp
 · exact admission42_05_pos hδ hp
 · exact admission42_06_pos hδ hp
 · exact admission42_07_pos hδ hp
 · exact admission42_08_pos hδ hp
 · exact admission42_09_pos hδ hp
 · exact admission42_10_pos hδ hp
 · exact admission42_11_pos hδ hp
 · exact admission42_12_pos hδ hp
 · exact admission42_13_pos hδ hp
 · exact admission42_14_pos hδ hp
#print axioms admission42_all
end
end LewkoStage1Finite
