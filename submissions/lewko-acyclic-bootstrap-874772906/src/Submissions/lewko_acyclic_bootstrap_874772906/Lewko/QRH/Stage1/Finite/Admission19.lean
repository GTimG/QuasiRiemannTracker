/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission19_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6499412455839973/104931017973333:ℝ),(18783444313599920/314793053919999:ℝ)]]
theorem admission19_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission19_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission19_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_00_coefficients]
def admission19_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4715585150293312/104931017973333:ℝ),(13746755450879936/314793053919999:ℝ)]]
theorem admission19_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission19_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission19_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_01_coefficients]
def admission19_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7906043094412/346306990011:ℝ),(23082973166048/1038920970033:ℝ)]]
theorem admission19_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission19_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission19_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_02_coefficients]
def admission19_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(178728858751743236800/944379161759997:ℝ),(1044728517858637404224/2833137485279991:ℝ),(508682341603407693824/2833137485279991:ℝ)],
![(174140233448242455040/944379161759997:ℝ),(1017238645238574794240/2833137485279991:ℝ),(494961944893847429120/2833137485279991:ℝ)]]
theorem admission19_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (60420159288799735/120880532705279616:ℝ) admission19_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission19_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_03_coefficients]
def admission19_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10475156113666868/346306990011:ℝ),(20069415921219392/346306990011:ℝ),(9602516837075968/346306990011:ℝ)],
![(3663322746869664/115435663337:ℝ),(63229359270994432/1038920970033:ℝ),(30284860793854976/1038920970033:ℝ)]]
theorem admission19_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9377457848707/118206119257088:ℝ) admission19_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission19_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_04_coefficients]
def admission19_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(421168097606980368248/23609479043999925:ℝ),(21120533730522169729412/590236976099998125:ℝ),(3528189263551213551904/196745658699999375:ℝ)],
![(1787016721345399652512/118047395219999625:ℝ),(3594594652426949931424/118047395219999625:ℝ),(602063515509643606304/39349131739999875:ℝ)]]
theorem admission19_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (55844272542043739141/1289392348856315904000:ℝ) admission19_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission19_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_05_coefficients]
def admission19_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(97014103100930386208677868126059272064/32998524043161039460837289280333:ℝ),(277886220541157930805307063362643617664/32998524043161039460837289280333:ℝ),(264987879048527713060429468443408486400/32998524043161039460837289280333:ℝ),(84114356611073383313765873206824140800/32998524043161039460837289280333:ℝ)],
![(101205853116440973103246321955529733120/32998524043161039460837289280333:ℝ),(290248633410825466809339644014450324480/32998524043161039460837289280333:ℝ),(277141896803419324095835634481397596160/32998524043161039460837289280333:ℝ),(88097675486238127671758312422477004800/32998524043161039460837289280333:ℝ)]]
theorem admission19_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (641741612328135553846480355887025/5631748103366150734649564037176832:ℝ) admission19_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission19_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_06_coefficients]
def admission19_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(274976062925712835430128333335164/2943405944443942508325509703:ℝ),(177752396366109234451299473797952/981135314814647502775169901:ℝ),(258412333669843173137892511631360/2943405944443942508325509703:ℝ)],
![(258851438769112122244982919627680/2943405944443942508325509703:ℝ),(167175950770103086223552270896640/981135314814647502775169901:ℝ),(242803534991798954626207729049600/2943405944443942508325509703:ℝ)]]
theorem admission19_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (29639103392553583328394498175/125585320296274880355221747328:ℝ) admission19_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission19_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_07_coefficients]
def admission19_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(439380321896068897789014403315164258492167269788444179/11148150014581432250282868000112500000000000000000:ℝ),(7991998085267052898356350663843734648851212522468604193/55740750072907161251414340000562500000000000000000:ℝ),(9388858622976163998540665165325366449419987950590147683/55740750072907161251414340000562500000000000000000:ℝ),(718665552670687782707448977860720602906799855412752877/11148150014581432250282868000112500000000000000000:ℝ)],
![(1259286183506836361355998596057812325370383204484789117/11148150014581432250282868000112500000000000000000:ℝ),(799835144231588621500069770169022347337738134278695083/2229630002916286450056573600022500000000000000000:ℝ),(4220540349078306763784400098516273265116393576452583879/11148150014581432250282868000112500000000000000000:ℝ),(1480561707050581212390379766035876401798986109543897581/11148150014581432250282868000112500000000000000000:ℝ)]]
theorem admission19_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (439380321896068897789014403315164258492167269788444179/249379894393381117936482316716500582400000000000000000000:ℝ) admission19_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission19_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_08_coefficients]
def admission19_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1954266500686129506332243805883013587094299/6967593759113395156426792500070312500:ℝ),(27619831316557656696567205415573010985961399/34837968795566975782133962500351562500:ℝ),(6484973164922370103421882609687216265370736/8709492198891743945533490625087890625:ℝ),(404580979572171239837568040204047342737152/1741898439778348789106698125017578125:ℝ)],
![(348445830626811533524693286333796261142882/1741898439778348789106698125017578125:ℝ),(970099586819762532578231117145631063849474/1741898439778348789106698125017578125:ℝ),(895429579618799523478003198374093777972352/1741898439778348789106698125017578125:ℝ),(54757480017282048966634783784144357553152/348379687955669757821339625003515625:ℝ)]]
theorem admission19_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (53474101579377000943979281039203474173/7610470409954257749526437888076800000000:ℝ) admission19_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission19_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_09_coefficients]
def admission19_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(37165218658910313988542517568/5533471650937482421875:ℝ),(57821306992098087424996806112/3074150917187490234375:ℝ),(53726047593574336774098582944/3074150917187490234375:ℝ),(148972394848462814084628579328/27667358254687412109375:ℝ)],
![(7032367976409833731996908544/614830183437498046875:ℝ),(175654171538783304489865613824/5533471650937482421875:ℝ),(319835492158509688958920192/10957369605816796875:ℝ),(16385185179650864007453753344/1844490550312494140625:ℝ)],
![(5161214346090943460069543936/1106694330187496484375:ℝ),(111238419777406750236821504/8714128584153515625:ℝ),(12778198468827354167944030208/1106694330187496484375:ℝ),(3812286503187640347937243136/1106694330187496484375:ℝ)]]
theorem admission19_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (116341751195911875852577/64469617442815795200000000:ℝ) admission19_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission19_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_10_coefficients]
def admission19_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(225659941022717022597059717566532/2943405944443942508325509703:ℝ),(145876404191507457697550051856128/981135314814647502775169901:ℝ),(212094974344000619169622693228544/2943405944443942508325509703:ℝ)],
![(212095671383250180288150600641120/2943405944443942508325509703:ℝ),(136982552049196036085554520975360/981135314814647502775169901:ℝ),(198973460363623811256133805096960/2943405944443942508325509703:ℝ)]]
theorem admission19_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12144376242896961136238635565/62792660148137440177610873664:ℝ) admission19_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission19_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_11_coefficients]
def admission19_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission19_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission19_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission19_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_12_coefficients]
def admission19_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission19_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission19_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission19_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_13_coefficients]
def admission19_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission19_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission19_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission19_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_14_coefficients]
theorem admission19_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission19_00_pos hδ hp
 · exact admission19_01_pos hδ hp
 · exact admission19_02_pos hδ hp
 · exact admission19_03_pos hδ hp
 · exact admission19_04_pos hδ hp
 · exact admission19_05_pos hδ hp
 · exact admission19_06_pos hδ hp
 · exact admission19_07_pos hδ hp
 · exact admission19_08_pos hδ hp
 · exact admission19_09_pos hδ hp
 · exact admission19_10_pos hδ hp
 · exact admission19_11_pos hδ hp
 · exact admission19_12_pos hδ hp
 · exact admission19_13_pos hδ hp
 · exact admission19_14_pos hδ hp
#print axioms admission19_all
end
end LewkoStage1Finite
