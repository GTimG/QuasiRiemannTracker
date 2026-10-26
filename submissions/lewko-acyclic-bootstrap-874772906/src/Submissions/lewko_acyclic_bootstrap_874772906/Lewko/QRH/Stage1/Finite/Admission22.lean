/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission22_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8427618923146631/34977005991111:ℝ),(75133777254399680/314793053919999:ℝ)]]
theorem admission22_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission22_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission22_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_00_coefficients]
def admission22_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6154113533724416/34977005991111:ℝ),(54987021803519744/314793053919999:ℝ)]]
theorem admission22_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission22_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission22_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_01_coefficients]
def admission22_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10329672086820/115435663337:ℝ),(92331892664192/1038920970033:ℝ)]]
theorem admission22_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission22_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission22_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_02_coefficients]
def admission22_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7197771095159790306304/314793053919999:ℝ),(128682747071232994272256/2833137485279991:ℝ),(63903944814794881515520/2833137485279991:ℝ)],
![(7173357865809042244352/314793053919999:ℝ),(128243498059723297479424/2833137485279991:ℝ),(63684418467441917280256/2833137485279991:ℝ)]]
theorem admission22_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3886988431850702959/7736354093137895424:ℝ) admission22_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission22_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_03_coefficients]
def admission22_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3818885654606058992/1038920970033:ℝ),(7553325339754265600/1038920970033:ℝ),(3734640394481238016/1038920970033:ℝ)],
![(3842789218052537780/1038920970033:ℝ),(2533621744188886784/346306990011:ℝ),(1252759119667757056/346306990011:ℝ)]]
theorem admission22_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (56986090003681/709236715542528:ℝ) admission22_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission22_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_04_coefficients]
def admission22_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1906966932566908741214/929507048976375:ℝ),(2424158152602665760505972/590236976099998125:ℝ),(404393116244283413721694/196745658699999375:ℝ)],
![(9337832019049577956378/4647535244881875:ℝ),(2374281149336900402749156/590236976099998125:ℝ),(15844286770729419415822/7869826347999975:ℝ)]]
theorem admission22_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4668916009524788978189/103963603561328148480000:ℝ) admission22_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission22_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_05_coefficients]
def admission22_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(45216204653451935454862580782505459431424/32998524043161039460837289280333:ℝ),(134000619562993960841113148731862282123264/32998524043161039460837289280333:ℝ),(132360841694512778872193800850854349373440/32998524043161039460837289280333:ℝ),(43576415400890659534471159301497526681600/32998524043161039460837289280333:ℝ)],
![(45474419411499921246753698331454879328768/32998524043161039460837289280333:ℝ),(134771964079107822040642210474671756896768/32998524043161039460837289280333:ℝ),(3598078483692291022603005696068005068800/891852001166514580022629440009:ℝ),(43831347808901203173382675411299309977600/32998524043161039460837289280333:ℝ)]]
theorem admission22_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1298678380277474508716796615764425/11263496206732301469299128074353664:ℝ) admission22_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission22_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_06_coefficients]
def admission22_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32221890607228998730222281703409008/2943405944443942508325509703:ℝ),(7102673524167745907687293031865344/327045104938215834258389967:ℝ),(31703204426072034932621980621619200/2943405944443942508325509703:ℝ)],
![(31970098784605944716382248420353876/2943405944443942508325509703:ℝ),(7046948133564953127352470674445568/327045104938215834258389967:ℝ),(31453463647223327436435024100311040/2943405944443942508325509703:ℝ)]]
theorem admission22_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1919767068311970668727723638935/8037460498961592342734191828992:ℝ) admission22_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission22_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_07_coefficients]
def admission22_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7323610360153679094206394066742971347894185244273543/215995838524192298233827035156250000000000000:ℝ),(573807777916521685490083611299743267847672211385025947/5486294298514484375139206692968750000000000000:ℝ),(374362168236656210994821960416801081412733645107398631531/3483796879556697578213396250035156250000000000000:ℝ),(128116520782153853143613674139656656865024326557795130233/3483796879556697578213396250035156250000000000000:ℝ)],
![(16572260553935030135107397037353268197788422924142423/431991677048384596467654070312500000000000000:ℝ),(6466986913402620376824572577397290379823215282087424581/54862942985144843751392066929687500000000000000:ℝ),(420361338306166785150935181211939092239044006474972914923/3483796879556697578213396250035156250000000000000:ℝ),(143354443869751721737272289903159772842868051640418024313/3483796879556697578213396250035156250000000000000:ℝ)]]
theorem admission22_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7323610360153679094206394066742971347894185244273543/2473853500089340868611641805111296000000000000000000000:ℝ) admission22_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission22_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_08_coefficients]
def admission22_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(855980083405883562315870397399003619620855948/8709492198891743945533490625087890625:ℝ),(2517383859864423104672944673844992826681608572/8709492198891743945533490625087890625:ℝ),(2466933926990266377177370818131038146624461824/8709492198891743945533490625087890625:ℝ),(32221224312392760911057621178548328826298368/348379687955669757821339625003515625:ℝ)],
![(813388539116005066866946615835223865360254841/8709492198891743945533490625087890625:ℝ),(2390349680958068821660804466451734700275869549/8709492198891743945533490625087890625:ℝ),(2340637345491264500997697184921975789036915968/8709492198891743945533490625087890625:ℝ),(152735332474875100875006882130608808613322752/1741898439778348789106698125017578125:ℝ)]]
theorem admission22_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (18644449764999401962281113541334083082681/2435350531185362479848460124184576000000000:ℝ) admission22_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission22_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_09_coefficients]
def admission22_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33058862061248752966458975778816/1844490550312494140625:ℝ),(1451595416360887513238927865161728/27667358254687412109375:ℝ),(1415596913779383871971987900276736/27667358254687412109375:ℝ),(51098296339497517025549407977472/3074150917187490234375:ℝ)],
![(963893049470267929919752682359808/27667358254687412109375:ℝ),(313330011276210145481148007537664/3074150917187490234375:ℝ),(101791455861392315611582800318464/1024716972395830078125:ℝ),(178458547037868828420431244623872/5533471650937482421875:ℝ)],
![(467912618112694812727527061668992/27667358254687412109375:ℝ),(1368083803425025722138470919544448/27667358254687412109375:ℝ),(266496625423523757698823124816384/5533471650937482421875:ℝ),(432312182036803504083171766206464/27667358254687412109375:ℝ)]]
theorem admission22_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (13193120789697372561131950873/6601688826144337428480000000000:ℝ) admission22_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission22_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_10_coefficients]
def admission22_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26417492188234630693136106519324304/2943405944443942508325509703:ℝ),(5823329662269736249179352967204864/327045104938215834258389967:ℝ),(25993463485758920157324682577674240/2943405944443942508325509703:ℝ)],
![(26205789623490969785097837631287724/2943405944443942508325509703:ℝ),(5776480488798982865927388557679616/327045104938215834258389967:ℝ),(25783519262072891230708860367568896/2943405944443942508325509703:ℝ)]]
theorem admission22_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (786850563417751807577785045397/4018730249480796171367095914496:ℝ) admission22_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission22_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_11_coefficients]
def admission22_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission22_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission22_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission22_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_12_coefficients]
def admission22_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission22_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission22_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission22_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_13_coefficients]
def admission22_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission22_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission22_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission22_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_14_coefficients]
theorem admission22_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission22_00_pos hδ hp
 · exact admission22_01_pos hδ hp
 · exact admission22_02_pos hδ hp
 · exact admission22_03_pos hδ hp
 · exact admission22_04_pos hδ hp
 · exact admission22_05_pos hδ hp
 · exact admission22_06_pos hδ hp
 · exact admission22_07_pos hδ hp
 · exact admission22_08_pos hδ hp
 · exact admission22_09_pos hδ hp
 · exact admission22_10_pos hδ hp
 · exact admission22_11_pos hδ hp
 · exact admission22_12_pos hδ hp
 · exact admission22_13_pos hδ hp
 · exact admission22_14_pos hδ hp
#print axioms admission22_all
end
end LewkoStage1Finite
