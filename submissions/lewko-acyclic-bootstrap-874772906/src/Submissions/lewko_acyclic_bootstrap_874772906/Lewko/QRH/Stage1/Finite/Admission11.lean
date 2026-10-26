/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission11_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6499412455839973/104931017973333:ℝ),(18783444313599920/314793053919999:ℝ)]]
theorem admission11_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission11_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission11_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_00_coefficients]
def admission11_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4715585150293312/104931017973333:ℝ),(13746755450879936/314793053919999:ℝ)]]
theorem admission11_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission11_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission11_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_01_coefficients]
def admission11_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7906043094412/346306990011:ℝ),(23082973166048/1038920970033:ℝ)]]
theorem admission11_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission11_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission11_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_02_coefficients]
def admission11_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(181030751270317307776/944379161759997:ℝ),(1058497993769139749504/2833137485279991:ℝ),(515542539958187826176/2833137485279991:ℝ)],
![(176442125966816526016/944379161759997:ℝ),(1031008121149077139520/2833137485279991:ℝ),(501822143248627561472/2833137485279991:ℝ)]]
theorem admission11_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (490060686766237853/967044261642236928:ℝ) admission11_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission11_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_03_coefficients]
def admission11_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30619687101487768/1038920970033:ℝ),(58664446538948992/1038920970033:ℝ),(28068895369914368/1038920970033:ℝ)],
![(32164123482314140/1038920970033:ℝ),(61685558046285248/1038920970033:ℝ),(29546205652541440/1038920970033:ℝ)]]
theorem admission11_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (13705515317341/177309178885632:ℝ) admission11_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission11_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_04_coefficients]
def admission11_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2265252371379652935604/118047395219999625:ℝ),(22673975365462078858064/590236976099998125:ℝ),(3780374477312957248348/196745658699999375:ℝ)],
![(1946428604690150746876/118047395219999625:ℝ),(19526414897074658785772/590236976099998125:ℝ),(3262502791309961727964/196745658699999375:ℝ)]]
theorem admission11_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (486607151172537686719/10315138790850527232000:ℝ) admission11_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission11_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_05_coefficients]
def admission11_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(94814012523002171493105633904415243008/32998524043161039460837289280333:ℝ),(271498785984237511338263141534316206848/32998524043161039460837289280333:ℝ),(258808839606383218562011961228898672640/32998524043161039460837289280333:ℝ),(82122697173491011134769653598997708800/32998524043161039460837289280333:ℝ)],
![(99005762538512758387674087733885704064/32998524043161039460837289280333:ℝ),(283861198853905047342295722186122913664/32998524043161039460837289280333:ℝ),(7323320469223644043173462899105075200/891852001166514580022629440009:ℝ),(86106016048655755492762092814650572800/32998524043161039460837289280333:ℝ)]]
theorem admission11_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (313273228353466076411322225948325/2815874051683075367324782018588416:ℝ) admission11_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission11_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_06_coefficients]
def admission11_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(283296287743291439359431355751768/2943405944443942508325509703:ℝ),(183125909069433976508485082505344/981135314814647502775169901:ℝ),(266216733008865282393734902922240/2943405944443942508325509703:ℝ)],
![(267171663586690726174285942044284/2943405944443942508325509703:ℝ),(172549463473427828280737879604032/981135314814647502775169901:ℝ),(250607934330821063882050120340480/2943405944443942508325509703:ℝ)]]
theorem admission11_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (244734310869942445197314570645/1004682562370199042841773978624:ℝ) admission11_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission11_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_07_coefficients]
def admission11_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2942739109068516600552230694384022505305930244027171/1114815001458143225028286800011250000000000000000:ℝ),(1068705763412573117981669259515885557922795599096209173/27870375036453580625707170000281250000000000000000:ℝ),(1912154731320775077455855641819613537422313764569981503/27870375036453580625707170000281250000000000000000:ℝ),(183361164548089042404005143028444418726860784314890321/5574075007290716125141434000056250000000000000000:ℝ)],
![(106166656587681578696563312460811036491409404642077081/1393518751822679031285358500014062500000000000000:ℝ),(3535323011836952218777183027353398787609458008172797807/13935187518226790312853585000140625000000000000000:ℝ),(7769076292528459987646523305447613475503303730406367359/27870375036453580625707170000281250000000000000000:ℝ),(564309241738035757245470537116022318172953911380462673/5574075007290716125141434000056250000000000000000:ℝ)]]
theorem admission11_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2942739109068516600552230694384022505305930244027171/24937989439338111793648231671650058240000000000000000000:ℝ) admission11_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission11_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_08_coefficients]
def admission11_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1126581259946745444278463111932095509837143/3483796879556697578213396250035156250:ℝ),(15956931756073616445718982424866817022895779/17418984397783487891066981250175781250:ℝ),(7511846585607535126920793317879021978594272/8709492198891743945533490625087890625:ℝ),(469977769315051737339765100845710120222848/1741898439778348789106698125017578125:ℝ)],
![(338535868342921503264691112663272495430303/1393518751822679031285358500014062500:ℝ),(23696023931984826846435381777073244336819639/34837968795566975782133962500351562500:ℝ),(5504021318779162640888926700062274603085296/8709492198891743945533490625087890625:ℝ),(339184189829290742335370979562384565251456/1741898439778348789106698125017578125:ℝ)]]
theorem admission11_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2649876483041333924495085777831129416027/304418816398170309981057515523072000000000:ℝ) admission11_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission11_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_09_coefficients]
def admission11_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(212588997819208927699768430336/27667358254687412109375:ℝ),(23908378828712273052953636224/1106694330187496484375:ℝ),(557925591285728340744306520192/27667358254687412109375:ℝ),(172808570449630442120234044928/27667358254687412109375:ℝ)],
![(373182581970991956444791965952/27667358254687412109375:ℝ),(1042300497215299208691964448128/27667358254687412109375:ℝ),(38622295954484949723507319936/1106694330187496484375:ℝ),(2935114548815014760797133824/273934240145419921875:ℝ)],
![(52997825720055222416537945792/9222452751562470703125:ℝ),(146631304841908359581891667872/9222452751562470703125:ℝ),(134345526646337107629196998368/9222452751562470703125:ℝ),(40713259571358970463843276288/9222452751562470703125:ℝ)]]
theorem admission11_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (79518085100310489187193899/34383795969501757440000000000:ℝ) admission11_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission11_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_10_coefficients]
def admission11_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(232663453671995460949224390426152/2943405944443942508325509703:ℝ),(150396418340359943338382620026368/981135314814647502775169901:ℝ),(218655731334189023126367137294336/2943405944443942508325509703:ℝ)],
![(219099184032528618640315273500740/2943405944443942508325509703:ℝ),(141502566198048521726387089145600/981135314814647502775169901:ℝ),(205534217353812215212878249162752/2943405944443942508325509703:ℝ)]]
theorem admission11_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (100358504567291120709413207599/502341281185099521420886989312:ℝ) admission11_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission11_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_11_coefficients]
def admission11_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission11_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission11_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission11_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_12_coefficients]
def admission11_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission11_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission11_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission11_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_13_coefficients]
def admission11_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission11_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission11_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission11_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_14_coefficients]
theorem admission11_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission11_00_pos hδ hp
 · exact admission11_01_pos hδ hp
 · exact admission11_02_pos hδ hp
 · exact admission11_03_pos hδ hp
 · exact admission11_04_pos hδ hp
 · exact admission11_05_pos hδ hp
 · exact admission11_06_pos hδ hp
 · exact admission11_07_pos hδ hp
 · exact admission11_08_pos hδ hp
 · exact admission11_09_pos hδ hp
 · exact admission11_10_pos hδ hp
 · exact admission11_11_pos hδ hp
 · exact admission11_12_pos hδ hp
 · exact admission11_13_pos hδ hp
 · exact admission11_14_pos hδ hp
#print axioms admission11_all
end
end LewkoStage1Finite
