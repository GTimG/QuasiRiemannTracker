/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6499412455839973/104931017973333:ℝ),(18783444313599920/314793053919999:ℝ)]]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission28_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission28_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]
def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4715585150293312/104931017973333:ℝ),(13746755450879936/314793053919999:ℝ)]]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission28_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission28_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]
def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7906043094412/346306990011:ℝ),(23082973166048/1038920970033:ℝ)]]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission28_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission28_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]
def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(176426966233169165824/944379161759997:ℝ),(1030959041948135058944/2833137485279991:ℝ),(501822143248627561472/2833137485279991:ℝ)],
![(171838340929668384064/944379161759997:ℝ),(1003469169328072448960/2833137485279991:ℝ),(488101746539067296768/2833137485279991:ℝ)]]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (476661861854557907/967044261642236928:ℝ) admission28_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission28_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]
def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32231249580513440/1038920970033:ℝ),(61752048988367360/1038920970033:ℝ),(29546205652541440/1038920970033:ℝ)],
![(265950283160156/8180480079:ℝ),(21591053498567872/346306990011:ℝ),(10341171978389504/346306990011:ℝ)]]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (3606714557195/44327294721408:ℝ) admission28_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission28_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]
def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1946428604690150746876/118047395219999625:ℝ),(3913418419116452120152/118047395219999625:ℝ),(655200809957893971092/39349131739999875:ℝ)],
![(1627604838000648558148/118047395219999625:ℝ),(16419531627194840528468/590236976099998125:ℝ),(2758132363786474335076/196745658699999375:ℝ)]]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (406901209500162139537/10315138790850527232000:ℝ) admission28_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission28_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]
def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(99214193678858600924250102347703301120/32998524043161039460837289280333:ℝ),(284273655098078350272350985190971028480/32998524043161039460837289280333:ℝ),(271166918490672207558846975657918300160/32998524043161039460837289280333:ℝ),(86106016048655755492762092814650572800/32998524043161039460837289280333:ℝ)],
![(103405943694369187818818556177173762176/32998524043161039460837289280333:ℝ),(296636067967745886276383565842777735296/32998524043161039460837289280333:ℝ),(283320936245563818594253141695907409920/32998524043161039460837289280333:ℝ),(90089334923820499850754532030303436800/32998524043161039460837289280333:ℝ)]]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82117095993667369358789532484675/703968512920768841831195504647104:ℝ) admission28_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission28_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]
def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(266655838108134231500825310918560/2943405944443942508325509703:ℝ),(172378883662784492394113865090560/981135314814647502775169901:ℝ),(250607934330821063882050120340480/2943405944443942508325509703:ℝ)],
![(250531213951533518315679897211076/2943405944443942508325509703:ℝ),(161802438066778344166366662189248/981135314814647502775169901:ℝ),(234999135652776845370365337758720/2943405944443942508325509703:ℝ)]]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (229491343410914888056997400155/1004682562370199042841773978624:ℝ) admission28_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission28_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]
def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(106166656587681578696563312460811036491409404642077081/1393518751822679031285358500014062500000000000000:ℝ),(346164616092723989018734070216392454546420846168619751/1393518751822679031285358500014062500000000000000:ℝ),(373835194582769446054240476175287645599883709301008309/1393518751822679031285358500014062500000000000000:ℝ),(133826097030649685075860958708069046044984767774465639/1393518751822679031285358500014062500000000000000:ℝ)],
![(834619557156110046569745346214568179404745585916480793/5574075007290716125141434000056250000000000000000:ℝ),(12925232582115811099947378199518761108224537340621781461/27870375036453580625707170000281250000000000000000:ℝ),(3333406363215768457818869296783438212519666037964138009/6967593759113395156426792500070312500000000000000:ℝ),(229063116328136363786227307229963520906508049540858727/1393518751822679031285358500014062500000000000000:ℝ)]]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (106166656587681578696563312460811036491409404642077081/31172486799172639742060289589562572800000000000000000000:ℝ) admission28_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission28_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]
def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(413842620369692031026890346975459038628578/1741898439778348789106698125017578125:ℝ),(1166289956048404025084822299070619396306562/1741898439778348789106698125017578125:ℝ),(218323989769488203196918876059816422085888/348379687955669757821339625003515625:ℝ),(339184189829290742335370979562384565251456/1741898439778348789106698125017578125:ℝ)],
![(1094887303299884751874090727354007611991541/6967593759113395156426792500070312500:ℝ),(15107959540805674456693862908751998217159321/34837968795566975782133962500351562500:ℝ),(3450274477408832593891105283678663176638224/8709492198891743945533490625087890625:ℝ),(208390610343529747330976858279059010280064/1741898439778348789106698125017578125:ℝ)]]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1628051643308826151023256705305148517813/304418816398170309981057515523072000000000:ℝ) admission28_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission28_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]
def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(150297225456799070223098368/26425366050322265625:ℝ),(438174491996251552067444453888/27667358254687412109375:ℝ),(404447470923668974264136933888/27667358254687412109375:ℝ),(41212666326895349573425490432/9222452751562470703125:ℝ)],
![(256326548472641908110784294912/27667358254687412109375:ℝ),(234814030628373148563125796352/9222452751562470703125:ℝ),(213406749196156230768067297792/9222452751562470703125:ℝ),(192112545425991154725608799232/27667358254687412109375:ℝ)],
![(97365246427755920091790605376/27667358254687412109375:ℝ),(261570487917100589999484396256/27667358254687412109375:ℝ),(231177549027415638584279476384/27667358254687412109375:ℝ),(66976326178695968676585685504/27667358254687412109375:ℝ)]]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (130813137067765563821456417/103151387908505272320000000000:ℝ) admission28_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission28_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]
def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(218656428373438584244895044706912/2943405944443942508325509703:ℝ),(141356390042654972056717483685888/981135314814647502775169901:ℝ),(205534217353812215212878249162752/2943405944443942508325509703:ℝ)],
![(205092158733971741935985927781500/2943405944443942508325509703:ℝ),(132462537900343550444721952805120/981135314814647502775169901:ℝ),(192412703373435407299389361031168/2943405944443942508325509703:ℝ)]]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (93951515319060257470404961441/502341281185099521420886989312:ℝ) admission28_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission28_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]
def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission28_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission28_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]
def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission28_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission28_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]
def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission28_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission28_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]
theorem admission28_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission28_00_pos hδ hp
 · exact admission28_01_pos hδ hp
 · exact admission28_02_pos hδ hp
 · exact admission28_03_pos hδ hp
 · exact admission28_04_pos hδ hp
 · exact admission28_05_pos hδ hp
 · exact admission28_06_pos hδ hp
 · exact admission28_07_pos hδ hp
 · exact admission28_08_pos hδ hp
 · exact admission28_09_pos hδ hp
 · exact admission28_10_pos hδ hp
 · exact admission28_11_pos hδ hp
 · exact admission28_12_pos hδ hp
 · exact admission28_13_pos hδ hp
 · exact admission28_14_pos hδ hp
#print axioms admission28_all
end
end LewkoStage1Finite
