/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission48_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8427618923146631/34977005991111:ℝ),(75133777254399680/314793053919999:ℝ)]]
theorem admission48_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission48_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission48_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_00_coefficients]
def admission48_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6154113533724416/34977005991111:ℝ),(54987021803519744/314793053919999:ℝ)]]
theorem admission48_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission48_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission48_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_01_coefficients]
def admission48_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10329672086820/115435663337:ℝ),(92331892664192/1038920970033:ℝ)]]
theorem admission48_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission48_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission48_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_02_coefficients]
def admission48_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3617200822837505319680/314793053919999:ℝ),(64670859373449711811328/2833137485279991:ℝ),(32116617167912163934208/2833137485279991:ℝ)],
![(399198621498528584192/34977005991111:ℝ),(64231610361940015018496/2833137485279991:ℝ),(31897090820559199698944/2833137485279991:ℝ)]]
theorem admission48_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (973421961076635733/1934088523284473856:ℝ) admission48_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission48_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_03_coefficients]
def admission48_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1897357746117567284/1038920970033:ℝ),(3752759741586771200/1038920970033:ℝ),(1855501714979602432/1038920970033:ℝ)],
![(1921261309564046072/1038920970033:ℝ),(1266766544799721984/346306990011:ℝ),(626379559833878528/346306990011:ℝ)]]
theorem admission48_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (113250837095923/1418473431085056:ℝ) admission48_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission48_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_04_coefficients]
def admission48_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4915169314255996165304/4647535244881875:ℝ),(249889282337350582580872/118047395219999625:ℝ),(208397560451465414336084/196745658699999375:ℝ)],
![(4718166670471030415612/4647535244881875:ℝ),(1199569408420987555147544/590236976099998125:ℝ),(40022322695083497201988/39349131739999875:ℝ)]]
theorem admission48_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1179541667617757603903/25990900890332037120000:ℝ) admission48_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission48_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_05_coefficients]
def admission48_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22477353772683253754995930897204201466368/32998524043161039460837289280333:ℝ),(66611363877398934679394786787824341232128/32998524043161039460837289280333:ℝ),(65794757257170215930346764686468011458560/32998524043161039460837289280333:ℝ),(21660741496440057947779821595847871692800/32998524043161039460837289280333:ℝ)],
![(22735568530731239546887048446153621363712/32998524043161039460837289280333:ℝ),(67382708393512795878923848530633816005632/32998524043161039460837289280333:ℝ),(66562819459272204894464174590129849630720/32998524043161039460837289280333:ℝ),(21915673904450601586691337705649654988800/32998524043161039460837289280333:ℝ)]]
theorem admission48_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2582161604933745616409757327538475/22526992413464602938598256148707328:ℝ) admission48_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission48_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_06_coefficients]
def admission48_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16300301931525376504904435004432596/2943405944443942508325509703:ℝ),(1197729221657616217018990429611776/109015034979405278086129989:ℝ),(16038907797172548088451207701790720/2943405944443942508325509703:ℝ)],
![(16048510108902322491064401721377464/2943405944443942508325509703:ℝ),(3537462274370055870722148931415552/327045104938215834258389967:ℝ),(15789167018323840592264251180482560/2943405944443942508325509703:ℝ)]]
theorem admission48_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (481847138010371111824470556045/2009365124740398085683547957248:ℝ) admission48_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission48_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_07_coefficients]
def admission48_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12722180886679686241718179229618617193788318052951749/863983354096769192935308140625000000000000000:ℝ),(1002739937460510564548801835314233658409151151067550529/21945177194057937500556826771875000000000000000:ℝ),(657874558625012287849903078684478398585502381945651700913/13935187518226790312853585000140625000000000000000:ℝ),(226330316690496952740830232235776942840432598518815874619/13935187518226790312853585000140625000000000000000:ℝ)],
![(16572260553935030135107397037353268197788422924142423/863983354096769192935308140625000000000000000:ℝ),(6471517955777359866591482105370883694738742091812082867/109725885970289687502784133859375000000000000000:ℝ),(841871238903054584474355961865030441890743827415948834481/13935187518226790312853585000140625000000000000000:ℝ),(287282009040888427115464695289789406751807498849307450939/13935187518226790312853585000140625000000000000000:ℝ)]]
theorem admission48_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (12722180886679686241718179229618617193788318052951749/4947707000178681737223283610222592000000000000000000000:ℝ) admission48_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission48_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_08_coefficients]
def admission48_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(460118099633959397006507450560615519673317721/8709492198891743945533490625087890625:ℝ),(1354335649761983196547557955207756406553409229/8709492198891743945533490625087890625:ℝ),(1328373085917552425967304453166583297706642688/8709492198891743945533490625087890625:ℝ),(86831152596298430037854970767970448704372736/1741898439778348789106698125017578125:ℝ)],
![(417526555344080901557583668996835765412716614/8709492198891743945533490625087890625:ℝ),(1227301470855628913535417747814498280147670206/8709492198891743945533490625087890625:ℝ),(1202076504418550549787630819957520940119096832/8709492198891743945533490625087890625:ℝ),(78460363509209726357573747005837613186203648/1741898439778348789106698125017578125:ℝ)]]
theorem admission48_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (4788840546216413962254257019399268382947/608837632796340619962115031046144000000000:ℝ) admission48_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission48_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_09_coefficients]
def admission48_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14929230871900451313615761940608/3074150917187490234375:ℝ),(393878656126182857000520674803328/27667358254687412109375:ℝ),(76936507770568182446389029442048/5533471650937482421875:ℝ),(41722339833425914017988776624128/9222452751562470703125:ℝ)],
![(50996950077658887899751477489152/5533471650937482421875:ℝ),(248909570011460001111048694876672/9222452751562470703125:ℝ),(242843784258757978447178122307584/9222452751562470703125:ℝ),(236787511733875871507145669738496/27667358254687412109375:ℝ)],
![(120524172102348554980874545971712/27667358254687412109375:ℝ),(352559172208219072379692126693888/27667358254687412109375:ℝ),(68711909312568632412591427094528/5533471650937482421875:ℝ),(111524606136535144664139554750464/27667358254687412109375:ℝ)]]
theorem admission48_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (850865220157891423524013937/412605551634021089280000000000:ℝ) admission48_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission48_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_10_coefficients]
def admission48_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13367962602939469022952366595172396/2943405944443942508325509703:ℝ),(327427826291451593916874776951808/36338344993135092695376663:ℝ),(13154189910643981773624207946416128/2943405944443942508325509703:ℝ)],
![(13156260038195808114914097707135816/2943405944443942508325509703:ℝ),(2900001263152310961999908583041024/327045104938215834258389967:ℝ),(12944245686957952847008385736310784/2943405944443942508325509703:ℝ)]]
theorem admission48_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (197513514510466809799322292119/1004682562370199042841773978624:ℝ) admission48_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission48_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_11_coefficients]
def admission48_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission48_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission48_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission48_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_12_coefficients]
def admission48_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission48_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission48_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission48_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_13_coefficients]
def admission48_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission48_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission48_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission48_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_14_coefficients]
theorem admission48_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission48_00_pos hδ hp
 · exact admission48_01_pos hδ hp
 · exact admission48_02_pos hδ hp
 · exact admission48_03_pos hδ hp
 · exact admission48_04_pos hδ hp
 · exact admission48_05_pos hδ hp
 · exact admission48_06_pos hδ hp
 · exact admission48_07_pos hδ hp
 · exact admission48_08_pos hδ hp
 · exact admission48_09_pos hδ hp
 · exact admission48_10_pos hδ hp
 · exact admission48_11_pos hδ hp
 · exact admission48_12_pos hδ hp
 · exact admission48_13_pos hδ hp
 · exact admission48_14_pos hδ hp
#print axioms admission48_all
end
end LewkoStage1Finite
