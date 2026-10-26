/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission29_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19140788478132169/157396201727529:ℝ),(18783392276404640/157396201727529:ℝ)]]
theorem admission29_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission29_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission29_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_00_coefficients]
def admission29_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13946713821123712/157396201727529:ℝ),(13746713821123712/157396201727529:ℝ)]]
theorem admission29_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission29_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission29_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_01_coefficients]
def admission29_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363448735396138/52465400575843:ℝ),(2331373351478144/52465400575843:ℝ)]]
theorem admission29_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission29_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission29_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_02_coefficients]
def admission29_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1031028140187607221248/1416565815547761:ℝ),(226066396283787858944/157396201727529:ℝ),(1003641426366483509248/1416565815547761:ℝ)],
![(1003540139129095560320/1416565815547761:ℝ),(219963004890297477248/157396201727529:ℝ),(976200704883581734912/1416565815547761:ℝ)]]
theorem admission29_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (238330250215718197/483521131706969088:ℝ) admission29_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission29_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_03_coefficients]
def admission29_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6238221646089084560/52465400575843:ℝ),(12205254410516413440/52465400575843:ℝ),(5968315779784048640/52465400575843:ℝ)],
![(6543385081735912890/52465400575843:ℝ),(12808801559768526208/52465400575843:ℝ),(6266731568773251072/52465400575843:ℝ)]]
theorem admission29_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (273207814626345/3357785636853952:ℝ) admission29_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission29_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_04_coefficients]
def admission29_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2165956505922476304633/32790875359901875:ℝ),(39083085277639695927394/295117878239116875:ℝ),(19586008262955860535697/295117878239116875:ℝ)],
![(1816218908075568226487/32790875359901875:ℝ),(32828312233284224633962/295117878239116875:ℝ),(16478786887688023229329/295117878239116875:ℝ)]]
theorem admission29_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (5448656724226704679461/137534899685537873920000:ℝ) admission29_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission29_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_05_coefficients]
def admission29_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(185189210013713739049239898335592714240/8249596917978249986997496465053:ℝ),(60273319265158612889059649564464353280/916621879775361109666388496117:ℝ),(529482130233104809984611583434491822080/8249596917978249986997496465053:ℝ),(172211106605019691683082635689905356800/8249596917978249986997496465053:ℝ)],
![(193362033094981312373242068946925890048/8249596917978249986997496465053:ℝ),(62974435711458991436628454364775422464/916621879775361109666388496117:ℝ),(553585951028943200394538690742186917888/8249596917978249986997496465053:ℝ),(180177693459037964955161870406134005760/8249596917978249986997496465053:ℝ)]]
theorem admission29_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41058327342276499672670992777325/351982801833738666111893182508928:ℝ) admission29_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission29_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_06_coefficients]
def admission29_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26118462490908323376544466622935920/74320692954759008891869337523:ℝ),(51426508594865133566965674699781120/74320692954759008891869337523:ℝ),(25311255917663558320896843188756480/74320692954759008891869337523:ℝ)],
![(24516036958011215518820052902920678/74320692954759008891869337523:ℝ),(48247706627222930775356523427303552/74320692954759008891869337523:ℝ),(23734776310335032197103960221982720/74320692954759008891869337523:ℝ)]]
theorem admission29_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (2897311561320194359998042019285/12684064930945537517545700270592:ℝ) admission29_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission29_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_07_coefficients]
def admission29_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(698002969408988274751811211894095300973770583760767/1075241506868619920310609628515625000000000000:ℝ),(58843446745522376297283880604018714332590999991691419/29031520685452737848386459969921875000000000000:ℝ),(183444611508356336209058306429926697403316852791437683/87094562056358213545159379909765625000000000000:ℝ),(63451815668046830505443585466136266448697395100985553/87094562056358213545159379909765625000000000000:ℝ)],
![(26161690675190271987767356584469598725625678975922171/21504830137372398406212192570312500000000000000:ℝ),(2153115879975856530145895308751191623208685172068868401/580630413709054756967729199398437500000000000000:ℝ),(1640417081990928816152907387220227979902220403503090463/435472810281791067725796899548828125000000000000:ℝ),(888561344858485580126629546403470558550483062942181/696756496450865708361275039278125000000000000:ℝ)]]
theorem admission29_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2094008908226964824255433635682285902921311751282301/577265888412810240798524314537164800000000000000000000:ℝ) admission29_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission29_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_08_coefficients]
def admission29_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(752733879467447315159276240260602052696276/435472810281791067725796899548828125:ℝ),(145569377042598397689148268618908784988028/29031520685452737848386459969921875:ℝ),(2109172302753953925240986577558900250650112/435472810281791067725796899548828125:ℝ),(678368420744932001680004356258862872275968/435472810281791067725796899548828125:ℝ)],
![(4818922701359160422556293652471133699112941/4354728102817910677257968995488281250:ℝ),(4601143095661057379945010560306342935131491/1451576034272636892419322998496093750:ℝ),(6576150773339069167716147997464053318374976/2177364051408955338628984497744140625:ℝ),(416782462621982056597745503564088305390592/435472810281791067725796899548828125:ℝ)]]
theorem admission29_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (407014123654279352146235843324304985733/76104389585673225105274201623552000000000:ℝ) admission29_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission29_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_09_coefficients]
def admission29_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(561808186251123727071441379328/13833650542458603515625:ℝ),(59925053228623616920577646592/512357427498466796875:ℝ),(1550716126289066281896868777984/13833650542458603515625:ℝ),(164849929289117450704237899776/4611216847486201171875:ℝ)],
![(896546624971963507020306359296/13833650542458603515625:ℝ),(853736099944472916929344992256/4611216847486201171875:ℝ),(811034732703760059587583625216/4611216847486201171875:ℝ),(768446443874824934995022258176/13833650542458603515625:ℝ)],
![(65708625008957374583600171584/2766730108491720703125:ℝ),(308283231136791696084561546304/4611216847486201171875:ℝ),(864208353267445352743781704064/13833650542458603515625:ℝ),(267903794222169637408097923072/13833650542458603515625:ℝ)]]
theorem admission29_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (65406199761271884132836407/51575587382076702720000000000:ℝ) admission29_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission29_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_10_coefficients]
def admission29_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21418442671860095079393909266438800/74320692954759008891869337523:ℝ),(42174215524183339460717767846922240/74320692954759008891869337523:ℝ),(2306537789842092874716791870812160/8257854772751000987985481947:ℝ)],
![(20070924678817121237169058152839578/74320692954759008891869337523:ℝ),(39501538637648239869579613886691584/74320692954759008891869337523:ℝ),(719762017724703704357258126110720/2752618257583666995995160649:ℝ)]]
theorem admission29_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (527169446575710720964788666585/2818681095765675003899044504576:ℝ) admission29_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission29_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_11_coefficients]
def admission29_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission29_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission29_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission29_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_12_coefficients]
def admission29_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission29_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission29_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission29_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_13_coefficients]
def admission29_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission29_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission29_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission29_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_14_coefficients]
theorem admission29_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission29_00_pos hδ hp
 · exact admission29_01_pos hδ hp
 · exact admission29_02_pos hδ hp
 · exact admission29_03_pos hδ hp
 · exact admission29_04_pos hδ hp
 · exact admission29_05_pos hδ hp
 · exact admission29_06_pos hδ hp
 · exact admission29_07_pos hδ hp
 · exact admission29_08_pos hδ hp
 · exact admission29_09_pos hδ hp
 · exact admission29_10_pos hδ hp
 · exact admission29_11_pos hδ hp
 · exact admission29_12_pos hδ hp
 · exact admission29_13_pos hδ hp
 · exact admission29_14_pos hδ hp
#print axioms admission29_all
end
end LewkoStage2Finite
