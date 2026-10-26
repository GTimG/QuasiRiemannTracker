/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission13_00_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission13_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]
def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission13_01_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission13_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]
def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission13_02_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission13_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]
def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1839138513385722419200/157396201727529:ℝ),(32884643057164255664128/1416565815547761:ℝ),(16332670036692753891328/1416565815547761:ℝ)],
![(608977310199580551936/52465400575843:ℝ),(32665019126149821696256/1416565815547761:ℝ),(16222907150761146793984/1416565815547761:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (990167672775948901/1934084526827876352:ℝ) admission13_03_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission13_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]
def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(92764808978280277232/52465400575843:ℝ),(183478333372642281472/52465400575843:ℝ),(90718399852717539328/52465400575843:ℝ)],
![(93971935352168420762/52465400575843:ℝ),(185879090827103316736/52465400575843:ℝ),(91912063008674349056/52465400575843:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1038189695580111/13431142547415808:ℝ) admission13_04_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission13_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]
def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(343386513170341264580653/295117878239116875:ℝ),(137373110386448350632434/59023575647823375:ℝ),(114488619536216867903839/98372626079705625:ℝ)],
![(330876880370095783277539/295117878239116875:ℝ),(661927120342459461349834/295117878239116875:ℝ),(22069131540505283632403/19674525215941125:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (330876880370095783277539/6601675184905817948160000:ℝ) admission13_05_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission13_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]
def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5455873830299026620107397318375540711424/8249596917978249986997496465053:ℝ),(16166572764600363801252291301438969274368/8249596917978249986997496465053:ℝ),(15966524935303793667424084414221083213824/8249596917978249986997496465053:ℝ),(5255824632032045389152108831157654650880/8249596917978249986997496465053:ℝ)],
![(5520427109046854264041525074213597254656/8249596917978249986997496465053:ℝ),(16359407664941233816380713625372720796672/8249596917978249986997496465053:ℝ),(16158539260735366508328743660046607384576/8249596917978249986997496465053:ℝ),(5319557326864191575328742708887483842560/8249596917978249986997496465053:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (156635780097009104166987801526715/1407931207334954664447572730035712:ℝ) admission13_06_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission13_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]
def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(427604013515463180519196096451003920/74320692954759008891869337523:ℝ),(848335239635870932850306713376708608/74320692954759008891869337523:ℝ),(420744890755902194372278320687841280/74320692954759008891869337523:ℝ)],
![(421246306407595343746069648491737350/74320692954759008891869337523:ℝ),(835671717271272422771916878964658432/74320692954759008891869337523:ℝ),(414438972326588089877106788820746240/74320692954759008891869337523:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12647673716021365047519128076805/50736259723782150070182801082368:ℝ) admission13_07_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission13_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]
def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(780246602547641779927099342367380827391544276354621677/217736405140895533862898449774414062500000000000:ℝ),(552229953705148069950103870451062920368103467660889911/43547281028179106772579689954882812500000000000:ℝ),(3180931281557997586195194883891565343734533546257889081/217736405140895533862898449774414062500000000000:ℝ),(1200021502384129959238506894509649499596202671808061203/217736405140895533862898449774414062500000000000:ℝ)],
![(7002094468203539079283417562996715388472962846209348211/870945620563582135451593799097656250000000000000:ℝ),(22615993251248197513086763809656319562324533252297358987/870945620563582135451593799097656250000000000000:ℝ),(6055869903634207866721979829061680930609195458353305337/217736405140895533862898449774414062500000000000:ℝ),(2152388551169407299446209051195600566998462427143802643/217736405140895533862898449774414062500000000000:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (780246602547641779927099342367380827391544276354621677/1246894318971670120124812519400275968000000000000000000000:ℝ) admission13_08_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission13_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]
def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(380992203979379084910853134458532985338152/5837437135144652382383336455078125:ℝ),(418900080372663330679758477381228163084580504/2177364051408955338628984497744140625:ℝ),(411487476430751418979314494712354021274892288/2177364051408955338628984497744140625:ℝ),(26939508626296822955405316454179103250538496/435472810281791067725796899548828125:ℝ)],
![(131462254871901998366561301318202394876498459/2177364051408955338628984497744140625:ℝ),(387141681397845442979798363627145845395707161/2177364051408955338628984497744140625:ℝ),(379913475981651620440423823989345755522267392/2177364051408955338628984497744140625:ℝ),(24846820961313223394747245632620906715455488/435472810281791067725796899548828125:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3033059199379055590179107132888294276789/304417558342692900421096806494208000000000:ℝ) admission13_09_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission13_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]
def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83742367368378809215279003328512/13833650542458603515625:ℝ),(246153037870295315036783809814528/13833650542458603515625:ℝ),(48217595760562573830032905928704/2766730108491720703125:ℝ),(78677335917396363328659723157504/13833650542458603515625:ℝ)],
![(32220310743108362842044873304064/2766730108491720703125:ℝ),(473246241243286686719215616239616/13833650542458603515625:ℝ),(463205489855165223571636692918272/13833650542458603515625:ℝ),(151060857923795351062645443198976/13833650542458603515625:ℝ)],
![(8590048475988519399182159351168/1537072282495400390625:ℝ),(25216418109951118646860070364032/1537072282495400390625:ℝ),(4932730618593547664428738534912/307414456499080078125:ℝ),(8037286568012951574465781661696/1537072282495400390625:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (735835562257045127056803741/275069799371075747840000000000:ℝ) admission13_10_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission13_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]
def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(117004611144982655716627684113613648/24773564318253002963956445841:ℝ),(696394808555147652845508746348179456/74320692954759008891869337523:ℝ),(38377122004153303611918844857794560/8257854772751000987985481947:ℝ)],
![(115222790975119352620571629944897022/24773564318253002963956445841:ℝ),(685748392262030110244011808698438144/74320692954759008891869337523:ℝ),(37788115057481376565338774887874560/8257854772751000987985481947:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2306403506926353550130540459465/11274724383062700015596178018304:ℝ) admission13_11_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission13_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]
def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission13_12_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission13_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]
def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission13_13_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission13_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]
def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission13_14_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission13_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]
theorem admission13_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission13_00_pos hδ hp
 · exact admission13_01_pos hδ hp
 · exact admission13_02_pos hδ hp
 · exact admission13_03_pos hδ hp
 · exact admission13_04_pos hδ hp
 · exact admission13_05_pos hδ hp
 · exact admission13_06_pos hδ hp
 · exact admission13_07_pos hδ hp
 · exact admission13_08_pos hδ hp
 · exact admission13_09_pos hδ hp
 · exact admission13_10_pos hδ hp
 · exact admission13_11_pos hδ hp
 · exact admission13_12_pos hδ hp
 · exact admission13_13_pos hδ hp
 · exact admission13_14_pos hδ hp
#print axioms admission13_all
end
end LewkoStage2Finite
