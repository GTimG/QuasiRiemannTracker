/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission46_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(200475316348892003/52465400575843:ℝ),(601068552844948480/157396201727529:ℝ)]]
theorem admission46_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission46_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission46_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_00_coefficients]
def admission46_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(146698280758652928/52465400575843:ℝ),(439894842275958784/157396201727529:ℝ)]]
theorem admission46_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission46_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission46_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_01_coefficients]
def admission46_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74636022631218602/52465400575843:ℝ),(74603947247300608/52465400575843:ℝ)]]
theorem admission46_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission46_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission46_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_02_coefficients]
def admission46_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21915460394136654268878848/472188605182587:ℝ),(131436723298968351817953280/1416565815547761:ℝ),(65690346621958389011316736/1416565815547761:ℝ)],
![(21906093438288350624448512/472188605182587:ℝ),(131380523130824949467742208/1416565815547761:ℝ),(65662247323159897594396672/1416565815547761:ℝ)]]
theorem admission46_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1956887463425394821/3868169053655752704:ℝ) admission46_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission46_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_03_coefficients]
def admission46_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(382968547239491382913318/52465400575843:ℝ),(765399043512871964069888/52465400575843:ℝ),(382430576558066527895552/52465400575843:ℝ)],
![(383274339937772468774608/52465400575843:ℝ),(766010413947002609303552/52465400575843:ℝ),(382736154325991471185920/52465400575843:ℝ)]]
theorem admission46_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (136767832001948307/1719186246069223424:ℝ) admission46_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission46_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_04_coefficients]
def admission46_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1269637367777177821131558706/295117878239116875:ℝ),(2539383738372831341425987408/295117878239116875:ℝ),(423248717852227523295884984/98372626079705625:ℝ)],
![(1266454282432789787697339352/295117878239116875:ℝ),(2533018858426880577128763472/295117878239116875:ℝ),(84437623924560553632395608/19674525215941125:ℝ)]]
theorem admission46_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (158306785304098723462167419/3380057694671778789457920000:ℝ) admission46_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission46_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_05_coefficients]
def admission46_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(354543375951036795640449787398936624960618496/8249596917978249986997496465053:ℝ),(1062799458530335060141165556520567639225843712/8249596917978249986997496465053:ℝ),(1061969049376846083625445280565718072569102336/8249596917978249986997496465053:ℝ),(353712966775004839263044583251687058303877120/8249596917978249986997496465053:ℝ)],
![(9589314435029763615834333392681091506765824/222962078864277026675608012569:ℝ),(1063583023869134847835749493595228986122305536/8249596917978249986997496465053:ℝ),(1062752405688622890337471695604097039044968448/8249596917978249986997496465053:ℝ),(353974015893037310041624075614868438672998400/8249596917978249986997496465053:ℝ)]]
theorem admission46_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20588804430736044844556866635783055/180215194538874197049289309444571136:ℝ) admission46_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission46_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_06_coefficients]
def admission46_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1655649456320178986579229870622407355450/74320692954759008891869337523:ℝ),(3309604767477550224987058444431044964352/74320692954759008891869337523:ℝ),(1653955522466285725866003778744415682560/74320692954759008891869337523:ℝ)],
![(1654034314131006467579867301988170952240/74320692954759008891869337523:ℝ),(3306375310273645878668121871784246542336/74320692954759008891869337523:ℝ),(1652341207348381315115239866586439352320/74320692954759008891869337523:ℝ)]]
theorem admission46_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (24621802677935083435702917972005/101472519447564300140365602164736:ℝ) admission46_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission46_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_07_coefficients]
def admission46_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(101337446724383797999311734444626586358937517246758805453249/108868202570447766931449224887207031250000000000:ℝ),(60941740307768679290798485748610368251909844347027304651299/21773640514089553386289844977441406250000000000:ℝ),(305405021236699799716736220518415028464185256738283352519357/108868202570447766931449224887207031250000000000:ℝ),(102033766367790105834588405924750716204624761254495478466111/108868202570447766931449224887207031250000000000:ℝ)],
![(4131607128671277044267214032195645937095105920681079059847/4354728102817910677257968995488281250000000000:ℝ),(310564611659936475030668618148798074886681268200650586055469/108868202570447766931449224887207031250000000000:ℝ),(12450345903253150084489600536556315256301689186150617459781/4354728102817910677257968995488281250000000000:ℝ),(103984214083702353827333779941643543990664589233423076935231/108868202570447766931449224887207031250000000000:ℝ)]]
theorem admission46_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (101337446724383797999311734444626586358937517246758805453249/40858233044063686496249856635708242919424000000000000000000000:ℝ) admission46_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission46_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_08_coefficients]
def admission46_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7011588082488724361996266401391265962962163003694/2177364051408955338628984497744140625:ℝ),(21007806152420778769881047024435330439587817002096/2177364051408955338628984497744140625:ℝ),(20980851790400329142521980947350461501877057421312/2177364051408955338628984497744140625:ℝ),(1396926744274757165785858121481679671296190840832/435472810281791067725796899548828125:ℝ)],
![(6968682804219243990023106466740648471464308909712/2177364051408955338628984497744140625:ℝ),(20879137363912499404103644316304078542049052646528/2177364051408955338628984497744140625:ℝ),(20852230036782304259402120056323619265423604187136/2177364051408955338628984497744140625:ℝ),(1388355095598984341985402663396577298288490840064/435472810281791067725796899548828125:ℝ)]]
theorem admission46_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5172025768455059610252837327854995795669/608835116685385800842193612988416000000000:ℝ) admission46_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission46_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_09_coefficients]
def admission46_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4304086062228161922663042771034605568/922243369497240234375:ℝ),(193379391502826157759682524701714102272/13833650542458603515625:ℝ),(193074941001811022697437842663190953984/13833650542458603515625:ℝ),(2379882979255405086963461463962812416/512357427498466796875:ℝ)],
![(128681831366723320587160884618436050944/13833650542458603515625:ℝ),(14275441688469490173079744761861865472/512357427498466796875:ℝ),(42758713175200346590865570988172509184/1537072282495400390625:ℝ),(128073324369833476106797914941718265856/13833650542458603515625:ℝ)],
![(64120343853203354222156636433153916928/13833650542458603515625:ℝ),(192056944551602183337549195124837056512/13833650542458603515625:ℝ),(38350577649349351713451943034458472448/2766730108491720703125:ℝ),(63816287555842557951867156480609222656/13833650542458603515625:ℝ)]]
theorem admission46_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7429193653613626718505653143/3300837592452908974080000000000:ℝ) admission46_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission46_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_10_coefficients]
def admission46_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(150862812184483735695595615243653352214/8257854772751000987985481947:ℝ),(2714145236612397867919888161090883477504/74320692954759008891869337523:ℝ),(150708903260047358665666178308647157760/8257854772751000987985481947:ℝ)],
![(150711947654270735104747252586282211152/8257854772751000987985481947:ℝ),(2711430383942085262397038307818433216512/74320692954759008891869337523:ℝ),(50186039160566448447247226798782545920/2752618257583666995995160649:ℝ)]]
theorem admission46_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4486981555274109403542926323305/22549448766125400031192356036608:ℝ) admission46_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission46_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_11_coefficients]
def admission46_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission46_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission46_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission46_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_12_coefficients]
def admission46_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission46_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission46_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission46_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_13_coefficients]
def admission46_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission46_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission46_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission46_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission46_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission46_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission46_14_coefficients]
theorem admission46_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (7509/16384:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission46_00_pos hδ hp
 · exact admission46_01_pos hδ hp
 · exact admission46_02_pos hδ hp
 · exact admission46_03_pos hδ hp
 · exact admission46_04_pos hδ hp
 · exact admission46_05_pos hδ hp
 · exact admission46_06_pos hδ hp
 · exact admission46_07_pos hδ hp
 · exact admission46_08_pos hδ hp
 · exact admission46_09_pos hδ hp
 · exact admission46_10_pos hδ hp
 · exact admission46_11_pos hδ hp
 · exact admission46_12_pos hδ hp
 · exact admission46_13_pos hδ hp
 · exact admission46_14_pos hδ hp
#print axioms admission46_all
end
end LewkoStage2Finite
