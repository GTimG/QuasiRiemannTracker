/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission47_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(75490965307346089/157396201727529:ℝ),(75133569105618560/157396201727529:ℝ)]]
theorem admission47_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission47_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission47_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_00_coefficients]
def admission47_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(55186855284494848/157396201727529:ℝ),(54986855284494848/157396201727529:ℝ)]]
theorem admission47_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission47_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission47_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_01_coefficients]
def admission47_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9357568789830570/52465400575843:ℝ),(9325493405912576/52465400575843:ℝ)]]
theorem admission47_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission47_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission47_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_02_coefficients]
def admission47_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129342111045302924792320/1416565815547761:ℝ),(85935883406737604658688/472188605182587:ℝ),(128466102574909889183744/1416565815547761:ℝ)],
![(128902864983274056856576/1416565815547761:ℝ),(85643116938152505883648/472188605182587:ℝ),(128027051031183460794368/1416565815547761:ℝ)]]
theorem admission47_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (976768882989375769/1934084526827876352:ℝ) admission47_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission47_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_03_coefficients]
def admission47_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(755651070458811517658/52465400575843:ℝ),(1502874166492608075264/52465400575843:ℝ),(747233135628962889728/52465400575843:ℝ)],
![(760452617443117506180/52465400575843:ℝ),(1512450334025357384704/52465400575843:ℝ),(752007788252790128640/52465400575843:ℝ)]]
theorem admission47_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (17102809195609197/214898280758652928:ℝ) admission47_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission47_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_04_coefficients]
def admission47_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(832572548542406755066936/98372626079705625:ℝ),(4997206124392812264322628/295117878239116875:ℝ),(499892267611056276187114/59023575647823375:ℝ)],
![(815946898578707047619962/98372626079705625:ℝ),(4897613719208962283796068/295117878239116875:ℝ),(2449745796050995984033682/295117878239116875:ℝ)]]
theorem admission47_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (407973449289353523809981/8802233579874423930880000:ℝ) admission47_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission47_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_05_coefficients]
def admission47_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(88013432104684946428807532962057097652224/8249596917978249986997496465053:ℝ),(87470121508650912568522750592177339938816/2749865639326083328999165488351:ℝ),(260784506366736060951611020111271247478784/8249596917978249986997496465053:ℝ),(86387571126469988928792560896796325314560/8249596917978249986997496465053:ℝ)],
![(88526567304037363114951376165384259080192/8249596917978249986997496465053:ℝ),(87982162599117882072167845558026864898048/2749865639326083328999165488351:ℝ),(262317356006448106549349263627331294461952/8249596917978249986997496465053:ℝ),(86897432685127158418205631918634958848000/8249596917978249986997496465053:ℝ)]]
theorem admission47_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2574550245001017717385070350670705/22526899317359274631161163680571392:ℝ) admission47_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission47_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_06_coefficients]
def admission47_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3266318651567474225286116442758922182/74320692954759008891869337523:ℝ),(6506133008310671686987750272124281344/74320692954759008891869337523:ℝ),(3239840757460935465074795928160829440/74320692954759008891869337523:ℝ)],
![(3240991503665693773939428628520510396/74320692954759008891869337523:ℝ),(6455582289864218248850284475831800832/74320692954759008891869337523:ℝ),(3214617083743679047094109800692449280/74320692954759008891869337523:ℝ)]]
theorem admission47_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12262790999388424099327506258745/50736259723782150070182801082368:ℝ) admission47_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission47_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_07_coefficients]
def admission47_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(21676116670589476573644656483887907432908535729713968719/96771735618175792827954866566406250000000000000:ℝ),(66234329589905088509949475409637232737597876463934774833/96771735618175792827954866566406250000000000000:ℝ),(121391557895235568893664922123969513351822819195683355119/174189124112716427090318759819531250000000000000:ℝ),(205933818730487976123615111930692681442889792651679520569/870945620563582135451593799097656250000000000000:ℝ)],
![(1003763444239597545419553614918123052209572257231203429/3870869424727031713118194662656250000000000000:ℝ),(76456397976389143274569784707909987995106071188350727743/96771735618175792827954866566406250000000000000:ℝ),(698670425771090521286722873263495067384417154828059024811/870945620563582135451593799097656250000000000000:ℝ),(236409564291616851010261580944643115599762104822423246649/870945620563582135451593799097656250000000000000:ℝ)]]
theorem admission47_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (21676116670589476573644656483887907432908535729713968719/8866804046020765298665333471290851328000000000000000000000:ℝ) admission47_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission47_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_08_coefficients]
def admission47_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1789227335784611696795034370706924680955963572/2177364051408955338628984497744140625:ℝ),(354334657496447682241114502226662200296199022/145157603427263689241932299849609375:ℝ),(5262415570535021385443605536878535201064281088/2177364051408955338628984497744140625:ℝ),(347324631421405184860162230404537790605295616/435472810281791067725796899548828125:ℝ)],
![(1704783660823369612447706314287212706184418056/2177364051408955338628984497744140625:ℝ),(337495095516744818482766166556865960666816588/145157603427263689241932299849609375:ℝ),(5010558308839606217648558604693010345948801024/2177364051408955338628984497744140625:ℝ),(330583130101536388374897663832072218324631552/435472810281791067725796899548828125:ℝ)]]
theorem admission47_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2522149124920168978690320311218812700841/304417558342692900421096806494208000000000:ℝ) admission47_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission47_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_09_coefficients]
def admission47_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2075797601217774476047976268037888/13833650542458603515625:ℝ),(2051016046006848886061160408358144/4611216847486201171875:ℝ),(243150525283421425109486519441408/553346021698344140625:ℝ),(667170904128777919367219342999552/4611216847486201171875:ℝ)],
![(161728752402255354560735744543744/553346021698344140625:ℝ),(3993913383734640382837481447638016/4611216847486201171875:ℝ),(438294138207858205481344151298048/512357427498466796875:ℝ),(3895420625420040513502241355726848/13833650542458603515625:ℝ)],
![(1967034442281986620621447629085696/13833650542458603515625:ℝ),(388502329479216433542406862947328/922243369497240234375:ℝ),(5754024751932675999404889161162752/13833650542458603515625:ℝ),(5076472841499858892467114868736/37087534966376953125:ℝ)]]
theorem admission47_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4841301766872271435229411/2212357635692298240000000000:ℝ) admission47_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission47_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_10_coefficients]
def admission47_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2678786026470915041932881311520282170/74320692954759008891869337523:ℝ),(5335892275163323330936364418541462528/74320692954759008891869337523:ℝ),(295236837099787887963749359463956480/8257854772751000987985481947:ℝ)],
![(2657493087148160246623995581635110980/74320692954759008891869337523:ℝ),(5293395192496898872056488024324859904/74320692954759008891869337523:ℝ),(292880809313100179777429079584276480/8257854772751000987985481947:ℝ)]]
theorem admission47_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2234503244881440580577309261965/11274724383062700015596178018304:ℝ) admission47_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission47_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_11_coefficients]
def admission47_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission47_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission47_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission47_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_12_coefficients]
def admission47_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission47_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission47_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission47_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_13_coefficients]
def admission47_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission47_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission47_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission47_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_14_coefficients]
theorem admission47_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission47_00_pos hδ hp
 · exact admission47_01_pos hδ hp
 · exact admission47_02_pos hδ hp
 · exact admission47_03_pos hδ hp
 · exact admission47_04_pos hδ hp
 · exact admission47_05_pos hδ hp
 · exact admission47_06_pos hδ hp
 · exact admission47_07_pos hδ hp
 · exact admission47_08_pos hδ hp
 · exact admission47_09_pos hδ hp
 · exact admission47_10_pos hδ hp
 · exact admission47_11_pos hδ hp
 · exact admission47_12_pos hδ hp
 · exact admission47_13_pos hδ hp
 · exact admission47_14_pos hδ hp
#print axioms admission47_all
end
end LewkoStage2Finite
