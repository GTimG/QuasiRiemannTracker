/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission40_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(300891672624201769/157396201727529:ℝ),(300534276422474240/157396201727529:ℝ)]]
theorem admission40_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission40_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission40_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_00_coefficients]
def admission40_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(220147421137979392/157396201727529:ℝ),(219947421137979392/157396201727529:ℝ)]]
theorem admission40_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission40_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission40_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_01_coefficients]
def admission40_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(37334049007568298/52465400575843:ℝ),(37301973623650304/52465400575843:ℝ)]]
theorem admission40_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission40_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission40_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_02_coefficients]
def admission40_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8228815898294108381452288/1416565815547761:ℝ),(5481206462196239478327296/472188605182587:ℝ),(8214805740094610053529600/1416565815547761:ℝ)],
![(8221790290121275769036800/1416565815547761:ℝ),(5476522983972087656112128/472188605182587:ℝ),(8207780915394987199299584/1416565815547761:ℝ)]]
theorem admission40_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1956887463425394821/3868169053655752704:ℝ) admission40_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission40_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_03_coefficients]
def admission40_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(47919182460182825848254/52465400575843:ℝ),(95703865793140551469056/52465400575843:ℝ),(47784723459263007031296/52465400575843:ℝ)],
![(47995684383379824915304/52465400575843:ℝ),(95856762126243402440704/52465400575843:ℝ),(47861117901244242853888/52465400575843:ℝ)]]
theorem admission40_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68356595219511519/859593123034611712:ℝ) admission40_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission40_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_04_coefficients]
def admission40_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10606398161976231545382106/19674525215941125:ℝ),(318218981354329253443405736/295117878239116875:ℝ),(159122900448556072328645396/295117878239116875:ℝ)],
![(52766626128720751848231332/98372626079705625:ℝ),(316627438725491003995654184/295117878239116875:ℝ),(158327451776487505978215188/295117878239116875:ℝ)]]
theorem admission40_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (13191656532180187962057833/281671474555981565788160000:ℝ) admission40_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission40_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_05_coefficients]
def admission40_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22202710169613751931598113919595060530372608/8249596917978249986997496465053:ℝ),(22168085982371454036539906810094955193802752/2749865639326083328999165488351:ℝ),(66400450427266884658831981058370828058492928/8249596917978249986997496465053:ℝ),(22098902638499287742109677316881023007457280/8249596917978249986997496465053:ℝ)],
![(22235393583468459060410860726725216944685056/8249596917978249986997496465053:ℝ),(22200751959962676380955263694873024476708864/2749865639326083328999165488351:ℝ),(1797253948268889453915439869777636541595648/222962078864277026675608012569:ℝ),(22131533778253346589432113862278695553597440/8249596917978249986997496465053:ℝ)]]
theorem admission40_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10290603450731973975016585233100235/90107597269437098524644654722285568:ℝ) admission40_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission40_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_06_coefficients]
def admission40_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(207369972782335877039893426721660034338/74320692954759008891869337523:ℝ),(414316096774316108672306831543862843392/74320692954759008891869337523:ℝ),(206946229698023767077095961362799001600/74320692954759008891869337523:ℝ)],
![(206965980415639428512308166371328759576/74320692954759008891869337523:ℝ),(413508525731316140888220501299451797504/74320692954759008891869337523:ℝ),(206542650918547664389404983323304919040/74320692954759008891869337523:ℝ)]]
theorem admission40_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (24621802677935083435702917972005/101472519447564300140365602164736:ℝ) admission40_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission40_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_07_coefficients]
def admission40_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(463017301022064172282901724787700955500739681366270129623/8064311301514649402329572213867187500000000000:ℝ),(12559694632050219421186634510523205567268483492871740833681/72578801713631844620966149924804687500000000000:ℝ),(37853745367420241434443830649215028212279375754229033682681/217736405140895533862898449774414062500000000000:ℝ),(12676128544436974328505999224792633548670334918401542181459/217736405140895533862898449774414062500000000000:ℝ)],
![(481119304986493499602405289910149475312470960552619079889/8064311301514649402329572213867187500000000000:ℝ),(13048067819849656813097110184830872741703465004280966725563/72578801713631844620966149924804687500000000000:ℝ),(1572708910112021265505467863371673353777119649110975072737/8709456205635821354515937990976562500000000000:ℝ),(13163740473415036326692342729015840495180291913133441798739/217736405140895533862898449774414062500000000000:ℝ)]]
theorem admission40_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (463017301022064172282901724787700955500739681366270129623/189158486315109659704860447387538161664000000000000000000000:ℝ) admission40_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission40_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_08_coefficients]
def admission40_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(442593890352091464529607971061839721394711153358/2177364051408955338628984497744140625:ℝ),(49052040467362884916345220533006585786441308872/80643113015146494023295722138671875:ℝ),(1321029449611172387968061248953304800756416167936/2177364051408955338628984497744140625:ℝ),(3513745982376324973965783948916955110759727104/17418912411271642709031875981953125:ℝ)],
![(437224848354602569540468829023326602682688429096/2177364051408955338628984497744140625:ℝ),(48455916070614689140248002293681705048215639904/80643113015146494023295722138671875:ℝ),(1304945852473740211813950010106161191032490360832/2177364051408955338628984497744140625:ℝ),(86772193474936521374087666462286081143030677504/435472810281791067725796899548828125:ℝ)]]
theorem admission40_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5172025768455059610252837327854995795669/608835116685385800842193612988416000000000:ℝ) admission40_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission40_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_09_coefficients]
def admission40_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2040835965948872295424487871031245824/13833650542458603515625:ℝ),(2034483113207885444011922595086210048/4611216847486201171875:ℝ),(2028131546598866208873813770421174272/4611216847486201171875:ℝ),(2021781267992479847822661397036138496/13833650542458603515625:ℝ)],
![(4054124987874083057734276292620951552/13833650542458603515625:ℝ),(4041435693125906600105963214167072768/4611216847486201171875:ℝ),(12086246888633747939766785753699581952/13833650542458603515625:ℝ),(17849176892775255043036321794752512/61482891299816015625:ℝ)],
![(80530576946086324512135731037323264/553346021698344140625:ℝ),(222991999869154366824952996819451904/512357427498466796875:ℝ),(6001778557061432602466186278211158016/13833650542458603515625:ℝ),(1994258986120079935995848640019038208/13833650542458603515625:ℝ)]]
theorem admission40_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7429193653613626718505653143/3300837592452908974080000000000:ℝ) admission40_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission40_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_10_coefficients]
def admission40_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(170063673063652488416602907712341797598/74320692954759008891869337523:ℝ),(339780721984288031384105482093703409664/74320692954759008891869337523:ℝ),(18857461129799421498698834527618334720/8257854772751000987985481947:ℝ)],
![(169724050625608755881562450129552738536/74320692954759008891869337523:ℝ),(339101831651697788580340796062826119168/74320692954759008891869337523:ℝ),(6273254895070806055905903349847818240/2752618257583666995995160649:ℝ)]]
theorem admission40_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4486981555274109403542926323305/22549448766125400031192356036608:ℝ) admission40_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission40_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_11_coefficients]
def admission40_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission40_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission40_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission40_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_12_coefficients]
def admission40_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission40_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission40_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission40_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_13_coefficients]
def admission40_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission40_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission40_14_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission40_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_14_coefficients]
theorem admission40_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission40_00_pos hδ hp
 · exact admission40_01_pos hδ hp
 · exact admission40_02_pos hδ hp
 · exact admission40_03_pos hδ hp
 · exact admission40_04_pos hδ hp
 · exact admission40_05_pos hδ hp
 · exact admission40_06_pos hδ hp
 · exact admission40_07_pos hδ hp
 · exact admission40_08_pos hδ hp
 · exact admission40_09_pos hδ hp
 · exact admission40_10_pos hδ hp
 · exact admission40_11_pos hδ hp
 · exact admission40_12_pos hδ hp
 · exact admission40_13_pos hδ hp
 · exact admission40_14_pos hδ hp
#print axioms admission40_all
end
end LewkoStage2Finite
