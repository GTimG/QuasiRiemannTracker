/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission39_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(300891672624201769/157396201727529:ℝ),(300534276422474240/157396201727529:ℝ)]]
theorem admission39_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission39_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission39_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_00_coefficients]
def admission39_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(220147421137979392/157396201727529:ℝ),(219947421137979392/157396201727529:ℝ)]]
theorem admission39_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission39_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission39_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_01_coefficients]
def admission39_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(37334049007568298/52465400575843:ℝ),(37301973623650304/52465400575843:ℝ)]]
theorem admission39_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission39_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission39_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_02_coefficients]
def admission39_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8232329094117129566752768/1416565815547761:ℝ),(5483548332187183682465792/472188605182587:ℝ),(8218318152444421480644608/1416565815547761:ℝ)],
![(8225303485944296954337280/1416565815547761:ℝ),(5478864853963031860250624/472188605182587:ℝ),(8211293327744798626414592/1416565815547761:ℝ)]]
theorem admission39_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (7830899551148222567/15472676214623010816:ℝ) admission39_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission39_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_03_coefficients]
def admission39_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(47880877757976444692500/52465400575843:ℝ),(95627363902018936320000/52465400575843:ℝ),(47746526238272389120000/52465400575843:ℝ)],
![(47957379681173443759550/52465400575843:ℝ),(95780260235121787291648/52465400575843:ℝ),(47822920680253624942592/52465400575843:ℝ)]]
theorem admission39_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (34150976828293125/429796561517305856:ℝ) admission39_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission39_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_04_coefficients]
def admission39_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53164673150461360666250129/98372626079705625:ℝ),(319014429939686285255119694/295117878239116875:ℝ),(159520302098884029861056807/295117878239116875:ℝ)],
![(52899308469300954787570931/98372626079705625:ℝ),(317422887310848035807368142/295117878239116875:ℝ),(158724853426815463510626599/295117878239116875:ℝ)]]
theorem admission39_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (52899308469300954787570931/1126685898223926263152640000:ℝ) admission39_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission39_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_05_coefficients]
def admission39_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22186342325636074226446585385163740389130240/8249596917978249986997496465053:ℝ),(22151735574657261115785768198015722183966720/2749865639326083328999165488351:ℝ),(66351451478215947793776341753065612897157120/8249596917978249986997496465053:ℝ),(22082587068622258318448459044182186734387200/8249596917978249986997496465053:ℝ)],
![(22219025739490781355259332192293896803442688/8249596917978249986997496465053:ℝ),(599578420331040093518949326561994363969536/74320692954759008891869337523:ℝ),(66449397136897972929815635876467336877703168/8249596917978249986997496465053:ℝ),(22115218208376317165770895589579859280527360/8249596917978249986997496465053:ℝ)]]
theorem admission39_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5141502960729938540246444531758825/45053798634718549262322327361142784:ℝ) admission39_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission39_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_06_coefficients]
def admission39_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(207572175759294274223633198052244267820/74320692954759008891869337523:ℝ),(414720089037839973768702183748779806720/74320692954759008891869337523:ℝ),(207148019087761818420941450382546042880/74320692954759008891869337523:ℝ)],
![(207168183392597825696047937701912993058/74320692954759008891869337523:ℝ),(413912517994840005984615853504368760832/74320692954759008891869337523:ℝ),(206744440308285715733250472343051960320/74320692954759008891869337523:ℝ)]]
theorem admission39_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (98583431390898568979859577342535/405890077790257200561462408658944:ℝ) admission39_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission39_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_07_coefficients]
def admission39_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(45396629903984950862314994222647669559487404177309565449/806431130151464940232957221386718750000000000:ℝ),(1231569849777057794808945696536859341029187425047822577039/7257880171363184462096614992480468750000000000:ℝ),(3712289914259933898769085910159738763250587708773082303271/21773640514089553386289844977441406250000000000:ℝ),(1243289366897870824913295384972248161961875019268535339277/21773640514089553386289844977441406250000000000:ℝ)],
![(118017075751069708985663376837231303851651330239861151189/2016077825378662350582393053466796875000000000:ℝ),(200063620087031489687498947494941571636357121279491432223/1134043776775497572202596092575073242187500000:ℝ),(19293438263989814595441862518337096632327246280638083084227/108868202570447766931449224887207031250000000000:ℝ),(258410111959135404946385947078913771322574143748345060201/4354728102817910677257968995488281250000000000:ℝ)]]
theorem admission39_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (45396629903984950862314994222647669559487404177309565449/18915848631510965970486044738753816166400000000000000000000:ℝ) admission39_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission39_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_08_coefficients]
def admission39_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(89056858427680270416220956489751669708365525476/435472810281791067725796899548828125:ℝ),(9870107634796015973207547073319749047935478896/16128622603029298804659144427734375:ℝ),(265815425223013508361849099169132987157124644864/435472810281791067725796899548828125:ℝ),(88379377601643925836673064853242776081974427648/435472810281791067725796899548828125:ℝ)],
![(439915250140912457091965640410245229829804903118/2177364051408955338628984497744140625:ℝ),(16251471259077294696646839042424621500483908504/26881037671715498007765240712890625:ℝ),(1312993528977635365655134256998521326061697417216/2177364051408955338628984497744140625:ℝ),(87307921517172322861616132592604979456011927552/435472810281791067725796899548828125:ℝ)]]
theorem admission39_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (20815830592434960093883546016837353576663/2435340466741543203368774451953664000000000:ℝ) admission39_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission39_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_09_coefficients]
def admission39_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(684865723587760407706461932102537216/4611216847486201171875:ℝ),(2048227924465917921346934544877211648/4611216847486201171875:ℝ),(6125579916171731361678160880340434944/13833650542458603515625:ℝ),(2035493315404934602006743042016411648/13833650542458603515625:ℝ)],
![(1360565531349668737378954144828977152/4611216847486201171875:ℝ),(4068974477833235264114914409160667136/4611216847486201171875:ℝ),(12168764824935446831238541220303208448/13833650542458603515625:ℝ),(4043537989223087094780660427308138496/13833650542458603515625:ℝ)],
![(45046107222503829766912922056059904/307414456499080078125:ℝ),(224524663585742832010946246286406656/512357427498466796875:ℝ),(671456801887555417653469130637541376/1537072282495400390625:ℝ),(223113347450697765767695002058620928/1537072282495400390625:ℝ)]]
theorem admission39_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39895775458341437417452633749/17604467159748847861760000000000:ℝ) admission39_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission39_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_10_coefficients]
def admission39_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(170233661501054705962228305143793896660/74320692954759008891869337523:ℝ),(340120344315595244209040047821906780160/74320692954759008891869337523:ℝ),(6292103117364307721396465588885258240/2752618257583666995995160649:ℝ)],
![(169894039063010973427187847561004837598/74320692954759008891869337523:ℝ),(339441453983005001405275361791029489664/74320692954759008891869337523:ℝ),(18838612907505919833208272288580894720/8257854772751000987985481947:ℝ)]]
theorem admission39_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (17965901286607665856560013092595/90197795064501600124769424146432:ℝ) admission39_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission39_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_11_coefficients]
def admission39_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission39_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission39_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission39_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_12_coefficients]
def admission39_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission39_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission39_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission39_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_13_coefficients]
def admission39_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission39_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission39_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission39_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_14_coefficients]
theorem admission39_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission39_00_pos hδ hp
 · exact admission39_01_pos hδ hp
 · exact admission39_02_pos hδ hp
 · exact admission39_03_pos hδ hp
 · exact admission39_04_pos hδ hp
 · exact admission39_05_pos hδ hp
 · exact admission39_06_pos hδ hp
 · exact admission39_07_pos hδ hp
 · exact admission39_08_pos hδ hp
 · exact admission39_09_pos hδ hp
 · exact admission39_10_pos hδ hp
 · exact admission39_11_pos hδ hp
 · exact admission39_12_pos hδ hp
 · exact admission39_13_pos hδ hp
 · exact admission39_14_pos hδ hp
#print axioms admission39_all
end
end LewkoStage2Finite
