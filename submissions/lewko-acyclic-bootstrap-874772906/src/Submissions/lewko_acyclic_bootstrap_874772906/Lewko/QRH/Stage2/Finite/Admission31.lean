/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission31_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20146605990674669/163643515470029:ℝ),(19782962475204640/163643515470029:ℝ)]]
theorem admission31_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618217577350145/654574061880116:ℝ) admission31_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission31_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_00_coefficients]
def admission31_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(14746369980163712/163643515470029:ℝ),(14546369980163712/163643515470029:ℝ)]]
theorem admission31_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113643515470029/163643515470029:ℝ) admission31_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission31_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_01_coefficients]
def admission31_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7474275026253354/163643515470029:ℝ),(7377535995162112/163643515470029:ℝ)]]
theorem admission31_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57636999962204/163643515470029:ℝ) admission31_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission31_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_02_coefficients]
def admission31_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1072316026764291407488/1472791639230261:ℝ),(100781522200885601408/70132935201441:ℝ),(1044169739454306222080/1472791639230261:ℝ)],
![(1043453416768389986560/1472791639230261:ℝ),(98034525185570157824/70132935201441:ℝ),(1015347212128583327744/1472791639230261:ℝ)]]
theorem admission31_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123943751480539957/251356439761964544:ℝ) admission31_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission31_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_03_coefficients]
def admission31_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20221421920766835002/163643515470029:ℝ),(39576110071797475968/163643515470029:ℝ),(19358654451305381888/163643515470029:ℝ)],
![(21186789637158840292/163643515470029:ℝ),(41485705656539140352/163643515470029:ℝ),(20302979058686132224/163643515470029:ℝ)]]
theorem admission31_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1772337748837773/20946369980163712:ℝ) admission31_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission31_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_04_coefficients]
def admission31_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(179947848944626247048/2922205633393375:ℝ),(37944965801050771982276/306831591506304375:ℝ),(19046847061349876813486/306831591506304375:ℝ)],
![(105998639714551893158/2087289738138125:ℝ),(4480163986479012192692/43833084500900625:ℝ),(2253666513373645963874/43833084500900625:ℝ)]]
theorem admission31_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (158997959571827839737/4377363848915845120000:ℝ) admission31_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission31_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_05_coefficients]
def admission31_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(210142310079458080394742203942019519488/8917473651744743674717487860053:ℝ),(615912505476721512261566963032316220416/8917473651744743674717487860053:ℝ),(601537854585498830291810749250546679808/8917473651744743674717487860053:ℝ),(195767283471755214791023190160249978880/8917473651744743674717487860053:ℝ)],
![(219284865700017505761327249302201993216/8917473651744743674717487860053:ℝ),(643113664740559604813099585186078001152/8917473651744743674717487860053:ℝ),(628514817028489352872004137833159294976/8917473651744743674717487860053:ℝ),(204685633107650480341538201949283287040/8917473651744743674717487860053:ℝ)]]
theorem admission31_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373396460479269437391325359650135/3043831006462205840970235856231424:ℝ) admission31_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission31_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_06_coefficients]
def admission31_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84232608459013428414828155549869054/241012801398506585803175347569:ℝ),(165954805020715405672585020756078976/241012801398506585803175347569:ℝ),(11675961420141086576303773967974400/34430400199786655114739335367:ℝ)],
![(78895370813816240557239370031932108/241012801398506585803175347569:ℝ),(155363701343146871508749300691027712/241012801398506585803175347569:ℝ),(76477547301924117074789719490232320/241012801398506585803175347569:ℝ)]]
theorem admission31_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1166954762297426102825770866245/5141606429834807163801074081472:ℝ) admission31_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission31_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_07_coefficients]
def admission31_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(18057349303359980228892890685631115429628212963777353/25617857291507927912752481671875000000000000000:ℝ),(1175973093192620523687056262468702341264906824009371139/537975003121666486167802115109375000000000000000:ℝ),(8500686433725649580900535861981124283513780547212446271/3765825021851665403174614805765625000000000000000:ℝ),(2923275622459873885139888425289708574628308209822119189/3765825021851665403174614805765625000000000000000:ℝ)],
![(32949314590077024508068728484384415792773034088624779/25617857291507927912752481671875000000000000000:ℝ),(2102883827789860094862542644911765147081274846923426157/537975003121666486167802115109375000000000000000:ℝ),(2982139355875408848049718400155606651662522397437468531/753165004370333080634922961153125000000000000000:ℝ),(5034029003406988540088668323153174689212255319751202069/3765825021851665403174614805765625000000000000000:ℝ)]]
theorem admission31_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (18057349303359980228892890685631115429628212963777353/4584494135859237037916560421814272000000000000000000000:ℝ) admission31_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission31_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_08_coefficients]
def admission31_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2262334147258768020921663869026251308976607/1569093759104860584656089502402343750:ℝ),(19649010913703827707881175092287782562970113/4707281277314581753968268507207031250:ℝ),(9469603800471681583884524484762332018655296/2353640638657290876984134253603515625:ℝ),(40514871045867305032358000970718902935552/31381875182097211693121790048046875:ℝ)],
![(636771544866550888337060972926968240811667/784546879552430292328044751201171875:ℝ),(5425508885956986760932152294426604116927693/2353640638657290876984134253603515625:ℝ),(5120790729219427177357367237136597193219712/2353640638657290876984134253603515625:ℝ),(107040841752024710918877788956525220435968/156909375910486058465608950240234375:ℝ)]]
theorem admission31_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52266036011730815878358295388928330291/13710950479559485770136197550592000000000:ℝ) admission31_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission31_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_09_coefficients]
def admission31_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67496110509211219190112208832/2054675835979716796875:ℝ),(1353395505918693509922602290624/14382730851858017578125:ℝ),(1289496188142514435655763195776/14382730851858017578125:ℝ),(19455974528981521907806969856/684891945326572265625:ℝ)],
![(98810968786261418716059251456/2054675835979716796875:ℝ),(1954153768798581999345582402304/14382730851858017578125:ℝ),(1833472602309001161617980524032/14382730851858017578125:ℝ),(38066648778033272885654192128/958848723457201171875:ℝ)],
![(2025264782925933669049571584/136978389065314453125:ℝ),(27681789847767587269618094848/684891945326572265625:ℝ),(24987968932272889794752615936/684891945326572265625:ℝ),(2477534468461656956794126336/228297315108857421875:ℝ)]]
theorem admission31_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1360950330575861365426461/1915096683900682240000000000:ℝ) admission31_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission31_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_10_coefficients]
def admission31_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(69197491312159434302595063318426754/241012801398506585803175347569:ℝ),(136352570413294324956255924812102912/241012801398506585803175347569:ℝ),(3198296126511688643999573362769920/11476800066595551704913111789:ℝ)],
![(64719410565821732241889374483849268/241012801398506585803175347569:ℝ),(127467187089607569416334295240077824/241012801398506585803175347569:ℝ),(20918863289082925391488287873064960/80337600466168861934391782523:ℝ)]]
theorem admission31_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2553572178843130540953160140755/13710950479559485770136197550592:ℝ) admission31_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission31_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_11_coefficients]
def admission31_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission31_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission31_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission31_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_12_coefficients]
def admission31_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4510380152884669971/1000000000000000000000:ℝ)]]
theorem admission31_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4510380152884669971/1000000000000000000000:ℝ) admission31_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission31_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_13_coefficients]
def admission31_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission31_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission31_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission31_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission31_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission31_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission31_14_coefficients]
theorem admission31_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission31_00_pos hδ hp
 · exact admission31_01_pos hδ hp
 · exact admission31_02_pos hδ hp
 · exact admission31_03_pos hδ hp
 · exact admission31_04_pos hδ hp
 · exact admission31_05_pos hδ hp
 · exact admission31_06_pos hδ hp
 · exact admission31_07_pos hδ hp
 · exact admission31_08_pos hδ hp
 · exact admission31_09_pos hδ hp
 · exact admission31_10_pos hδ hp
 · exact admission31_11_pos hδ hp
 · exact admission31_12_pos hδ hp
 · exact admission31_13_pos hδ hp
 · exact admission31_14_pos hδ hp
#print axioms admission31_all
end
end LewkoStage2Finite
