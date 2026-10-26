/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission27_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(758483447753027/23377645067147:ℝ),(4945740618801160/163643515470029:ℝ)]]
theorem admission27_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618217577350145/654574061880116:ℝ) admission27_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission27_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_00_coefficients]
def admission27_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(548084642148704/23377645067147:ℝ),(3636592495040928/163643515470029:ℝ)]]
theorem admission27_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113643515470029/163643515470029:ℝ) admission27_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission27_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_01_coefficients]
def admission27_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(277303289983110/23377645067147:ℝ),(1844383998790528/163643515470029:ℝ)]]
theorem admission27_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57636999962204/163643515470029:ℝ) admission27_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission27_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_02_coefficients]
def admission27_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37081304584396373888/1472791639230261:ℝ),(3360776805774870656/70132935201441:ℝ),(4790144048125129984/210398805604323:ℝ)],
![(5038746565570580192/210398805604323:ℝ),(22321008779337430112/490930546410087:ℝ),(31729600379018228992/1472791639230261:ℝ)]]
theorem admission27_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123943751480539957/251356439761964544:ℝ) admission27_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission27_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_03_coefficients]
def admission27_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(696869510135612360/163643515470029:ℝ),(1285137609126756480/163643515470029:ℝ),(590202879612968960/163643515470029:ℝ)],
![(761223129623041426/163643515470029:ℝ),(1408414777544391200/163643515470029:ℝ),(649223167574265856/163643515470029:ℝ)]]
theorem admission27_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (216138749858265/2618296247520464:ℝ) admission27_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission27_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_04_coefficients]
def admission27_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(230684543975520030502/102277197168768125:ℝ),(1401023361362463976012/306831591506304375:ℝ),(707216265769982309506/306831591506304375:ℝ)],
![(22721589378696318854/14611028166966875:ℝ),(140251705405489352506/43833084500900625:ℝ),(71823917719512159694/43833084500900625:ℝ)]]
theorem admission27_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (34082384068044478281/957548341950341120000:ℝ) admission27_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission27_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_05_coefficients]
def admission27_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(278537662423144929263584219848494080/1273924807392106239245355408579:ℝ),(768101412955353636273689879166131200/1273924807392106239245355408579:ℝ),(100443349569696522003773653541826560/181989258198872319892193629797:ℝ),(213513514122553104928309915475148800/1273924807392106239245355408579:ℝ)],
![(2103562431181724255015928763021765888/8917473651744743674717487860053:ℝ),(5823067543168867778349984572622059776/8917473651744743674717487860053:ℝ),(5353641364054265521405822277129980928/8917473651744743674717487860053:ℝ),(1633943811918735258724966467529687040/8917473651744743674717487860053:ℝ)]]
theorem admission27_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (6515915347978305204111020369725/54354125115396532874468497432704:ℝ) admission27_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission27_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_06_coefficients]
def admission27_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3044995203388201164462194118250520/241012801398506585803175347569:ℝ),(5758379978525912168278258341127040/241012801398506585803175347569:ℝ),(2718309768126596718545722376919040/241012801398506585803175347569:ℝ)],
![(2695607581894201390123305863458502/241012801398506585803175347569:ℝ),(725846078397512426724370025994272/34430400199786655114739335367:ℝ),(2389923353185128658587178734069760/241012801398506585803175347569:ℝ)]]
theorem admission27_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1166954762297426102825770866245/5141606429834807163801074081472:ℝ) admission27_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission27_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_07_coefficients]
def admission27_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(540533681758160527454986613552754920693353833786881/251055001456777693544974320384375000000000000000:ℝ),(7041680633749678784370758351966344599293188563280573/753165004370333080634922961153125000000000000000:ℝ),(9218470647713958214517162569062707274582609944259767/753165004370333080634922961153125000000000000000:ℝ),(3795512375204700173632483062801135906981982882339837/753165004370333080634922961153125000000000000000:ℝ)],
![(30734855053410446070756337637372185260664593696755579/2510550014567776935449743203843750000000000000000:ℝ),(57608956672683456511980171359000213886260351970697937/1506330008740666161269845922306250000000000000000:ℝ),(149893305646093958929667148383070424934472452385952579/3765825021851665403174614805765625000000000000000:ℝ),(10391616690664433470347420243624467515056817600868221/753165004370333080634922961153125000000000000000:ℝ)]]
theorem admission27_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (540533681758160527454986613552754920693353833786881/351000332276722835715486657295155200000000000000000000:ℝ) admission27_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission27_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_08_coefficients]
def admission27_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2121264890043903541182918304054634532113/104606250606990705643739300160156250:ℝ),(52086607339898652625651258101512792159113/941456255462916350793653701441406250:ℝ),(939319075718638633875745445513290823264/18829125109258327015873074028828125:ℝ),(332709674895812878799890871373508715312/22415625130069436923658421462890625:ℝ)],
![(19671079380359559018695226937678397935093/2092125012139814112874786003203125000:ℝ),(90758819795194298006039094336750593876713/3765825021851665403174614805765625000:ℝ),(47130072502768536995163808120433468859556/2353640638657290876984134253603515625:ℝ),(836256576187693054053732726222853284656/156909375910486058465608950240234375:ℝ)]]
theorem admission27_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52266036011730815878358295388928330291/13710950479559485770136197550592000000000:ℝ) admission27_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission27_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_09_coefficients]
def admission27_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74429147775782731911790528/293525119425673828125:ℝ),(9816556741223525741278087616/14382730851858017578125:ℝ),(8701812361954445479022967616/14382730851858017578125:ℝ),(844253995581424533807538624/4794243617286005859375:ℝ)],
![(5256253791220104892185079744/14382730851858017578125:ℝ),(13739682989274283436285651072/14382730851858017578125:ℝ),(11723949043033980926966062912/14382730851858017578125:ℝ),(1080507969159934127621830528/4794243617286005859375:ℝ)],
![(10181588984310493451430968/97841706475224609375:ℝ),(34279433699317386515742944/136978389065314453125:ℝ),(129134551096198520881129112/684891945326572265625:ℝ),(9677869017428347487477056/228297315108857421875:ℝ)]]
theorem admission27_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1360950330575861365426461/1915096683900682240000000000:ℝ) admission27_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission27_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_10_coefficients]
def admission27_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2503135472136266803760510637275240/241012801398506585803175347569:ℝ),(4735022820952232523237715994801920/241012801398506585803175347569:ℝ),(745540077565022363265804350178560/80337600466168861934391782523:ℝ)],
![(2209801024471745888887569419794010/241012801398506585803175347569:ℝ),(595219683727400092047089282344384/34430400199786655114739335367:ℝ),(653714477783841418484008996033280/80337600466168861934391782523:ℝ)]]
theorem admission27_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2553572178843130540953160140755/13710950479559485770136197550592:ℝ) admission27_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission27_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_11_coefficients]
def admission27_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission27_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission27_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission27_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_12_coefficients]
def admission27_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4510380152884669971/1000000000000000000000:ℝ)]]
theorem admission27_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4510380152884669971/1000000000000000000000:ℝ) admission27_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission27_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_13_coefficients]
def admission27_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission27_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission27_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission27_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_14_coefficients]
theorem admission27_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission27_00_pos hδ hp
 · exact admission27_01_pos hδ hp
 · exact admission27_02_pos hδ hp
 · exact admission27_03_pos hδ hp
 · exact admission27_04_pos hδ hp
 · exact admission27_05_pos hδ hp
 · exact admission27_06_pos hδ hp
 · exact admission27_07_pos hδ hp
 · exact admission27_08_pos hδ hp
 · exact admission27_09_pos hδ hp
 · exact admission27_10_pos hδ hp
 · exact admission27_11_pos hδ hp
 · exact admission27_12_pos hδ hp
 · exact admission27_13_pos hδ hp
 · exact admission27_14_pos hδ hp
#print axioms admission27_all
end
end LewkoStage2Finite
