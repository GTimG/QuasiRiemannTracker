/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission30_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10255124753072349/163643515470029:ℝ),(9891481237602320/163643515470029:ℝ)]]
theorem admission30_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (618217577350145/654574061880116:ℝ) admission30_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission30_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_00_coefficients]
def admission30_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7473184990081856/163643515470029:ℝ),(7273184990081856/163643515470029:ℝ)]]
theorem admission30_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (113643515470029/163643515470029:ℝ) admission30_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission30_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_01_coefficients]
def admission30_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3785507028672298/163643515470029:ℝ),(3688767997581056/163643515470029:ℝ)]]
theorem admission30_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (57636999962204/163643515470029:ℝ) admission30_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission30_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_02_coefficients]
def admission30_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13102498977074721344/70132935201441:ℝ),(536121113382145703744/1472791639230261:ℝ),(261042434863576555520/1472791639230261:ℝ)],
![(89309235117349720448/490930546410087:ℝ),(521688908384194993280/1472791639230261:ℝ),(253836803032145831936/1472791639230261:ℝ)]]
theorem admission30_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (123943751480539957/251356439761964544:ℝ) admission30_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission30_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_03_coefficients]
def admission30_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(753290071099206070/23377645067147:ℝ),(10108727810246047040/163643515470029:ℝ),(4839663612826345472/163643515470029:ℝ)],
![(5519681573560803172/163643515470029:ℝ),(10591363298926504064/163643515470029:ℝ),(5075744764671533056/163643515470029:ℝ)]]
theorem admission30_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1772337748837773/20946369980163712:ℝ) admission30_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission30_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_04_coefficients]
def admission30_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(941781353373899432152/61366318301260875:ℝ),(9499366895593763601368/306831591506304375:ℝ),(1595621842736375737286/102277197168768125:ℝ)],
![(110579892761089259002/8766616900180125:ℝ),(1120435525944585402548/43833084500900625:ℝ),(189003341013120878346/14611028166966875:ℝ)]]
theorem admission30_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (55289946380544629501/1532077347120545792000:ℝ) admission30_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission30_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_05_coefficients]
def admission30_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9366536851167543329344503656155610624/2972491217248247891572495953351:ℝ),(80600056747519546531511803200978512384/8917473651744743674717487860053:ℝ),(76971732344466502026318991002542927872/8917473651744743674717487860053:ℝ),(24470910433969401848877898770031247360/8917473651744743674717487860053:ℝ)],
![(9757011149467910510028738641264135168/2972491217248247891572495953351:ℝ),(1715439515742939920380092845049807872/181989258198872319892193629797:ℝ),(11481655977393344012846315532472655872/1273924807392106239245355408579:ℝ),(25585704138456310042692275243660410880/8917473651744743674717487860053:ℝ)]]
theorem admission30_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (373396460479269437391325359650135/3043831006462205840970235856231424:ℝ) admission30_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission30_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_06_coefficients]
def admission30_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3098305490557518155295321373683538/34430400199786655114739335367:ℝ),(42111537539863899819229301490129088/241012801398506585803175347569:ℝ),(2918990355035271644075943491993600/34430400199786655114739335367:ℝ)],
![(20332906967723834071562149558976332/241012801398506585803175347569:ℝ),(39443077020611377216979790600397696/241012801398506585803175347569:ℝ),(19119386825481029268697429872558080/241012801398506585803175347569:ℝ)]]
theorem admission30_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1166954762297426102825770866245/5141606429834807163801074081472:ℝ) admission30_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission30_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_07_coefficients]
def admission30_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(126018094098582611406222558165971003759499689085445487/1506330008740666161269845922306250000000000000000:ℝ),(2024133284684298147905877119868338956035813521194511957/7531650043703330806349229611531250000000000000000:ℝ),(2158437849234618025737454437624546130509674259214404607/7531650043703330806349229611531250000000000000000:ℝ),(50955734801368979177711536545967707793227695563141339/502110002913555387089948640768750000000000000000:ℝ)],
![(47890798007838629712689500859778945744037145529566521/301266001748133232253969184461250000000000000000:ℝ),(3685563116923916477997810581570469207889518574064812859/7531650043703330806349229611531250000000000000000:ℝ),(3780377986349979364199897583625401031971129646755040639/7531650043703330806349229611531250000000000000000:ℝ),(86134957817154223426857868177025476369626814061959387/502110002913555387089948640768750000000000000000:ℝ)]]
theorem admission30_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (126018094098582611406222558165971003759499689085445487/33696031898565392228686719100334899200000000000000000000:ℝ) admission30_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission30_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_08_coefficients]
def admission30_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(15002320848803504502559260561840787595693/75316500437033308063492296115312500:ℝ),(585302922824504039583600136885443900656569/1046062506069907056437393001601562500:ℝ),(175417171707557491705151763412730551371632/336234376951041553854876321943359375:ℝ),(5064358880733413129044750121339862866944/31381875182097211693121790048046875:ℝ)],
![(110822518256387898364621090623306869583457/941456255462916350793653701441406250:ℝ),(167658625160870842379128909227879517068069/523031253034953528218696500800781250:ℝ),(678092947449717795420654246403694933352608/2353640638657290876984134253603515625:ℝ),(13380105219003088864859723619565652554496/156909375910486058465608950240234375:ℝ)]]
theorem admission30_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (52266036011730815878358295388928330291/13710950479559485770136197550592000000000:ℝ) admission30_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission30_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_09_coefficients]
def admission30_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67077134502183893275431819584/14382730851858017578125:ℝ),(37033091660763804431479887008/2876546170371603515625:ℝ),(169158247619899123889960911328/14382730851858017578125:ℝ),(2431996816122690238475871232/684891945326572265625:ℝ)],
![(101593081222976835083517079808/14382730851858017578125:ℝ),(274465482621227578845605769856/14382730851858017578125:ℝ),(244243251200813130422690300288/14382730851858017578125:ℝ),(4758331097254159110706774016/958848723457201171875:ℝ)],
![(1603345798140975800329167104/684891945326572265625:ℝ),(4134136734766712813826131584/684891945326572265625:ℝ),(3459765956048858372294761856/684891945326572265625:ℝ),(309691808557707119599265792/228297315108857421875:ℝ)]]
theorem admission30_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1360950330575861365426461/1915096683900682240000000000:ℝ) admission30_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission30_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_10_coefficients]
def admission30_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(282734297931724400086743826459006/3825600022198517234971037263:ℝ),(34594175878274431716132442096967296/241012801398506585803175347569:ℝ),(799574031627922160999893340692480/11476800066595551704913111789:ℝ)],
![(1852773831981126841926493640956564/26779200155389620644797260841:ℝ),(32355298611179396620934715810441472/241012801398506585803175347569:ℝ),(5229715822270731347872071968266240/80337600466168861934391782523:ℝ)]]
theorem admission30_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2553572178843130540953160140755/13710950479559485770136197550592:ℝ) admission30_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission30_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_11_coefficients]
def admission30_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission30_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission30_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission30_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_12_coefficients]
def admission30_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4510380152884669971/1000000000000000000000:ℝ)]]
theorem admission30_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4510380152884669971/1000000000000000000000:ℝ) admission30_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission30_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_13_coefficients]
def admission30_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission30_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission30_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission30_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission30_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission30_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission30_14_coefficients]
theorem admission30_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .P δ p j := by
 fin_cases j
 · exact admission30_00_pos hδ hp
 · exact admission30_01_pos hδ hp
 · exact admission30_02_pos hδ hp
 · exact admission30_03_pos hδ hp
 · exact admission30_04_pos hδ hp
 · exact admission30_05_pos hδ hp
 · exact admission30_06_pos hδ hp
 · exact admission30_07_pos hδ hp
 · exact admission30_08_pos hδ hp
 · exact admission30_09_pos hδ hp
 · exact admission30_10_pos hδ hp
 · exact admission30_11_pos hδ hp
 · exact admission30_12_pos hδ hp
 · exact admission30_13_pos hδ hp
 · exact admission30_14_pos hδ hp
#print axioms admission30_all
end
end LewkoStage2Finite
