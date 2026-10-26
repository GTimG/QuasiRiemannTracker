/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission21_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391013200118207/3198839752287:ℝ), (383814360365920/3198839752287:ℝ)]]
theorem admission21_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission21_00_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission21_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_00_coefficients]
def admission21_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(285451488292736/3198839752287:ℝ), (281451488292736/3198839752287:ℝ)]]
theorem admission21_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission21_01_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission21_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_01_coefficients]
def admission21_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(144952152528932/3198839752287:ℝ), (143023972154176/3198839752287:ℝ)]]
theorem admission21_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission21_02_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission21_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_02_coefficients]
def admission21_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84021089947153287424/28789557770583:ℝ), (18424190229769433344/3198839752287:ℝ), (81802310120771612672/28789557770583:ℝ)],
![(83460126838778074240/28789557770583:ℝ), (18299626309753315456/3198839752287:ℝ), (81242233949001764864/28789557770583:ℝ)]]
theorem admission21_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (19834529772705509/39307342876102656:ℝ) admission21_03_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission21_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_03_coefficients]
def admission21_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1511256394072491448/3198839752287:ℝ), (2957210147996307712/3198839752287:ℝ), (1446258406423027712/3198839752287:ℝ)],
![(1529974842176893468/3198839752287:ℝ), (2994233736356069504/3198839752287:ℝ), (1464565474858762240/3198839752287:ℝ)]]
theorem admission21_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (176545215627811/2183741270894592:ℝ) admission21_04_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission21_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_04_coefficients]
def admission21_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(173499098968889572702/666424948393125:ℝ), (625922975101556467372/1199564907107625:ℝ), (1567847892851754717542/5997824535538125:ℝ)],
![(166354406521607536714/666424948393125:ℝ), (3001829665560676738964/5997824535538125:ℝ), (1504363173841984776038/5997824535538125:ℝ)]]
theorem admission21_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (83177203260803768357/1863459217830051840000:ℝ) admission21_05_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission21_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_05_coefficients]
def admission21_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(305737100357026480744632051017954816/3407447728350247988736212877:ℝ), (298550157206488993818543803402883584/1135815909450082662912070959:ℝ), (874300722690770031013850199739498496/3407447728350247988736212877:ℝ), (284386778170322376184466840548802560/3407447728350247988736212877:ℝ)],
![(309162776352033747065309305868872448/3407447728350247988736212877:ℝ), (301947074019056693597098870114072832/1135815909450082662912070959:ℝ), (884406091982974368645848778407886848/3407447728350247988736212877:ℝ), (287727069391615645648829473934540800/3407447728350247988736212877:ℝ)]]
theorem admission21_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (135606183133279026119454784655/1163075491276884646821960662016:ℝ) admission21_06_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission21_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_06_coefficients]
def admission21_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129971902221629273452728299427448/92093181847303999695573321:ℝ), (255884443197971375247323331137792/92093181847303999695573321:ℝ), (125928337169164804425488891924480/92093181847303999695573321:ℝ)],
![(127963715678136305193189848187004/92093181847303999695573321:ℝ), (251900174022415653618337113550976/92093181847303999695573321:ℝ), (123952129611148268697800312975360/92093181847303999695573321:ℝ)]]
theorem admission21_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (30261750393346745287548904535/125737890948852394251022774272:ℝ) admission21_07_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission21_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_07_coefficients]
def admission21_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(397046514626116707168469607889708498622949144183/177648884736311727807818906250000000000000:ℝ), (11288223913459306063254302749081407760681319400401/1598839962626805550270370156250000000000000:ℝ), (106701144393775381037669999897587611617243491669003/14389559663641249952433331406250000000000000:ℝ), (37267446605325590849142559635378350932007997744217/14389559663641249952433331406250000000000000:ℝ)],
![(6226991113905891039388519878301903741769154409/2220611059203896597597736328125000000000:ℝ), (1398494399028582634983430176933037669174362793829/159883996262680555027037015625000000000000:ℝ), (130674087874884288467258302112625433395735565621387/14389559663641249952433331406250000000000000:ℝ), (45160041278694134525622157988862723105425784747097/14389559663641249952433331406250000000000000:ℝ)]]
theorem admission21_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (397046514626116707168469607889708498622949144183/127166025018888742432639329239040000000000000000000:ℝ) admission21_08_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission21_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_08_coefficients]
def admission21_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(20026198026467507843642869801922198711383/2997824929925260406756944042968750:ℝ), (19296121323708290959376357876147113745773/999274976641753468918981347656250:ℝ), (27853488215681890241520964698900398641088/1498912464962630203378472021484375:ℝ), (1784488847294980954927756451132149850624/299782492992526040675694404296875:ℝ)],
![(36304062758806385709622544751662681840423/5995649859850520813513888085937500:ℝ), (34886775068463163886760580470174040858973/1998549953283506937837962695312500:ℝ), (25106292449177245048227385311199092772064/1498912464962630203378472021484375:ℝ), (1603453215489015017185157983389463705088/299782492992526040675694404296875:ℝ)]]
theorem admission21_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3131744561501982455439761686307546299/419126303162841314170075914240000000000:ℝ) admission21_09_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission21_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_09_coefficients]
def admission21_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(96873684741673070872871524864/156193347279638671875:ℝ), (2500230601395867434029900864256/1405740125516748046875:ℝ), (2385200598916056447489170557184/1405740125516748046875:ℝ), (252278714724457217105037805568/468580041838916015625:ℝ)],
![(61232874348553678334949197312/52064449093212890625:ℝ), (946338707285890526473262077696/281148025103349609375:ℝ), (4504163163467200628142635794688/1405740125516748046875:ℝ), (475254413392274103606651244544/468580041838916015625:ℝ)],
![(17350896708298448922036735616/31238669455927734375:ℝ), (743193802374452670926561889344/468580041838916015625:ℝ), (705700551601798805368545675968/468580041838916015625:ℝ), (74257069047222206090844940288/156193347279638671875:ℝ)]]
theorem admission21_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (36258334495713967817795381/18634592178300518400000000000:ℝ) admission21_10_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission21_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_10_coefficients]
def admission21_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(106644167052174342936332168474248/92093181847303999695573321:ℝ), (209972912776447564482224358585344/92093181847303999695573321:ℝ), (103343888538036916668882832793600/92093181847303999695573321:ℝ)],
![(104957274528526335098444815895044/92093181847303999695573321:ℝ), (206626557450843575086440067676672/92093181847303999695573321:ℝ), (101684296674816652705226707066880/92093181847303999695573321:ℝ)]]
theorem admission21_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12412633871437579675930994515/62868945474426197125511387136:ℝ) admission21_11_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission21_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_11_coefficients]
def admission21_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission21_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission21_12_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission21_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_12_coefficients]
def admission21_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission21_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission21_13_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission21_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_13_coefficients]
def admission21_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission21_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission21_14_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission21_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_14_coefficients]
theorem admission21_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission21_00_pos hδ hp
 · exact admission21_01_pos hδ hp
 · exact admission21_02_pos hδ hp
 · exact admission21_03_pos hδ hp
 · exact admission21_04_pos hδ hp
 · exact admission21_05_pos hδ hp
 · exact admission21_06_pos hδ hp
 · exact admission21_07_pos hδ hp
 · exact admission21_08_pos hδ hp
 · exact admission21_09_pos hδ hp
 · exact admission21_10_pos hδ hp
 · exact admission21_11_pos hδ hp
 · exact admission21_12_pos hδ hp
 · exact admission21_13_pos hδ hp
 · exact admission21_14_pos hδ hp
#print axioms admission21_all
end
end LewkoStage1Return.C30
