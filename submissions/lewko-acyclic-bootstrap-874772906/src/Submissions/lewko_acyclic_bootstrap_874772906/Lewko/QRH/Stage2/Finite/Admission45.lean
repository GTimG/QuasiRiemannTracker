/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission45_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(801543869193840483/52465400575843:ℝ),(2404274211379793920/157396201727529:ℝ)]]
theorem admission45_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission45_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission45_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_00_coefficients]
def admission45_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(586593123034611712/52465400575843:ℝ),(1759579369103835136/157396201727529:ℝ)]]
theorem admission45_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission45_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission45_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_01_coefficients]
def admission45_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(298447864373120426/52465400575843:ℝ),(298415788989202432/52465400575843:ℝ)]]
theorem admission45_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission45_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission45_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_02_coefficients]
def admission45_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(155727003711384144179412992/52465400575843:ℝ),(8408361677212132926897700864/1416565815547761:ℝ),(4203732595024561034053550080/1416565815547761:ℝ)],
![(467131056127356705789771776/157396201727529:ℝ),(8407462493368395523490775040/1416565815547761:ℝ),(4203283006243785171382829056/1416565815547761:ℝ)]]
theorem admission45_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15658449404849801851/30945352429246021632:ℝ) admission45_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission45_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_03_coefficients]
def admission45_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24481717985434226139879150/52465400575843:ℝ),(48954829941900415975833600/52465400575843:ℝ),(24473112277572858238992384/52465400575843:ℝ)],
![(24486608089346223651054744/52465400575843:ℝ),(48964609290067137195737088/52465400575843:ℝ),(24478001521859657331638272/52465400575843:ℝ)]]
theorem admission45_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (547016686444867959/6876744984276893696:ℝ) admission45_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission45_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_04_coefficients]
def admission45_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16241691769007522374010613782/59023575647823375:ℝ),(162418651363784500113896926168/295117878239116875:ℝ),(27070063883559238658918492836/98372626079705625:ℝ)],
![(16231508993532180631022338052/59023575647823375:ℝ),(162316828771482114687066730456/295117878239116875:ℝ),(27053094311888442576775981732/98372626079705625:ℝ)]]
theorem admission45_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4057877248383045157755584513/86529476983597537010122752000:ℝ) admission45_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission45_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_05_coefficients]
def admission45_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(90595296280057856827436118286506859481942720512/8249596917978249986997496465053:ℝ),(271732754321210443390726732185788909234086150144/8249596917978249986997496465053:ℝ),(7342692539563971601696701071219754932597948416/222962078864277026675608012569:ℝ),(90542165922624199786424869556810082753980661760/8249596917978249986997496465053:ℝ)],
![(90612006767212188620095174675012415251670892544/8249596917978249986997496465053:ℝ),(271782882438795792746680287070232238896957882368/8249596917978249986997496465053:ℝ),(271729748737852053962285809176043114742891413504/8249596917978249986997496465053:ℝ),(90558873066178277916253957068053691097604423680/8249596917978249986997496465053:ℝ)]]
theorem admission45_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82347620193672082483703770373549635/720860778155496788197157237778284544:ℝ) admission45_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission45_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_06_coefficients]
def admission45_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(105854428109886688888026359157402309639922/74320692954759008891869337523:ℝ),(211681751660503674238174487674628765433856/74320692954759008891869337523:ℝ),(105827324395955815883412019245114982400000/74320692954759008891869337523:ℝ)],
![(105828595760024663633313311661405890998504/74320692954759008891869337523:ℝ),(211630090268858350994880407492250139820032/74320692954759008891869337523:ℝ),(105801495354069345311399796650587361116160/74320692954759008891869337523:ℝ)]]
theorem admission45_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (197070642102638902722671249230555/811780155580514401122924817317888:ℝ) admission45_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission45_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_07_coefficients]
def admission45_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1297340072794036595650148886499062690839634105530136144701923/5443410128522388346572461244360351562500000000:ℝ),(19471251006210143001514982517934799915089259753181054979009277/27217050642611941732862306221801757812500000000:ℝ),(19482400752768755579443281061150994595143559757982209135135667/27217050642611941732862306221801757812500000000:ℝ),(1299570022094870179846987713374909733058635609753350374364701/5443410128522388346572461244360351562500000000:ℝ)],
![(1303583332158385027210201707453714955322790324621995858396053/5443410128522388346572461244360351562500000000:ℝ),(19564890762728640490268806563169609616599608992570506704325499/27217050642611941732862306221801757812500000000:ℝ),(19576031375920112316764129697341107807214421456885531015924659/27217050642611941732862306221801757812500000000:ℝ),(261162290957157874684754582045793356394792611857183737893177/1088682025704477669314492248872070312500000000:ℝ)]]
theorem admission45_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1297340072794036595650148886499062690839634105530136144701923/522985382964015187151998164937065509368627200000000000000000000:ℝ) admission45_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission45_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_08_coefficients]
def admission45_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(357409791473375245547973287869764384127545260627374/435472810281791067725796899548828125:ℝ),(5359421160018938753911018205796765627727786734659264/2177364051408955338628984497744140625:ℝ),(5357695507743882712154049395051973617627176547385344/2177364051408955338628984497744140625:ℝ),(71412932203817674743590105956372688795866411040768/87094562056358213545159379909765625:ℝ)],
![(356861055473858070821884167285809429393898315352984/435472810281791067725796899548828125:ℝ),(5351190872493155714400785986213641125038590799202048/2177364051408955338628984497744140625:ℝ),(5349465972639437880887803690974270433278377295085568/2177364051408955338628984497744140625:ℝ),(356516075503838912994721380464416892106839255154688/435472810281791067725796899548828125:ℝ)]]
theorem admission45_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503933666255198534894895328257336759339/4870680933483086406737548903907328000000000:ℝ) admission45_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission45_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_09_coefficients]
def admission45_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(65764118850938490148269702076303436324864/13833650542458603515625:ℝ),(4382542132458702679335197938869013274624/307414456499080078125:ℝ),(21904048593556524102130020665517200637952/1537072282495400390625:ℝ),(65686160232425380860738793316852644708352/13833650542458603515625:ℝ)],
![(43805168788969006758878991100013453705216/4611216847486201171875:ℝ),(394090623122169253982131232781332366688256/13833650542458603515625:ℝ),(393934731089208190272102135325821730029568/13833650542458603515625:ℝ),(8750640955612371281728025056301981630464/922243369497240234375:ℝ)],
![(65651374944730916385849848150142326800384/13833650542458603515625:ℝ),(196876189451110495797322349746974014439424/13833650542458603515625:ℝ),(196798256040077870707886376992725528477696/13833650542458603515625:ℝ),(65573441533818109593538875395893840838656/13833650542458603515625:ℝ)]]
theorem admission45_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477109581216195580735357910423/211253605916986174341120000000000:ℝ) admission45_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission45_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_10_coefficients]
def admission45_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(28936259472303449723863251869917163978842/24773564318253002963956445841:ℝ),(173595392732955249399332368800787253788672/74320692954759008891869337523:ℝ),(3214319078729820913806614481718875258880/2752618257583666995995160649:ℝ)],
![(28929020810027101756821895485040513254664/24773564318253002963956445841:ℝ),(173551963594150828099273277838640756424704/74320692954759008891869337523:ℝ),(9640544663735894528237051478559833456640/8257854772751000987985481947:ℝ)]]
theorem admission45_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (35913827507704103470731718385815/180395590129003200249538848292864:ℝ) admission45_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission45_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_11_coefficients]
def admission45_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission45_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission45_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission45_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_12_coefficients]
def admission45_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission45_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission45_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission45_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_13_coefficients]
def admission45_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission45_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission45_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission45_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_14_coefficients]
theorem admission45_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission45_00_pos hδ hp
 · exact admission45_01_pos hδ hp
 · exact admission45_02_pos hδ hp
 · exact admission45_03_pos hδ hp
 · exact admission45_04_pos hδ hp
 · exact admission45_05_pos hδ hp
 · exact admission45_06_pos hδ hp
 · exact admission45_07_pos hδ hp
 · exact admission45_08_pos hδ hp
 · exact admission45_09_pos hδ hp
 · exact admission45_10_pos hδ hp
 · exact admission45_11_pos hδ hp
 · exact admission45_12_pos hδ hp
 · exact admission45_13_pos hδ hp
 · exact admission45_14_pos hδ hp
#print axioms admission45_all
end
end LewkoStage2Finite
