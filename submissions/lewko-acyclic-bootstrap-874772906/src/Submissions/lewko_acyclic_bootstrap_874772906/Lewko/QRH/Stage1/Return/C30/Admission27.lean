/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission27_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(103152429843767/3198839752287:ℝ), (95953590091480/3198839752287:ℝ)]]
theorem admission27_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission27_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission27_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_00_coefficients]
def admission27_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74362872073184/3198839752287:ℝ), (70362872073184/3198839752287:ℝ)]]
theorem admission27_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission27_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission27_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_01_coefficients]
def admission27_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(37684173413300/3198839752287:ℝ), (35755993038544/3198839752287:ℝ)]]
theorem admission27_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission27_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission27_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_02_coefficients]
def admission27_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(719840971585000064/28789557770583:ℝ), (456380169044469376/9596519256861:ℝ), (650019535548408064/28789557770583:ℝ)],
![(684641476698043232/28789557770583:ℝ), (432966750503611936/9596519256861:ℝ), (615014774812792576/28789557770583:ℝ)]]
theorem admission27_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2402401464112471/4913417859512832:ℝ) admission27_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission27_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_03_coefficients]
def admission27_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13527738821292880/3198839752287:ℝ), (24931092986131840/3198839752287:ℝ), (11441917772334080/3198839752287:ℝ)],
![(14776221650974228/3198839752287:ℝ), (27321839412671840/3198839752287:ℝ), (12586109549567488/3198839752287:ℝ)]]
theorem admission27_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (11173747824545/136483829430912:ℝ) admission27_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission27_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_04_coefficients]
def admission27_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4475216698664874481/1999274845179375:ℝ), (27161957909185275886/5997824535538125:ℝ), (13701486049137302443/5997824535538125:ℝ)],
![(3084057029263301959/1999274845179375:ℝ), (19022425051072604476/5997824535538125:ℝ), (9733691111026681099/5997824535538125:ℝ)]]
theorem admission27_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (3084057029263301959/87349650835783680000:ℝ) admission27_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission27_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_05_coefficients]
def admission27_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(735116891783811834161969349495040/3407447728350247988736212877:ℝ), (675152573045796113949317314630400/1135815909450082662912070959:ℝ), (1852380324063778868553852660674560/3407447728350247988736212877:ℝ), (561966932405499307907870066278400/3407447728350247988736212877:ℝ)],
![(792814926395595515811538641596992/3407447728350247988736212877:ℝ), (730939067656544873014256978748608/1135815909450082662912070959:ℝ), (2014237451832183952127768507579392/3407447728350247988736212877:ℝ), (614158982738206643288536212930560/3407447728350247988736212877:ℝ)]]
theorem admission27_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (8574934881675709654355927525/72692218204805290426372541376:ℝ) admission27_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission27_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_06_coefficients]
def admission27_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1148233128759642301342311024080/92093181847303999695573321:ℝ), (2168702774146860560046331173760/92093181847303999695573321:ℝ), (1022412938001610498005549525760/92093181847303999695573321:ℝ)],
![(1016631715549163916718697314868/92093181847303999695573321:ℝ), (1913713314514131050682993882976/92093181847303999695573321:ℝ), (898899965625577015025013341440/92093181847303999695573321:ℝ)]]
theorem admission27_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3511327990724910214941458365/15717236368606549281377846784:ℝ) admission27_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission27_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_07_coefficients]
def admission27_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2915808441777677991686888552594482456221874129/639535985050722220108148062500000000000000:ℝ), (30928126857381076569095697244378403518155367757/1918607955152166660324444187500000000000000:ℝ), (106895597782592568920085825444580480207552409909/5755823865456499980973332562500000000000000:ℝ), (40330695615233813295714717543378942009083173799/5755823865456499980973332562500000000000000:ℝ)],
![(92432104467605573608054052740150519351472060011/6395359850507222201081480625000000000000000:ℝ), (170510852453744745731315399901347857333989500833/3837215910304333320648888375000000000000000:ℝ), (1311303672166673364289079867185150449575518699033/28779119327282499904866662812500000000000000:ℝ), (89659412323787211273712207252656268092944342567/5755823865456499980973332562500000000000000:ℝ)]]
theorem admission27_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2915808441777677991686888552594482456221874129/894136113414061470229495283712000000000000000000:ℝ) admission27_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission27_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_08_coefficients]
def admission27_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(23967203604889755612133618405582037849/1199129971970104162702777617187500:ℝ), (21772733559421291802698401707107109587/399709990656701387567592539062500:ℝ), (588242197060248306913210032226835504/11991299719701041627027776171875:ℝ), (4369292825800577732977055899392314872/299782492992526040675694404296875:ℝ)],
![(220409781073581148689594295470362711389/23982599439402083254055552343750000:ℝ), (37545553485436278208951753063869631987/1598839962626805550270370156250000:ℝ), (29121217839560513758567089928599017266/1498912464962630203378472021484375:ℝ), (1540611078832359955748954840912843848/299782492992526040675694404296875:ℝ)]]
theorem admission27_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (192576384854044994468619355114105481/52390787895355164271259489280000000000:ℝ) admission27_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission27_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_09_coefficients]
def admission27_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(117795976515576291932644064/468580041838916015625:ℝ), (950944894002690185216476576/1405740125516748046875:ℝ), (842753746174146305539156576/1405740125516748046875:ℝ), (81748198072728332040204064/468580041838916015625:ℝ)],
![(169807407323106791768484128/468580041838916015625:ℝ), (1331304157610986754853659392/1405740125516748046875:ℝ), (1135780587977012523040961632/1405740125516748046875:ℝ), (104666352861782047830918208/468580041838916015625:ℝ)],
![(597264273384035556350492/5784938788134765625:ℝ), (23267256861531910564278088/93716008367783203125:ℝ), (87663281762758447468361324/468580041838916015625:ℝ), (6574324897651924903786912/156193347279638671875:ℝ)]]
theorem admission27_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (205447653051622653243341/291165502785945600000000000:ℝ) admission27_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission27_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_10_coefficients]
def admission27_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(942610884875288237434671013040/92093181847303999695573321:ℝ), (1780538331252831140516443363840/92093181847303999695573321:ℝ), (839788032781934192015805836800/92093181847303999695573321:ℝ)],
![(831964432368873966828965894060/92093181847303999695573321:ℝ), (1566296448559432777941417784192/92093181847303999695573321:ℝ), (736063541330667694287297978880/92093181847303999695573321:ℝ)]]
theorem admission27_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1437624104161460340404878865/7858618184303274640688923392:ℝ) admission27_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission27_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_11_coefficients]
def admission27_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission27_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission27_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission27_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_12_coefficients]
def admission27_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission27_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission27_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission27_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_13_coefficients]
def admission27_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission27_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission27_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission27_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission27_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission27_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission27_14_coefficients]
theorem admission27_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
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
end LewkoStage1Return.C30
