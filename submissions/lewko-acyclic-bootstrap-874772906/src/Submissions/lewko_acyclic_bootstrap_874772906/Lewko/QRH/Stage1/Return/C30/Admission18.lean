/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission18_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(86091951164903/355426639143:ℝ), (767628720731840/3198839752287:ℝ)]]
theorem admission18_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission18_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission18_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_00_coefficients]
def admission18_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(62989219620608/355426639143:ℝ), (562902976585472/3198839752287:ℝ)]]
theorem admission18_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission18_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission18_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_01_coefficients]
def admission18_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31997347187012/355426639143:ℝ), (286047944308352/3198839752287:ℝ)]]
theorem admission18_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission18_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission18_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_02_coefficients]
def admission18_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37222999865122342144/3198839752287:ℝ), (665571116299806616832/28789557770583:ℝ), (330569697513705537536/28789557770583:ℝ)],
![(36973876025090106368/3198839752287:ℝ), (661088661052437103616/28789557770583:ℝ), (328329392826626146304/28789557770583:ℝ)]]
theorem admission18_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (5009908948160189/9826835719025664:ℝ) admission18_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission18_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_03_coefficients]
def admission18_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5802420044406539020/3198839752287:ℝ), (11477312391526155520/3198839752287:ℝ), (5675191215077703680/3198839752287:ℝ)],
![(5876469149306437360/3198839752287:ℝ), (11624587841988617216/3198839752287:ℝ), (5748419488820641792/3198839752287:ℝ)]]
theorem admission18_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (346386182560895/4367482541789184:ℝ) admission18_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission18_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_04_coefficients]
def admission18_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6635000968893534991796/5997824535538125:ℝ), (13277808863955956815712/5997824535538125:ℝ), (2214179342130336120472/1999274845179375:ℝ)],
![(6379428807911121128504/5997824535538125:ℝ), (12768299568022665853904/5997824535538125:ℝ), (85181322004692381272/79970993807175:ℝ)]]
theorem admission18_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (797428600988890141063/16771132960470466560000:ℝ) admission18_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission18_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_05_coefficients]
def admission18_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2318972306654481184712821101027929600/3407447728350247988736212877:ℝ), (6872540810874556546834017918789332480/3407447728350247988736212877:ℝ), (6788579797300496586685019941522964480/3407447728350247988736212877:ℝ), (2235010730707059775903383123761561600/3407447728350247988736212877:ℝ)],
![(2346034393600689157465524768066541568/3407447728350247988736212877:ℝ), (6953385536246539712819518434044450816/3407447728350247988736212877:ℝ), (6869084769124833170785365856825376768/3407447728350247988736212877:ℝ), (2261733060477405931618284190847467520/3407447728350247988736212877:ℝ)]]
theorem admission18_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (266434041345961067188189402075/2326150982553769293643921324032:ℝ) admission18_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission18_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_06_coefficients]
def admission18_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(523833427071861915608048792124140/92093181847303999695573321:ℝ), (115487538902881810885613281721600/10232575760811555521730369:ℝ), (515570594024758432068087041392640/92093181847303999695573321:ℝ)],
![(515864763794796689991835544347760/92093181847303999695573321:ℝ), (113723831282528745755754753836032/10232575760811555521730369:ℝ), (507665763792692289157332725596160/92093181847303999695573321:ℝ)]]
theorem admission18_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7746364803965641619221995935/31434472737213098562755693568:ℝ) admission18_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission18_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_07_coefficients]
def admission18_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6840621092894824859245544829140350826449713141259/575582386545649998097333256250000000000000:ℝ), (107408844014561764373837903680307203670356127703881/2877911932728249990486666281250000000000000:ℝ), (112203409858098633424830920692213281481481874154331/2877911932728249990486666281250000000000000:ℝ), (7799516593484507332866392071336968469618612431349/575582386545649998097333256250000000000000:ℝ)],
![(235341680901681475821018083051601632850918706219237/14389559663641249952433331406250000000000000:ℝ), (728832523420333078804860299747074979265377210028223/14389559663641249952433331406250000000000000:ℝ), (751619959295351320960262992563030160602391110615751/14389559663641249952433331406250000000000000:ℝ), (51625734444812206546699317722259837825561521361353/2877911932728249990486666281250000000000000:ℝ)]]
theorem admission18_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6840621092894824859245544829140350826449713141259/3296143368489596203854011413875916800000000000000000:ℝ) admission18_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission18_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_08_coefficients]
def admission18_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(34790699736976046725495690523333066214623/599564985985052081351388808593750:ℝ), (102473891477404420623479730113248875398807/599564985985052081351388808593750:ℝ), (50289926579696432116254439703189251206016/299782492992526040675694404296875:ℝ), (16448338360031438892333233221969432551424/299782492992526040675694404296875:ℝ)],
![(79608191409158420913322754407282360069838/1498912464962630203378472021484375:ℝ), (234206675304883365605258850776856100705982/1498912464962630203378472021484375:ℝ), (229598711924105623543541972900579863821824/1498912464962630203378472021484375:ℝ), (15000053305583711390392445480027943387136/299782492992526040675694404296875:ℝ)]]
theorem admission18_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (915530597264630822167507658693111779/104781575790710328542518978560000000000:ℝ) admission18_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission18_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_09_coefficients]
def admission18_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7561733978699570215844893465984/1405740125516748046875:ℝ), (2466164134594125553488730022528/156193347279638671875:ℝ), (21706529617628255346563710007552/1405740125516748046875:ℝ), (2357596418906325610336677756928/468580041838916015625:ℝ)],
![(14440054521144182359609774578688/1405740125516748046875:ℝ), (4705593101903935779752750212096/156193347279638671875:ℝ), (41382030523304214010690180081664/1405740125516748046875:ℝ), (4490584302614741450841734250496/468580041838916015625:ℝ)],
![(2291110179115908304425653897216/468580041838916015625:ℝ), (745924931982005251072148371456/52064449093212890625:ℝ), (1310713038116770529979221798912/93716008367783203125:ℝ), (710450650499737898224142516224/156193347279638671875:ℝ)]]
theorem admission18_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2710154153822852700134821/1164662011143782400000000000:ℝ) admission18_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission18_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_10_coefficients]
def admission18_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(430081936324754023897485913136660/92093181847303999695573321:ℝ), (94822167962074081334965088199680/10232575760811555521730369:ℝ), (423333105331469250457468085534720/92093181847303999695573321:ℝ)],
![(423389096612281762700158143922064/92093181847303999695573321:ℝ), (93340937061619744152054745452544/10232575760811555521730369:ℝ), (416694737878588194602843582627840/92093181847303999695573321:ℝ)]]
theorem admission18_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3179128554371552998373745595/15717236368606549281377846784:ℝ) admission18_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission18_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_11_coefficients]
def admission18_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission18_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission18_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission18_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_12_coefficients]
def admission18_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission18_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission18_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission18_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_13_coefficients]
def admission18_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission18_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission18_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission18_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_14_coefficients]
theorem admission18_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission18_00_pos hδ hp
 · exact admission18_01_pos hδ hp
 · exact admission18_02_pos hδ hp
 · exact admission18_03_pos hδ hp
 · exact admission18_04_pos hδ hp
 · exact admission18_05_pos hδ hp
 · exact admission18_06_pos hδ hp
 · exact admission18_07_pos hδ hp
 · exact admission18_08_pos hδ hp
 · exact admission18_09_pos hδ hp
 · exact admission18_10_pos hδ hp
 · exact admission18_11_pos hδ hp
 · exact admission18_12_pos hδ hp
 · exact admission18_13_pos hδ hp
 · exact admission18_14_pos hδ hp
#print axioms admission18_all
end
end LewkoStage1Return.C30
