/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission43_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1202494501891624489/157396201727529:ℝ),(1202137105689896960/157396201727529:ℝ)]]
theorem admission43_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission43_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission43_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_00_coefficients]
def admission43_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(879989684551917568/157396201727529:ℝ),(879789684551917568/157396201727529:ℝ)]]
theorem admission43_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission43_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission43_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_01_coefficients]
def admission43_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(149239969878519210/52465400575843:ℝ),(149207894494601216/52465400575843:ℝ)]]
theorem admission43_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission43_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission43_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_02_coefficients]
def admission43_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(525746905345966246304555008/1416565815547761:ℝ),(38935913678245679940558848/52465400575843:ℝ),(525522772975667112090533888/1416565815547761:ℝ)],
![(525634505011479441604132864/1416565815547761:ℝ),(38927587843746392149147648/52465400575843:ℝ),(525410375780473146422853632/1416565815547761:ℝ)]]
theorem admission43_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15658449404849801851/30945352429246021632:ℝ) admission43_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission43_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_03_coefficients]
def admission43_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3060984749256372961952930/52465400575843:ℝ),(6119818045647758788976640/52465400575843:ℝ),(3058833456928682336583680/52465400575843:ℝ)],
![(3062207490156709636338252/52465400575843:ℝ),(6122263097587719852605440/52465400575843:ℝ),(3060055768000382109745152/52465400575843:ℝ)]]
theorem admission43_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (273481022440971345/3438372492138446848:ℝ) admission43_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission43_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_04_coefficients]
def admission43_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1128590461046273771818635844/32790875359901875:ℝ),(20315060860638719351694833132/295117878239116875:ℝ),(10157746277231025039052279286/295117878239116875:ℝ)],
![(1127176043270872320359395386/32790875359901875:ℝ),(20289603921993720761493501932/295117878239116875:ℝ),(10145019098477927977445395958/295117878239116875:ℝ)]]
theorem admission43_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1690764064906308480539093079/36053948743165640420884480000:ℝ) admission43_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission43_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_05_coefficients]
def admission43_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5665004668824901917123917992320058857064202240/8249596917978249986997496465053:ℝ),(209732982336045123495789665302524809378037760/101846875530595678851820944013:ℝ),(16981730172367777584468526582412718113942405120/8249596917978249986997496465053:ℝ),(5658363271927947545094395362574267411385548800/8249596917978249986997496465053:ℝ)],
![(5667093897738575440454528384926544311595368448/8249596917978249986997496465053:ℝ),(629431052587131727039544939925423570427117568/305540626591787036555462832039:ℝ),(16987996187031274460659586150924410544275324928/8249596917978249986997496465053:ℝ),(5660451664872207311323031301479718454338519040/8249596917978249986997496465053:ℝ)]]
theorem admission43_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41170011332199992794590037101983525/360430389077748394098578618889142272:ℝ) admission43_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission43_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_06_coefficients]
def admission43_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13238421146567393507930591592402841839230/74320692954759008891869337523:ℝ),(26470064903576677756511081504341196840960/74320692954759008891869337523:ℝ),(13231644179730285806928030229955325460480/74320692954759008891869337523:ℝ)],
![(13231962232056412231861528538963830683764/74320692954759008891869337523:ℝ),(26457148728697251420870152710415694675968/74320692954759008891869337523:ℝ),(13225186919258668163924974581323420139520/74320692954759008891869337523:ℝ)]]
theorem admission43_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (197070642102638902722671249230555/811780155580514401122924817317888:ℝ) admission43_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission43_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_07_coefficients]
def admission43_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5986585747502856594307317329069106018319675577346846833993/403215565075732470116478610693359375000000000:ℝ),(32364760985595908409674111816785437412355391557518088857883/725788017136318446209661499248046875000000000:ℝ),(486029367204420661484708806335275234180863410679857551203303/10886820257044776693144922488720703125000000000:ℝ),(162195767592171319693746357492623559378236542630499910977869/10886820257044776693144922488720703125000000000:ℝ)],
![(30222053101848216435838326880130650025394099703960010397487/2016077825378662350582393053466796875000000000:ℝ),(163384771991852057204765218900421215253241322869807846033193/3628940085681592231048307496240234375000000000:ℝ),(2453556775006834700171023861568718843507269967103817514781571/54434101285223883465724612443603515625000000000:ℝ),(32751225152980223617588531341227564321413681002728397950633/2177364051408955338628984497744140625000000000:ℝ)]]
theorem admission43_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5986585747502856594307317329069106018319675577346846833993/2421228624833403644222213726560488469299200000000000000000000:ℝ) admission43_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission43_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_08_coefficients]
def admission43_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22393989522022194398902330492400208218407310983874/435472810281791067725796899548828125:ℝ),(22379601320002685485922985381210430214755834627168/145157603427263689241932299849609375:ℝ),(67095642346019844627786187647121295827182234632192/435472810281791067725796899548828125:ℝ),(22350827908396114652573729943706874740739053453312/435472810281791067725796899548828125:ℝ)],
![(111626893546336323254638951637766817601507983231804/2177364051408955338628984497744140625:ℝ),(22311003049885229287386457866348900619347678515776/145157603427263689241932299849609375:ℝ),(334449425795080754178424167186392967809635360178176/2177364051408955338628984497744140625:ℝ),(22282254718989932062170086279026055756677453447168/435472810281791067725796899548828125:ℝ)]]
theorem admission43_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503933666255198534894895328257336759339/4870680933483086406737548903907328000000000:ℝ) admission43_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission43_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_09_coefficients]
def admission43_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2061088293258032251491500929513554030592/13833650542458603515625:ℝ),(228829278546312422275567757461639385088/512357427498466796875:ℝ),(6173516408560850997711431552395864702976/13833650542458603515625:ℝ),(76156080781421868732237612238709456896/512357427498466796875:ℝ)],
![(4115130874441686117694467829956711563264/13833650542458603515625:ℝ),(4111882351850336112073270836478255284224/4611216847486201171875:ℝ),(4108633993690797088151812819172599005184/4611216847486201171875:ℝ),(4105385800022966227023843778039742726144/13833650542458603515625:ℝ)],
![(2054041009366968116241977025087492898816/13833650542458603515625:ℝ),(410483454678301727371584410843073888256/922243369497240234375:ℝ),(6152380858709419144848628993680297951232/13833650542458603515625:ℝ),(2049170047931815924798089856121682526208/13833650542458603515625:ℝ)]]
theorem admission43_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477109581216195580735357910423/211253605916986174341120000000000:ℝ) admission43_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission43_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_10_coefficients]
def admission43_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10856582768653188685437012279679879625090/74320692954759008891869337523:ℝ),(21707623398493098026991935264288247070720/74320692954759008891869337523:ℝ),(1205671226080378869325329426469177262080/8257854772751000987985481947:ℝ)],
![(10851153063205826954681206681280393414540/74320692954759008891869337523:ℝ),(21696765405131944336284953632900563828736/74320692954759008891869337523:ℝ),(1205068082966986816029631434819979182080/8257854772751000987985481947:ℝ)]]
theorem admission43_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (35913827507704103470731718385815/180395590129003200249538848292864:ℝ) admission43_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission43_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_11_coefficients]
def admission43_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission43_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission43_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission43_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_12_coefficients]
def admission43_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission43_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission43_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission43_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_13_coefficients]
def admission43_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission43_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission43_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission43_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_14_coefficients]
theorem admission43_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission43_00_pos hδ hp
 · exact admission43_01_pos hδ hp
 · exact admission43_02_pos hδ hp
 · exact admission43_03_pos hδ hp
 · exact admission43_04_pos hδ hp
 · exact admission43_05_pos hδ hp
 · exact admission43_06_pos hδ hp
 · exact admission43_07_pos hδ hp
 · exact admission43_08_pos hδ hp
 · exact admission43_09_pos hδ hp
 · exact admission43_10_pos hδ hp
 · exact admission43_11_pos hδ hp
 · exact admission43_12_pos hδ hp
 · exact admission43_13_pos hδ hp
 · exact admission43_14_pos hδ hp
#print axioms admission43_all
end
end LewkoStage2Finite
