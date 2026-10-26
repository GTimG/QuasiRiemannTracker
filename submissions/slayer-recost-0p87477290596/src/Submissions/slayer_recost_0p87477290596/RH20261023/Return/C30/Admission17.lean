/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def admission17_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(86091951164903/355426639143:ℝ), (767628720731840/3198839752287:ℝ)]]
theorem admission17_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission17_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission17_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_00_coefficients]
def admission17_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(62989219620608/355426639143:ℝ), (562902976585472/3198839752287:ℝ)]]
theorem admission17_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission17_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission17_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_01_coefficients]
def admission17_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31997347187012/355426639143:ℝ), (286047944308352/3198839752287:ℝ)]]
theorem admission17_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission17_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission17_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_02_coefficients]
def admission17_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37347662333650167296/3198839752287:ℝ), (667813266860096738816/28789557770583:ℝ), (331689849857245233152/28789557770583:ℝ)],
![(12366179497872643840/1066279917429:ℝ), (663330811612727225600/28789557770583:ℝ), (329449545170165841920/28789557770583:ℝ)]]
theorem admission17_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (20108004465952505/39307342876102656:ℝ) admission17_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission17_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_03_coefficients]
def admission17_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5764985076378109736/3198839752287:ℝ), (11403265214806631936/3198839752287:ℝ), (5638577078206234624/3198839752287:ℝ)],
![(5839034181278008076/3198839752287:ℝ), (3850180221756364544/1066279917429:ℝ), (1903935117316390912/1066279917429:ℝ)]]
theorem admission17_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (172075716497993/2183741270894592:ℝ) admission17_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission17_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_04_coefficients]
def admission17_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6762787049384741923442/5997824535538125:ℝ), (13531745998906833914228/5997824535538125:ℝ), (752076757993209021754/666424948393125:ℝ)],
![(260288595536093122406/239912981421525:ℝ), (2604447340594708590484/1199564907107625:ℝ), (434316796393320095318/399854969035875:ℝ)]]
theorem admission17_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (130144297768046561203/2683381273675274649600:ℝ) admission17_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission17_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_05_coefficients]
def admission17_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2305271384593446289817567967532270592/3407447728350247988736212877:ℝ), (6831779580158092614420869004163073024/3407447728350247988736212877:ℝ), (6748158320131679236157025626849411072/3407447728350247988736212877:ℝ), (2221649565821886698045932590218608640/3407447728350247988736212877:ℝ)],
![(2332333471539654262570271634570882560/3407447728350247988736212877:ℝ), (6912624305530075780406369519418191360/3407447728350247988736212877:ℝ), (6828663291956015820257371542151823360/3407447728350247988736212877:ℝ), (2248371895592232853760833657304514560/3407447728350247988736212877:ℝ)]]
theorem admission17_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (132420633186214369418974673165/1163075491276884646821960662016:ℝ) admission17_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission17_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_06_coefficients]
def admission17_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(527849675232894069768884882002280/92093181847303999695573321:ℝ), (116372932053005304580943552296448/10232575760811555521730369:ℝ), (519523009140791503523464199290880/92093181847303999695573321:ℝ)],
![(519881011955828844152671634225900/92093181847303999695573321:ℝ), (114609224432652239451085024410880/10232575760811555521730369:ℝ), (511618178908725360612709883494400/92093181847303999695573321:ℝ)]]
theorem admission17_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (31226695490034506873334343475/125737890948852394251022774272:ℝ) admission17_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission17_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_07_coefficients]
def admission17_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(69426225266357597155599444783481169783202444843797/7194779831820624976216665703125000000000000:ℝ), (44174514709425084644333793054063635072269788354223/1438955966364124995243333140625000000000000:ℝ), (233451684827300647398932703921870973748470723729601/7194779831820624976216665703125000000000000:ℝ), (82005117119909880539881373058547832723980476802283/7194779831820624976216665703125000000000000:ℝ)],
![(50794651028006512162769587972513800439020191843839/3597389915910312488108332851562500000000000:ℝ), (79191681305221887922376088985771913954536806881381/1798694957955156244054166425781250000000000:ℝ), (328753139829729724316986898472852850345961593651649/7194779831820624976216665703125000000000000:ℝ), (113575495813384055245799766472485321417651624813803/7194779831820624976216665703125000000000000:ℝ)]]
theorem admission17_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (69426225266357597155599444783481169783202444843797/41201792106119952548175142673448960000000000000000000:ℝ) admission17_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission17_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_08_coefficients]
def admission17_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(90724594639602493959303728854529248092557/1498912464962630203378472021484375:ℝ), (267300644173780781247583891724827107555893/1498912464962630203378472021484375:ℝ), (262438415964500741354446516066751479506176/1498912464962630203378472021484375:ℝ), (17172480887255302643303627092940177133568/299782492992526040675694404296875:ℝ)],
![(6668482936505663844710980556278315410067/119912997197010416270277761718750:ℝ), (98129036314061238117657366887424407905943/599564985985052081351388808593750:ℝ), (48117498998024840863343258090277017459584/299782492992526040675694404296875:ℝ), (3144839166561515028272567870199737593856/59956498598505208135138880859375:ℝ)]]
theorem admission17_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (767782999648807379949357390185482811/83825260632568262834015182848000000000:ℝ) admission17_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission17_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_09_coefficients]
def admission17_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7900790708746973183940611085824/1405740125516748046875:ℝ), (515624579362218089966747935232/31238669455927734375:ℝ), (22704652892324147694073680913408/1405740125516748046875:ℝ), (822482262730492425501181657088/156193347279638671875:ℝ)],
![(1008543199428850850451803244032/93716008367783203125:ℝ), (328854597937696967902527977984/10412889818642578125:ℝ), (2893859182702986675639093871616/93716008367783203125:ℝ), (942711381120689814968145313792/93716008367783203125:ℝ)],
![(288894691103556093693940726144/56229605020669921875:ℝ), (31373892011874261275421398912/2082577963728515625:ℝ), (827537180571850069042983362816/56229605020669921875:ℝ), (89778967408110786100182106112/18743201673556640625:ℝ)]]
theorem admission17_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5479673303717699346934943/2236151061396062208000000000:ℝ) admission17_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission17_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_10_coefficients]
def admission17_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(433455592310785757167501430897816/92093181847303999695573321:ℝ), (95565802478874967867361597290496/10232575760811555521730369:ℝ), (426652289057909778384780336988160/92093181847303999695573321:ℝ)],
![(426762752598313495970173661683220/92093181847303999695573321:ℝ), (94084571578420630684451254543360/10232575760811555521730369:ℝ), (420013921605028722530155834081280/92093181847303999695573321:ℝ)]]
theorem admission17_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12817807666169089432682978335/62868945474426197125511387136:ℝ) admission17_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission17_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_11_coefficients]
def admission17_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission17_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission17_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission17_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_12_coefficients]
def admission17_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission17_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission17_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission17_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_13_coefficients]
def admission17_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission17_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission17_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission17_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_14_coefficients]
theorem admission17_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission17_00_pos hδ hp
 · exact admission17_01_pos hδ hp
 · exact admission17_02_pos hδ hp
 · exact admission17_03_pos hδ hp
 · exact admission17_04_pos hδ hp
 · exact admission17_05_pos hδ hp
 · exact admission17_06_pos hδ hp
 · exact admission17_07_pos hδ hp
 · exact admission17_08_pos hδ hp
 · exact admission17_09_pos hδ hp
 · exact admission17_10_pos hδ hp
 · exact admission17_11_pos hδ hp
 · exact admission17_12_pos hδ hp
 · exact admission17_13_pos hδ hp
 · exact admission17_14_pos hδ hp
#print axioms admission17_all
end
end RH20261023Return.C30
