/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def admission22_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(86091951164903/355426639143:ℝ), (767628720731840/3198839752287:ℝ)]]
theorem admission22_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission22_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission22_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_00_coefficients]
def admission22_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(62989219620608/355426639143:ℝ), (562902976585472/3198839752287:ℝ)]]
theorem admission22_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission22_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission22_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_01_coefficients]
def admission22_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(31997347187012/355426639143:ℝ), (286047944308352/3198839752287:ℝ)]]
theorem admission22_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2234749564909/6397679504574:ℝ) admission22_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission22_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_02_coefficients]
def admission22_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(73573563547573322752/3198839752287:ℝ), (1315449024550793110528/28789557770583:ℝ), (653298328622633205760/28789557770583:ℝ)],
![(73324439707541086976/3198839752287:ℝ), (1310966569303423597312/28789557770583:ℝ), (651058023935553814528/28789557770583:ℝ)]]
theorem admission22_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (39737428218722767/78614685752205312:ℝ) admission22_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission22_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_03_coefficients]
def admission22_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11829449896983653744/3198839752287:ℝ), (23398907843369452544/3198839752287:ℝ), (11570067251384221696/3198839752287:ℝ)],
![(11903499001883552084/3198839752287:ℝ), (7848727764610638080/1066279917429:ℝ), (3881098508375719936/1066279917429:ℝ)]]
theorem admission22_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (176545215627811/2183741270894592:ℝ) admission22_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission22_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_04_coefficients]
def admission22_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2475099874869724292414/1199564907107625:ℝ), (24776422757224237177036/5997824535538125:ℝ), (4133457733001190928322/1999274845179375:ℝ)],
![(12119927213366207598778/5997824535538125:ℝ), (24266913461290946215228/5997824535538125:ℝ), (53984152546508857862/26656997935725:ℝ)]]
theorem admission22_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6059963606683103799389/134169063683763732480000:ℝ) admission22_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission22_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_05_coefficients]
def admission22_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(4720150145675171738797161003029813248/3407447728350247988736212877:ℝ), (13989649006047896688146929325336221696/3407447728350247988736212877:ℝ), (13819688457613897276538005771087249408/3407447728350247988736212877:ℝ), (4550188450725158018951469448780840960/3407447728350247988736212877:ℝ)],
![(128303033314091343555401747839687168/92093181847303999695573321:ℝ), (14070493731419879854132429840591340032/3407447728350247988736212877:ℝ), (13900193429438233860638351686389661696/3407447728350247988736212877:ℝ), (4576910780495504174666370515866746880/3407447728350247988736212877:ℝ)]]
theorem admission22_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (135606183133279026119454784655/1163075491276884646821960662016:ℝ) admission22_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission22_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_06_coefficients]
def admission22_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1019616950061497834795703887081200/92093181847303999695573321:ℝ), (24976044937199232018301853631488/1136952862312395057970041:ℝ), (1003474282237285363948533977497600/92093181847303999695573321:ℝ)],
![(1011648286784432609179490639304820/92093181847303999695573321:ℝ), (223020696814440023034858154797824/10232575760811555521730369:ℝ), (995569452005219221037779661701120/92093181847303999695573321:ℝ)]]
theorem admission22_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (60764737060865430971544168805/251475781897704788502045548544:ℝ) admission22_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission22_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_07_coefficients]
def admission22_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(133752378845668451495478907106574031972878322531559/3597389915910312488108332851562500000000000:ℝ), (82294143900848274814674428198423502123902890345093/719477983182062497621666570312500000000000:ℝ), (421679044099084392051511095156519893569406570354507/3597389915910312488108332851562500000000000:ℝ), (143960478314495725023675484391204925308989191160601/3597389915910312488108332851562500000000000:ℝ)],
![(299667834480992330160897545374694495040594583906999/7194779831820624976216665703125000000000000:ℝ), (918835590682244876614579672657004501695827189205339/7194779831820624976216665703125000000000000:ℝ), (469329771600298930510538192432010831868152005315531/3597389915910312488108332851562500000000000:ℝ), (159745667661232812376634681098173669655824765166361/3597389915910312488108332851562500000000000:ℝ)]]
theorem admission22_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (133752378845668451495478907106574031972878322531559/41201792106119952548175142673448960000000000000000000:ℝ) admission22_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission22_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_08_coefficients]
def admission22_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(147845714265786651999239467984632112826398/1498912464962630203378472021484375:ℝ), (434811826597045768719535343851453693908622/1498912464962630203378472021484375:ℝ), (426104429492494880258942583662500002471424/1498912464962630203378472021484375:ℝ), (5565535805899166305574741869428730605568/59956498598505208135138880859375:ℝ)],
![(280954312665009912197645992167163614719357/2997824929925260406756944042968750:ℝ), (825667546416836165532189738690375212235173/2997824929925260406756944042968750:ℝ), (404253508518118343221212358047133610263168/1498912464962630203378472021484375:ℝ), (26379393975048104025932921605202163863552/299782492992526040675694404296875:ℝ)]]
theorem admission22_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (6440281732189478521956279688770059537/838252606325682628340151828480000000000:ℝ) admission22_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission22_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_09_coefficients]
def admission22_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5069177589668127018406219839488/281148025103349609375:ℝ), (8244135512564714387937956964352/156193347279638671875:ℝ), (72359442262076409650765127766016/1405740125516748046875:ℝ), (2612013614805235027928290476032/156193347279638671875:ℝ)],
![(16421689654336235758015713545216/468580041838916015625:ℝ), (16014950634195264444855593360384/156193347279638671875:ℝ), (46826387697718472454466019526656/468580041838916015625:ℝ), (3040646686385032975582990598144/93716008367783203125:ℝ)],
![(23914191009571184951528122017152/1405740125516748046875:ℝ), (7769160950266755583870061320832/156193347279638671875:ℝ), (13620983099430921399638957544704/281148025103349609375:ℝ), (7365556655300257648297452617728/468580041838916015625:ℝ)]]
theorem admission22_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (449557901324478616229092567/223615106139606220800000000000:ℝ) admission22_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission22_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_10_coefficients]
def admission22_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(836602753006877120247566468252944/92093181847303999695573321:ℝ), (20493881382187710313893032022016/1136952862312395057970041:ℝ), (823431924577854805423750410895360/92093181847303999695573321:ℝ)],
![(829909913294404859050238699038348/92093181847303999695573321:ℝ), (182963701539235055642126945451008/10232575760811555521730369:ℝ), (816793557124973749569125907988480/92093181847303999695573321:ℝ)]]
theorem admission22_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (24926561191558036791049984985/125737890948852394251022774272:ℝ) admission22_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission22_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_11_coefficients]
def admission22_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission22_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission22_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission22_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_12_coefficients]
def admission22_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission22_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission22_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission22_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_13_coefficients]
def admission22_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission22_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission22_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission22_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_14_coefficients]
theorem admission22_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission22_00_pos hδ hp
 · exact admission22_01_pos hδ hp
 · exact admission22_02_pos hδ hp
 · exact admission22_03_pos hδ hp
 · exact admission22_04_pos hδ hp
 · exact admission22_05_pos hδ hp
 · exact admission22_06_pos hδ hp
 · exact admission22_07_pos hδ hp
 · exact admission22_08_pos hδ hp
 · exact admission22_09_pos hδ hp
 · exact admission22_10_pos hδ hp
 · exact admission22_11_pos hδ hp
 · exact admission22_12_pos hδ hp
 · exact admission22_13_pos hδ hp
 · exact admission22_14_pos hδ hp
#print axioms admission22_all
end
end LewkoStage2Return.C30
