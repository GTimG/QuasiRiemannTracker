/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission37_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(50212613157466903/52468862730263:ℝ), (150280432884209920/157406588190789:ℝ)]]
theorem admission37_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission37_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission37_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_00_coefficients]
def admission37_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(36728115435789312/52468862730263:ℝ), (109984346307367936/157406588190789:ℝ)]]
theorem admission37_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission37_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission37_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_01_coefficients]
def admission37_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(18684834818806186/52468862730263:ℝ), (18652759434888192/52468862730263:ℝ)]]
theorem admission37_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission37_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission37_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_02_coefficients]
def admission37_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(344068128823502069186560/472219764572367:ℝ), (2060903792345962789126144/1416659293717101:ℝ), (1028700529075456581566464/1416659293717101:ℝ)],
![(343482547508756639841280/472219764572367:ℝ), (2057390693398373446743040/1416659293717101:ℝ), (1026944175872103527219200/1416659293717101:ℝ)]]
theorem admission37_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3917481139648832425/7736848622753660928:ℝ) admission37_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission37_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_03_coefficients]
def admission37_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5992879165405056044640/52468862730263:ℝ), (11952191956699049902080/52468862730263:ℝ), (5959332806333558685696/52468862730263:ℝ)],
![(6012033351257201260554/52468862730263:ℝ), (11990446536137136708608/52468862730263:ℝ), (5978433231994884194304/52468862730263:ℝ)]]
theorem admission37_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131223490119061/26864057717894656:ℝ) admission37_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission37_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_04_coefficients]
def admission37_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(573891892327821857773823/8432495795935125:ℝ), (40178765265092483693895802/295137352857729375:ℝ), (2232499436180129612541333/32793039206414375:ℝ)],
![(568200384413104183905761/8432495795935125:ℝ), (1591227301671775010774218/11805494114309175:ℝ), (442080330947258714111057/6558607841282875:ℝ)]]
theorem admission37_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (568200384413104183905761/12072431222399617204224000:ℝ) admission37_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission37_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_05_coefficients]
def admission37_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1391324108844339671105733780489829197611008/8250685723952923479064059359493:ℝ), (4160989699760917085636922022069893664669696/8250685723952923479064059359493:ℝ), (4148023317461173794284096076476442820476928/8250685723952923479064059359493:ℝ), (1378357720924449261770388967696378353418240/8250685723952923479064059359493:ℝ)],
![(1395416912590359427263344408606342692679680/8250685723952923479064059359493:ℝ), (4173255014611764937739118765019417898659840/8250685723952923479064059359493:ℝ), (4160275553289159543588851346922001866424320/8250685723952923479064059359493:ℝ), (197491063662657181301164320072703808634880/1178669389136131925580579908499:ℝ)]]
theorem admission37_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320923915348120327519809121195315/2816234060442597880853865594706944:ℝ) admission37_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission37_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_06_coefficients]
def admission37_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26080223429139104803456851435324928288/74330502017593905216793327563:ℝ), (52054109787845999439211455061163884544/74330502017593905216793327563:ℝ), (961997754371408228312105085889413120/2752981556207181674696049169:ℝ)],
![(25979103349928140380112567451913834430/74330502017593905216793327563:ℝ), (51852076600365655776672826590510679040/74330502017593905216793327563:ℝ), (958260228021594857254557515946393600/2752981556207181674696049169:ℝ)]]
theorem admission37_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (5483209007386750358130784125975/22552424908449232279110034792448:ℝ) admission37_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission37_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_07_coefficients]
def admission37_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(373455293839876971365182013524272645395290092576541609/111104664606974308260114388696289062500000000:ℝ), (39610397035406960432538909340730147825539962845714586149/3888663261244100789104003604370117187500000000:ℝ), (280055211313216202448598324181404951282793528247415008713/27220642828708705523728025230590820312500000000:ℝ), (754231805297609173241263404403206535369644109944324799/217765142629669644189824201844726562500000000:ℝ)],
![(647523282376683961736687077770314895598497384662369611/177767463371158893216183021914062500000000000:ℝ), (68617918611150092364062643148321499772914753234233883057/6221861217990561262566405766992187500000000000:ℝ), (60590022007833676644217153006114056208353411792916276597/5444128565741741104745605046118164062500000000:ℝ), (20379743065988253942682992072283433717638726451254510759/5444128565741741104745605046118164062500000000:ℝ)]]
theorem admission37_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (373455293839876971365182013524272645395290092576541609/162881160847361142609719965241887948800000000000000000000:ℝ) admission37_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission37_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_08_coefficients]
def admission37_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5709468565281961907738606754361852400285462944/435530285259339288379648403689453125:ℝ), (85215243262589733049109839598975153593112524736/2177651426296696441898242018447265625:ℝ), (12112670840053578885540547716175159160033312768/311093060899528063128320288349609375:ℝ), (5624159133989272937570548898694284540022095872/435530285259339288379648403689453125:ℝ)],
![(5574928470723910076548962773783331667490074102/435530285259339288379648403689453125:ℝ), (16640017387770772603067873121404880644880601492/435530285259339288379648403689453125:ℝ), (2476484122593558803352084178190879069999104/65150379245974463482370741015625:ℝ), (219608299508547257566854647806609874827608064/17421211410373571535185936147578125:ℝ)]]
theorem admission37_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (418869589821905627378186507809848546653/48713237802250341722877675151687680000000:ℝ) admission37_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission37_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_09_coefficients]
def admission37_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13220416200601193071680644966121472/2766912683041212890625:ℝ), (7300195789291190584017798763249664/512391237600224609375:ℝ), (3109600315153556151413537140375552/219596244685810546875:ℝ), (9271659287463408161282214009503744/1976366202172294921875:ℝ)],
![(8699231694656161794310731310088192/922304227680404296875:ℝ), (77813926894431527216417622314074112/2766912683041212890625:ℝ), (77334963475029449736862415797354496/2766912683041212890625:ℝ), (1707915456735677193558465827569664/184460845536080859375:ℝ)],
![(20602660119135239025426198715904/4427060292865940625:ℝ), (61425637255123442705327812771328/4427060292865940625:ℝ), (61043449172952526114259069394944/4427060292865940625:ℝ), (4044094437275676986871491067904/885412058573188125:ℝ)]]
theorem admission37_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1928374498975599759517427/845070185567973204295680000:ℝ) admission37_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission37_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_10_coefficients]
def admission37_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21390186394745623653417453428690480864/74330502017593905216793327563:ℝ), (42693392322436178745727293816014471168/74330502017593905216793327563:ℝ), (21303256712968691248439870802329600000/74330502017593905216793327563:ℝ)],
![(21305177222932137810246773485809450050/74330502017593905216793327563:ℝ), (42523551372893173565968430673857669120/74330502017593905216793327563:ℝ), (21218424828499418671959327504273244160/74330502017593905216793327563:ℝ)]]
theorem admission37_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (80941867174146341979825315491765/405943648352086181023980626264064:ℝ) admission37_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission37_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_11_coefficients]
def admission37_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission37_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission37_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission37_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_12_coefficients]
def admission37_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission37_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission37_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission37_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_13_coefficients]
def admission37_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission37_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission37_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission37_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission37_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission37_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission37_14_coefficients]
theorem admission37_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (1875/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission37_00_pos hδ hp
 · exact admission37_01_pos hδ hp
 · exact admission37_02_pos hδ hp
 · exact admission37_03_pos hδ hp
 · exact admission37_04_pos hδ hp
 · exact admission37_05_pos hδ hp
 · exact admission37_06_pos hδ hp
 · exact admission37_07_pos hδ hp
 · exact admission37_08_pos hδ hp
 · exact admission37_09_pos hδ hp
 · exact admission37_10_pos hδ hp
 · exact admission37_11_pos hδ hp
 · exact admission37_12_pos hδ hp
 · exact admission37_13_pos hδ hp
 · exact admission37_14_pos hδ hp
#print axioms admission37_all
end
end Record1252270103Finite
