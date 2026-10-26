/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission15_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission15_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission15_00_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission15_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_00_coefficients]
def admission15_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission15_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission15_01_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission15_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_01_coefficients]
def admission15_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission15_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission15_02_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission15_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_02_coefficients]
def admission15_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(34392790366400136669587747840/9190091093611410197319:ℝ), (45529591838961540638183699456/9190091093611410197319:ℝ), (3714872570581567509531983872/3063363697870470065773:ℝ)],
![(23244665678396496705033850880/9190091093611410197319:ℝ), (23236836812009347905033850880/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission15_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (6183829733376699872211465/6273768853238722694703104:ℝ) admission15_03_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission15_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_03_coefficients]
def admission15_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1214370097168579185968049461237/1914602311169043791108125:ℝ), (633856:ℝ), (0:ℝ)],
![(1886447809996712527421136092948/1914602311169043791108125:ℝ), (2555774489607235023467038437376/1914602311169043791108125:ℝ), (670115887146116250684156018688/1914602311169043791108125:ℝ)]]
theorem admission15_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4747029123040534505922232539/31368844266193613473515520000:ℝ) admission15_04_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission15_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_04_coefficients]
def admission15_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1252476954397322847107673892191/1914602311169043791108125:ℝ), (2509347018797959623649429635944/1914602311169043791108125:ℝ), (1256489062732903493110337962516/1914602311169043791108125:ℝ)],
![(0:ℝ), (1307626629678297453881777416/382920462233808758221625:ℝ), (1231303193815733406231042564/382920462233808758221625:ℝ)]]
theorem admission15_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (38953639023119020052348934483069/411157715565852930520062623744000:ℝ) admission15_05_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission15_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_05_coefficients]
def admission15_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(331877107438918087807590865461597639967481918527835077632/217009558988083564045804464859904678128274108125:ℝ), (1989939683662399867637421952255515412625152441199244735488/651028676964250692137413394579714034384822324375:ℝ), (994308858722466144210750292407241097814341885615739502592/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(6605755899254354817180471529646521822630067229351407616/3338608599816670216089299459383148894281140125:ℝ), (573277917352788961810991184630013355410058891803844841472/130205735392850138427482678915942806876964464875:ℝ), (373947377966040934691050786105197778305250072989043523584/130205735392850138427482678915942806876964464875:ℝ), (19431280349368122722021615713412780862074867709967859712/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission15_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (154215175982089757211154897918836933736321000502529/711096922892152222665292070452935649290728597504000:ℝ) admission15_06_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission15_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_06_coefficients]
def admission15_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16141747119835787724408289361459524439605403206022831/5865123215894150379616336888105531841304705625:ℝ), (70741274406456858196333357748762474385234540471387136/17595369647682451138849010664316595523914116875:ℝ), (1488696021364448447507099824504615349153329177165824/1173024643178830075923267377621106368260941125:ℝ)],
![(1736300033439414091618213857932912668806537121957708/1173024643178830075923267377621106368260941125:ℝ), (5206024199928852697940496536452683864791498806120448/3519073929536490227769802132863319104782823375:ℝ), (0:ℝ)]]
theorem admission15_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (441063147198888763769981713752206645142524335581/960941787692097598196340635747210336879362969600:ℝ) admission15_07_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission15_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_07_coefficients]
def admission15_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (3142723278255802977997743344829311760977084941010700762370323214762695225251/41328184405061733503228218062216022168507642596556800000000000000000:ℝ), (12571941020016752583894603103158100527327168791232105242029931450487732737257/82656368810123467006456436124432044337015285193113600000000000000000:ℝ), (59871255535963794141195245599531648727849466136097449875381703663260402731/787203512477366352442442248804114707971574144696320000000000000000:ℝ)],
![(1490320924522130047935770984899358453304744055951065920100322615647920935737/5510424587341564467097095741628802955801019012874240000000000000000:ℝ), (14648911099033292800703741393324450346307232504815727961676630734304796424377/16531273762024693401291287224886408867403057038622720000000000000000:ℝ), (2269309466678719970239542822204116925023615657272958187480606781103308608899/2361610537432099057327326746412344123914722434088960000000000000000:ℝ), (1902405136918950621587464462860893611911905018165742147622796065880708881709/5510424587341564467097095741628802955801019012874240000000000000000:ℝ)]]
theorem admission15_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (100077354051749345063770692151409451840420259397060499336539939026274127030393/24235103631059266526881478929281612253996554387219521291115560960000000000000000:ℝ) admission15_08_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission15_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_08_coefficients]
def admission15_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(73767059164353069739248341262205084681094721620860477727/146628080397353759490408422202638296032617640625:ℝ), (2880665363322194100586644706448017797303400817018903294584/2199421205960306392356126333039574440489264609375:ℝ), (2442040801816523750547769184277539103445556926085183954944/2199421205960306392356126333039574440489264609375:ℝ), (44525439605281188336183475066600291420135420150495051776/146628080397353759490408422202638296032617640625:ℝ)],
![(29046909085502285691500974081371623576991175667978809916/146628080397353759490408422202638296032617640625:ℝ), (174236449065596208967582667081211187706722826677484412512/439884241192061278471225266607914888097852921875:ℝ), (87095668098541009413079884376168299894992689429765259264/439884241192061278471225266607914888097852921875:ℝ), (0:ℝ)]]
theorem admission15_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (353688370230972106367598316296778813733250747257511/15375068603073561571141450171955365390069807513600000:ℝ) admission15_09_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission15_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_09_coefficients]
def admission15_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3503768088654356832637248915416687104/17231420800521394119973125:ℝ), (3006230161350412376545198353738282496/5743806933507131373324375:ℝ), (7526902380192970137115292802631991296/17231420800521394119973125:ℝ), (2011980601673226783997548256833830912/17231420800521394119973125:ℝ)],
![(998355845791637500175836960312446976/3446284160104278823994625:ℝ), (799834891485305139038713566021873664/1148761386701426274664875:ℝ), (601423531667224044461953501629513728/1148761386701426274664875:ℝ), (403122013486877192346023967135367168/3446284160104278823994625:ℝ)],
![(59374632680680775339612039789879296/689256832020855764798925:ℝ), (39572170534190405091675340032335872/229752277340285254932975:ℝ), (11868370833402984754181676061425664/137851366404171152959785:ℝ), (0:ℝ)]]
theorem admission15_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5419865130643122797006391329/1284867861143290407875195699200:ℝ) admission15_10_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission15_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_10_coefficients]
def admission15_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(41087459205586507350853062599650494564786568306363379/17595369647682451138849010664316595523914116875:ℝ), (20035927167891862341598397223214466085114595955454976/5865123215894150379616336888105531841304705625:ℝ), (6344748987957489039113815740587195252719181685325824/5865123215894150379616336888105531841304705625:ℝ)],
![(4401789923566215166692334619014047904252352530119196/3519073929536490227769802132863319104782823375:ℝ), (1466336900218336955621398414339338922924762209947648/1173024643178830075923267377621106368260941125:ℝ), (0:ℝ)]]
theorem admission15_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1835435545348457508771098665331888720247132164063/4804708938460487990981703178736051684396814848000:ℝ) admission15_11_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission15_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_11_coefficients]
def admission15_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission15_12_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission15_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_12_coefficients]
def admission15_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission15_13_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission15_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_13_coefficients]
def admission15_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission15_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission15_14_coefficients (1857/4096:ℝ) (465/1024:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission15_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_14_coefficients]
theorem admission15_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission15_00_pos hδ hp
 · exact admission15_01_pos hδ hp
 · exact admission15_02_pos hδ hp
 · exact admission15_03_pos hδ hp
 · exact admission15_04_pos hδ hp
 · exact admission15_05_pos hδ hp
 · exact admission15_06_pos hδ hp
 · exact admission15_07_pos hδ hp
 · exact admission15_08_pos hδ hp
 · exact admission15_09_pos hδ hp
 · exact admission15_10_pos hδ hp
 · exact admission15_11_pos hδ hp
 · exact admission15_12_pos hδ hp
 · exact admission15_13_pos hδ hp
 · exact admission15_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
