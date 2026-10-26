/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission08_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission08_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]
def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission08_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission08_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]
def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission08_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission08_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]
def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(134947371892041551816895104/9190091093611410197319:ℝ), (178001201082235176069223040/9190091093611410197319:ℝ), (14511220978834248084109312/3063363697870470065773:ℝ)],
![(91206360942964817817195584/9190091093611410197319:ℝ), (90713899992805457817195584/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1540643265505246410404877/1568442213309680673675776:ℝ) admission08_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission08_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]
def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4704683605202731719738894874/1914602311169043791108125:ℝ), (2432:ℝ), (0:ℝ)],
![(1489226250532411410688138469/382920462233808758221625:ℝ), (10014127737006966511075848896/1914602311169043791108125:ℝ), (2617640184164516604234984448/1914602311169043791108125:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (145708486813845162540423939/980276383318550421047360000:ℝ) admission08_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission08_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]
def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5018714029995632797561153731/1914602311169043791108125:ℝ), (10006274882718656805794859026/1914602311169043791108125:ℝ), (4964171412700625348469770421/1914602311169043791108125:ℝ)],
![(0:ℝ), (104064853506370088197790702/1914602311169043791108125:ℝ), (16011980380886924319592561/382920462233808758221625:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (186304561370732433228741746913/2007606033036391262304993280000:ℝ) admission08_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission08_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]
def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(81714229473768902049167225347665448764578659962913664/217009558988083564045804464859904678128274108125:ℝ), (485122967647736341178385564371624531127478589611780736/651028676964250692137413394579714034384822324375:ℝ), (240010812860000749492653821103599095144142609723039744/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(106793333817660018036147927500244963612762408155947712/217009558988083564045804464859904678128274108125:ℝ), (706664422636323627798456206537301908966424401913985088/651028676964250692137413394579714034384822324375:ℝ), (457475232269261889763031653951826052539162132438700032/651028676964250692137413394579714034384822324375:ℝ), (4743964929044951836431058523782417202654996999503872/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (4744574990512729128831874112474478493526419729209/22221778840379756958290377201654239040335268672000:ℝ) admission08_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission08_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]
def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(64061508702221799841788268454707474971240806010222/5865123215894150379616336888105531841304705625:ℝ), (278493261059091454265351724194253964213607120528512/17595369647682451138849010664316595523914116875:ℝ), (5815218833454876748074608689471153707630192098304/1173024643178830075923267377621106368260941125:ℝ)],
![(33928808055704037762781879285653164963634111929211/5865123215894150379616336888105531841304705625:ℝ), (100894648187998821734495942800082191317378162216256/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (547069740517076621156758434654024551271199712373/1201177234615121997745425794684012921099203712000:ℝ) admission08_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission08_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]
def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (7267506451224028894390764689905527201371801974452040845665638469698449451/330625475240493868025825744497728177348061140772454400000000000000000:ℝ), (29081020068150547923861537833774081982524732150522703067193953287429769697/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (969320219490530479185285413700843492886139905328874162401758881868858053/44083396698732515736776765933030423646408152102993920000000000000000:ℝ)],
![(891388828077251553835736682556198502152203773425797961667979681984197247/12595256199637861639079075980865835327545186315141120000000000000000:ℝ), (303059529297593514901387754029758637692188342681395866022455317780211516547/1322501900961975472103302977990912709392244563089817600000000000000000:ℝ), (162734262269229453661047775744828226073428848643349660357139460220000091841/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (3866402930754600913949148194294929568700512474104381971962548218270979269/44083396698732515736776765933030423646408152102993920000000000000000:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (99621676947152530756515040600481335259401802980347218256132226194696219/84525333534665410598777479524559194524262536227746656288768000000000000000:ℝ) admission08_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission08_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]
def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(18595139817589102653393042932326628331907778731861879/146628080397353759490408422202638296032617640625:ℝ), (719923458726600598687321134963966244336958936622185623/2199421205960306392356126333039574440489264609375:ℝ), (604036931583091128526127053875505003455823295871598528/2199421205960306392356126333039574440489264609375:ℝ), (10870468653633102621138543717431711772493999060179456/146628080397353759490408422202638296032617640625:ℝ)],
![(13904846848680456748436666244017393710629448992457019/293256160794707518980816844405276592065235281250:ℝ), (415543804876249779408123673416537680054948076384059483/4398842411920612784712252666079148880978529218750:ℝ), (103468658239268587316637178779810434379141884397584224/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (426186924721869767791814481722391908124824177636079/19218835753841951963926812714944206737587259392000000:ℝ) admission08_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission08_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]
def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18164921421654728814212214652288/5743806933507131373324375:ℝ), (46361773653047857372326297331072/5743806933507131373324375:ℝ), (114900950731238462749135290103808/17231420800521394119973125:ℝ), (30312718831559944761193042067456/17231420800521394119973125:ℝ)],
![(8645980235708568475355163804288/1914602311169043791108125:ℝ), (12428044792990069851942370961792/1148761386701426274664875:ℝ), (139800896697772334439848240371712/17231420800521394119973125:ℝ), (31198818870905447137309150183424/17231420800521394119973125:ℝ)],
![(573594426326286704832006814688/441831302577471644101875:ℝ), (380789650647976238793009570976/147277100859157214700625:ℝ), (113742347369299338629404379648/88366260515494328820375:ℝ), (0:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (615066405682826940530834901/154431233310491635561922560000:ℝ) admission08_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission08_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]
def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(163234097685801985176034022782394305087815064264886/17595369647682451138849010664316595523914116875:ℝ), (78898901436051002654296514050748658987075128285824/5865123215894150379616336888105531841304705625:ℝ), (24784175734208941559038342736668731455934303458304/5865123215894150379616336888105531841304705625:ℝ)],
![(86088389714834312753340159594477789562687121470607/17595369647682451138849010664316595523914116875:ℝ), (28409006787308151707233974180949885759430175427648/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2276141959223993071345437045480777356762088322663/6005886173075609988727128973420064605496018560000:ℝ) admission08_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission08_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]
def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission08_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission08_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]
def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission08_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission08_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]
def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission08_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission08_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]
theorem admission08_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission08_00_pos hδ hp
 · exact admission08_01_pos hδ hp
 · exact admission08_02_pos hδ hp
 · exact admission08_03_pos hδ hp
 · exact admission08_04_pos hδ hp
 · exact admission08_05_pos hδ hp
 · exact admission08_06_pos hδ hp
 · exact admission08_07_pos hδ hp
 · exact admission08_08_pos hδ hp
 · exact admission08_09_pos hδ hp
 · exact admission08_10_pos hδ hp
 · exact admission08_11_pos hδ hp
 · exact admission08_12_pos hδ hp
 · exact admission08_13_pos hδ hp
 · exact admission08_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
