/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission10_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission10_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]
def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission10_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission10_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]
def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission10_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission10_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]
def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(538402496846549747772837248/9190091093611410197319:ℝ), (711564853896092244782148992/9190091093611410197319:ℝ), (58044883915336992336437248/3063363697870470065773:ℝ)],
![(363840521871540551268782336/9190091093611410197319:ℝ), (362855599971221831268782336/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1540643265505246410404877/1568442213309680673675776:ℝ) admission10_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission10_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]
def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(18968334863141319971525442771/1914602311169043791108125:ℝ), (9856:ℝ), (0:ℝ)],
![(29685237611009013920563113586/1914602311169043791108125:ℝ), (40056510948027866044303395584/1914602311169043791108125:ℝ), (10470560736658066416939937792/1914602311169043791108125:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (590502814982425132400665437/3921105533274201684189440000:ℝ) admission10_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission10_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]
def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19805035570004110242030029671/1914602311169043791108125:ℝ), (39661105709227074829073218332/1914602311169043791108125:ℝ), (3961735149519726092135885178/382920462233808758221625:ℝ)],
![(0:ℝ), (64047921523547697278370244/382920462233808758221625:ℝ), (272229704413867553192195426/1914602311169043791108125:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (745770619749162147044354248173/8030424132145565049219973120000:ℝ) admission10_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission10_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]
def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1956679807737889425663211559510929018630456253096183168/651028676964250692137413394579714034384822324375:ℝ), (1297549476747677833046679880206100275401391920610815104/217009558988083564045804464859904678128274108125:ℝ), (1936030493288959226465151365940865494255319508736262144/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(2542082469103085478061068018839308156448797787685708032/651028676964250692137413394579714034384822324375:ℝ), (1877515287157099432913495841160993653233698402418281216/217009558988083564045804464859904678128274108125:ℝ), (3659801858154095118104253231614608420313297059509600256/651028676964250692137413394579714034384822324375:ℝ), (37951719432359614691448468190259337621239975996030976/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (19195461442567500614285217024411879605330730659367/88887115361519027833161508806616956161341074688000:ℝ) admission10_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission10_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]
def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(760587142022690940034677240557485380950062918037627/17595369647682451138849010664316595523914116875:ℝ), (1107688948501473156884171855356941533519782091387776/17595369647682451138849010664316595523914116875:ℝ), (23260875333819506992298434757884614830520768393216/1173024643178830075923267377621106368260941125:ℝ)],
![(405362144710221870045683161314083372416560996007778/17595369647682451138849010664316595523914116875:ℝ), (403578592751995286937983771200328765269512648865024/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (547069740517076621156758434654024551271199712373/1201177234615121997745425794684012921099203712000:ℝ) admission10_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission10_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]
def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (52802208269230245798643534380061773584381060648309587592544357575235291/339103051528711659513667430254080181895447323869184000000000000000:ℝ), (206049834544571174210503103971359287534666231833992718493131264625288862079/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (103072957413058272878354633032063068798816445652163122993790962873580044629/661250950480987736051651488995456354696122281544908800000000000000000:ℝ)],
![(120300716030148122832310901029744707011486990173702606246940887411160451741/220416983493662578683883829665152118232040760514969600000000000000000:ℝ), (390768074145259446902890729736313770187718066736298310155169109726532911403/220416983493662578683883829665152118232040760514969600000000000000000:ℝ), (36061076896469127869049810174928895929853421719568341524967296368798627701/18892884299456792458618613971298752991317779472711680000000000000000:ℝ), (450722882764746725050018166703353397896541153905224060141085683241834590549/661250950480987736051651488995456354696122281544908800000000000000000:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (756154516068384580416019513608777437317906888224799824247096122488349847211/236670933897063149676576942668765744667935101437690637608550400000000000000000:ℝ) admission10_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission10_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]
def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2181471429420521708965396000904056076595145689407445784/2199421205960306392356126333039574440489264609375:ℝ), (1887918420148623025352097269511528659864395528707104259/733140401986768797452042111013191480163088203125:ℝ), (368208208995645948859691907673766913106829273223771776/169186246612331260950471256387659572345328046875:ℝ), (86963749229064820969108349739453694179951992481435648/146628080397353759490408422202638296032617640625:ℝ)],
![(831053824084993805267948024636419454472673580066083216/2199421205960306392356126333039574440489264609375:ℝ), (552945625222216085783114925690519611714343742649597586/733140401986768797452042111013191480163088203125:ℝ), (827749265914148698533097430238483475033135075180673792/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (426186924721869767791814481722391908124824177636079/19218835753841951963926812714944206737587259392000000:ℝ) admission10_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission10_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]
def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(863130293861363884164397536950336/17231420800521394119973125:ℝ), (2216712410838504703947675843981376/17231420800521394119973125:ℝ), (369132974618736275133779169007616/3446284160104278823994625:ℝ), (98418460323944627037603507601408/3446284160104278823994625:ℝ)],
![(1226877737128018981108835816874752/17231420800521394119973125:ℝ), (9076218228957439779437035710208/53019756309296597292225:ℝ), (2222054950276123343337947191877632/17231420800521394119973125:ℝ), (499181101934487154196946402934784/17231420800521394119973125:ℝ)],
![(3046233486822282819144076567808/147277100859157214700625:ℝ), (18238339405095376821384580075264/441831302577471644101875:ℝ), (1819877557908789418070470074368/88366260515494328820375:ℝ), (0:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (615066405682826940530834901/154431233310491635561922560000:ℝ) admission10_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission10_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]
def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(645598739273340585691080675281973923257821007250821/17595369647682451138849010664316595523914116875:ℝ), (62750503876710814991842869482014403063349564252032/1173024643178830075923267377621106368260941125:ℝ), (99136702936835766236153370946674925823737213833216/5865123215894150379616336888105531841304705625:ℝ)],
![(342630820153517535750084164274654893681955295507102/17595369647682451138849010664316595523914116875:ℝ), (113636027149232606828935896723799543037720701710592/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2276141959223993071345437045480777356762088322663/6005886173075609988727128973420064605496018560000:ℝ) admission10_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission10_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]
def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission10_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission10_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]
def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission10_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission10_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]
def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission10_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission10_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]
theorem admission10_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission10_00_pos hδ hp
 · exact admission10_01_pos hδ hp
 · exact admission10_02_pos hδ hp
 · exact admission10_03_pos hδ hp
 · exact admission10_04_pos hδ hp
 · exact admission10_05_pos hδ hp
 · exact admission10_06_pos hδ hp
 · exact admission10_07_pos hδ hp
 · exact admission10_08_pos hδ hp
 · exact admission10_09_pos hδ hp
 · exact admission10_10_pos hδ hp
 · exact admission10_11_pos hδ hp
 · exact admission10_12_pos hδ hp
 · exact admission10_13_pos hδ hp
 · exact admission10_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
