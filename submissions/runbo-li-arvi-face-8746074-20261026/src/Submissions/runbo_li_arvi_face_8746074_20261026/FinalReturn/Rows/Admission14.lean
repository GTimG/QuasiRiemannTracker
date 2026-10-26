/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission14_00_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission14_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]
def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission14_01_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission14_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]
def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission14_02_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission14_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]
def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2645869026358390315811207168/706930084123954630563:ℝ), (45533111442424328314141644800/9190091093611410197319:ℝ), (3714872570581567509531983872/3063363697870470065773:ℝ)],
![(23248172654655434140991796224/9190091093611410197319:ℝ), (23240356415472135580991796224/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (24756575604862513719437817/25095075412954890778812416:ℝ) admission14_03_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission14_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]
def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1212408271486562095199118848214/1914602311169043791108125:ℝ), (632832:ℝ), (0:ℝ)],
![(75379439372587817466088219197/76584092446761751644325:ℝ), (2553813936840597922624943717376/1914602311169043791108125:ℝ), (670115887146116250684156018688/1914602311169043791108125:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2369680127656745011841631429/15684422133096806736757760000:ℝ) admission14_04_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission14_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]
def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1252476954397322847107673892191/1914602311169043791108125:ℝ), (2507201995652882065814102600426/1914602311169043791108125:ℝ), (1254344655099405472081846820021/1914602311169043791108125:ℝ)],
![(0:ℝ), (4393110003313929434081851562/1914602311169043791108125:ℝ), (160484333423225840106562813/76584092446761751644325:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (782830211325572369588301711337953/8223154311317058610401252474880000:ℝ) admission14_05_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission14_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]
def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(25502806397934132777581473851018097367260292745974458368/16693042999083351080446497296915744471405700625:ℝ), (1987897396282420448710860688464539186993379470327818950656/651028676964250692137413394579714034384822324375:ℝ), (76406803333561010573632258568620649453523265633447313408/50079128997250053241339491890747233414217101875:ℝ), (0:ℝ)],
![(429033509185758701417698944028661544277856257077674376192/217009558988083564045804464859904678128274108125:ℝ), (2864347299383965390128394659359090551418521488147798422528/651028676964250692137413394579714034384822324375:ℝ), (1868716474444031666701722999510816236607710932564293189632/651028676964250692137413394579714034384822324375:ℝ), (19431280349368122722021615713412780862074867709967859712/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2081054250021259096110772666815175244663458767027/9609417876920975981963406357472103368793629696000:ℝ) admission14_06_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission14_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]
def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16158513965652262753190010310731408789411474916428002/5865123215894150379616336888105531841304705625:ℝ), (70791547172335999477751238080123068971911711597197312/17595369647682451138849010664316595523914116875:ℝ), (1488696021364448447507099824504615349153329177165824/1173024643178830075923267377621106368260941125:ℝ)],
![(8698267013013545486872790238936447693838757320193711/5865123215894150379616336888105531841304705625:ℝ), (26080393765523404771120363013624013910634665156412416/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (8838299717903912609622509105189067923478309540033/19218835753841951963926812714944206737587259392000:ℝ) admission14_07_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission14_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]
def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (1597694805338150016395490183291531427771414939440532411403164222920810221821/20664092202530866751614109031108011084253821298278400000000000000000:ℝ), (6391246154887079183257450874821619538770636047854320163376571633258053135607/41328184405061733503228218062216022168507642596556800000000000000000:ℝ), (213056682553336272162519980215953961791365781845344035366435200526428846131/2755212293670782233548547870814401477900509506437120000000000000000:ℝ)],
![(1490320924522130047935770984899358453304744055951065920100322615647920935737/5510424587341564467097095741628802955801019012874240000000000000000:ℝ), (10478555451429636873300740144304250560095378914259909704179309161954547508381/11808052687160495286636633732061720619573612170444800000000000000000:ℝ), (5688313044536614624357449815973516494717189379216433689038889225331726774673/5904026343580247643318316866030860309786806085222400000000000000000:ℝ), (954709856636938303462068852048039997199845159451874034613997270645371877427/2755212293670782233548547870814401477900509506437120000000000000000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6829027948441639637140241371193669748607573373514807255445640798523597444513/1731078830789947609062962780662972303856896741944251520793968640000000000000000:ℝ) admission14_08_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission14_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]
def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(73961769637922665450812233376438254365062847423247093762/146628080397353759490408422202638296032617640625:ℝ), (2886503699078753681207119699492966542167093593878107196688/2199421205960306392356126333039574440489264609375:ℝ), (2444958480902688978901882568677223593510056498249264283648/2199421205960306392356126333039574440489264609375:ℝ), (44525439605281188336183475066600291420135420150495051776/146628080397353759490408422202638296032617640625:ℝ)],
![(29241619559071881403064866195604793260959301470365425951/146628080397353759490408422202638296032617640625:ℝ), (877020581084540625458388328451004683397306910246625964664/2199421205960306392356126333039574440489264609375:ℝ), (438396019578870275419512806280525989539463019312906625024/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (7137461556886823588022699980529902710831971970893459/307501372061471231422829003439107307801396150272000000:ℝ) admission14_09_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission14_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]
def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(269530700926526532944875292035033088/1325493907732414932305625:ℝ), (231068876325394727622153307592996864/441831302577471644101875:ℝ), (2504169373303617318960876966273089536/5743806933507131373324375:ℝ), (2004721670150908428532405099147821056/17231420800521394119973125:ℝ)],
![(4999331922312786261674714346436851712/17231420800521394119973125:ℝ), (800356996925734048598425814235219968/1148761386701426274664875:ℝ), (693413302748012244426659934237097984/1325493907732414932305625:ℝ), (2008351135912067606264976677990825984/17231420800521394119973125:ℝ)],
![(1491787486981130048639700658582856192/17231420800521394119973125:ℝ), (994249559677185592547650096904451584/5743806933507131373324375:ℝ), (298192115034657957024529606426099712/3446284160104278823994625:ℝ), (0:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2197926899521676464555236062233/513947144457316163150078279680000:ℝ) admission14_10_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission14_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]
def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(41131721829469471750903004882469163850153828906153306/17595369647682451138849010664316595523914116875:ℝ), (20050671858777061826862170893557847050167017490520064/5865123215894150379616336888105531841304705625:ℝ), (6344748987957489039113815740587195252719181685325824/5865123215894150379616336888105531841304705625:ℝ)],
![(22053212241714040233511615377888908806629023250385907/17595369647682451138849010664316595523914116875:ℝ), (7346429191976884263370765742040075579676232584803328/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (36781320796815465433895718451374108579129950810923/96094178769209759819634063574721033687936296960000:ℝ) admission14_11_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission14_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_11_coefficients]
def admission14_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission14_12_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission14_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_12_coefficients]
def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission14_13_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission14_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_13_coefficients]
def admission14_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission14_14_coefficients (927/2048:ℝ) (1857/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission14_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_14_coefficients]
theorem admission14_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (927/2048:ℝ) (1857/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission14_00_pos hδ hp
 · exact admission14_01_pos hδ hp
 · exact admission14_02_pos hδ hp
 · exact admission14_03_pos hδ hp
 · exact admission14_04_pos hδ hp
 · exact admission14_05_pos hδ hp
 · exact admission14_06_pos hδ hp
 · exact admission14_07_pos hδ hp
 · exact admission14_08_pos hδ hp
 · exact admission14_09_pos hδ hp
 · exact admission14_10_pos hδ hp
 · exact admission14_11_pos hδ hp
 · exact admission14_12_pos hδ hp
 · exact admission14_13_pos hδ hp
 · exact admission14_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
