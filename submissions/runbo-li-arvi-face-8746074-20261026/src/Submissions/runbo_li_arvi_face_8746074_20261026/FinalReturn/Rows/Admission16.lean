/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission16_00_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission16_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]
def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission16_01_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission16_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]
def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission16_02_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission16_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]
def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10581194537479534581411614720/706930084123954630563:ℝ), (182118367355846162552734797824/9190091093611410197319:ℝ), (14859490282326270038127935488/3063363697870470065773:ℝ)],
![(92970031560533414332051294208/9190091093611410197319:ℝ), (92954386454962966972051294208/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3807068810643793323714129/3860780832762290889048064:ℝ) admission16_03_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission16_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]
def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4855904519433889214449362282474/1914602311169043791108125:ℝ), (2535424:ℝ), (0:ℝ)],
![(7540290446467008408797011690249/1914602311169043791108125:ℝ), (10219176852895665892183964309504/1914602311169043791108125:ℝ), (2680463548584465002736624074752/1914602311169043791108125:ℝ)]]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4747029123040534505922232539/31368844266193613473515520000:ℝ) admission16_04_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission16_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]
def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5005618386810715809566877390751/1914602311169043791108125:ℝ), (10027285206963754203144411062802/1914602311169043791108125:ℝ), (5020904816817571826714698109577/1914602311169043791108125:ℝ)],
![(0:ℝ), (4067449721863725213527713258/382920462233808758221625:ℝ), (19574629762272522397967110793/1914602311169043791108125:ℝ)]]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6247675266754180176730333534062693/65785234490536468883210019799040000:ℝ) admission16_05_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission16_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]
def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7959759729403240550541889682095098860683880164796978941952/651028676964250692137413394579714034384822324375:ℝ), (5304743201476442874745230049426663477671781616574298320896/217009558988083564045804464859904678128274108125:ℝ), (7954470869779729153686002339257928782514735084925916020736/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(10295597946890890787961670878705868567262471031735973677056/651028676964250692137413394579714034384822324375:ℝ), (7639218922168834556343572685583744871433333632192624580608/217009558988083564045804464859904678128274108125:ℝ), (1150293342853611181586762132319016962502757322310618710016/50079128997250053241339491890747233414217101875:ℝ), (155450242794944981776172925707302246896598941679742877696/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (154215175982089757211154897918836933736321000502529/711096922892152222665292070452935649290728597504000:ℝ) admission16_06_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission16_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]
def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(193672150890994989313903456931143634933501624863936538/17595369647682451138849010664316595523914116875:ℝ), (282965097625827432785333430995049897540938161885548544/17595369647682451138849010664316595523914116875:ℝ), (5954784085457793790028399298018461396613316708663296/1173024643178830075923267377621106368260941125:ℝ)],
![(104249816305799516095714424281690466348206487976961409/17595369647682451138849010664316595523914116875:ℝ), (104221029530335336521645691391774866469184318374029312/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (17659562661881687885022143380233200826328796251653/38437671507683903927853625429888413475174518784000:ℝ) admission16_07_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission16_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]
def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (59871285612699385196132425660361777034870430338289048638177432559260402731/98400439059670794055305281100514338496446768087040000000000000000:ℝ), (25146968915983860089668825062869819004641202321889995400021851061846320983273/20664092202530866751614109031108011084253821298278400000000000000000:ℝ), (12573992621202515076944207861419518882844009468389059445817487156241636409763/20664092202530866751614109031108011084253821298278400000000000000000:ℝ)],
![(29736234723788886013339274479900429653317819003806759730394252411402294203421/13776061468353911167742739354072007389502547532185600000000000000000:ℝ), (97520538396996558465279009622391767149329825265123067094513409001282990261153/13776061468353911167742739354072007389502547532185600000000000000000:ℝ), (158749644897246489281117619201743554039903725519799126652093743260679262374121/20664092202530866751614109031108011084253821298278400000000000000000:ℝ), (4390244851247587458070549243949590846719444009598527646205477797182939868271/1589545554040835903970316079316000852634909330636800000000000000000:ℝ)]]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (154932231979914552287520895255274831568558304173075527402510892992908482565009/37284774817014256195202275275817865006148545211106955832485478400000000000000000:ℝ) admission16_08_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission16_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]
def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(680856503133286218783828097178710778009120717022264167002/169186246612331260950471256387659572345328046875:ℝ), (7681469579623450835405235596008110520384561016555991832736/733140401986768797452042111013191480163088203125:ℝ), (19536326414532190004382153474220312827564455408681471639552/2199421205960306392356126333039574440489264609375:ℝ), (356203516842249506689467800532802331361083361203960414208/146628080397353759490408422202638296032617640625:ℝ)],
![(3496405116152709499199701496173074363514604667170944486573/2199421205960306392356126333039574440489264609375:ℝ), (2330634364370448210177417413453197066639849317705009246608/733140401986768797452042111013191480163088203125:ℝ), (3495497440286301289939648912645469956057705865846931685376/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1093171458577405055028820485112729152730537455080283/47307903394072497141973692836785739661753253888000000:ℝ) admission16_09_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission16_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]
def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(56024640865426261567721395404304093184/17231420800521394119973125:ℝ), (28841064067414431229881313855117316096/3446284160104278823994625:ℝ), (120343330904819701928262966949879742464/17231420800521394119973125:ℝ), (32162653900682355122100199478597255168/17231420800521394119973125:ℝ)],
![(79856446799926382032138671968238522368/17231420800521394119973125:ℝ), (191891382376887275470461207240306675712/17231420800521394119973125:ℝ), (144226620264729144447756228981409447936/17231420800521394119973125:ℝ), (32191689626771628543960772109341294592/17231420800521394119973125:ℝ)],
![(2644745200738674776924701328096920576/1914602311169043791108125:ℝ), (15866276028786658454785030593918635008/5743806933507131373324375:ℝ), (1586407920547697509635813481925574656/1148761386701426274664875:ℝ), (0:ℝ)]]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (8731799986812205750600846180593/2055788577829264652600313118720000:ℝ) admission16_10_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission16_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]
def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32864397498155850903322722819012922824789124446700334/3519073929536490227769802132863319104782823375:ℝ), (80143708671567449366393588892857864340458383821819904/5865123215894150379616336888105531841304705625:ℝ), (25378995951829956156455262962348781010876726741303296/5865123215894150379616336888105531841304705625:ℝ)],
![(88096502938750823191406561914169458910790916804606591/17595369647682451138849010664316595523914116875:ℝ), (29356227386137138082955515627473540388600087269083136/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (73490031703784615609317691758011882984072594092183/192188357538419519639268127149442067375872593920000:ℝ) admission16_11_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission16_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]
def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission16_12_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission16_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]
def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission16_13_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission16_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]
def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission16_14_coefficients (1857/4096:ℝ) (3717/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission16_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]
theorem admission16_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1857/4096:ℝ) (3717/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission16_00_pos hδ hp
 · exact admission16_01_pos hδ hp
 · exact admission16_02_pos hδ hp
 · exact admission16_03_pos hδ hp
 · exact admission16_04_pos hδ hp
 · exact admission16_05_pos hδ hp
 · exact admission16_06_pos hδ hp
 · exact admission16_07_pos hδ hp
 · exact admission16_08_pos hδ hp
 · exact admission16_09_pos hδ hp
 · exact admission16_10_pos hδ hp
 · exact admission16_11_pos hδ hp
 · exact admission16_12_pos hδ hp
 · exact admission16_13_pos hδ hp
 · exact admission16_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
