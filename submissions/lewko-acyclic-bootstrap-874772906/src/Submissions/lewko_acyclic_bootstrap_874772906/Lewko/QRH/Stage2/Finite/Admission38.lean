/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission38_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(50208178137654883/52465400575843:ℝ),(150267138211237120/157396201727529:ℝ)]]
theorem admission38_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission38_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission38_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_00_coefficients]
def admission38_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(36724570189663232/52465400575843:ℝ),(109973710568989696/157396201727529:ℝ)]]
theorem admission38_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission38_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission38_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_01_coefficients]
def admission38_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(18683062195743146/52465400575843:ℝ),(18650986811825152/52465400575843:ℝ)]]
theorem admission38_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission38_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission38_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_02_coefficients]
def admission38_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(343744039505818711665664/472188605182587:ℝ),(2058959814116735248466944/1416565815547761:ℝ),(1027728820599279113469952/1416565815547761:ℝ)],
![(343158507168648514115584/472188605182587:ℝ),(2055447009130318942259200/1416565815547761:ℝ),(1025972614424373399912448/1416565815547761:ℝ)]]
theorem admission38_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1956887463425394821/3868169053655752704:ℝ) admission38_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission38_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_03_coefficients]
def admission38_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6001913683267536906250/52465400575843:ℝ),(11970209415936636800000/52465400575843:ℝ),(5968315779784048640000/52465400575843:ℝ)],
![(6021066050408419443124/52465400575843:ℝ),(12008460361497444374528/52465400575843:ℝ),(5987414390279357595648/52465400575843:ℝ)]]
theorem admission38_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (34150976828293125/429796561517305856:ℝ) admission38_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission38_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_04_coefficients]
def admission38_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3996986557619806596333584/59023575647823375:ℝ),(7995303506027336595079364/59023575647823375:ℝ),(88851246877015836871434/1311635014396075:ℝ)],
![(791429915640791939275942/11804715129564675:ℝ),(39578470551751841426736148/295117878239116875:ℝ),(2199185375479046856496122/32790875359901875:ℝ)]]
theorem admission38_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (395714957820395969637971/8450144236679446973644800:ℝ) admission38_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission38_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_05_coefficients]
def admission38_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1393139224813193605702980572941893497835520/8249596917978249986997496465053:ℝ),(4166423886805632323104326781029548426383360/8249596917978249986997496465053:ℝ),(4153446359410320039512956648349041599447040/8249596917978249986997496465053:ℝ),(1380161691788891144903028690261386670899200/8249596917978249986997496465053:ℝ)],
![(1397231194482316145987211015580667914657792/8249596917978249986997496465053:ℝ),(4178686701259225339453628751019917565272064/8249596917978249986997496465053:ℝ),(4165696096673054255776866474675345389780992/8249596917978249986997496465053:ℝ),(1384240584258148500818333258436095739166720/8249596917978249986997496465053:ℝ)]]
theorem admission38_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5141502960729938540246444531758825/45053798634718549262322327361142784:ℝ) admission38_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission38_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_06_coefficients]
def admission38_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(26024791679874627390239420514213817750/74320692954759008891869337523:ℝ),(51943464834954051672901555596495201280/74320692954759008891869337523:ℝ),(25918726059687483720598367425286635520/74320692954759008891869337523:ℝ)],
![(25923690139809137082774580776214545292/74320692954759008891869337523:ℝ),(51741468703192119124703879494036719616/74320692954759008891869337523:ℝ),(25817831364818458048675622915413114880/74320692954759008891869337523:ℝ)]]
theorem admission38_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (24621802677935083435702917972005/101472519447564300140365602164736:ℝ) admission38_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission38_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_07_coefficients]
def admission38_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(304229166370705811807508959126037621893061314098747843363/87094562056358213545159379909765625000000000000:ℝ),(921480916688220423882074473810527824208816823116062102557/87094562056358213545159379909765625000000000000:ℝ),(930272188400141650238923171981185703054323582229414817431/87094562056358213545159379909765625000000000000:ℝ),(313020427205660312741441098119896188123947418915225558237/87094562056358213545159379909765625000000000000:ℝ)],
![(328724038596006032121831476160401547088133920083720303817/87094562056358213545159379909765625000000000000:ℝ),(4974255708192670590588691085066240222082880922311569765647/435472810281791067725796899548828125000000000000:ℝ),(5017640687957306854151291199276926121463457901870820942067/435472810281791067725796899548828125000000000000:ℝ),(337401023654563412650758273331056535449445268651820539101/87094562056358213545159379909765625000000000000:ℝ)]]
theorem admission38_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (304229166370705811807508959126037621893061314098747843363/127681978262699020300780801986588259123200000000000000000000:ℝ) admission38_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission38_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_08_coefficients]
def admission38_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5641902734380708162369135475926409814696787198/435472810281791067725796899548828125:ℝ),(673638101493887184079058200481714929333500436/17418912411271642709031875981953125:ℝ),(16756243860487665229766525135593396312954359808/435472810281791067725796899548828125:ℝ),(5557194102742482957762595686472604649684729856/435472810281791067725796899548828125:ℝ)],
![(5507382359790399324180350904623508157550570716/435472810281791067725796899548828125:ℝ),(82189901740967087531393700264204412388924239304/2177364051408955338628984497744140625:ℝ),(81769300176464537688536563954876947807470034944/2177364051408955338628984497744140625:ℝ),(5423262092183532585880479153892880071439417344/435472810281791067725796899548828125:ℝ)]]
theorem admission38_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5172025768455059610252837327854995795669/608835116685385800842193612988416000000000:ℝ) admission38_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission38_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_09_coefficients]
def admission38_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21744478441562112563071426344868352/4611216847486201171875:ℝ),(194505587435234165100344352460615168/13833650542458603515625:ℝ),(193311353404289337033634742817415168/13833650542458603515625:ℝ),(21346400586886818311668223130468352/4611216847486201171875:ℝ)],
![(128745189407716887574019025448466432/13833650542458603515625:ℝ),(127950759367000074604921006311483392/4611216847486201171875:ℝ),(127156650393366111011233909574500352/4611216847486201171875:ℝ),(126362863422147028042957735237517312/13833650542458603515625:ℝ)],
![(63508672854730579820898327105222656/13833650542458603515625:ℝ),(189337459874474406725553889491040256/13833650542458603515625:ℝ),(188149379867582043654525832386412544/13833650542458603515625:ℝ),(62320593316252497999870270000594944/13833650542458603515625:ℝ)]]
theorem admission38_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7429193653613626718505653143/3300837592452908974080000000000:ℝ) admission38_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission38_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_10_coefficients]
def admission38_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7114598980937756620748031499275039950/24773564318253002963956445841:ℝ),(42600798536850112680187634268335441920/74320692954759008891869337523:ℝ),(2361894696798303103709994875711651840/8257854772751000987985481947:ℝ)],
![(7086267556914633744792816618268742012/24773564318253002963956445841:ℝ),(42430987371196506267720351404233756672/74320692954759008891869337523:ℝ),(784156861883850756988237918730977280/2752618257583666995995160649:ℝ)]]
theorem admission38_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4486981555274109403542926323305/22549448766125400031192356036608:ℝ) admission38_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission38_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_11_coefficients]
def admission38_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission38_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission38_12_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission38_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_12_coefficients]
def admission38_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission38_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission38_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission38_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_13_coefficients]
def admission38_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission38_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission38_14_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission38_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_14_coefficients]
theorem admission38_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission38_00_pos hδ hp
 · exact admission38_01_pos hδ hp
 · exact admission38_02_pos hδ hp
 · exact admission38_03_pos hδ hp
 · exact admission38_04_pos hδ hp
 · exact admission38_05_pos hδ hp
 · exact admission38_06_pos hδ hp
 · exact admission38_07_pos hδ hp
 · exact admission38_08_pos hδ hp
 · exact admission38_09_pos hδ hp
 · exact admission38_10_pos hδ hp
 · exact admission38_11_pos hδ hp
 · exact admission38_12_pos hδ hp
 · exact admission38_13_pos hδ hp
 · exact admission38_14_pos hδ hp
#print axioms admission38_all
end
end LewkoStage2Finite
