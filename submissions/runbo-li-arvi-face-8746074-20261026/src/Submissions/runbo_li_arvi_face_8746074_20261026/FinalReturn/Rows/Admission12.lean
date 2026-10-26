/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission12_00_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission12_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]
def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission12_01_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission12_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]
def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission12_02_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission12_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]
def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8602772413187174204365395968/9190091093611410197319:ℝ), (11385037662337475916514383872/9190091093611410197319:ℝ), (928718142645391877382995968/3063363697870470065773:ℝ)],
![(5814870810723454974237435392/9190091093611410197319:ℝ), (5810969004733730814237435392/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (12388916138109113975014887/12547537706477445389406208:ℝ) admission12_03_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission12_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]
def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(302317183999150427148041931084/1914602311169043791108125:ℝ), (157696:ℝ), (0:ℝ)],
![(470827705084378030166964188779/1914602311169043791108125:ℝ), (637963346018490205445712249344/1914602311169043791108125:ℝ), (167528971786529062671039004672/1914602311169043791108125:ℝ)]]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (590502814982425132400665437/3921105533274201684189440000:ℝ) admission12_04_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission12_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]
def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(313655648263494985437459205183/1914602311169043791108125:ℝ), (626990384235507621362398647702/1914602311169043791108125:ℝ), (62629031681103059883896878287/382920462233808758221625:ℝ)],
![(0:ℝ), (752214792635966211979648118/1914602311169043791108125:ℝ), (562021714559092899688704011/1914602311169043791108125:ℝ)]]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (98322469596215145971869340362719/1027894288914632326300156559360000:ℝ) admission12_05_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission12_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]
def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(4969423926090819673803150843973379351286537458755180544/26041147078570027685496535783188561375392892975:ℝ), (82713767413209540575631721793405300222592495009333430272/217009558988083564045804464859904678128274108125:ℝ), (123905951570493390493769687420215391632340448559120777216/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(2475770488634036142631792578698086482947638839616751104/10015825799450010648267898378149446682843420375:ℝ), (119317730067242506041593973385354859457855128380606726656/217009558988083564045804464859904678128274108125:ℝ), (233462007382232332493524008561955447711146437522921095168/651028676964250692137413394579714034384822324375:ℝ), (2428910043671015340252701964176597607759358463745982464/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (19195461442567500614285217024411879605330730659367/88887115361519027833161508806616956161341074688000:ℝ) admission12_06_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission12_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]
def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2429531678004186076827010594018801851308779691604988/3519073929536490227769802132863319104782823375:ℝ), (17723023176023570510146749685711064536316513462204416/17595369647682451138849010664316595523914116875:ℝ), (372174005341112111876774956126153837288332294291456/1173024643178830075923267377621106368260941125:ℝ)],
![(261595366215775770413888237842653837645571379013707/703814785907298045553960426572663820956564675:ℝ), (6532666632850636513134560836246152124327959070555648/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4427668245915024971922691967667001472053066184223/9609417876920975981963406357472103368793629696000:ℝ) admission12_07_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission12_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]
def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (9821421523177767550876734046107277991168630927294093370986039984239586497/984004390596707940553052811005143384964467680870400000000000000000:ℝ), (825092345476849365313653427241234261259554977883630895733808318677996492927/41328184405061733503228218062216022168507642596556800000000000000000:ℝ), (412589498751754647670632202580184645568895799457872499228924938219933860053/41328184405061733503228218062216022168507642596556800000000000000000:ℝ)],
![(267384054678631016335618598489022668964115395766022856424100411695761807291/7872035124773663524424422488041147079715741446963200000000000000000:ℝ), (6147471285897107441940321846315198286763243140222713211082334216299663944277/55104245873415644670970957416288029558010190128742400000000000000000:ℝ), (715718504353413390866409354633428470449897268644582652134312130039278644809/5904026343580247643318316866030860309786806085222400000000000000000:ℝ), (1803189200158508456357286337265345961959794632470116247818103819692952043733/41328184405061733503228218062216022168507642596556800000000000000000:ℝ)]]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1905007153850190143577050591953323350328382506081933522375038346795849201341/540962134621858627832175868957178844955280231857578600248115200000000000000000:ℝ) admission12_08_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission12_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]
def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(139438066624373145393796377825642516728755411133201811148/2199421205960306392356126333039574440489264609375:ℝ), (4830696408785600481340295123682593384028234861350762416/29325616079470751898081684440527659206523528125:ℝ), (23565325375721340727020282091121082438837073486321393664/169186246612331260950471256387659572345328046875:ℝ), (5565679950660148542022934383325036427516927518811881472/146628080397353759490408422202638296032617640625:ℝ)],
![(55221958367665464811703130784822674972201106703806217419/2199421205960306392356126333039574440489264609375:ℝ), (7359086969601078371753952180262382477617284927147381884/146628080397353759490408422202638296032617640625:ℝ), (55164212333129437971703273835026309950495323934623369216/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (3600577854577102524346716817562114573499464498318349/153750686030735615711414501719553653900698075136000000:ℝ) admission12_09_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission12_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]
def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(219283959142858500959551567951302656/17231420800521394119973125:ℝ), (22523063633894933939682645216759808/689256832020855764798925:ℝ), (468407058530678357222094310131367936/17231420800521394119973125:ℝ), (124614579554214430958418147663675392/17231420800521394119973125:ℝ)],
![(313492269322407865779947539261048832/17231420800521394119973125:ℝ), (57834063566713223996425218532796416/1325493907732414932305625:ℝ), (563418513371380941413043496684355584/17231420800521394119973125:ℝ), (125068262774359328174989595019051008/17231420800521394119973125:ℝ)],
![(10416739892767600603859604119718144/1914602311169043791108125:ℝ), (62465752365814267515889504054483712/5743806933507131373324375:ℝ), (6243096289408861130355898339065856/1148761386701426274664875:ℝ), (0:ℝ)]]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (556949895069348660634348401753/128486786114329040787519569920000:ℝ) admission12_10_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission12_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]
def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10308564349175221456794517853810190914779665896373268/17595369647682451138849010664316595523914116875:ℝ), (1004008062027373039869485911712230449013593028032512/1173024643178830075923267377621106368260941125:ℝ), (1586187246989372259778453935146798813179795421331456/5865123215894150379616336888105531841304705625:ℝ)],
![(1105571404130387901060974854213239327490330267037321/3519073929536490227769802132863319104782823375:ℝ), (1840293470715520937158634853095864136182163529967104/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (18426965343330890346184731798055221376658629170293/48047089384604879909817031787360516843968148480000:ℝ) admission12_11_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission12_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]
def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission12_12_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission12_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]
def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission12_13_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission12_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]
def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission12_14_coefficients (231/512:ℝ) (927/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission12_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]
theorem admission12_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (927/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission12_00_pos hδ hp
 · exact admission12_01_pos hδ hp
 · exact admission12_02_pos hδ hp
 · exact admission12_03_pos hδ hp
 · exact admission12_04_pos hδ hp
 · exact admission12_05_pos hδ hp
 · exact admission12_06_pos hδ hp
 · exact admission12_07_pos hδ hp
 · exact admission12_08_pos hδ hp
 · exact admission12_09_pos hδ hp
 · exact admission12_10_pos hδ hp
 · exact admission12_11_pos hδ hp
 · exact admission12_12_pos hδ hp
 · exact admission12_13_pos hδ hp
 · exact admission12_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
