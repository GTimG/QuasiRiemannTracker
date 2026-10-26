/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission21_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission21_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission21_00_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission21_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_00_coefficients]
def admission21_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission21_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission21_01_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission21_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_01_coefficients]
def admission21_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission21_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission21_02_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission21_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_02_coefficients]
def admission21_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(535411234243562211309635072/9190091093611410197319:ℝ), (54498861605088694486072832/706930084123954630563:ℝ), (58044883915336992336437248/3063363697870470065773:ℝ)],
![(360849259268553014805580160/9190091093611410197319:ℝ), (359775946941282614805580160/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission21_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2932489831520493206666055/3136884426619361347351552:ℝ) admission21_03_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission21_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_03_coefficients]
def admission21_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20692728941608712696209573932/1914602311169043791108125:ℝ), (10752:ℝ), (0:ℝ)],
![(31409631689476406645247244747/1914602311169043791108125:ℝ), (41771994618835329281136275584/1914602311169043791108125:ℝ), (10470560736658066416939937792/1914602311169043791108125:ℝ)]]
theorem admission21_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (161046222267934127018363301/980276383318550421047360000:ℝ) admission21_04_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission21_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_04_coefficients]
def admission21_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19805035570004110242030029671/1914602311169043791108125:ℝ), (41545540978019263818724063942/1914602311169043791108125:ℝ), (21688802435334061802479020339/1914602311169043791108125:ℝ)],
![(0:ℝ), (440934975281985495208539366/382920462233808758221625:ℝ), (17218851137194391159934319/15316818489352350328865:ℝ)]]
theorem admission21_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (215127098505647595801215574651/3212169652858226019687989248000:ℝ) admission21_05_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission21_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_05_coefficients]
def admission21_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2069567896896502249846117614832352533128649515639604736/651028676964250692137413394579714034384822324375:ℝ), (1372379609215869489512302446913123469997339813679825408/217009558988083564045804464859904678128274108125:ℝ), (2047638426151631840132596945725374625970569925399871488/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(106198822330467932089758962966429266837879642009165184/26041147078570027685496535783188561375392892975:ℝ), (390469083925058217875823681573603369565929259097458304/43401911797616712809160892971980935625654821625:ℝ), (150856391640670709270867952455964702081141899046928384/26041147078570027685496535783188561375392892975:ℝ), (37951719432359614691448468190259337621239975996030976/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission21_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (398376765503530563595947327807877673536655631867/1709367603106135150637721323204172233871943744000:ℝ) admission21_06_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission21_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_06_coefficients]
def admission21_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(716404070886455684303054335431555878420230145116364/17595369647682451138849010664316595523914116875:ℝ), (81823098335171118126425120416647790013635181254144/1353489972898650087603770051101276578762624375:ℝ), (23260875333819506992298434757884614830520768393216/1173024643178830075923267377621106368260941125:ℝ)],
![(72235814714797322862812051237630773977345644617303/3519073929536490227769802132863319104782823375:ℝ), (71917984521549333139467696251961700385397582756224/3519073929536490227769802132863319104782823375:ℝ), (0:ℝ)]]
theorem admission21_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (194976412710238380550678611658700791629527925171/480470893846048799098170317873605168439681484800:ℝ) admission21_07_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission21_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_07_coefficients]
def admission21_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (78321753342689755674910061182915677342838424448151207237553447698581459/5510424587341564467097095741628802955801019012874240000000000000000:ℝ), (4929930617044386054649526038876808970602637336755792275231028925205538647/165312737620246934012912872248864088674030570386227200000000000000000:ℝ), (2576849560441714650367611776614131310415652443958737959773842454248094877/165312737620246934012912872248864088674030570386227200000000000000000:ℝ)],
![(120300716030148122832310901029744707011486990173702606246940887411160451741/220416983493662578683883829665152118232040760514969600000000000000000:ℝ), (359579508903967377360768834836590244451583914292823126509517415210573230613/220416983493662578683883829665152118232040760514969600000000000000000:ℝ), (38421699260715208765172798439523546639021931346354371570773150856553045073/23616105374320990573273267464123441239147224340889600000000000000000:ℝ), (89489330898363827693283495194436713584846829507223972246597522546311731357/165312737620246934012912872248864088674030570386227200000000000000000:ℝ)]]
theorem admission21_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (820617388175373789973637108808354071139783420468138638858213689530679833443/59167733474265787419144235667191436166983775359422659402137600000000000000000:ℝ) admission21_08_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission21_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_08_coefficients]
def admission21_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1859741861123632584839636889673237610632800134568650848/2199421205960306392356126333039574440489264609375:ℝ), (1674302524715580650125597585407103211708992236855300588/733140401986768797452042111013191480163088203125:ℝ), (4467585566894075483944843381043478769584139846462747136/2199421205960306392356126333039574440489264609375:ℝ), (86963749229064820969108349739453694179951992481435648/146628080397353759490408422202638296032617640625:ℝ)],
![(101864851157620936228437782681120197702065605045457656/439884241192061278471225266607914888097852921875:ℝ), (5220457381371903239332542178247602516291391550735291/11279083107488750730031417092510638156355203125:ℝ), (101725623172965369460389202304598474845698873946877568/439884241192061278471225266607914888097852921875:ℝ), (0:ℝ)]]
theorem admission21_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (81302956714413862177698676256899752616189835013897/7687534301536780785570725085977682695034903756800000:ℝ) admission21_09_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission21_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_09_coefficients]
def admission21_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(169900225709859407263267437343744/3446284160104278823994625:ℝ), (763197118316307496971714356276224/5743806933507131373324375:ℝ), (677138124162791008666075843035136/5743806933507131373324375:ℝ), (591335506026419401313021646995456/17231420800521394119973125:ℝ)],
![(43875426087424527437943064621568/689256832020855764798925:ℝ), (111633717511871764222276044435968/689256832020855764798925:ℝ), (91694344064092568318491000291328/689256832020855764798925:ℝ), (23936972253647336812878020476928/689256832020855764798925:ℝ)],
![(3200618644371575233702108097728/229752277340285254932975:ℝ), (19179532242957123452255836126784/689256832020855764798925:ℝ), (383088441157941041309980473344/27570273280834230591957:ℝ), (0:ℝ)]]
theorem admission21_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (106969065908644595991594113/321216965285822601968798924800:ℝ) admission21_10_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission21_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_10_coefficients]
def admission21_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(606694067108130327063325888110914158525242515542324/17595369647682451138849010664316595523914116875:ℝ), (23142378066077271181031721989201051607375306006016/451163324299550029201256683700425526254208125:ℝ), (99136702936835766236153370946674925823737213833216/5865123215894150379616336888105531841304705625:ℝ)],
![(60745229597661455424465875420719025789875360759721/3519073929536490227769802132863319104782823375:ℝ), (20146884524936611444626787034668239723370371705728/1173024643178830075923267377621106368260941125:ℝ), (0:ℝ)]]
theorem admission21_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (808802937904755866674931615561443098842604787537/2402354469230243995490851589368025842198407424000:ℝ) admission21_11_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission21_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_11_coefficients]
def admission21_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission21_12_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission21_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_12_coefficients]
def admission21_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission21_13_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission21_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_13_coefficients]
def admission21_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission21_14_coefficients (63/128:ℝ) (255/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission21_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_14_coefficients]
theorem admission21_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (255/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission21_00_pos hδ hp
 · exact admission21_01_pos hδ hp
 · exact admission21_02_pos hδ hp
 · exact admission21_03_pos hδ hp
 · exact admission21_04_pos hδ hp
 · exact admission21_05_pos hδ hp
 · exact admission21_06_pos hδ hp
 · exact admission21_07_pos hδ hp
 · exact admission21_08_pos hδ hp
 · exact admission21_09_pos hδ hp
 · exact admission21_10_pos hδ hp
 · exact admission21_11_pos hδ hp
 · exact admission21_12_pos hδ hp
 · exact admission21_13_pos hδ hp
 · exact admission21_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
