/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission35_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8427618923146631/34977005991111:ℝ),(75133777254399680/314793053919999:ℝ)]]
theorem admission35_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission35_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission35_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_00_coefficients]
def admission35_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6154113533724416/34977005991111:ℝ),(54987021803519744/314793053919999:ℝ)]]
theorem admission35_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission35_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission35_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_01_coefficients]
def admission35_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10329672086820/115435663337:ℝ),(92331892664192/1038920970033:ℝ)]]
theorem admission35_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission35_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission35_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_02_coefficients]
def admission35_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(403268682666886398976/34977005991111:ℝ),(64890582037606444368896/2833137485279991:ℝ),(32226380341588646051840/2833137485279991:ℝ)],
![(3605004914651229528832/314793053919999:ℝ),(64451333026096747576064/2833137485279991:ℝ),(32006853994235681816576/2833137485279991:ℝ)]]
theorem admission35_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1953543334609111439/3868177046568947712:ℝ) admission35_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission35_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_03_coefficients]
def admission35_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(628424221644035024/346306990011:ℝ),(1242952271098803200/346306990011:ℝ),(614561077572861952/346306990011:ℝ)],
![(636392076126194620/346306990011:ℝ),(3776396706108804352/1038920970033:ℝ),(1867320197240619008/1038920970033:ℝ)]]
theorem admission35_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9377457848707/118206119257088:ℝ) admission35_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission35_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_04_coefficients]
def admission35_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(200546825445939161606/185901409795275:ℝ),(1274304079191827620450292/590236976099998125:ℝ),(212513618134064900960414/196745658699999375:ℝ)],
![(4816667992363513290458/4647535244881875:ℝ),(1224427075926062262693476/590236976099998125:ℝ),(40845534231603394526854/39349131739999875:ℝ)]]
theorem admission35_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2408333996181756645229/51981801780664074240000:ℝ) admission35_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission35_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_05_coefficients]
def admission35_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22346605218640539782560571403155673217024/32998524043161039460837289280333:ℝ),(66222417973300888938232999209717541402624/32998524043161039460837289280333:ℝ),(65409093667084042424596628947508848230400/32998524043161039460837289280333:ℝ),(21533275292434786128324063540946980044800/32998524043161039460837289280333:ℝ)],
![(22604819976688525574451688952105093114368/32998524043161039460837289280333:ℝ),(66993762489414750137762060952527016176128/32998524043161039460837289280333:ℝ),(66177155869186031388714038851170686402560/32998524043161039460837289280333:ℝ),(21788207700445329767235579650748763340800/32998524043161039460837289280333:ℝ)]]
theorem admission35_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (641741612328135553846480355887025/5631748103366150734649564037176832:ℝ) admission35_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission35_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_06_coefficients]
def admission35_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16427223364724076770650990026833648/2943405944443942508325509703:ℝ),(1207054693382669088382932825740288/109015034979405278086129989:ℝ),(16163778186596901836544685962444800/2943405944443942508325509703:ℝ)],
![(16175431542101022756810956743778516/2943405944443942508325509703:ℝ),(3565438689545214484813976119801088/327045104938215834258389967:ℝ),(15914037407748194340357729441136640/2943405944443942508325509703:ℝ)]]
theorem admission35_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (971315759750256002219099697335/4018730249480796171367095914496:ℝ) admission35_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission35_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_07_coefficients]
def admission35_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2699285263263003573755892581437822922947066404339103/215995838524192298233827035156250000000000000:ℝ),(214466079771994439529359112007245195280739469841262291/5486294298514484375139206692968750000000000000:ℝ),(141756195194178038427540559133838658586384368419126534691/3483796879556697578213396250035156250000000000000:ℝ),(49106897954171549798608279048060142987704135980510372193/3483796879556697578213396250035156250000000000000:ℝ)],
![(7323610360153679094206394066742971347894185244273543/431991677048384596467654070312500000000000000:ℝ),(2873569931957347917217327584472309654153887866649788021/54862942985144843751392066929687500000000000000:ℝ),(187755365263688612583653779928976669412694729786700818083/3483796879556697578213396250035156250000000000000:ℝ),(64344821041769418392266894811563258965547861063133266273/3483796879556697578213396250035156250000000000000:ℝ)]]
theorem admission35_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2699285263263003573755892581437822922947066404339103/1236926750044670434305820902555648000000000000000000000:ℝ) admission35_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission35_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_08_coefficients]
def admission35_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(481782671206116133254728172719063185138496108/8709492198891743945533490625087890625:ℝ),(1418588910515172201957588984385018266572880092/8709492198891743945533490625087890625:ℝ),(1391888749263389024544868908159649388907920384/8709492198891743945533490625087890625:ℝ),(18203309427968556375599116529807373292691456/348379687955669757821339625003515625:ℝ)],
![(439191126916237637805804391155283430877895001/8709492198891743945533490625087890625:ℝ),(1291554731608817918945448776991760140167141069/8709492198891743945533490625087890625:ℝ),(1265592167764387148365195274950587031320374528/8709492198891743945533490625087890625:ℝ),(82645758052754078197714358886904030945288192/1741898439778348789106698125017578125:ℝ)]]
theorem admission35_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10088593512299081811244428575061527215001/1217675265592681239924230062092288000000000:ℝ) admission35_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission35_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_09_coefficients]
def admission35_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28237155206460924915722762676224/5533471650937482421875:ℝ),(14650421189238267983683274752/978717261123046875:ℝ),(44973708486227227135880980865024/3074150917187490234375:ℝ),(131796453988023071170800147202048/27667358254687412109375:ℝ)],
![(89608382545459736800527755764736/9222452751562470703125:ℝ),(787858674379123632499456289217536/27667358254687412109375:ℝ),(2204216511586996909503627210752/79276098150966796875:ℝ),(16682543526899499954592858308608/1844490550312494140625:ℝ)],
![(127541871165232763127628469904512/27667358254687412109375:ℝ),(373415036080568960915780512120448/27667358254687412109375:ℝ),(72843783761445403229440996905472/5533471650937482421875:ℝ),(118345812818406443359052942311424/27667358254687412109375:ℝ)]]
theorem admission35_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3611627588452345073213285593/1650422206536084357120000000000:ℝ) admission35_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission35_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_10_coefficients]
def admission35_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13474693055840115467682724378156304/2943405944443942508325509703:ℝ),(330041386014300378147144622329856/36338344993135092695376663:ℝ),(13259162022486996236932119051468800/2943405944443942508325509703:ℝ)],
![(13262990491096454559644455490119724/2943405944443942508325509703:ℝ),(2923523300657950020072337191443456/327045104938215834258389967:ℝ),(13049217798800967310316296841363456/2943405944443942508325509703:ℝ)]]
theorem admission35_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (398230523645049051218148707317/2009365124740398085683547957248:ℝ) admission35_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission35_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_11_coefficients]
def admission35_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission35_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission35_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission35_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_12_coefficients]
def admission35_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission35_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission35_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission35_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_13_coefficients]
def admission35_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission35_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission35_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission35_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_14_coefficients]
theorem admission35_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission35_00_pos hδ hp
 · exact admission35_01_pos hδ hp
 · exact admission35_02_pos hδ hp
 · exact admission35_03_pos hδ hp
 · exact admission35_04_pos hδ hp
 · exact admission35_05_pos hδ hp
 · exact admission35_06_pos hδ hp
 · exact admission35_07_pos hδ hp
 · exact admission35_08_pos hδ hp
 · exact admission35_09_pos hδ hp
 · exact admission35_10_pos hδ hp
 · exact admission35_11_pos hδ hp
 · exact admission35_12_pos hδ hp
 · exact admission35_13_pos hδ hp
 · exact admission35_14_pos hδ hp
#print axioms admission35_all
end
end LewkoStage1Finite
