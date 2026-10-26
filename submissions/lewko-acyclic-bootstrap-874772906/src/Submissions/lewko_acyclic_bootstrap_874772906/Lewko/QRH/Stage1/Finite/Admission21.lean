/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission21_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38281681681119839/314793053919999:ℝ),(37566888627199840/314793053919999:ℝ)]]
theorem admission21_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission21_00_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission21_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_00_coefficients]
def admission21_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(27893510901759872/314793053919999:ℝ),(27493510901759872/314793053919999:ℝ)]]
theorem admission21_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission21_01_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission21_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_01_coefficients]
def admission21_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(46801102449284/1038920970033:ℝ),(46165946332096/1038920970033:ℝ)]]
theorem admission21_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission21_02_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission21_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_02_coefficients]
def admission21_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8220996658969728264448/2833137485279991:ℝ),(1802460150836516524288/314793053919999:ℝ),(8001713498558920454144/2833137485279991:ℝ)],
![(8166020513729603044480/2833137485279991:ℝ),(1790253336161142493312/314793053919999:ℝ),(7946831911720679395328/2833137485279991:ℝ)]]
theorem admission21_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1940144509697431493/3868177046568947712:ℝ) admission21_03_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission21_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_03_coefficients]
def admission21_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(487941541674617848/1038920970033:ℝ),(954671236318256896/1038920970033:ℝ),(466830049310154752/1038920970033:ℝ)],
![(493984399845407548/1038920970033:ℝ),(966622700463437696/1038920970033:ℝ),(472739290440663040/1038920970033:ℝ)]]
theorem admission21_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (56986090003681/709236715542528:ℝ) admission21_04_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission21_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_04_coefficients]
def admission21_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16977958844066074054954/65581886233333125:ℝ),(61241639419755296423044/118047395219999625:ℝ),(153379166657267581285634/590236976099998125:ℝ)],
![(16278481692972305435278/65581886233333125:ℝ),(293698615929965695726028/590236976099998125:ℝ),(147164706425231635041026/590236976099998125:ℝ)]]
theorem admission21_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (8139240846486152717639/183380245170676039680000:ℝ) admission21_05_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission21_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_05_coefficients]
def admission21_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2929526685235908655272780858300357438976/32998524043161039460837289280333:ℝ),(2860174118262431384981059779760923146752/10999508014387013153612429760111:ℝ),(8374527324147098696310882737326007418880/32998524043161039460837289280333:ℝ),(2723525962555666220904447456343595417600/32998524043161039460837289280333:ℝ)],
![(2962218184751143133564780498035276580608/32998524043161039460837289280333:ℝ),(2892587721599061379080274600010752158976/10999508014387013153612429760111:ℝ),(8470943221668642072748416672065798225920/32998524043161039460837289280333:ℝ),(2755392513556984175768386970068818329600/32998524043161039460837289280333:ℝ)]]
theorem admission21_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1298678380277474508716796615764425/11263496206732301469299128074353664:ℝ) admission21_06_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission21_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_06_coefficients]
def admission21_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4108439226174119657904163890291640/2943405944443942508325509703:ℝ),(8086431920215507996164283731455744/2943405944443942508325509703:ℝ),(3978509351937048585089432360284160/2943405944443942508325509703:ℝ)],
![(4044976466551456281524092085298460/2943405944443942508325509703:ℝ),(7960538051927294232751061383720832/2943405944443942508325509703:ℝ),(3916074157224871711042693229957120/2943405944443942508325509703:ℝ)]]
theorem admission21_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (956072792291228445078782526845/4018730249480796171367095914496:ℝ) admission21_07_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission21_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_07_coefficients]
def admission21_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(349133739619539658480420128264003193609603967566401239/172039352076873954479673888890625000000000000000:ℝ),(9982838469287925524576721624666516547201297252829963633/1548354168691865590317065000015625000000000000000:ℝ),(94846078428353596211799830862378310663103798870383448299/13935187518226790312853585000140625000000000000000:ℝ),(33279925161085423476603120621154251751424488717792275961/13935187518226790312853585000140625000000000000000:ℝ)],
![(5584338941343448544499707769281013810536956682169097/2150491900960924430995923611132812500000000000:ℝ),(12461556739726868161030418884021917415837312709612257/1533023929397886723086202970312500000000000000:ℝ),(117988363866467367477425128012261647522648572614023390571/13935187518226790312853585000140625000000000000000:ℝ),(40898886704884357773432428502905809740346351259103723001/13935187518226790312853585000140625000000000000000:ℝ)]]
theorem admission21_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (349133739619539658480420128264003193609603967566401239/123150565132533885400732008255062016000000000000000000000:ℝ) admission21_08_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission21_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_08_coefficients]
def admission21_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(57973090417363223163386790625984863226706279/8709492198891743945533490625087890625:ℝ),(55857759855817692831535962280477909345567349/2903164066297247981844496875029296875:ℝ),(161253559294015060226720576630434243603925888/8709492198891743945533490625087890625:ℝ),(10330719756594259774714294860863003868161024/1741898439778348789106698125017578125:ℝ)],
![(105112466770683679951580938615803209941887799/17418984397783487891066981250175781250:ℝ),(101006167550323703785231536796891184687358949/5806328132594495963688993750058593750:ℝ),(145374643457555910582329462882167720803606464/8709492198891743945533490625087890625:ℝ),(9284371120708171814679141890596399428389888/1741898439778348789106698125017578125:ℝ)]]
theorem admission21_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (9066768672566574037772599502535546316787/1217675265592681239924230062092288000000000:ℝ) admission21_09_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission21_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_09_coefficients]
def admission21_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5686177823083233886414822911232/9222452751562470703125:ℝ),(16305149971996330237967422798592/9222452751562470703125:ℝ),(46662069131610467573169390590464/27667358254687412109375:ℝ),(14805212364433678518511590928384/27667358254687412109375:ℝ)],
![(10783355361275599345604951207168/9222452751562470703125:ℝ),(6171998970033250962110580604672/1844490550312494140625:ℝ),(88122935648376125659508717275648/27667358254687412109375:ℝ),(27893137296266659264664861827072/27667358254687412109375:ℝ)],
![(1018609463180647899711199635008/1844490550312494140625:ℝ),(1615843339941372146989478585536/1024716972395830078125:ℝ),(13808168987672270706857075014528/9222452751562470703125:ℝ),(4358646389900035882507765919744/9222452751562470703125:ℝ)]]
theorem admission21_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1064122653784188447877872539/550140735512028119040000000000:ℝ) admission21_10_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission21_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_10_coefficients]
def admission21_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3368558803710650613493583293792072/2943405944443942508325509703:ℝ),(6630368896627930137149351308055552/2943405944443942508325509703:ℝ),(3262304449700241827579074210340864/2943405944443942508325509703:ℝ)],
![(3315191463663872698435198696092772/2943405944443942508325509703:ℝ),(6524519727852554375823422570244608/2943405944443942508325509703:ℝ),(3209818393778734595925118657814528/2943405944443942508325509703:ℝ)]]
theorem admission21_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (391823534396818187979140461159/2009365124740398085683547957248:ℝ) admission21_11_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission21_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_11_coefficients]
def admission21_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission21_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission21_12_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission21_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_12_coefficients]
def admission21_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission21_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission21_13_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission21_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_13_coefficients]
def admission21_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission21_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission21_14_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission21_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission21_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission21_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission21_14_coefficients]
theorem admission21_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
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
#print axioms admission21_all
end
end LewkoStage1Finite
