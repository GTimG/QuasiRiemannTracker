/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission38_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(100416634023839573/104931017973333:ℝ),(300535109017598720/314793053919999:ℝ)]]
theorem admission38_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission38_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission38_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_00_coefficients]
def admission38_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(73449362404692992/104931017973333:ℝ),(219948087214078976/314793053919999:ℝ)]]
theorem admission38_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission38_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission38_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_01_coefficients]
def admission38_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(123320908924652/346306990011:ℝ),(369327570656768/1038920970033:ℝ)]]
theorem admission38_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission38_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission38_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_02_coefficients]
def admission38_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(687490035050009951581184/944379161759997:ℝ),(4117931353896408346532864/2833137485279991:ℝ),(2055463498746378491789312/2833137485279991:ℝ)],
![(686318967308389117896704/944379161759997:ℝ),(4110905725513898417715200/2833137485279991:ℝ),(2051951077188731064025088/2833137485279991:ℝ)]]
theorem admission38_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (3913786081674062851/7736354093137895424:ℝ) admission38_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission38_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_03_coefficients]
def admission38_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(118850129003560122500/1038920970033:ℝ),(237034554641152640000/1038920970033:ℝ),(118184822610165760000/1038920970033:ℝ)],
![(119229384926142083912/1038920970033:ℝ),(79264000453643671552/346306990011:ℝ),(39521004680839430144/346306990011:ℝ)]]
theorem admission38_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (450839319649375/5673893724340224:ℝ) admission38_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission38_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_04_coefficients]
def admission38_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7993994183387500412636704/118047395219999625:ℝ),(15990649194430050126637384/118047395219999625:ℝ),(177702962959087000776404/2623275449333325:ℝ)],
![(1582864000121048850995852/23609479043999925:ℝ),(79157149776811738362677288/590236976099998125:ℝ),(1466127452257195356112444/21860628744444375:ℝ)]]
theorem admission38_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (395716000030262212748963/8450161697464751908454400:ℝ) admission38_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission38_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_05_coefficients]
def admission38_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5572586686237410007406493192023151042119680/32998524043161039460837289280333:ℝ),(165007768967878609968444278158239295907840/326718059833277618424131577033:ℝ),(16613874313953953443182476183955101801512960/32998524043161039460837289280333:ℝ),(5520676311919642645296128781996083956940800/32998524043161039460837289280333:ℝ)],
![(151052828902135193397963219429679285915648/891852001166514580022629440009:ℝ),(16714836236735781499752249918499883497885696/32998524043161039460837289280333:ℝ),(16662873575941103550611613062225148006891520/32998524043161039460837289280333:ℝ),(5536991986032317438186465813023398087884800/32998524043161039460837289280333:ℝ)]]
theorem admission38_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10283060952871372262567521598182775/90107969653858411754393024594829312:ℝ) admission38_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission38_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_06_coefficients]
def admission38_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1030690731992253411346728740329107620/2943405944443942508325509703:ℝ),(685726245259129154203731221018045440/981135314814647502775169901:ℝ),(1026490099019043077660877292914606080/2943405944443942508325509703:ℝ)],
![(1026686687613716584798165894703945096/2943405944443942508325509703:ℝ),(683059614341105980870217700558542848/981135314814647502775169901:ℝ),(1022494246557463757721885988573675520/2943405944443942508325509703:ℝ)]]
theorem admission38_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1950253003230025783008357979915/8037460498961592342734191828992:ℝ) admission38_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission38_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_07_coefficients]
def admission38_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2434035838460872374831754855821090064757251975938132133733/696759375911339515642679250007031250000000000000:ℝ),(7372454409643296674397332932064628383810192694427749512987/696759375911339515642679250007031250000000000000:ℝ),(7442784137484232797848169142426959696582725639526911431121/696759375911339515642679250007031250000000000000:ℝ),(2504365479285815706480589435248174212049317049943544051867/696759375911339515642679250007031250000000000000:ℝ)],
![(2629995464021123044986633272369937498248444016129137181647/696759375911339515642679250007031250000000000000:ℝ),(39797090743441607454417141523822354560631543718616042865177/3483796879556697578213396250035156250000000000000:ℝ),(40144168333147426253225497914801455356944090391413442437397/3483796879556697578213396250035156250000000000000:ℝ),(2699410894807068424479419717021014096565716731001117096091/696759375911339515642679250007031250000000000000:ℝ)]]
theorem admission38_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2434035838460872374831754855821090064757251975938132133733/1021460047435289059067831569270786385510400000000000000000000:ℝ) admission38_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission38_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_08_coefficients]
def admission38_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22567611138175663929922502382665640463569588928/1741898439778348789106698125017578125:ℝ),(2694552368138831942106533870284931862371331796/69675937591133951564267925000703125:ℝ),(67024972949062211435550330819943114982587813888/1741898439778348789106698125017578125:ℝ),(22228775064652398089690872516600434868319420416/1741898439778348789106698125017578125:ℝ)],
![(22029527169924277284534427920563030834225877376/1741898439778348789106698125017578125:ℝ),(328759565238724630615604144927474222528881110344/8709492198891743945533490625087890625:ℝ),(327077151298623160509074394859634935618456592384/8709492198891743945533490625087890625:ℝ),(21693044563078721054152874195823933395156598784/1741898439778348789106698125017578125:ℝ)]]
theorem admission38_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (20688099444464417509224771686386044879109/2435350531185362479848460124184576000000000:ℝ) admission38_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission38_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_09_coefficients]
def admission38_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43489150313037672423223989432499712/9222452751562470703125:ℝ),(389012909248117887751759639673297408/27667358254687412109375:ℝ),(386624434690270922322870999454097408/27667358254687412109375:ℝ),(42692992438367980821927776026099712/9222452751562470703125:ℝ)],
![(257491528846555181405121502532872192/27667358254687412109375:ℝ),(255902664446646827347476668688381952/9222452751562470703125:ℝ),(254314442177977109467354989243891712/9222452751562470703125:ℝ),(252726863911210090264756464199401472/27667358254687412109375:ℝ)],
![(127017915431037378752171630445684736/27667358254687412109375:ℝ),(378676622449885722972523166445070336/27667358254687412109375:ℝ),(376300455967913898492826125873086464/27667358254687412109375:ℝ),(124641749885894116772474589873700864/27667358254687412109375:ℝ)]]
theorem admission38_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (14858454452263607594069789633/6601688826144337428480000000000:ℝ) admission38_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission38_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_10_coefficients]
def admission38_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(845303596398187568538074893072270172/2943405944443942508325509703:ℝ),(562389914553973395712208698990563328/981135314814647502775169901:ℝ),(841868154281214833511949308570632192/2943405944443942508325509703:ℝ)],
![(841937468136559305942691185236103800/2943405944443942508325509703:ℝ),(560148170682836123700258548395417600/981135314814647502775169901:ℝ),(838509046702238370686096153208946688/2943405944443942508325509703:ℝ)]]
theorem admission38_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (799664541914213534055801537713/4018730249480796171367095914496:ℝ) admission38_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
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
def admission38_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission38_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission38_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Finite
