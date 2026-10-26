/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission44_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(534364059703944391/34977005991111:ℝ),(4808561744281579520/314793053919999:ℝ)]]
theorem admission44_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission44_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission44_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_00_coefficients]
def admission44_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391063266158362624/34977005991111:ℝ),(3519169395425263616/314793053919999:ℝ)]]
theorem admission44_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission44_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission44_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_01_coefficients]
def admission44_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(656652920736164/115435663337:ℝ),(5909241130508288/1038920970033:ℝ)]]
theorem admission44_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission44_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission44_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_02_coefficients]
def admission44_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(311471546944936106322722816/104931017973333:ℝ),(16817670473357969404237021184/2833137485279991:ℝ),(8407938741880694533523505152/2833137485279991:ℝ)],
![(934314730559315743114805248/314793053919999:ℝ),(16815872100956178480049111040/2833137485279991:ℝ),(8407039561961936792015863808/2833137485279991:ℝ)]]
theorem admission44_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (125274651675849211097/247563330980412653568:ℝ) admission44_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission44_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_03_coefficients]
def admission44_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(484739511831104861891560/1038920970033:ℝ),(969308623917842320752640/1038920970033:ℝ),(484569118444650191912960/1038920970033:ℝ)],
![(484836345860103438820012/1038920970033:ℝ),(969502274952887989354496/1038920970033:ℝ),(484665935451332439703552/1038920970033:ℝ)]]
theorem admission44_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (3610321271752195/45391149794721792:ℝ) admission44_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission44_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_04_coefficients]
def admission44_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32493651980657517383892369982/118047395219999625:ℝ),(64987995377644688176132041676/118047395219999625:ℝ),(10831447683264728833073268898/39349131739999875:ℝ)],
![(32473286372420456065738712602/118047395219999625:ℝ),(324736331130769880415697696508/590236976099998125:ℝ),(54123299177509751850942458666/196745658699999375:ℝ)]]
theorem admission44_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (16236643186210228032869356301/346118623128156238170292224000:ℝ) admission44_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission44_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_05_coefficients]
def admission44_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(362349696831080815755995880194441460606505123840/32998524043161039460837289280333:ℝ),(1086836564800895346465660815510008726890343628800/32998524043161039460837289280333:ℝ),(1086624055753968426825060988743398017887643893760/32998524043161039460837289280333:ℝ),(362137187783793280160521198252334751603805388800/32998524043161039460837289280333:ℝ)],
![(362416539206706044176714732285064046896355966976/32998524043161039460837289280333:ℝ),(1087037078552201746950729471191865625116899639296/32998524043161039460837289280333:ℝ),(1086824556130815150866659530381669808504695685120/32998524043161039460837289280333:ℝ),(362204016784958796112200018731422630284152012800/32998524043161039460837289280333:ℝ)]]
theorem admission44_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82340463401076995105659352305414075/720863757230867294035144196758634496:ℝ) admission44_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission44_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_06_coefficients]
def admission44_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4192790266796144094298140811262523216680/2943405944443942508325509703:ℝ),(931611883446467626492761063012512727040/327045104938215834258389967:ℝ),(4191716717704946622294181217887248711680/2943405944443942508325509703:ℝ)],
![(4191767197556599167685311096519511061516/2943405944443942508325509703:ℝ),(310461516427873535279412040446181916672/109015034979405278086129989:ℝ),(4190693779474782316389799443975970488320/2943405944443942508325509703:ℝ)]]
theorem admission44_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (62446203522008393949118248283505/257198735966770954967494138527744:ℝ) admission44_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission44_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_07_coefficients]
def admission44_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5177288492015784950304060487808154306949488864426518359301389/21773730497229359863833726562719726562500000000:ℝ),(15540792657324252995176064822646276065442080681250500249416123/21773730497229359863833726562719726562500000000:ℝ),(3109943940789731053705284923525067766766054176665262455480773/4354746099445871972766745312543945312500000000:ℝ),(5186215538596635719262123380970933984131356092332847965414131/21773730497229359863833726562719726562500000000:ℝ)],
![(2601130805963410371215199116702676851208064004948712019539527/10886865248614679931916863281359863281250000000:ℝ),(4879907721834180339594020952199674818235192193191692355380351/6804290780384174957448039550849914550781250000:ℝ),(78123122248847341333141894812939139216273117540085423948876861/108868652486146799319168632813598632812500000000:ℝ),(5211181351783356067165973657037857489349455251508217315074803/21773730497229359863833726562719726562500000000:ℝ)]]
theorem admission44_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5177288492015784950304060487808154306949488864426518359301389/2091950177147471992970919053866570517525299200000000000000000000:ℝ) admission44_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission44_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_08_coefficients]
def admission44_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1430736731016620259261699698908691056856940800352568/1741898439778348789106698125017578125:ℝ),(4290829015104783699392603029563487581822635855621248/1741898439778348789106698125017578125:ℝ),(4289447885041753677811768305599650771614621295968256/1741898439778348789106698125017578125:ℝ),(1429355600956487296986435507224169224104245068824576/1741898439778348789106698125017578125:ℝ)],
![(1428541776942404004443579952069230206226332616073028/1741898439778348789106698125017578125:ℝ),(21421223774292071676848634752638537846536754755164864/8709492198891743945533490625087890625:ℝ),(21414321133675772490264671446356066729559540439711744/8709492198891743945533490625087890625:ℝ),(1427161248822041515848871866102268674070170151419904/1741898439778348789106698125017578125:ℝ)]]
theorem admission44_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (664573744322192629728872266645668388377023/77931216997931599355150723973906432000000000:ℝ) admission44_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission44_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_09_coefficients]
def admission44_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(131641549989914209597895407124222818942976/27667358254687412109375:ℝ),(394768677955560181233517923479139412246528/27667358254687412109375:ℝ),(394612709891423598708850203517194367664128/27667358254687412109375:ℝ),(131485581926017167937290187162277774360576/27667358254687412109375:ℝ)],
![(263057686903626442285694600705409360822272/27667358254687412109375:ℝ),(788861167081037178215358942954174692294656/27667358254687412109375:ℝ),(788549281348305133162832382924626902122496/27667358254687412109375:ℝ),(262745801171373526821605540675861570650112/27667358254687412109375:ℝ)],
![(43805370590385372887007557579052520005632/9222452751562470703125:ℝ),(131364137901466692577724096085336679964672/9222452751562470703125:ℝ),(131312165347465233583538268662335639912448/9222452751562470703125:ℝ),(43753398036463776801743605156051479953408/9222452751562470703125:ℝ)]]
theorem admission44_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5093565913436908368224232126499/2253376452657267175587840000000000:ℝ) admission44_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission44_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_10_coefficients]
def admission44_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3438420684505735214054369948575189462232/2943405944443942508325509703:ℝ),(763995940902095411636869301529165561856/327045104938215834258389967:ℝ),(3437542815683131277022214270747915845632/2943405944443942508325509703:ℝ)],
![(3437560640698002704415419848134192499700/2943405944443942508325509703:ℝ),(84867203614507844611343711011855728640/36338344993135092695376663:ℝ),(3436682884142913302538795862975324356608/2943405944443942508325509703:ℝ)]]
theorem admission44_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (25605282814375410247883169822211/128599367983385477483747069263872:ℝ) admission44_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission44_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_11_coefficients]
def admission44_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission44_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission44_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission44_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_12_coefficients]
def admission44_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission44_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission44_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission44_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_13_coefficients]
def admission44_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission44_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission44_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission44_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_14_coefficients]
theorem admission44_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission44_00_pos hδ hp
 · exact admission44_01_pos hδ hp
 · exact admission44_02_pos hδ hp
 · exact admission44_03_pos hδ hp
 · exact admission44_04_pos hδ hp
 · exact admission44_05_pos hδ hp
 · exact admission44_06_pos hδ hp
 · exact admission44_07_pos hδ hp
 · exact admission44_08_pos hδ hp
 · exact admission44_09_pos hδ hp
 · exact admission44_10_pos hδ hp
 · exact admission44_11_pos hδ hp
 · exact admission44_12_pos hδ hp
 · exact admission44_13_pos hδ hp
 · exact admission44_14_pos hδ hp
#print axioms admission44_all
end
end LewkoStage1Finite
