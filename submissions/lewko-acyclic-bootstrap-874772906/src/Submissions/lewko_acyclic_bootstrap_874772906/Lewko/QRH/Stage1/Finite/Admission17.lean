/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission17_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8427618923146631/34977005991111:ℝ),(75133777254399680/314793053919999:ℝ)]]
theorem admission17_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission17_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission17_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_00_coefficients]
def admission17_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(6154113533724416/34977005991111:ℝ),(54987021803519744/314793053919999:ℝ)]]
theorem admission17_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission17_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission17_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_01_coefficients]
def admission17_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(10329672086820/115435663337:ℝ),(92331892664192/1038920970033:ℝ)]]
theorem admission17_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission17_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission17_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_02_coefficients]
def admission17_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3653852786330922132992/314793053919999:ℝ),(65330027365919909484032/2833137485279991:ℝ),(32445906688941610287104/2833137485279991:ℝ)],
![(1209813185660058023680/104931017973333:ℝ),(64890778354410212691200/2833137485279991:ℝ),(32226380341588646051840/2833137485279991:ℝ)]]
theorem admission17_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1966942159520791385/3868177046568947712:ℝ) admission17_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission17_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_03_coefficients]
def admission17_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1861102502561180648/1038920970033:ℝ),(3681050956715686400/1038920970033:ℝ),(1820046268196552704/1038920970033:ℝ)],
![(1885006066007659436/1038920970033:ℝ),(1242863616509360384/346306990011:ℝ),(614561077572861952/346306990011:ℝ)]]
theorem admission17_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (55543404180803/709236715542528:ℝ) admission17_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission17_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_04_coefficients]
def admission17_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5210673279933444789842/4647535244881875:ℝ),(1324019414201977035542156/590236976099998125:ℝ),(220745733499263874209074/196745658699999375:ℝ)],
![(200546825445939161606/185901409795275:ℝ),(254828482187242335557068/118047395219999625:ℝ),(42491957304643189176586/39349131739999875:ℝ)]]
theorem admission17_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (100273412722969580803/2079272071226562969600:ℝ) admission17_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission17_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_05_coefficients]
def admission17_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22085108110555111837689852415058616718336/32998524043161039460837289280333:ℝ),(65444526165104797455909424053503941743616/32998524043161039460837289280333:ℝ),(64637766486911695413096357469590521774080/32998524043161039460837289280333:ℝ),(21278342884424242489412547431145196748800/32998524043161039460837289280333:ℝ)],
![(22343322868603097629580969964008036615680/32998524043161039460837289280333:ℝ),(66215870681218658655438485796313416517120/32998524043161039460837289280333:ℝ),(65405828689013684377213767373252359946240/32998524043161039460837289280333:ℝ),(21533275292434786128324063540946980044800/32998524043161039460837289280333:ℝ)]]
theorem admission17_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1268288069035067706669124807783675/11263496206732301469299128074353664:ℝ) admission17_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission17_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_06_coefficients]
def admission17_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16681066231121477302144100071635752/2943405944443942508325509703:ℝ),(1225705636832774831110817617997312/109015034979405278086129989:ℝ),(16413518965445609332731642483752960/2943405944443942508325509703:ℝ)],
![(16429274408498423288304066788580620/2943405944443942508325509703:ℝ),(3621391519895531712997630496572160/327045104938215834258389967:ℝ),(16163778186596901836544685962444800/2943405944443942508325509703:ℝ)]]
theorem admission17_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (986558727209283559359416867825/4018730249480796171367095914496:ℝ) admission17_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission17_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_07_coefficients]
def admission17_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3473530692898335200817176259008320343894080373082869/431991677048384596467654070312500000000000000:ℝ),(284056541171456072627352836729237513275285667980023217/10972588597028968750278413385937500000000000000:ℝ),(192662612540055942715340276118553552932803828569107507233/6967593759113395156426792500070312500000000000000:ℝ),(68311071034532346050819442052583915085792217364246358539/6967593759113395156426792500070312500000000000000:ℝ)],
![(2699285263263003573755892581437822922947066404339103/215995838524192298233827035156250000000000000:ℝ),(537297960023670971265125162011511316930730377034320299/13715735746286210937848016732421875000000000000:ℝ),(284660952679077091027566717708829574585424551304256074017/6967593759113395156426792500070312500000000000000:ℝ),(98786917209728083238136673579590147041479667529492146699/6967593759113395156426792500070312500000000000000:ℝ)]]
theorem admission17_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3473530692898335200817176259008320343894080373082869/2473853500089340868611641805111296000000000000000000000:ℝ) admission17_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission17_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_08_coefficients]
def admission17_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(525111814350429605751169617035958516068852882/8709492198891743945533490625087890625:ℝ),(1547095432021550212777651042739541986611821818/8709492198891743945533490625087890625:ℝ),(1518920075955062221699997818145781571310475776/8709492198891743945533490625087890625:ℝ),(99387336226931485558276806411169701981626368/1741898439778348789106698125017578125:ℝ)],
![(19300810802422044412089833418887150472330071/348379687955669757821339625003515625:ℝ),(284012250623039185953102167069256772041216559/1741898439778348789106698125017578125:ℝ),(278524698891212069104064836987343842744585984/1741898439778348789106698125017578125:ℝ),(18203309427968556375599116529807373292691456/348379687955669757821339625003515625:ℝ)]]
theorem admission17_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2222083670406317916943251529517501622643/243535053118536247984846012418457600000000:ℝ) admission17_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission17_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_09_coefficients]
def admission17_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(51511276020281256095277058835968/9222452751562470703125:ℝ),(90763728443412499654988899906048/5533471650937482421875:ℝ),(444052422132481005026461749536768/27667358254687412109375:ℝ),(1787255119411416975769733660672/341572324131943359375:ℝ)],
![(59182250689764957719476385916416/5533471650937482421875:ℝ),(19296754942577949546657631841792/614830183437498046875:ℝ),(2096312897528625400519407597568/68314464826388671875:ℝ),(55312823732069569241629714743296/5533471650937482421875:ℝ)],
![(5651196997965567904648390762624/1106694330187496484375:ℝ),(16569777939958686294868626008704/1106694330187496484375:ℝ),(16186601360240896845490649729536/1106694330187496484375:ℝ),(5268022715638403455270414483456/1106694330187496484375:ℝ)]]
theorem admission17_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (160767294788769636696484817/66016888261443374284800000000:ℝ) admission17_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission17_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_10_coefficients]
def admission17_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13688153961641408357143439944124120/2943405944443942508325509703:ℝ),(335268505459997946607684313085952/36338344993135092695376663:ℝ),(13469106246173025163547941261574144/2943405944443942508325509703:ℝ)],
![(13476451396897747449105171056087540/2943405944443942508325509703:ℝ),(2970567375669228136217194408248320/327045104938215834258389967:ℝ),(13259162022486996236932119051468800/2943405944443942508325509703:ℝ)]]
theorem admission17_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (404637512893279914457156953475/2009365124740398085683547957248:ℝ) admission17_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission17_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_11_coefficients]
def admission17_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission17_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission17_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission17_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_12_coefficients]
def admission17_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission17_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission17_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission17_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_13_coefficients]
def admission17_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission17_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission17_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission17_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_14_coefficients]
theorem admission17_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission17_00_pos hδ hp
 · exact admission17_01_pos hδ hp
 · exact admission17_02_pos hδ hp
 · exact admission17_03_pos hδ hp
 · exact admission17_04_pos hδ hp
 · exact admission17_05_pos hδ hp
 · exact admission17_06_pos hδ hp
 · exact admission17_07_pos hδ hp
 · exact admission17_08_pos hδ hp
 · exact admission17_09_pos hδ hp
 · exact admission17_10_pos hδ hp
 · exact admission17_11_pos hδ hp
 · exact admission17_12_pos hδ hp
 · exact admission17_13_pos hδ hp
 · exact admission17_14_pos hδ hp
#print axioms admission17_all
end
end LewkoStage1Finite
