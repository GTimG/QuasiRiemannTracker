/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission01_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission01_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission01_00_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission01_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_00_coefficients]
def admission01_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission01_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission01_01_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission01_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_01_coefficients]
def admission01_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission01_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission01_02_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission01_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_02_coefficients]
def admission01_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(237897431694308106680124640/64169064140007830059431:ℝ), (312286909685680236051410656/64169064140007830059431:ℝ), (8432759042985408863476224/7129896015556425562159:ℝ)],
![(161310954168131850270740416/64169064140007830059431:ℝ), (159717050572900208670740416/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission01_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2795602206404551438122563/2737880069973667415869056:ℝ) admission01_03_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission01_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_03_coefficients]
def admission01_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1979329163097112916736126289573/3564948007778212781079500000:ℝ), (544:ℝ), (0:ℝ)],
![(1659349588170991606105099972989/1782474003889106390539750000:ℝ), (140602744515249308391501315696/111404625243069149408734375:ℝ), (38216840187620739166035157848/111404625243069149408734375:ℝ)]]
theorem admission01_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (243632356196082212183474131281/1825253379982444943912704000000:ℝ) admission01_04_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission01_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_04_coefficients]
def admission01_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7639257198788184852958187540689/10694844023334638343238500000:ℝ), (453949623616803765396820629038/334213875729207448226203125:ℝ), (71144129013277827837639976248/111404625243069149408734375:ℝ)],
![(215660185044166443542556820937/5347422011667319171619250000:ℝ), (614981248650677506788702908/13368555029168297929048125:ℝ), (0:ℝ)]]
theorem admission01_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (103891828160279140110240840163/912626689991222471956352000000:ℝ) admission01_05_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission01_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_05_coefficients]
def admission01_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2375904286545073125936694731528378386434978310164162883/52900606016098693363386369178953088764133895540625:ℝ), (23262814998701225924981588211660583470405688745041677839/264503030080493466816931845894765443820669477703125:ℝ), (11388881327215529732614025673349375817424397194220863424/264503030080493466816931845894765443820669477703125:ℝ), (0:ℝ)],
![(3191290392100527127245058765092093229277625282235789334/52900606016098693363386369178953088764133895540625:ℝ), (35052571144692741903998109435594480857723883655904259566/264503030080493466816931845894765443820669477703125:ℝ), (22756986149321692765138169173978798621366218238707081856/264503030080493466816931845894765443820669477703125:ℝ), (81221122490095321024215177042364718228801355421817088/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission01_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (55019479319824792835461881438556834157611304679049009/288907842989253664021907424209322468770523248179200000:ℝ) admission01_06_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission01_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_06_coefficients]
def admission01_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(44640621398361311013974631319184689847891803273700819/15250625157794217906561836159698187751822384300000:ℝ), (29594523124981599085402642979748049474436427775012394/7148730542716039643700860699858525508666742640625:ℝ), (197279678095143193887586882182730615560826420673832/158860678727023103193352459996856122414816503125:ℝ)],
![(12158323423933997530901418920609350356707454396598939/7625312578897108953280918079849093875911192150000:ℝ), (11201303181042852924623545665639296189736550218383636/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission01_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (649378940396513013213306820518154942887720301384697/1301386680131773261359943352294245354822176793600000:ℝ) admission01_07_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission01_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_07_coefficients]
def admission01_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (471055595109900425421397266754432695407029205222903376735575718842327516483/117226206927750411863589843033220340468677709612143607808000000000000000:ℝ), (5613328792720078757502753035308733264960027341779846333188277112287478055659/703357241566502471181539058199322042812066257672861646848000000000000000:ℝ), (2784035677188908736085314328027413085960566867408892850919885134516712956761/703357241566502471181539058199322042812066257672861646848000000000000000:ℝ)],
![(234619266708161638978907311010332628040824378238943415800105127228286191061/26050268206166758191908854007382297881928379913809690624000000000000000:ℝ), (6967469114841856508316081720467027494815172367516742538892861484847765951651/234452413855500823727179686066440680937355419224287215616000000000000000:ℝ), (22792488678872464712528915474585508699461341179877684431505757821632145877707/703357241566502471181539058199322042812066257672861646848000000000000000:ℝ), (8221667899720682120010991715076052341645662620684599747701254274905375181401/703357241566502471181539058199322042812066257672861646848000000000000000:ℝ)]]
theorem admission01_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (197892151864910155780522054120351730400281164522351372832841060062325727791/109262744138198058551356073998579601535363731586011640623005696000000000000000:ℝ) admission01_08_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission01_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_08_coefficients]
def admission01_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2644658147025281220379703863538735557040586505626949656961/142974610854320792874017213997170510173334852812500000:ℝ), (328318540064699953084282534057833059670397588136644114649/7148730542716039643700860699858525508666742640625000:ℝ), (18155702411629573714783236626595479189861257317250090268/496439621021947197479226437490175382546301572265625:ℝ), (908032235068293981359846282072732444907727614750626016/99287924204389439495845287498035076509260314453125:ℝ)],
![(572254049084441665727909108113739859601311528674219589497/71487305427160396437008606998585255086667426406250000:ℝ), (2264635638499347299253962250889105877885847840448697113/142974610854320792874017213997170510173334852812500:ℝ), (3887725934987438000337109663617386109320813897689101112/496439621021947197479226437490175382546301572265625:ℝ), (0:ℝ)]]
theorem admission01_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (546370502169838117751719437910190750661845341520494697/19520800201976598920399150284413680322332651904000000000:ℝ) admission01_09_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission01_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_09_coefficients]
def admission01_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(123862506728446721074933499805815147/626651016992263965424130859375:ℝ), (100319073306543825850095659645695153/208883672330754655141376953125:ℝ), (77229291079707195632034025367385784/208883672330754655141376953125:ℝ), (10922030815300635639349719394177408/125330203398452793084826171875:ℝ)],
![(38283032994766813986535627386711964/125330203398452793084826171875:ℝ), (146312169446148102200374298951230948/208883672330754655141376953125:ℝ), (102051456934039462876718307198724576/208883672330754655141376953125:ℝ), (58669014792119241369710161676040704/626651016992263965424130859375:ℝ)],
![(6990603497260680372063164902070028/69627890776918218380458984375:ℝ), (13851344283275272865627194578512556/69627890776918218380458984375:ℝ), (6858623882802175469564029676442528/69627890776918218380458984375:ℝ), (0:ℝ)]]
theorem admission01_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (505915245315347897235867293556747/73010135199297797756508160000000000:ℝ) admission01_10_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission01_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_10_coefficients]
def admission01_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(564237021483553625707567023853443557026428916573354051/228759377366913268598427542395472816277335764500000:ℝ), (24954609447537666170791190134655575997998485216523687/7148730542716039643700860699858525508666742640625:ℝ), (835918365101112742906031478418117664090996044673832/794303393635115515966762299984280612074082515625:ℝ)],
![(30519098186923655826807841957750571801017797776180623/22875937736691326859842754239547281627733576450000:ℝ), (9347812941628347829696599844698674165780544115168894/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission01_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (8010710460292792413923597372169146081586527834200811/19520800201976598920399150284413680322332651904000000:ℝ) admission01_11_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission01_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_11_coefficients]
def admission01_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission01_12_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission01_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_12_coefficients]
def admission01_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission01_13_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission01_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_13_coefficients]
def admission01_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission01_14_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission01_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_14_coefficients]
theorem admission01_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission01_00_pos hδ hp
 · exact admission01_01_pos hδ hp
 · exact admission01_02_pos hδ hp
 · exact admission01_03_pos hδ hp
 · exact admission01_04_pos hδ hp
 · exact admission01_05_pos hδ hp
 · exact admission01_06_pos hδ hp
 · exact admission01_07_pos hδ hp
 · exact admission01_08_pos hδ hp
 · exact admission01_09_pos hδ hp
 · exact admission01_10_pos hδ hp
 · exact admission01_11_pos hδ hp
 · exact admission01_12_pos hδ hp
 · exact admission01_13_pos hδ hp
 · exact admission01_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
