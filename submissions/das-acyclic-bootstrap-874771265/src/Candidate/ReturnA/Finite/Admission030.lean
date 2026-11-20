/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission030_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45218258172392676083579748352/23638787823:ℝ),(406883801009916662119432978432/70916363469:ℝ),(406803278468299239486648221696/70916363469:ℝ),(135574251975560605617954488320/70916363469:ℝ)],
![(90436516344785352167159496704/23638787823:ℝ),(813767602019833324238865956864/70916363469:ℝ),(813606556936598478973296443392/70916363469:ℝ),(271148503951121211235908976640/70916363469:ℝ)],
![(45218258172392676083579748352/23638787823:ℝ),(406883801009916662119432978432/70916363469:ℝ),(406803278468299239486648221696/70916363469:ℝ),(135574251975560605617954488320/70916363469:ℝ)]]
theorem admission030_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission030_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission030_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_00_coefficients]
def admission030_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(99281065539867413646363590656/70916363469:ℝ),(297798160623328535979090771968/70916363469:ℝ),(297753124627054831019090771968/70916363469:ℝ),(33078676514531236228787863552/23638787823:ℝ)],
![(198562131079734827292727181312/70916363469:ℝ),(595596321246657071958181543936/70916363469:ℝ),(595506249254109662038181543936/70916363469:ℝ),(66157353029062472457575727104/23638787823:ℝ)],
![(99281065539867413646363590656/70916363469:ℝ),(297798160623328535979090771968/70916363469:ℝ),(297753124627054831019090771968/70916363469:ℝ),(33078676514531236228787863552/23638787823:ℝ)]]
theorem admission030_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission030_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission030_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_01_coefficients]
def admission030_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31563890130978222364947139002368/44322727168125:ℝ),(18935624618585177720278245965824/8864545433625:ℝ),(94664575792917110107941042651136/44322727168125:ℝ),(31550342830969443871496951824384/44322727168125:ℝ)],
![(63127780261956444729894278004736/44322727168125:ℝ),(37871249237170355440556491931648/8864545433625:ℝ),(189329151585834220215882085302272/44322727168125:ℝ),(63100685661938887742993903648768/44322727168125:ℝ)],
![(31563890130978222364947139002368/44322727168125:ℝ),(18935624618585177720278245965824/8864545433625:ℝ),(94664575792917110107941042651136/44322727168125:ℝ),(31550342830969443871496951824384/44322727168125:ℝ)]]
theorem admission030_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission030_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission030_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_02_coefficients]
def admission030_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73677893759278984549409751040/70916363469:ℝ),(662912831922825749707827970048/212749090407:ℝ),(662724635123714633990968180736/212749090407:ℝ),(220845484478725837931369463808/212749090407:ℝ)],
![(147324307657804183476490993664/70916363469:ℝ),(1325542350332457899816036335616/212749090407:ℝ),(1325165961973865937143653728256/212749090407:ℝ),(63085219230688655393870053376/30392727201:ℝ)],
![(73646413898525198927081242624/70916363469:ℝ),(662629518409632150108208365568/212749090407:ℝ),(662441326850151303152685547520/212749090407:ℝ),(220751050136094749825720909824/212749090407:ℝ)]]
theorem admission030_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (784265275428079/1549191598768128:ℝ) admission030_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission030_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_03_coefficients]
def admission030_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(114876823038895767620815945728/703535351875:ℝ),(482256791546311118440718401536/984949492625:ℝ),(2410154800006298042003280101376/4924747463125:ℝ),(803008603547012823145399713792/4924747463125:ℝ)],
![(1608917867214732306721995227136/4924747463125:ℝ),(4824494498104347233192811429888/4924747463125:ℝ),(14466707194055351005630519312384/14774242389375:ℝ),(4819977301386506226218070704128/14774242389375:ℝ)],
![(160956021188492386675256721408/984949492625:ℝ),(2413210540372791640989219422208/4924747463125:ℝ),(7236242794036456879620679008256/14774242389375:ℝ),(2410951490745467756781871562752/14774242389375:ℝ)]]
theorem admission030_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821623579204596741/10327943991787520000:ℝ) admission030_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission030_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_04_coefficients]
def admission030_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34187192634589905903420440576/354581817345:ℝ),(12820562390138470860515538108416/44322727168125:ℝ),(12820926813812066350309332484096/44322727168125:ℝ),(94972522288829638393807765504/984949492625:ℝ)],
![(1707220059172854108738505670656/8864545433625:ℝ),(5121807105345035100561046765568/8864545433625:ℝ),(204878149668632428224144474112/354581817345:ℝ),(569122231847876571260356919296/2954848477875:ℝ)],
![(852540243308106461152994656256/8864545433625:ℝ),(1826924733798100663184242245632/6331818166875:ℝ),(12788841894766987177708726779904/44322727168125:ℝ),(284204664981387656078933622784/2954848477875:ℝ)]]
theorem admission030_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (813045733745676480439181/17327414718612144914432000:ℝ) admission030_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission030_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_05_coefficients]
def admission030_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3035043479243908488604226956334363601534976/12922071700256302459483125:ℝ),(5458814580994237753707282027772731914715136/7753243020153781475689875:ℝ),(27272761166795935527103352077157140730478592/38766215100768907378449375:ℝ),(1816763739795857319661877698099314392301568/7753243020153781475689875:ℝ)],
![(1214464797096491363332549952116724007436288/2584414340051260491896625:ℝ),(10921654737067414750562573136244210864750592/7753243020153781475689875:ℝ),(10913128968641714487580286565812411765358592/7753243020153781475689875:ℝ),(3634868622632853438647535727518372922916864/7753243020153781475689875:ℝ)],
![(433897215176935475436931829178465205092352/1846010242893757494211875:ℝ),(5462840156073176996855291108471478950035456/7753243020153781475689875:ℝ),(27292883676412636910798080751904918096314368/38766215100768907378449375:ℝ),(259729268976713731283665432774151218659328/1107606145736254496527125:ℝ)]]
theorem admission030_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (206542124464687881261611175671/1806636567355727014367330304000:ℝ) admission030_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission030_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_06_coefficients]
def admission030_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(522799998488108038769507026986831934652416/1047735543264024523741875:ℝ),(44796162176029811623408769225086556176384/29935301236114986392625:ℝ),(10662118526677789258469719196593303846912/7127452675265472950625:ℝ),(104453149149739930589049765201603626795008/209547108652804904748375:ℝ)],
![(209018047262083510767174211383684782620672/209547108652804904748375:ℝ),(626840466216263804588533022619865255510016/209547108652804904748375:ℝ),(208875605755109717651155365848548661788672/69849036217601634916125:ℝ),(208804398311148859132107286309465512476672/209547108652804904748375:ℝ)],
![(522290237822309515066364029931591978450944/1047735543264024523741875:ℝ),(313267330984055123224671638044259362275328/209547108652804904748375:ℝ),(521934220968336914590760588609671420444672/349245181088008174580625:ℝ),(104351249161408928543057521107861885681664/209547108652804904748375:ℝ)]]
theorem admission030_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (23726727058922035335639866641/97656030667877135911747584000:ℝ) admission030_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission030_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_07_coefficients]
def admission030_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2056299667448861644541705394994084651878780418816/426324683945322478736114501953125:ℝ),(75721755595609561443104873344973297884510548224/5220302252391703821258544921875:ℝ),(688776314913773150941424858108902541459973674752/47369409327258053192901611328125:ℝ),(6214029380604462123987984435185701996245546159872/1278974051835967436208343505859375:ℝ)],
![(593487815713705834890665643436116204968895613184/60903526277903211248016357421875:ℝ),(37479852020388893126217840565340573684306383764992/1278974051835967436208343505859375:ℝ),(4174440691522613143091260429234255334667398056448/142108227981774159578704833984375:ℝ),(1793336903760248897854590624505930033737072374272/182710578833709633744049072265625:ℝ)],
![(2098115042547079199692954109058728782903488873472/426324683945322478736114501953125:ℝ),(18928021899464550572657146595822115702601299450112/1278974051835967436208343505859375:ℝ),(43022688709822320209530323569541790005866878208/2900167917995391011810302734375:ℝ),(6339328945717280160994149936355808239913960460032/1278974051835967436208343505859375:ℝ)]]
theorem admission030_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (8032420575972115798991036699195643171401486011/3413325667119997855526554488012800000000000000000:ℝ) admission030_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission030_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_08_coefficients]
def admission030_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36258154959774920649575382832078176111148964864/2046358482937547897933349609375:ℝ),(5173134200063239597324080926815041500713517056/97445642044645137996826171875:ℝ),(108497190661344566682690851720418654121552248832/2046358482937547897933349609375:ℝ),(802656164987592864071124768514535198038163456/45474632954167731065185546875:ℝ)],
![(2065598606529760510221668376837619623773783552/58467385226787082798095703125:ℝ),(14440720120415268130349998683227480190258479104/136423898862503193195556640625:ℝ),(43266757628866318501729469312340358759463256064/409271696587509579586669921875:ℝ),(228631547860147597469815649882450101620703232/6496376136309675866455078125:ℝ)],
![(36037796268766697208183010357238510720933459456/2046358482937547897933349609375:ℝ),(35991661201633663470481426928432110446297776128/682119494312515965977783203125:ℝ),(15405228211855289403708070691611877096537718784/292336926133935413990478515625:ℝ),(265921556677813439405861593554205171102253056/15158210984722577021728515625:ℝ)]]
theorem admission030_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (34827011551538030539126402319930589/4069001277828213996322816000000000000:ℝ) admission030_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission030_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_09_coefficients]
def admission030_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45025084150184289273373276829256192/9618647388916015625:ℝ),(134863182013074083048094682179916288/9618647388916015625:ℝ),(1077209064087461811617813686976512/76949179111328125:ℝ),(44813035153239225060317805521403904/9618647388916015625:ℝ)],
![(161538872743548095557422432189966848/17313565300048828125:ℝ),(345609755292930706558966113542845952/12366832357177734375:ℝ),(2415453868201395824677130815750340608/86567826500244140625:ℝ),(89319993884688000315615853544472576/9618647388916015625:ℝ)],
![(402467375667359886560824699889523328/86567826500244140625:ℝ),(1205495958126296628436261974009007232/86567826500244140625:ℝ),(240717996317160096793949040519888896/17313565300048828125:ℝ),(6358117447201075625535889737777152/1374092484130859375:ℝ)]]
theorem admission030_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3410759986925702132572114923/1510830663941488640000000000000:ℝ) admission030_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission030_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_10_coefficients]
def admission030_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(142955187133942029634688584746036807860224/349245181088008174580625:ℝ),(183737095700726704889444873192386563407872/149676506180574931963125:ℝ),(36734934839564431099251589509948939173888/29935301236114986392625:ℝ),(142809536960498081050585758246539116937216/349245181088008174580625:ℝ)],
![(285767527710016053393452076008960996409344/349245181088008174580625:ℝ),(2571033944186446313620572309404161855717376/1047735543264024523741875:ℝ),(2570160266509270218200575722886315215159296/1047735543264024523741875:ℝ),(285476301817624021586786547169678782889984/349245181088008174580625:ℝ)],
![(28562468115214804751752698252584837709824/69849036217601634916125:ℝ),(1284874274281359379394458197057455911862272/1047735543264024523741875:ℝ),(1284437547124515129726770090038102344073216/1047735543264024523741875:ℝ),(142666764857125940536200788923139665952768/349245181088008174580625:ℝ)]]
theorem admission030_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (32438666689160059044343322267/162760051113128559852912640000:ℝ) admission030_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission030_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_11_coefficients]
def admission030_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(185250953342856592476864512/10986328125:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/10986328125:ℝ)],
![(370501906685713184953729024/10986328125:ℝ),(370501906685713184953729024/3662109375:ℝ),(370501906685713184953729024/3662109375:ℝ),(370501906685713184953729024/10986328125:ℝ)],
![(185250953342856592476864512/10986328125:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/10986328125:ℝ)]]
theorem admission030_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission030_12_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission030_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_12_coefficients]
def admission030_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6519211330033437406559993856/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(6519211330033437406559993856/762939453125:ℝ)],
![(13038422660066874813119987712/762939453125:ℝ),(39115267980200624439359963136/762939453125:ℝ),(39115267980200624439359963136/762939453125:ℝ),(13038422660066874813119987712/762939453125:ℝ)],
![(6519211330033437406559993856/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(6519211330033437406559993856/762939453125:ℝ)]]
theorem admission030_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission030_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission030_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_13_coefficients]
def admission030_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)],
![(18446744073709551616/9:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/9:ℝ)],
![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)]]
theorem admission030_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission030_14_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission030_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission030_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission030_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission030_14_coefficients]
theorem admission030_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3753/8192:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission030_00_pos hd hp
 · exact admission030_01_pos hd hp
 · exact admission030_02_pos hd hp
 · exact admission030_03_pos hd hp
 · exact admission030_04_pos hd hp
 · exact admission030_05_pos hd hp
 · exact admission030_06_pos hd hp
 · exact admission030_07_pos hd hp
 · exact admission030_08_pos hd hp
 · exact admission030_09_pos hd hp
 · exact admission030_10_pos hd hp
 · exact admission030_11_pos hd hp
 · exact admission030_12_pos hd hp
 · exact admission030_13_pos hd hp
 · exact admission030_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission030_all
