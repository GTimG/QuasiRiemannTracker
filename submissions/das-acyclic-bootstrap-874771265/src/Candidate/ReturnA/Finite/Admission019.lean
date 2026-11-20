/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission019_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4460443008810090496/73726050969:ℝ),(13076121546215391232/73726050969:ℝ),(12770914066000510976/73726050969:ℝ),(4155235528595210240/73726050969:ℝ)],
![(8920886017620180992/73726050969:ℝ),(26152243092430782464/73726050969:ℝ),(25541828132001021952/73726050969:ℝ),(8310471057190420480/73726050969:ℝ)],
![(4460443008810090496/73726050969:ℝ),(13076121546215391232/73726050969:ℝ),(12770914066000510976/73726050969:ℝ),(4155235528595210240/73726050969:ℝ)]]
theorem admission019_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (30958917205/32767133764:ℝ) admission019_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission019_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_00_coefficients]
def admission019_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3223525126876168192/73726050969:ℝ),(9502803220628504576/73726050969:ℝ),(9335031060628504576/73726050969:ℝ),(1018584322292056064/24575350323:ℝ)],
![(6447050253752336384/73726050969:ℝ),(19005606441257009152/73726050969:ℝ),(18670062121257009152/73726050969:ℝ),(2037168644584112128/24575350323:ℝ)],
![(3223525126876168192/73726050969:ℝ),(9502803220628504576/73726050969:ℝ),(9335031060628504576/73726050969:ℝ),(1018584322292056064/24575350323:ℝ)]]
theorem admission019_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5691783441/8191783441:ℝ) admission019_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission019_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_01_coefficients]
def admission019_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1019202535276216844288/46078781855625:ℝ),(3006871796275424002048/46078781855625:ℝ),(2956135986722197471232/46078781855625:ℝ),(322822241907663437824/15359593951875:ℝ)],
![(2038405070552433688576/46078781855625:ℝ),(6013743592550848004096/46078781855625:ℝ),(5912271973444394942464/46078781855625:ℝ),(645644483815326875648/15359593951875:ℝ)],
![(1019202535276216844288/46078781855625:ℝ),(3006871796275424002048/46078781855625:ℝ),(2956135986722197471232/46078781855625:ℝ),(322822241907663437824/15359593951875:ℝ)]]
theorem admission019_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115450230327009/327671337640000:ℝ) admission019_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission019_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_02_coefficients]
def admission019_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7605831666687803392/221178152907:ℝ),(22082391880474034176/221178152907:ℝ),(21354661560884658176/221178152907:ℝ),(6878101347098427392/221178152907:ℝ)],
![(14840426548602994688/221178152907:ℝ),(43052469185677623296/221178152907:ℝ),(41598772965546262528/221178152907:ℝ),(13386730328471633920/221178152907:ℝ)],
![(7234594881915191296/221178152907:ℝ),(20970077305203589120/221178152907:ℝ),(20244111404661604352/221178152907:ℝ),(6508628981373206528/221178152907:ℝ)]]
theorem admission019_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (6207112294553/12582579365376:ℝ) admission019_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission019_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_03_coefficients]
def admission019_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17866122876385426432/3071918790375:ℝ),(16938330551058584576/1023972930125:ℝ),(48081161366212050944/3071918790375:ℝ),(5044097529807241216/1023972930125:ℝ)],
![(37382166526061210368/3071918790375:ℝ),(177400961295705922816/5119864650625:ℝ),(504181123445739814912/15359593951875:ℝ),(52963024062976032768/5119864650625:ℝ)],
![(6505347883225261312/1023972930125:ℝ),(92709308540412999936/5119864650625:ℝ),(87925105538226520064/5119864650625:ℝ),(27742536413939826688/5119864650625:ℝ)]]
theorem admission019_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (346350690981027/4194193121792000:ℝ) admission019_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission019_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_04_coefficients]
def admission019_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(47322367034858092928/15359593951875:ℝ),(429380651789808831872/46078781855625:ℝ),(432500646330642485632/46078781855625:ℝ),(145087095645407932544/46078781855625:ℝ)],
![(5330175011168201728/1023972930125:ℝ),(728692523938519424512/46078781855625:ℝ),(737074745802064315136/46078781855625:ℝ),(248240097366113968384/46078781855625:ℝ)],
![(32630258132664932992/15359593951875:ℝ),(59862374429742118528/9215756371125:ℝ),(304574099471421829504/46078781855625:ℝ),(20630600344141207168/9215756371125:ℝ)]]
theorem admission019_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (764771674984334367/21474268783575040000:ℝ) admission019_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission019_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_05_coefficients]
def admission019_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3129358455890419653262524689408/335191053141487793402595:ℝ),(215751079170150673985160538049536/8379776328537194835064875:ℝ),(65835070169855087515274441326592/2793258776179064945021625:ℝ),(11996151561918333738445180633088/1675955265707438967012975:ℝ)],
![(162639079046991053628142698217216/8379776328537194835064875:ℝ),(2247062867293897129491109074664192/41898881642685974175324375:ℝ),(687236256831862915784583116570624/13966293880895324725108125:ℝ),(125553223086808384240670753226752/8379776328537194835064875:ℝ)],
![(84405117649730562296579580982016/8379776328537194835064875:ℝ),(1168307471443143759565306384416512/41898881642685974175324375:ℝ),(358060905982587478208210909937664/13966293880895324725108125:ℝ),(65572465277216715548444850061312/8379776328537194835064875:ℝ)]]
theorem admission019_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (91523373122545881183206029/762745863148630000987238400:ℝ) admission019_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission019_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_06_coefficients]
def admission019_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1303050657242138337041121381376/75493480437272025541125:ℝ),(11302166025808321128488737350656/226480441311816076623375:ℝ),(10883185534895085516654201307136/226480441311816076623375:ℝ),(1163390493604393133096276033536/75493480437272025541125:ℝ)],
![(2456579343088241822026027364096/75493480437272025541125:ℝ),(106429871866845154197498116129024/1132402206559080383116875:ℝ),(102374739258363480954385285136384/1132402206559080383116875:ℝ),(437247433837892721163701059584/15098696087454405108225:ℝ)],
![(230705737169220696996981196544/15098696087454405108225:ℝ),(49919041737803548555054429375744/1132402206559080383116875:ℝ),(47958811583888053371114278600704/1132402206559080383116875:ℝ),(1022846675585070472722229264384/75493480437272025541125:ℝ)]]
theorem admission019_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (31214803332063918234931313/137431687053807207385088000:ℝ) admission019_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission019_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_07_coefficients]
def admission019_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63059922743811343144191924139738122409/737241019895234624425048828125000:ℝ),(842198445667681619675961261712797940997/2211723059685703873275146484375000:ℝ),(1116828144275586863723979787428880749263/2211723059685703873275146484375000:ℝ),(17164778460900706709126518781145265759/81915668877248291602783203125000:ℝ)],
![(4438188960694977429594230022059270780621/7372410198952346244250488281250000:ℝ),(8828285779937702875504400892336603428387/4423446119371407746550292968750000:ℝ),(12094396599939526581087630896056980917923/5529307649214259683187866210937500:ℝ),(32487657759364093134741767078357465503/40957834438624145801391601562500:ℝ)],
![(3807589733256863998152310780661889556531/7372410198952346244250488281250000:ℝ),(7143888888602339636152478368911007546393/4423446119371407746550292968750000:ℝ),(18604652478501118843555362854969558089531/11058615298428519366375732421875000:ℝ),(47810537057827479560357015375569665247/81915668877248291602783203125000:ℝ)]]
theorem admission019_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (63059922743811343144191924139738122409/43978139857218306363228160000000000000000:ℝ) admission019_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission019_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_08_coefficients]
def admission019_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(383687181646365777376949670337046408/442344611937140774655029296875:ℝ),(1047057087794216923353773612029108712/442344611937140774655029296875:ℝ),(37775443769106569100943096513756672/17693784477485630986201171875:ℝ),(281077900700474661148656721089354496/442344611937140774655029296875:ℝ)],
![(2810025496668905339877851137118404562/2211723059685703873275146484375:ℝ),(300898687882277381500727209909738298/88468922387428154931005859375:ℝ),(6624354141145986367593179530271802688/2211723059685703873275146484375:ℝ),(76501799804789534434894349260244992/88468922387428154931005859375:ℝ)],
![(891589588437076452993102785433172522/2211723059685703873275146484375:ℝ),(457436351617169984149862437519582778/442344611937140774655029296875:ℝ),(1902423670007665229975292466052218688/2211723059685703873275146484375:ℝ),(101431098323473011025815025211870464/442344611937140774655029296875:ℝ)]]
theorem admission019_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (396215227826066449319589942233869/103073765290355405538816000000000000:ℝ) admission019_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission019_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_09_coefficients]
def admission019_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22820660626052548896310888/89997620811767578125:ℝ),(20474329232032604569400888/29999206937255859375:ℝ),(54445061653313132289972664/89997620811767578125:ℝ),(15845722864517867478080888/89997620811767578125:ℝ)],
![(32884516035711241069028776/89997620811767578125:ℝ),(28650705023492326800978896/29999206937255859375:ℝ),(73333906344106667130037048/89997620811767578125:ℝ),(20272582699965927796129136/89997620811767578125:ℝ)],
![(1039938503748957544580751/9999735645751953125:ℝ),(500051688854516436012844/1999947129150390625:ℝ),(5648790099311507315877311/29999206937255859375:ℝ),(1268928471100008409426904/29999206937255859375:ℝ)]]
theorem admission019_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (475848176662503153535089/671070899486720000000000000:ℝ) admission019_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission019_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_10_coefficients]
def admission019_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5357108629706140391093639791616/377467402186360127705625:ℝ),(15491448576364923250789004919808/377467402186360127705625:ℝ),(44765041862224584140841611362304/1132402206559080383116875:ℝ),(14362022022248235561755515977728/1132402206559080383116875:ℝ)],
![(2017310230641606104969486430464/75493480437272025541125:ℝ),(29138755454147878977552859288832/377467402186360127705625:ℝ),(84112139521817880408218852417536/1132402206559080383116875:ℝ),(215644212951986680400820568064/9059217652472643064935:ℝ)],
![(4729442523501890133753792360704/377467402186360127705625:ℝ),(13647306877782955726763854369024/377467402186360127705625:ℝ),(39347097659593296267377241055232/1132402206559080383116875:ℝ),(12593504596750099488347055030272/1132402206559080383116875:ℝ)]]
theorem admission019_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (384323260398867782237153779/2061475305807108110776320000:ℝ) admission019_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission019_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_11_coefficients]
def admission019_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5391512338038784/10986328125:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/10986328125:ℝ)],
![(10783024676077568/10986328125:ℝ),(10783024676077568/3662109375:ℝ),(10783024676077568/3662109375:ℝ),(10783024676077568/10986328125:ℝ)],
![(5391512338038784/10986328125:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/10986328125:ℝ)]]
theorem admission019_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission019_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission019_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_12_coefficients]
def admission019_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1885668800201187328/6866455078125:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/6866455078125:ℝ)],
![(3771337600402374656/6866455078125:ℝ),(3771337600402374656/2288818359375:ℝ),(3771337600402374656/2288818359375:ℝ),(3771337600402374656/6866455078125:ℝ)],
![(1885668800201187328/6866455078125:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/6866455078125:ℝ)]]
theorem admission019_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (230184179712059/50000000000000000:ℝ) admission019_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission019_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_13_coefficients]
def admission019_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(268435456/9:ℝ),(268435456/3:ℝ),(268435456/3:ℝ),(268435456/9:ℝ)],
![(536870912/9:ℝ),(536870912/3:ℝ),(536870912/3:ℝ),(536870912/9:ℝ)],
![(268435456/9:ℝ),(268435456/3:ℝ),(268435456/3:ℝ),(268435456/9:ℝ)]]
theorem admission019_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission019_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission019_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission019_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission019_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission019_14_coefficients]
theorem admission019_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission019_00_pos hd hp
 · exact admission019_01_pos hd hp
 · exact admission019_02_pos hd hp
 · exact admission019_03_pos hd hp
 · exact admission019_04_pos hd hp
 · exact admission019_05_pos hd hp
 · exact admission019_06_pos hd hp
 · exact admission019_07_pos hd hp
 · exact admission019_08_pos hd hp
 · exact admission019_09_pos hd hp
 · exact admission019_10_pos hd hp
 · exact admission019_11_pos hd hp
 · exact admission019_12_pos hd hp
 · exact admission019_13_pos hd hp
 · exact admission019_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission019_all
