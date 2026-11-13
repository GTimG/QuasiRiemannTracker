/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission023_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1083273574054126157824/73726050969:ℝ),(3230287443428626137088/73726050969:ℝ),(3210754164694873800704/73726050969:ℝ),(1063740295320373821440/73726050969:ℝ)],
![(2166547148108252315648/73726050969:ℝ),(6460574886857252274176/73726050969:ℝ),(6421508329389747601408/73726050969:ℝ),(2127480590640747642880/73726050969:ℝ)],
![(1083273574054126157824/73726050969:ℝ),(3230287443428626137088/73726050969:ℝ),(3210754164694873800704/73726050969:ℝ),(1063740295320373821440/73726050969:ℝ)]]
theorem admission023_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (30958917205/32767133764:ℝ) admission023_00_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission023_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_00_coefficients]
def admission023_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(793010177760299057152/73726050969:ℝ),(2368293115040897171456/73726050969:ℝ),(2357555696800897171456/73726050969:ℝ),(260757586506766352384/24575350323:ℝ)],
![(1586020355520598114304/73726050969:ℝ),(4736586230081794342912/73726050969:ℝ),(4715111393601794342912/73726050969:ℝ),(521515173013532704768/24575350323:ℝ)],
![(793010177760299057152/73726050969:ℝ),(2368293115040897171456/73726050969:ℝ),(2357555696800897171456/73726050969:ℝ),(260757586506766352384/24575350323:ℝ)]]
theorem admission023_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5691783441/8191783441:ℝ) admission023_01_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission023_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_01_coefficients]
def admission023_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(251174573596492018221056/46078781855625:ℝ),(750276628978069556690944/46078781855625:ℝ),(149405907433332611743744/9215756371125:ℝ),(82642493928361840082944/15359593951875:ℝ)],
![(502349147192984036442112/46078781855625:ℝ),(1500553257956139113381888/46078781855625:ℝ),(298811814866665223487488/9215756371125:ℝ),(165284987856723680165888/15359593951875:ℝ)],
![(251174573596492018221056/46078781855625:ℝ),(750276628978069556690944/46078781855625:ℝ),(149405907433332611743744/9215756371125:ℝ),(82642493928361840082944/15359593951875:ℝ)]]
theorem admission023_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115450230327009/327671337640000:ℝ) admission023_02_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission023_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_02_coefficients]
def admission023_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1759657019328572686336/221178152907:ℝ),(5232694606781514514432/221178152907:ℝ),(5186539069497310969856/221178152907:ℝ),(1713501482044369141760/221178152907:ℝ)],
![(3471956267074800582656/221178152907:ℝ),(10323378258465511178240/221178152907:ℝ),(10231132492666620608512/221178152907:ℝ),(3379710501275910012928/221178152907:ℝ)],
![(1712299247746227896320/221178152907:ℝ),(5090683651683996663808/221178152907:ℝ),(5044593423169309638656/221178152907:ℝ),(1666209019231540871168/221178152907:ℝ)]]
theorem admission023_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (6207112294553/12582579365376:ℝ) admission023_03_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission023_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_03_coefficients]
def admission023_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20738075725947257534464/15359593951875:ℝ),(20441885500238812342272/5119864650625:ℝ),(60441148652090480918528/15359593951875:ℝ),(6617855959107100475392/5119864650625:ℝ)],
![(42466191539779114067968/15359593951875:ℝ),(41866586936515676239872/5119864650625:ℝ),(123809171750133507817472/15359593951875:ℝ),(13558534160121864388608/5119864650625:ℝ)],
![(7242705271277285511168/5119864650625:ℝ),(856988057451074555904/204794586025:ℝ),(21122674366014342299648/5119864650625:ℝ),(6940678201014763913216/5119864650625:ℝ)]]
theorem admission023_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (14200378330222107/167767724871680000:ℝ) admission023_04_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission023_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_04_coefficients]
def admission023_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2067330135646328594432/3071918790375:ℝ),(18657260078928389287936/9215756371125:ℝ),(93536851280660967725056/46078781855625:ℝ),(31260502920713950201856/46078781855625:ℝ)],
![(6287135535858915022848/5119864650625:ℝ),(170333812015176905783296/46078781855625:ℝ),(170903034011512728203264/46078781855625:ℝ),(2286137672762642305024/1843151274225:ℝ)],
![(8524755929345102096384/15359593951875:ℝ),(77047511620534959343616/46078781855625:ℝ),(77366182730851760478208/46078781855625:ℝ),(25892938898352107423744/46078781855625:ℝ)]]
theorem admission023_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (12487435443376614399/343588300537200640000:ℝ) admission023_05_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission023_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_05_coefficients]
def admission023_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(84329549706952139516586610089515008/41898881642685974175324375:ℝ),(247167965686972446906863065848338432/41898881642685974175324375:ℝ),(80467760910647622746638558272421888/13966293880895324725108125:ℝ),(15712943277183470184007843811688448/8379776328537194835064875:ℝ)],
![(172327704423440934925958812621850624/41898881642685974175324375:ℝ),(505250911982916001386543397173446656/41898881642685974175324375:ℝ),(164543879170021253284481049560612864/13966293880895324725108125:ℝ),(32141625110222946365611712826048512/8379776328537194835064875:ℝ)],
![(87998154716488795409372202532335616/41898881642685974175324375:ℝ),(258082946295943554479680331325108224/41898881642685974175324375:ℝ),(84076118259373630537842491288190976/13966293880895324725108125:ℝ),(16428681833039476181603869014360064/8379776328537194835064875:ℝ)]]
theorem admission023_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3746257609649531885148964837/30509834525945200039489536000:ℝ) admission023_06_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission023_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_06_coefficients]
def admission023_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(480652669465302928637521549051904/125822467395453375901875:ℝ),(12848834887510070402242435780839424/1132402206559080383116875:ℝ),(12720536227166114167676272011378688/1132402206559080383116875:ℝ),(55967671531250268308953735626752/15098696087454405108225:ℝ)],
![(930849230962213248518618543429632/125822467395453375901875:ℝ),(24879631925159436965990323029727232/1132402206559080383116875:ℝ),(24627295445589958467747646686101504/1132402206559080383116875:ℝ),(541687106606029382561659369816064/75493480437272025541125:ℝ)],
![(450196561496910319881096994377728/125822467395453375901875:ℝ),(12030797037649366563747887248887808/1132402206559080383116875:ℝ),(11906759218423844300071374674722816/1132402206559080383116875:ℝ),(261848748949778041016890691682304/75493480437272025541125:ℝ)]]
theorem admission023_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (31214803332063918234931313/137431687053807207385088000:ℝ) admission023_07_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission023_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_07_coefficients]
def admission023_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(108079773720561455659894614034027034491433/1843102549738086561062622070312500:ℝ),(1006661186378831496027814176677653087064597/5529307649214259683187866210937500:ℝ),(1040648016401441027245058049419009922783119/5529307649214259683187866210937500:ℝ),(119407485529414980408500795786744365147607/1843102549738086561062622070312500:ℝ)],
![(76923226163458827546049314641775240179413/460775637434521640265655517578125:ℝ),(706806183811120383198256421546167934886352/1382326912303564920796966552734375:ℝ),(1442688884020554735558502187659416320552207/2764653824607129841593933105468750:ℝ),(163537377908989533314272710882715500410327/921551274869043280531311035156250:ℝ)],
![(199613130933273854524302644533073926226219/1843102549738086561062622070312500:ℝ),(1820563548865650036765211509507018652480811/5529307649214259683187866210937500:ℝ),(368945950327933688774389265179964543664259/1105861529842851936637573242187500:ℝ),(207667270288564086220044625978686635673047/1843102549738086561062622070312500:ℝ)]]
theorem admission023_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (108079773720561455659894614034027034491433/28146009508619716072466022400000000000000000:ℝ) admission023_08_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission023_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_08_coefficients]
def admission023_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(273270658452773044008649386806920741408/2211723059685703873275146484375:ℝ),(791258455297326307893047545440317145424/2211723059685703873275146484375:ℝ),(762792291111156211694221059642461628416/2211723059685703873275146484375:ℝ),(9792230375013060407666476705311358976/88468922387428154931005859375:ℝ)],
![(427543243118502923102664186592118321504/2211723059685703873275146484375:ℝ),(1229577208126137472518425071640536963952/2211723059685703873275146484375:ℝ),(1176668969163249058166987050079990560768/2211723059685703873275146484375:ℝ),(74927513045874392860941029980795633664/442344611937140774655029296875:ℝ)],
![(154272584665729879094014799785197580096/2211723059685703873275146484375:ℝ),(438318752828811164625377526200219818528/2211723059685703873275146484375:ℝ),(413876678052092846472765990437528932352/2211723059685703873275146484375:ℝ),(25966361170809090822608646454238838784/442344611937140774655029296875:ℝ)]]
theorem admission023_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (396215227826066449319589942233869/103073765290355405538816000000000000:ℝ) admission023_09_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission023_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_09_coefficients]
def admission023_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2955202410548940554937743096/89997620811767578125:ℝ),(2821609219916422820673089432/29999206937255859375:ℝ),(8064818513526539294240932304/89997620811767578125:ℝ),(2555205822578164512159407104/89997620811767578125:ℝ)],
![(4324879355964811335708227168/89997620811767578125:ℝ),(4072647450465384369649448672/29999206937255859375:ℝ),(11462464917730224489584510528/89997620811767578125:ℝ),(713885530280089043268878336/17999524162353515625:ℝ)],
![(29525952299521041373797984/1999947129150390625:ℝ),(403491118124730759946575648/9999735645751953125:ℝ),(1092425365709541312046044608/29999206937255859375:ℝ),(324845688601602152813287424/29999206937255859375:ℝ)]]
theorem admission023_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (475848176662503153535089/671070899486720000000000000:ℝ) admission023_10_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission023_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_10_coefficients]
def admission023_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1184877951304180648266171412686848/377467402186360127705625:ℝ),(3519702192550149241959309625567232/377467402186360127705625:ℝ),(10454780130969692667492543727665152/1132402206559080383116875:ℝ),(27602459257854295091305032712192/9059217652472643064935:ℝ)],
![(2293094741329706814311373708310528/377467402186360127705625:ℝ),(6810630889633676340465578933598208/377467402186360127705625:ℝ),(20226853028911720933892590852636672/1132402206559080383116875:ℝ),(6674244583999812355429975176773632/1132402206559080383116875:ℝ)],
![(221643358005105233209040459124736/75493480437272025541125:ℝ),(3290928697083527098506269308030976/377467402186360127705625:ℝ),(1954414579588405653280009424994304/226480441311816076623375:ℝ),(3223937176768025469016846087749632/1132402206559080383116875:ℝ)]]
theorem admission023_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (384323260398867782237153779/2061475305807108110776320000:ℝ) admission023_11_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission023_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_11_coefficients]
def admission023_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1380227158537928704/10986328125:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/10986328125:ℝ)],
![(2760454317075857408/10986328125:ℝ),(2760454317075857408/3662109375:ℝ),(2760454317075857408/3662109375:ℝ),(2760454317075857408/10986328125:ℝ)],
![(1380227158537928704/10986328125:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/3662109375:ℝ),(1380227158537928704/10986328125:ℝ)]]
theorem admission023_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission023_12_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission023_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_12_coefficients]
def admission023_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(482731212851503955968/6866455078125:ℝ),(482731212851503955968/2288818359375:ℝ),(482731212851503955968/2288818359375:ℝ),(482731212851503955968/6866455078125:ℝ)],
![(965462425703007911936/6866455078125:ℝ),(965462425703007911936/2288818359375:ℝ),(965462425703007911936/2288818359375:ℝ),(965462425703007911936/6866455078125:ℝ)],
![(482731212851503955968/6866455078125:ℝ),(482731212851503955968/2288818359375:ℝ),(482731212851503955968/2288818359375:ℝ),(482731212851503955968/6866455078125:ℝ)]]
theorem admission023_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (230184179712059/50000000000000000:ℝ) admission023_13_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission023_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_13_coefficients]
def admission023_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)],
![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)],
![(68719476736/9:ℝ),(68719476736/3:ℝ),(68719476736/3:ℝ),(68719476736/9:ℝ)]]
theorem admission023_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission023_14_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission023_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission023_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission023_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission023_14_coefficients]
theorem admission023_all {δ p : ℝ}
 (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission023_00_pos hd hp
 · exact admission023_01_pos hd hp
 · exact admission023_02_pos hd hp
 · exact admission023_03_pos hd hp
 · exact admission023_04_pos hd hp
 · exact admission023_05_pos hd hp
 · exact admission023_06_pos hd hp
 · exact admission023_07_pos hd hp
 · exact admission023_08_pos hd hp
 · exact admission023_09_pos hd hp
 · exact admission023_10_pos hd hp
 · exact admission023_11_pos hd hp
 · exact admission023_12_pos hd hp
 · exact admission023_13_pos hd hp
 · exact admission023_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission023_all
