/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission010_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)],
![(8234439689357169262592/70916363469:ℝ),(24549734508406929096704/70916363469:ℝ),(24396149948742350405632/70916363469:ℝ),(8080855129692590571520/70916363469:ℝ)],
![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)]]
theorem admission010_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission010_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission010_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_00_coefficients]
def admission010_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)],
![(6000827635786072457216/70916363469:ℝ),(17916583561438217371648/70916363469:ℝ),(17830684215518217371648/70916363469:ℝ),(1971642763288690819072/23638787823:ℝ)],
![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)]]
theorem admission010_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission010_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission010_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_01_coefficients]
def admission010_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)],
![(635462133710590117412864/14774242389375:ℝ),(5693319779245266627985408/44322727168125:ℝ),(1133496071019044439851008/8864545433625:ℝ),(1880546976981725923508224/44322727168125:ℝ)],
![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)]]
theorem admission010_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission010_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission010_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_02_coefficients]
def admission010_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6858912148077729021952/212749090407:ℝ),(20396173971940087693312/212749090407:ℝ),(20216065664126988320768/212749090407:ℝ),(954114834323518521344/30392727201:ℝ)],
![(13627610502095408463872/212749090407:ℝ),(40521854850366099685376/212749090407:ℝ),(40161792421645973979136/212749090407:ℝ),(13267548073375282757632/212749090407:ℝ)],
![(6768698354017679441920/212749090407:ℝ),(20125680878426011992064/212749090407:ℝ),(2849389536788426522624/30392727201:ℝ),(6588744233110653108224/212749090407:ℝ)]]
theorem admission010_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (12272492485327/24206118730752:ℝ) admission010_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission010_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_03_coefficients]
def admission010_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10557192181060903831552/2110606055625:ℝ),(31212809945995438655488/2110606055625:ℝ),(30756211879582476795904/2110606055625:ℝ),(10100594114647941971968/2110606055625:ℝ)],
![(7127555767009039116288/703535351875:ℝ),(442571574906657892501504/14774242389375:ℝ),(436137693061747975389184/14774242389375:ℝ),(47748263087426634776576/4924747463125:ℝ)],
![(10825475119966213517312/2110606055625:ℝ),(74693968428229940637696/4924747463125:ℝ),(73614736634890212605952/4924747463125:ℝ),(72540630459744310525952/14774242389375:ℝ)]]
theorem admission010_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (7224507890687901/92213785640960000:ℝ) admission010_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission010_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_04_coefficients]
def admission010_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2195522186555533471744/703535351875:ℝ),(59312465440881295671296/6331818166875:ℝ),(59342704100760254666752/6331818166875:ℝ),(19789938338878760241152/6331818166875:ℝ)],
![(12681195149320684894208/2110606055625:ℝ),(799515262503096319227904/44322727168125:ℝ),(800071157842584525983744/44322727168125:ℝ),(266860993475222589534208/44322727168125:ℝ)],
![(6094628589654084478976/2110606055625:ℝ),(384328004416927249528832/44322727168125:ℝ),(76934445827452548663296/8864545433625:ℝ),(128331425103071267846144/44322727168125:ℝ)]]
theorem admission010_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (8927678598126100311/188853832992686080000:ℝ) admission010_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission010_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_05_coefficients]
def admission010_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(287247523802653922580909491499972608/38766215100768907378449375:ℝ),(841214320382490783651569261083768832/38766215100768907378449375:ℝ),(820889173213676885074970638917566464/38766215100768907378449375:ℝ),(53384364307350520268382173866754048/7753243020153781475689875:ℝ)],
![(116211111230275468586559015955982336/7753243020153781475689875:ℝ),(68077719004362229601849908108773376/1550648604030756295137975:ℝ),(332225449559843349373284979552288768/7753243020153781475689875:ℝ),(108047742287662084203394454964404224/7753243020153781475689875:ℝ)],
![(293808032348723420351885588279939072/38766215100768907378449375:ℝ),(860728654726564956394678441635565568/38766215100768907378449375:ℝ),(840238074585539861791454258843877376/38766215100768907378449375:ℝ),(54663377980311563935012281097650176/7753243020153781475689875:ℝ)]]
theorem admission010_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (12727824284398679797263663737/112914785459732938397958144000:ℝ) admission010_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission010_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_06_coefficients]
def admission010_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16609545881856974743965199245387776/1047735543264024523741875:ℝ),(49305612563790162730624606261356544/1047735543264024523741875:ℝ),(258119875773265609463764074627072/5543574302984256739375:ℝ),(3217717967842802440398400617709568/209547108652804904748375:ℝ)],
![(6545041470830511503292840426223616/209547108652804904748375:ℝ),(19427518204561521852644890931771392/209547108652804904748375:ℝ),(711879009914934888966041786384384/7761004024177959435125:ℝ),(6338256533972231652731077726830592/209547108652804904748375:ℝ)],
![(16115661472295582772499002885730304/1047735543264024523741875:ℝ),(47831978459017446532599848397500416/1047735543264024523741875:ℝ),(1752555919161815178583860409532416/38805020120889797175625:ℝ),(3120538566129429212332677109121024/209547108652804904748375:ℝ)]]
theorem admission010_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (371997185484102870503983153/1525875479185580248621056000:ℝ) admission010_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission010_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_07_coefficients]
def admission010_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1215437381051993060663093147814397046299/17401007507972346070861816406250:ℝ),(90455561054972550159188471178655063122937/365421157667419267488098144531250:ℝ),(243378842164288015748323890842595207170431/852649367890644957472229003906250:ℝ),(275610181905959440137128620222843576706687/2557948103671934872416687011718750:ℝ)],
![(2058994092954685973541249451555926473506/8700503753986173035430908203125:ℝ),(142950457486953836683552827748385648553988/182710578833709633744049072265625:ℝ),(364364328519275777540652152682800107344127/426324683945322478736114501953125:ℝ),(395105159010926592738528519867796583134847/1278974051835967436208343505859375:ℝ)],
![(2902550804857378886419405755297455900713/17401007507972346070861816406250:ℝ),(195445353918935123207917184318116233985039/365421157667419267488098144531250:ℝ),(485349814874263539332980414523005007517823/852649367890644957472229003906250:ℝ),(514600136115893745339928419512749589563007/2557948103671934872416687011718750:ℝ)]]
theorem admission010_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1215437381051993060663093147814397046299/1062922782779615084753715200000000000000000:ℝ) admission010_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission010_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_08_coefficients]
def admission010_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(481449303457375521217302714527946548624/682119494312515965977783203125:ℝ),(4190818432401770234800657815840485802016/2046358482937547897933349609375:ℝ),(4049232055187321737204973444283997425664/2046358482937547897933349609375:ℝ),(4135765096570149898606770163799031808/6496376136309675866455078125:ℝ)],
![(178090180873647456762075220323594114608/136423898862503193195556640625:ℝ),(1547417545364120705664380510073991390048/409271696587509579586669921875:ℝ),(298453513286106076713116206992129978368/81854339317501915917333984375:ℝ),(17745272748458682742945642148952670208/15158210984722577021728515625:ℝ)],
![(409001600910861762593073387090024024416/682119494312515965977783203125:ℝ),(3546269294418833293521244734529471148224/2046358482937547897933349609375:ℝ),(3412105776965330180622931730519252033536/2046358482937547897933349609375:ℝ),(24285462569384998938589535300264787968/45474632954167731065185546875:ℝ)]]
theorem admission010_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (555850125947227453733586165624957/63578144966065843692544000000000000:ℝ) admission010_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission010_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_09_coefficients]
def admission010_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(477533398960946688711980828/2473366471435546875:ℝ),(6888673303393432384028584316/12366832357177734375:ℝ),(6615263127495413618088393712/12366832357177734375:ℝ),(234918127399140172513301504/1374092484130859375:ℝ)],
![(4402379472186863453095608976/12366832357177734375:ℝ),(88682646130941926622118143152/86567826500244140625:ℝ),(84927615805735193952947247808/86567826500244140625:ℝ),(3006857302020805444722040832/9618647388916015625:ℝ)],
![(133944777389330277456321872/824455490478515625:ℝ),(1921278630076791151293647312/4122277452392578125:ℝ),(12835653083160981404916015808/28855942166748046875:ℝ),(194037382468378121753892864/1374092484130859375:ℝ)]]
theorem admission010_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (852703340925489792863787/368855142563840000000000000:ℝ) admission010_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission010_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_10_coefficients]
def admission010_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13635280326601090406396720349304832/1047735543264024523741875:ℝ),(899491759483479915398817575876608/23283012072533878305375:ℝ),(817355158120595614965474396995584/21382358025796418851875:ℝ),(4402851299251226448919391629213696/349245181088008174580625:ℝ)],
![(26855238092084772475997654518392832/1047735543264024523741875:ℝ),(2952413769499889896763368869541888/38805020120889797175625:ℝ),(78868567215663687733608937142091776/1047735543264024523741875:ℝ),(8669544510417144332331877394284544/349245181088008174580625:ℝ)],
![(105759662123869456556807473352704/8381884346112196189935:ℝ),(4359782511082270113296018729242624/116415060362669391526875:ℝ),(7763632893550900520060138337861632/209547108652804904748375:ℝ),(4266693211165917883412485765070848/349245181088008174580625:ℝ)]]
theorem admission010_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (508629466434230552126465531/2543125798642633747701760000:ℝ) admission010_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission010_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_11_coefficients]
def admission010_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)],
![(11041817268303429632/10986328125:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/10986328125:ℝ)],
![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)]]
theorem admission010_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission010_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission010_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_12_coefficients]
def admission010_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)],
![(388575275542344892416/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(388575275542344892416/762939453125:ℝ)],
![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)]]
theorem admission010_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission010_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission010_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_13_coefficients]
def admission010_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission010_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission010_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission010_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_14_coefficients]
theorem admission010_all {δ p : ℝ}
 (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission010_00_pos hd hp
 · exact admission010_01_pos hd hp
 · exact admission010_02_pos hd hp
 · exact admission010_03_pos hd hp
 · exact admission010_04_pos hd hp
 · exact admission010_05_pos hd hp
 · exact admission010_06_pos hd hp
 · exact admission010_07_pos hd hp
 · exact admission010_08_pos hd hp
 · exact admission010_09_pos hd hp
 · exact admission010_10_pos hd hp
 · exact admission010_11_pos hd hp
 · exact admission010_12_pos hd hp
 · exact admission010_13_pos hd hp
 · exact admission010_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission010_all
