/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission025_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4157056650039672445075456/70916363469:ℝ),(12451511126481951262769152/70916363469:ℝ),(12431852302844885190311936/70916363469:ℝ),(4137397826402606372618240/70916363469:ℝ)],
![(8314113300079344890150912/70916363469:ℝ),(24903022252963902525538304/70916363469:ℝ),(24863704605689770380623872/70916363469:ℝ),(8274795652805212745236480/70916363469:ℝ)],
![(4157056650039672445075456/70916363469:ℝ),(12451511126481951262769152/70916363469:ℝ),(12431852302844885190311936/70916363469:ℝ),(4137397826402606372618240/70916363469:ℝ)]]
theorem admission025_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission025_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission025_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_00_coefficients]
def admission025_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3039438400689189098094592/70916363469:ℝ),(9107320085789807294283776/70916363469:ℝ),(9096324969512047294283776/70916363469:ℝ),(1009481094803809699364864/23638787823:ℝ)],
![(6078876801378378196189184/70916363469:ℝ),(18214640171579614588567552/70916363469:ℝ),(18192649939024094588567552/70916363469:ℝ),(2018962189607619398729728/23638787823:ℝ)],
![(3039438400689189098094592/70916363469:ℝ),(9107320085789807294283776/70916363469:ℝ),(9096324969512047294283776/70916363469:ℝ),(1009481094803809699364864/23638787823:ℝ)]]
theorem admission025_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission025_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission025_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_01_coefficients]
def admission025_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(107349722056205484412633088/4924747463125:ℝ),(2895135049226342392263606272/44322727168125:ℝ),(2891827602935136705386119168/44322727168125:ℝ),(962840052214643672836210688/44322727168125:ℝ)],
![(214699444112410968825266176/4924747463125:ℝ),(5790270098452684784527212544/44322727168125:ℝ),(5783655205870273410772238336/44322727168125:ℝ),(1925680104429287345672421376/44322727168125:ℝ)],
![(107349722056205484412633088/4924747463125:ℝ),(2895135049226342392263606272/44322727168125:ℝ),(2891827602935136705386119168/44322727168125:ℝ),(962840052214643672836210688/44322727168125:ℝ)]]
theorem admission025_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission025_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission025_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_02_coefficients]
def admission025_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6804381647330976521519104/212749090407:ℝ),(20367135575068890823131136/212749090407:ℝ),(20321155652158932081704960/212749090407:ℝ),(965485960631573968584704/30392727201:ℝ)],
![(13585697884153026374008832/212749090407:ℝ),(40665084975316670313660416/212749090407:ℝ),(5796162182939180215042048/30392727201:ℝ),(13493748189410617565642752/212749090407:ℝ)],
![(968759462403149978927104/30392727201:ℝ),(20297949400247779490529280/212749090407:ℝ),(20251979628415329423589376/212749090407:ℝ),(6735346464989599785549824/212749090407:ℝ)]]
theorem admission025_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (98012190792209/193648949846016:ℝ) admission025_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission025_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_03_coefficients]
def admission025_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3531772845880598971285504/703535351875:ℝ),(73891602503526417742692352/4924747463125:ℝ),(73616303283124661949300736/4924747463125:ℝ),(24447110700762437005606912/4924747463125:ℝ)],
![(148807243379119066695958528/14774242389375:ℝ),(63537902330777882417856512/2110606055625:ℝ),(443110873885146163743555584/14774242389375:ℝ),(147152800948820053514518528/14774242389375:ℝ)],
![(74640013615626488298962944/14774242389375:ℝ),(223090508804865923696918528/14774242389375:ℝ),(222261964035772177895653376/14774242389375:ℝ),(73811468846532742497697792/14774242389375:ℝ)]]
theorem admission025_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25614164339711649/322748249743360000:ℝ) admission025_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission025_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_04_coefficients]
def admission025_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44167600623562176692928512/14774242389375:ℝ),(397593688286272269149585408/44322727168125:ℝ),(397677551533388344314609664/44322727168125:ℝ),(132586665117802605243809792/44322727168125:ℝ)],
![(29154045472261148416147456/4924747463125:ℝ),(787338267463060418139062272/44322727168125:ℝ),(787514463771430799097823232/44322727168125:ℝ),(262562605558720716704088064/44322727168125:ℝ)],
![(43294535793221268555513856/14774242389375:ℝ),(55677797025255449855639552/6331818166875:ℝ),(389836912238042454783213568/44322727168125:ℝ),(129975940440918111460278272/44322727168125:ℝ)]]
theorem admission025_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (7927466270731433451327/169213034361446727680000:ℝ) admission025_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission025_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_05_coefficients]
def admission025_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(56361761623893027808719520108866961408/7753243020153781475689875:ℝ),(840206815284898561175964740811140366336/38766215100768907378449375:ℝ),(835000236418746605790234544975680372736/38766215100768907378449375:ℝ),(55320444051282987112137960941774962688/7753243020153781475689875:ℝ)],
![(16150435946229413625513430967555489792/1107606145736254496527125:ℝ),(337069204796919401840104537528554192896/7753243020153781475689875:ℝ),(334984472380684049570043750090325098496/7753243020153781475689875:ℝ),(15852616514692000200419032762094190592/1107606145736254496527125:ℝ)],
![(56691289999712867569874496664021467136/7753243020153781475689875:ℝ),(845139208699698448024557946831630598144/38766215100768907378449375:ℝ),(839922125484673642059984205475945119744/38766215100768907378449375:ℝ),(55647871551561014290795268392884371456/7753243020153781475689875:ℝ)]]
theorem admission025_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6440147297839050543510583339/56457392729866469198979072000:ℝ) admission025_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission025_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_06_coefficients]
def admission025_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3234056216645366027371894328542363648/209547108652804904748375:ℝ),(48379784053894761342084374382767767552/1047735543264024523741875:ℝ),(5360983916260796404258919176028028928/116415060362669391526875:ℝ),(3207870455135847286621073968839262208/209547108652804904748375:ℝ)],
![(6443132572259381143018670453056765952/209547108652804904748375:ℝ),(19277076074169913355431444134527401984/209547108652804904748375:ℝ),(2136089609482622582141121822327832576/23283012072533878305375:ℝ),(6390862983433071026857322719479857152/209547108652804904748375:ℝ)],
![(65491354196204390115240329071722496/4276471605159283770375:ℝ),(979706047284791947654547883466719232/21382358025796418851875:ℝ),(108560492472496255233605917053288448/2375817558421824316875:ℝ),(64959031189739260004821403074297856/4276471605159283770375:ℝ)]]
theorem admission025_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (60497812172155138109644319/249122527213972285489152000:ℝ) admission025_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission025_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_07_coefficients]
def admission025_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(909301819222922109726070526355817745266752/6767058475322579027557373046875:ℝ),(526817675892644243166627462099084242437048256/1278974051835967436208343505859375:ℝ),(35870372757354771644934743869538741758341568/85264936789064495747222900390625:ℝ),(183095904905702524593563063986381015293491392/1278974051835967436208343505859375:ℝ)],
![(13873835569141662953029491194864946300119952/47369409327258053192901611328125:ℝ),(1145980430365252675743979028190577020469363792/1278974051835967436208343505859375:ℝ),(55627119186345803786217889740713072632676992/60903526277903211248016357421875:ℝ),(396782523950276640253084502281870000232591744/1278974051835967436208343505859375:ℝ)],
![(7508722834581208184946997510374222083252688/47369409327258053192901611328125:ℝ),(619162754472608432577351566091492778032315536/1278974051835967436208343505859375:ℝ),(210037970517646768278851508837297799637031104/426324683945322478736114501953125:ℝ),(213686619044574115659521438295488984939100352/1278974051835967436208343505859375:ℝ)]]
theorem admission025_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (127870568328223421680228667768786870428137/59523675835658444746208051200000000000000000:ℝ) admission025_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission025_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_08_coefficients]
def admission025_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(131130601277969793121657694993834147001856/227373164770838655325927734375:ℝ),(701251355095004437537187092300484839632896/409271696587509579586669921875:ℝ),(3472025190979113766269081291968937088516096/2046358482937547897933349609375:ℝ),(1212639047080753017053709033133389643776/2165458712103225288818359375:ℝ)],
![(51247531875622350378777424886118674959936/45474632954167731065185546875:ℝ),(1370070224008116915208659118305966366777856/409271696587509579586669921875:ℝ),(1356472054165758249560388058144019488964608/409271696587509579586669921875:ℝ),(49736627342100477826231368294942285758464/45474632954167731065185546875:ℝ)],
![(125107058100141958772229429436759227797824/227373164770838655325927734375:ℝ),(133763773782622495534294405201096305428992/81854339317501915917333984375:ℝ),(3310335079849677481532858998751160356306944/2046358482937547897933349609375:ℝ),(24271207353404664468103478599141103239168/45474632954167731065185546875:ℝ)]]
theorem admission025_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4340030077708601558465387570704419/508625159728526749540352000000000000:ℝ) admission025_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission025_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_09_coefficients]
def admission025_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(634441186708735423177075004416/4122277452392578125:ℝ),(2633303489557553037796571831296/5771188433349609375:ℝ),(13009897205206258894109143220224/28855942166748046875:ℝ),(1428156102263005555788603031552/9618647388916015625:ℝ)],
![(25972811805561864240313272932096/86567826500244140625:ℝ),(10997535465550733855084269510912/12366832357177734375:ℝ),(15209563083990694590025090871296/17313565300048828125:ℝ),(2781986713975352106094315634688/9618647388916015625:ℝ)],
![(12647125519555432971167425022096/86567826500244140625:ℝ),(7495190405606617470332107878992/17313565300048828125:ℝ),(37010900091813308706444959973632/86567826500244140625:ℝ),(1353563812803663197675205066752/9618647388916015625:ℝ)]]
theorem admission025_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (371767404639678002291163501/165247103868600320000000000000:ℝ) admission025_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission025_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_10_coefficients]
def admission025_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13266680159887716042558028044361269248/1047735543264024523741875:ℝ),(13230933868719836786282751386119307264/349245181088008174580625:ℝ),(39585687696798252543288034236125151232/1047735543264024523741875:ℝ),(4386522083508819408999269374042832896/349245181088008174580625:ℝ)],
![(26428354191981559923276972040319107072/1047735543264024523741875:ℝ),(26357007356677784216952770399290949632/349245181088008174580625:ℝ),(78857230967455192203267651698149031936/1047735543264024523741875:ℝ),(8738187696467799825228770846865096704/349245181088008174580625:ℝ)],
![(1880239147441977697245563427993976832/149676506180574931963125:ℝ),(1875153355422563918667145573310234624/49892168726858310654375:ℝ),(5610220467236705665711373923146268672/149676506180574931963125:ℝ),(621666516136997202318500210403180544/49892168726858310654375:ℝ)]]
theorem admission025_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (578972060360943155659828531/2906429484163009997373440000:ℝ) admission025_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission025_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_11_coefficients]
def admission025_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5653410441371355971584/10986328125:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/10986328125:ℝ)],
![(11306820882742711943168/10986328125:ℝ),(11306820882742711943168/3662109375:ℝ),(11306820882742711943168/3662109375:ℝ),(11306820882742711943168/10986328125:ℝ)],
![(5653410441371355971584/10986328125:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/3662109375:ℝ),(5653410441371355971584/10986328125:ℝ)]]
theorem admission025_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission025_12_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission025_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_12_coefficients]
def admission025_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(198950541077680584916992/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(198950541077680584916992/762939453125:ℝ)],
![(397901082155361169833984/762939453125:ℝ),(1193703246466083509501952/762939453125:ℝ),(1193703246466083509501952/762939453125:ℝ),(397901082155361169833984/762939453125:ℝ)],
![(198950541077680584916992/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(596851623233041754750976/762939453125:ℝ),(198950541077680584916992/762939453125:ℝ)]]
theorem admission025_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission025_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission025_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_13_coefficients]
def admission025_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)],
![(562949953421312/9:ℝ),(562949953421312/3:ℝ),(562949953421312/3:ℝ),(562949953421312/9:ℝ)],
![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)]]
theorem admission025_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission025_14_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission025_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_14_coefficients]
theorem admission025_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission025_00_pos hd hp
 · exact admission025_01_pos hd hp
 · exact admission025_02_pos hd hp
 · exact admission025_03_pos hd hp
 · exact admission025_04_pos hd hp
 · exact admission025_05_pos hd hp
 · exact admission025_06_pos hd hp
 · exact admission025_07_pos hd hp
 · exact admission025_08_pos hd hp
 · exact admission025_09_pos hd hp
 · exact admission025_10_pos hd hp
 · exact admission025_11_pos hd hp
 · exact admission025_12_pos hd hp
 · exact admission025_13_pos hd hp
 · exact admission025_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission025_all
