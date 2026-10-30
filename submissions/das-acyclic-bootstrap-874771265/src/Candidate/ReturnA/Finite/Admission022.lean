/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission022_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45950285532828270592/24575350323:ℝ),(408669250112016351232/73726050969:ℝ),(403785930428578267136/73726050969:ℝ),(132967536915046727680/73726050969:ℝ)],
![(91900571065656541184/24575350323:ℝ),(817338500224032702464/73726050969:ℝ),(807571860857156534272/73726050969:ℝ),(265935073830093455360/73726050969:ℝ)],
![(45950285532828270592/24575350323:ℝ),(408669250112016351232/73726050969:ℝ),(403785930428578267136/73726050969:ℝ),(132967536915046727680/73726050969:ℝ)]]
theorem admission022_00_identity (δ p : ℝ) : admissionGuard .P δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (30958917205/32767133764:ℝ) admission022_00_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 0 := by
 rw [admission022_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_00_coefficients]
def admission022_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(100468449500037382144/73726050969:ℝ),(298720993940112146432/73726050969:ℝ),(296036639380112146432/73726050969:ℝ),(32594698313345794048/24575350323:ℝ)],
![(200936899000074764288/73726050969:ℝ),(597441987880224292864/73726050969:ℝ),(592073278760224292864/73726050969:ℝ),(65189396626691588096/24575350323:ℝ)],
![(100468449500037382144/73726050969:ℝ),(298720993940112146432/73726050969:ℝ),(296036639380112146432/73726050969:ℝ),(32594698313345794048/24575350323:ℝ)]]
theorem admission022_01_identity (δ p : ℝ) : admissionGuard .P δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5691783441/8191783441:ℝ) admission022_01_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 1 := by
 rw [admission022_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_01_coefficients]
def admission022_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6360541635197462904832/9215756371125:ℝ),(94596351575110319079424/46078781855625:ℝ),(93784578622258694586368/46078781855625:ℝ),(10330311741045230010368/15359593951875:ℝ)],
![(12721083270394925809664/9215756371125:ℝ),(189192703150220638158848/46078781855625:ℝ),(187569157244517389172736/46078781855625:ℝ),(20660623482090460020736/15359593951875:ℝ)],
![(6360541635197462904832/9215756371125:ℝ),(94596351575110319079424/46078781855625:ℝ),(93784578622258694586368/46078781855625:ℝ),(10330311741045230010368/15359593951875:ℝ)]]
theorem admission022_02_identity (δ p : ℝ) : admissionGuard .P δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (115450230327009/327671337640000:ℝ) admission022_02_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 2 := by
 rw [admission022_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_02_coefficients]
def admission022_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75252266018865676288/73726050969:ℝ),(665640824408740200448/221178152907:ℝ),(654071711607689314304/221178152907:ℝ),(214187685255546142720/221178152907:ℝ)],
![(148528816116403798016/73726050969:ℝ),(1313514320877911539712/221178152907:ℝ),(1290391685188188897280/221178152907:ℝ),(422463812659488751616/221178152907:ℝ)],
![(73276550097538121728/73726050969:ℝ),(647873496469171339264/221178152907:ℝ),(636319973580499582976/221178152907:ℝ),(208276127403942608896/221178152907:ℝ)]]
theorem admission022_03_identity (δ p : ℝ) : admissionGuard .P δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (6207112294553/12582579365376:ℝ) admission022_03_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 3 := by
 rw [admission022_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_03_coefficients]
def admission022_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(901279551315498857472/5119864650625:ℝ),(1577468375661693217792/3071918790375:ℝ),(7665199209027132194816/15359593951875:ℝ),(827231994888387559424/5119864650625:ℝ)],
![(73788716833243700224/204794586025:ℝ),(16148645459843857888256/15359593951875:ℝ),(15698942007396279517184/15359593951875:ℝ),(1694816770015233048576/5119864650625:ℝ)],
![(943438369515593648128/5119864650625:ℝ),(2753767860511797266432/5119864650625:ℝ),(2677914266123049107456/5119864650625:ℝ),(867584775126845489152/5119864650625:ℝ)]]
theorem admission022_04_identity (δ p : ℝ) : admissionGuard .P δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (14200378330222107/167767724871680000:ℝ) admission022_04_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 4 := by
 rw [admission022_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_04_coefficients]
def admission022_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(772824676021756768256/9215756371125:ℝ),(11659427915234710648832/46078781855625:ℝ),(11723538987874000571392/46078781855625:ℝ),(87294098949957194752/1023972930125:ℝ)],
![(7040235265954367138816/46078781855625:ℝ),(21271959209934840331264/46078781855625:ℝ),(21417247346681390372864/46078781855625:ℝ),(798391489188990797824/5119864650625:ℝ)],
![(3176111885845583297536/46078781855625:ℝ),(9612531294700129682432/46078781855625:ℝ),(9693708358807389801472/46078781855625:ℝ),(361920994439204824064/5119864650625:ℝ)]]
theorem admission022_05_identity (δ p : ℝ) : admissionGuard .P δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (3101671763521077439/85897075134300160000:ℝ) admission022_05_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 5 := by
 rw [admission022_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_05_coefficients]
def admission022_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11275797998211964258129093487356928/41898881642685974175324375:ℝ),(32344110122233795928488402662452224/41898881642685974175324375:ℝ),(1144038964380248535739415242866688/1551810431210591636123125:ℝ),(1964117909647933773000980476461056/8379776328537194835064875:ℝ)],
![(23021642115609532717540580689306624/41898881642685974175324375:ℝ),(66075184318094145202072085794644992/41898881642685974175324375:ℝ),(7015818032871990614204313957957632/4655431293631774908369375:ℝ),(4017703138777868295701464103256064/8379776328537194835064875:ℝ)],
![(11745844117397568459411487201949696/41898881642685974175324375:ℝ),(33731074195860349273583683132192768/41898881642685974175324375:ℝ),(3583701139731245006986068229357568/4655431293631774908369375:ℝ),(2053585229129934522700483626795008/8379776328537194835064875:ℝ)]]
theorem admission022_06_identity (δ p : ℝ) : admissionGuard .P δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3746257609649531885148964837/30509834525945200039489536000:ℝ) admission022_06_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 6 := by
 rw [admission022_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_06_coefficients]
def admission022_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(556893717618748433139102782391296/1132402206559080383116875:ℝ),(546080030662797304490801899744256/377467402186360127705625:ℝ),(1606043294975114745729744188342272/1132402206559080383116875:ℝ),(6995958941406283538619216953344/15098696087454405108225:ℝ)],
![(1078987652591385278306205729123328/1132402206559080383116875:ℝ),(1057719404814551508676890709009408/377467402186360127705625:ℝ),(3109833886738574340027577716310016/1132402206559080383116875:ℝ),(67710888325753672820207421227008/75493480437272025541125:ℝ)],
![(522093934972636845167102946732032/1132402206559080383116875:ℝ),(511639374151754204186088809265152/377467402186360127705625:ℝ),(1503790591763459594297833527967744/1132402206559080383116875:ℝ),(32731093618722255127111336460288/75493480437272025541125:ℝ)]]
theorem admission022_07_identity (δ p : ℝ) : admissionGuard .P δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (31214803332063918234931313/137431687053807207385088000:ℝ) admission022_07_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 7 := by
 rw [admission022_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_07_coefficients]
def admission022_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15364568028861760799262789592147608328343/2211723059685703873275146484375000:ℝ),(82463660952303679315901318491054896181391/3686205099476173122125244140625000:ℝ),(264368136197873670949223271883676842490023/11058615298428519366375732421875000:ℝ),(18758520858634704610996521880968101617513/2211723059685703873275146484375000:ℝ)],
![(11239474506391266969823250584142078157547/552930764921425968318786621093750:ℝ),(29299462861270778670078774384448010652026/460775637434521640265655517578125:ℝ),(366096312153387781067958532037944987033447/5529307649214259683187866210937500:ℝ),(25378004715570887546862309145363771906921/1105861529842851936637573242187500:ℝ)],
![(5918665999340661416006042548884140860369/442344611937140774655029296875000:ℝ),(151932041937862550044728876584529189034817/3686205099476173122125244140625000:ℝ),(467824488108901891186693792192213131576871/11058615298428519366375732421875000:ℝ),(31997488572507070482728096409759442196329/2211723059685703873275146484375000:ℝ)]]
theorem admission022_08_identity (δ p : ℝ) : admissionGuard .P δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (15364568028861760799262789592147608328343/4221901426292957410869903360000000000000000:ℝ) admission022_08_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 8 := by
 rw [admission022_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_08_coefficients]
def admission022_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33545585475540559299309457149581848/1965976053053958998466796875:ℝ),(106035241858832489421286462011221748904/2211723059685703873275146484375:ℝ),(98895913012041611601682045798321416704/2211723059685703873275146484375:ℝ),(1224028796876632550958309588163919872/88468922387428154931005859375:ℝ)],
![(445127301426481154423039033732223768/16383133775449658320556640625:ℝ),(166943206442458693789983441994265014712/2211723059685703873275146484375:ℝ),(153678155329797777927482331306005827072/2211723059685703873275146484375:ℝ),(9365939130734299107617628747599454208/442344611937140774655029296875:ℝ)],
![(496742267390929480786380672457125104/49149401326348974961669921875:ℝ),(60907964583626204368696979983043265808/2211723059685703873275146484375:ℝ),(54782242317756166325800285507684410368/2211723059685703873275146484375:ℝ),(3245795146351136352826080806779854848/442344611937140774655029296875:ℝ)]]
theorem admission022_09_identity (δ p : ℝ) : admissionGuard .P δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (396215227826066449319589942233869/103073765290355405538816000000000000:ℝ) admission022_09_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 9 := by
 rw [admission022_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_09_coefficients]
def admission022_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(419592481233670583468416136/89997620811767578125:ℝ),(231641351315635255189789132/17999524162353515625:ℝ),(1058002444914823131500455412/89997620811767578125:ℝ),(319400727822270564019925888/89997620811767578125:ℝ)],
![(635345953274235251587132832/89997620811767578125:ℝ),(1716274086108131265811064624/89997620811767578125:ℝ),(1527080860157389166266980752/89997620811767578125:ℝ),(89235691285011130408609792/17999524162353515625:ℝ)],
![(70153237657904539596956512/29999206937255859375:ℝ),(180841127557926291201823952/29999206937255859375:ℝ),(151289208201784520706528368/29999206937255859375:ℝ),(40605711075200269101660928/29999206937255859375:ℝ)]]
theorem admission022_10_identity (δ p : ℝ) : admissionGuard .P δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (475848176662503153535089/671070899486720000000000000:ℝ) admission022_10_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 10 := by
 rw [admission022_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_10_coefficients]
def admission022_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(457487171925767887931044595497984/1132402206559080383116875:ℝ),(1346028501052297611597615982902272/1132402206559080383116875:ℝ),(1319829755030503084468212523532288/1132402206559080383116875:ℝ),(3450307407231786886413129089024/9059217652472643064935:ℝ)],
![(885770573766559621280153540596736/1132402206559080383116875:ℝ),(2605361538994583677038313665369088/1132402206559080383116875:ℝ),(2553871538228000600186907021869056/1132402206559080383116875:ℝ),(834280572999976544428746897096704/1132402206559080383116875:ℝ)],
![(428283401840791733349108945098752/1132402206559080383116875:ℝ),(1259333037942286065440697682466816/1132402206559080383116875:ℝ),(1234041783197497515718694498336768/1132402206559080383116875:ℝ),(402992147096003183627105760968704/1132402206559080383116875:ℝ)]]
theorem admission022_11_identity (δ p : ℝ) : admissionGuard .P δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (384323260398867782237153779/2061475305807108110776320000:ℝ) admission022_11_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 11 := by
 rw [admission022_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_11_coefficients]
def admission022_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission022_12_identity (δ p : ℝ) : admissionGuard .P δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission022_12_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 12 := by
 rw [admission022_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_12_coefficients]
def admission022_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60341401606437994496/6866455078125:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/6866455078125:ℝ)],
![(120682803212875988992/6866455078125:ℝ),(120682803212875988992/2288818359375:ℝ),(120682803212875988992/2288818359375:ℝ),(120682803212875988992/6866455078125:ℝ)],
![(60341401606437994496/6866455078125:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/6866455078125:ℝ)]]
theorem admission022_13_identity (δ p : ℝ) : admissionGuard .P δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (230184179712059/50000000000000000:ℝ) admission022_13_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 13 := by
 rw [admission022_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_13_coefficients]
def admission022_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission022_14_identity (δ p : ℝ) : admissionGuard .P δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission022_14_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission022_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission022_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .P δ p 14 := by
 rw [admission022_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission022_14_coefficients]
theorem admission022_all {δ p : ℝ}
 (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .P δ p j := by
 intro j
 fin_cases j
 · exact admission022_00_pos hd hp
 · exact admission022_01_pos hd hp
 · exact admission022_02_pos hd hp
 · exact admission022_03_pos hd hp
 · exact admission022_04_pos hd hp
 · exact admission022_05_pos hd hp
 · exact admission022_06_pos hd hp
 · exact admission022_07_pos hd hp
 · exact admission022_08_pos hd hp
 · exact admission022_09_pos hd hp
 · exact admission022_10_pos hd hp
 · exact admission022_11_pos hd hp
 · exact admission022_12_pos hd hp
 · exact admission022_13_pos hd hp
 · exact admission022_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission022_all
