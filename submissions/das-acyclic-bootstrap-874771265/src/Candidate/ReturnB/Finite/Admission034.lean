/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission034_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(925649530507344389088502349824/472772661:ℝ),(8330433500342625764800100040704/1418317983:ℝ),(8330021226119152027803678932992/1418317983:ℝ),(2776536317298559430269085941760/1418317983:ℝ)],
![(1851299061014688778177004699648/472772661:ℝ),(16660867000685251529600200081408/1418317983:ℝ),(16660042452238304055607357865984/1418317983:ℝ),(5553072634597118860538171883520/1418317983:ℝ)],
![(925649530507344389088502349824/472772661:ℝ),(8330433500342625764800100040704/1418317983:ℝ),(8330021226119152027803678932992/1418317983:ℝ),(2776536317298559430269085941760/1418317983:ℝ)]]
theorem admission034_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission034_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission034_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_00_coefficients]
def admission034_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2032564978824983105062628753408/1418317983:ℝ),(6097464352174027945792686260224/1418317983:ℝ),(6097233767873106576397486260224/1418317983:ℝ),(225814932724895748407492083712/157590887:ℝ)],
![(4065129957649966210125257506816/1418317983:ℝ),(12194928704348055891585372520448/1418317983:ℝ),(12194467535746213152794972520448/1418317983:ℝ),(451629865449791496814984167424/157590887:ℝ)],
![(2032564978824983105062628753408/1418317983:ℝ),(6097464352174027945792686260224/1418317983:ℝ),(6097233767873106576397486260224/1418317983:ℝ),(225814932724895748407492083712/157590887:ℝ)]]
theorem admission034_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission034_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission034_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_01_coefficients]
def admission034_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3231072523119809574034347533533184/4432243696875:ℝ),(16154784597896882301992158502060032/7387072828125:ℝ),(16154206580194716733812579336454144/7387072828125:ℝ),(16153628562492551165633000170848256/22161218484375:ℝ)],
![(6462145046239619148068695067066368/4432243696875:ℝ),(32309569195793764603984317004120064/7387072828125:ℝ),(32308413160389433467625158672908288/7387072828125:ℝ),(32307257124985102331266000341696512/22161218484375:ℝ)],
![(3231072523119809574034347533533184/4432243696875:ℝ),(16154784597896882301992158502060032/7387072828125:ℝ),(16154206580194716733812579336454144/7387072828125:ℝ),(16153628562492551165633000170848256/22161218484375:ℝ)]]
theorem admission034_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission034_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission034_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_02_coefficients]
def admission034_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1507462560751917946243347644416/1418317983:ℝ),(13566199542582711634564801888256/4254953949:ℝ),(13565236057746774673054674976768/4254953949:ℝ),(4521424197419816877219916021760/4254953949:ℝ)],
![(3014763952659824463167338053632/1418317983:ℝ),(27130948572280075987560939126784/4254953949:ℝ),(27129021609320890382129435770880/4254953949:ℝ),(9042364895020287784070510804992/4254953949:ℝ)],
![(1507301391907906516923990409216/1418317983:ℝ),(13564749029697364352996137238528/4254953949:ℝ),(13563785551574115709074760794112/4254953949:ℝ),(4520940697600470906850594783232/4254953949:ℝ)]]
theorem admission034_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (15685163923253/30983629111296:ℝ) admission034_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission034_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_03_coefficients]
def admission034_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13271111782846258712112233709568/79430890625:ℝ),(246813766403121063297550502592512/492471521875:ℝ),(1233924273615639448570761133948928/2462357609375:ℝ),(411259906868268152158487865982976/2462357609375:ℝ)],
![(164578221316006753613494743990272/492471521875:ℝ),(7405152533164240352559407860547584/7387072828125:ℝ),(7404285139444577010245377779040256/7387072828125:ℝ),(2467805926020437961888391078346752/7387072828125:ℝ)],
![(411486641311799747991994474954752/2462357609375:ℝ),(3702946037117424403096150321659904/7387072828125:ℝ),(119435881245085763372035302490112/238292671875:ℝ),(39807296948891403400417015496704/238292671875:ℝ)]]
theorem admission034_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (6574899135029023557/82623010963456000000:ℝ) admission034_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission034_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_04_coefficients]
def admission034_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(436784664354079039948315955298304/4432243696875:ℝ),(6551816978497853087569941769486336/22161218484375:ℝ),(6551863968365771697357339622375424/22161218484375:ℝ),(727990103879437936509659209793536/7387072828125:ℝ)],
![(4366477745178097970314094779039744/22161218484375:ℝ),(523981096024261839722979604299776/886448739375:ℝ),(13099621519038971005447139265347584/22161218484375:ℝ),(1455523954536840994228914645630976/7387072828125:ℝ)],
![(2182554423407702770572515002548224/22161218484375:ℝ),(6547710422108692905504548338008064/22161218484375:ℝ),(1309551510134639861617959928594432/4432243696875:ℝ),(48502256710493537181283695722496/492471521875:ℝ)]]
theorem admission034_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (65045190555086814480200857/1386184101504269418496000000:ℝ) admission034_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission034_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_05_coefficients]
def admission034_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(93096966003212656274963009920685217157218304/387657074652833159859375:ℝ),(3002541279516845343997602727754410905042944/4168355641428313546875:ℝ),(279181784249308534838031180045642103707926528/387657074652833159859375:ℝ),(6202827417157479800322268723437807113076736/25843804976855543990625:ℝ)],
![(186211101739043690040318984282101406815485952/387657074652833159859375:ℝ),(186174727918169330843261159343260214684024832/129219024884277719953125:ℝ),(558415070829796019573597976996003715118792704/387657074652833159859375:ℝ),(12406799254276463574920396768234965192146944/25843804976855543990625:ℝ)],
![(93114135735831033765355974361416189658267648/387657074652833159859375:ℝ),(93095948253147125179335474782873476627693568/129219024884277719953125:ℝ),(279233286580487484735566796950361611410866176/387657074652833159859375:ℝ),(6203971837118983774598128044797158079070208/25843804976855543990625:ℝ)]]
theorem admission034_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (11018434906087079739340361903/96352688524128991628492800000:ℝ) admission034_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission034_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_06_coefficients]
def admission034_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1781786602802743361166751704309125271781376/3492406077953451890625:ℝ),(16034712338942232517113609979070992711942144/10477218233860355671875:ℝ),(16033345295244905950626925460316603878998016/10477218233860355671875:ℝ),(1710077684707489125444342590135355834368/3352709834835313815:ℝ)],
![(3563138384477081359648333667211391793102848/3492406077953451890625:ℝ),(32065511454580046643802579219455079362854912/10477218233860355671875:ℝ),(32062777534031425920738194060123554371862528/10477218233860355671875:ℝ),(2137336246576524671176123168460530077663232/2095443646772071134375:ℝ)],
![(1781351781674337998481581962902266521321472/3492406077953451890625:ℝ),(16030799115637814126688969240384086650912768/10477218233860355671875:ℝ),(16029432238786519970111268599806950492864512/10477218233860355671875:ℝ),(1068537693634343967773409049625932681183232/2095443646772071134375:ℝ)]]
theorem admission034_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (474526060061084095208898259/1953095037651263343820800000:ℝ) admission034_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission034_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_07_coefficients]
def admission034_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20422346581601364516982777578400380962304193024/4092663372601701434326171875:ℝ),(102173198480621813238606318520972017767285704192/6821105621002835723876953125:ℝ),(306703989382411834054680239024634199513713168896/20463316863008507171630859375:ℝ),(20459225369531921159403594206690474215155404288/4092663372601701434326171875:ℝ)],
![(40947367107782782158241661857127774657443647488/4092663372601701434326171875:ℝ),(204859716665296446259199209348818518038812855296/6821105621002835723876953125:ℝ),(614947787829952695558769713650903990669103244288/20463316863008507171630859375:ℝ),(41021094674237991211188506867085092462616583168/4092663372601701434326171875:ℝ)],
![(20525020526181417641258884278727393695139454464/4092663372601701434326171875:ℝ),(102686518184674633020592890827846500271527151104/6821105621002835723876953125:ℝ),(308243798447540861504089474626269791155390075392/20463316863008507171630859375:ℝ),(132657221320684322914741372002545924177168896/26404279823236783447265625:ℝ)]]
theorem admission034_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (39887395667190165072231987457813244067000377/16776958625384129429587879369113600000000000000:ℝ) admission034_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission034_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_08_coefficients]
def admission034_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(117931751827108198122909674632787474557297664/6548261396162722294921875:ℝ),(1768409239717111139009025387110911156844232704/32741306980813611474609375:ℝ),(589280740530349929676028378335133953874198528/10913768993604537158203125:ℝ),(23563669640426817460729718545737293703938048/1309652279232544458984375:ℝ)],
![(235683136420330699701481395689523825482380288/6548261396162722294921875:ℝ),(3534113218104892472235426915490611208055160832/32741306980813611474609375:ℝ),(1177659809672247814101855368388122170982662144/10913768993604537158203125:ℝ),(235456378603177235859112139489414041365905408/6548261396162722294921875:ℝ)],
![(117751384593222501578571721056736350925082624/6548261396162722294921875:ℝ),(1765703978387781333226401528379700051210928128/32741306980813611474609375:ℝ),(588379069141897884425826990052988217108463616/10913768993604537158203125:ℝ),(117638030401043148555463546760727572846215168/6548261396162722294921875:ℝ)]]
theorem admission034_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (417934239752935172004781160953/48827375941281583595520000000000:ℝ) admission034_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission034_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_09_coefficients]
def admission034_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(329115324015133284142480801137215488/69253807763671875:ℝ),(65797034658113651461594519118100224/4616920517578125:ℝ),(109618341950958929749912338729795584/7694867529296875:ℝ),(328724881702657851784688125433872384/69253807763671875:ℝ)],
![(657665991720673473526297463140335616/69253807763671875:ℝ),(657405732337553742775044894912477184/23084602587890625:ℝ),(1971436438577083619394143530313056256/69253807763671875:ℝ),(43792348885752928526124587247730688/4616920517578125:ℝ)],
![(109516868247877762858198551144267776/23084602587890625:ℝ),(109473498696859737386887797136986112/7694867529296875:ℝ),(984871172165735470687251034938540032/69253807763671875:ℝ),(328160288638230214265481514138468352/69253807763671875:ℝ)]]
theorem admission034_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4775360701579923832694207/2115149080664473600000000000:ℝ) admission034_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission034_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_10_coefficients]
def admission034_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4384857843972547568463338603441958611320832/10477218233860355671875:ℝ),(4384485153447516983302488453822361068634112/3492406077953451890625:ℝ),(4384112476523464503379657902121571852484608/3492406077953451890625:ℝ),(876747962640078025738969389667918192574464/2095443646772071134375:ℝ)],
![(8768619074370344873118401346831680492535808/10477218233860355671875:ℝ),(8767873740967145322252052476446192611360768/3492406077953451890625:ℝ),(8767128434764110152631150489986868189331456/3492406077953451890625:ℝ),(8766383155761239364255695387453707226447872/10477218233860355671875:ℝ)],
![(4383761230397797304655062743389721881214976/10477218233860355671875:ℝ),(4383388587519628338949564022623831542726656/3492406077953451890625:ℝ),(4383015958240645649251492587865296336846848/3492406077953451890625:ℝ),(4382643342560849235560848439114116263575552/10477218233860355671875:ℝ)]]
theorem admission034_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1946284619052484836903382099/9765475188256316719104000000:ℝ) admission034_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission034_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_11_coefficients]
def admission034_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7587717262307909880441208832/439453125:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/439453125:ℝ)],
![(15175434524615819760882417664/439453125:ℝ),(15175434524615819760882417664/146484375:ℝ),(15175434524615819760882417664/146484375:ℝ),(15175434524615819760882417664/439453125:ℝ)],
![(7587717262307909880441208832/439453125:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/439453125:ℝ)]]
theorem admission034_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission034_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission034_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_12_coefficients]
def admission034_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2403034924987510437162080272384/274658203125:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/274658203125:ℝ)],
![(4806069849975020874324160544768/274658203125:ℝ),(4806069849975020874324160544768/91552734375:ℝ),(4806069849975020874324160544768/91552734375:ℝ),(4806069849975020874324160544768/274658203125:ℝ)],
![(2403034924987510437162080272384/274658203125:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/274658203125:ℝ)]]
theorem admission034_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission034_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission034_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_13_coefficients]
def admission034_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)],
![(18889465931478580854784/9:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/9:ℝ)],
![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)]]
theorem admission034_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission034_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission034_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission034_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission034_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission034_14_coefficients]
theorem admission034_all {δ p : ℝ}
 (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission034_00_pos hd hp
 · exact admission034_01_pos hd hp
 · exact admission034_02_pos hd hp
 · exact admission034_03_pos hd hp
 · exact admission034_04_pos hd hp
 · exact admission034_05_pos hd hp
 · exact admission034_06_pos hd hp
 · exact admission034_07_pos hd hp
 · exact admission034_08_pos hd hp
 · exact admission034_09_pos hd hp
 · exact admission034_10_pos hd hp
 · exact admission034_11_pos hd hp
 · exact admission034_12_pos hd hp
 · exact admission034_13_pos hd hp
 · exact admission034_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission034_all
