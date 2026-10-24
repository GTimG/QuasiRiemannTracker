/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission033_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6611840371125148587941823512576/3376969689:ℝ),(416525329610230300846341983567872/70916363469:ℝ),(416504715839576240652349085843456/70916363469:ℝ),(138828034022974060152785396039680/70916363469:ℝ)],
![(13223680742250297175883647025152/3376969689:ℝ),(833050659220460601692683967135744/70916363469:ℝ),(833009431679152481304698171686912/70916363469:ℝ),(277656068045948120305570792079360/70916363469:ℝ)],
![(6611840371125148587941823512576/3376969689:ℝ),(416525329610230300846341983567872/70916363469:ℝ),(416504715839576240652349085843456/70916363469:ℝ),(138828034022974060152785396039680/70916363469:ℝ)]]
theorem admission033_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission033_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission033_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_00_coefficients]
def admission033_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14518460495383718023513759547392/10130909067:ℝ),(304876141188012010024028950495232/70916363469:ℝ),(304864611972965941554268950495232/70916363469:ℝ),(33872564750879985898278772277248/23638787823:ℝ)],
![(29036920990767436047027519094784/10130909067:ℝ),(609752282376024020048057900990464/70916363469:ℝ),(609729223945931883108537900990464/70916363469:ℝ),(67745129501759971796557544554496/23638787823:ℝ)],
![(14518460495383718023513759547392/10130909067:ℝ),(304876141188012010024028950495232/70916363469:ℝ),(304864611972965941554268950495232/70916363469:ℝ),(33872564750879985898278772277248/23638787823:ℝ)]]
theorem admission033_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission033_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission033_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_01_coefficients]
def admission033_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(923171976220427366249603616735232/1266363633375:ℝ),(96929589394342626161885131839635456/44322727168125:ℝ),(96926121285540378867561883922071552/44322727168125:ℝ),(32307551058912710524412878668169216/44322727168125:ℝ)],
![(1846343952440854732499207233470464/1266363633375:ℝ),(193859178788685252323770263679270912/44322727168125:ℝ),(193852242571080757735123767844143104/44322727168125:ℝ),(64615102117825421048825757336338432/44322727168125:ℝ)],
![(923171976220427366249603616735232/1266363633375:ℝ),(96929589394342626161885131839635456/44322727168125:ℝ),(96926121285540378867561883922071552/44322727168125:ℝ),(32307551058912710524412878668169216/44322727168125:ℝ)]]
theorem admission033_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission033_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission033_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_02_coefficients]
def admission033_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75377837644943035050457410043904/70916363469:ℝ),(678352363029255562715251716653056/212749090407:ℝ),(678304188221357819217986742910976/212749090407:ℝ),(226085338126931361654107256389632/212749090407:ℝ)],
![(150747616780772801418164288094208/70916363469:ℝ),(1356632199812021318014794211524608/212749090407:ℝ),(1356535850531852078513469830201344/212749090407:ℝ),(452146501062149164753168482959360/212749090407:ℝ)],
![(75369779135829766367706878050304/70916363469:ℝ),(678279836782765755299542494871552/212749090407:ℝ),(678231662310494259295483087290368/212749090407:ℝ),(226061162935217803099061226569728/212749090407:ℝ)]]
theorem admission033_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (3137228850802723/6196766395072512:ℝ) admission033_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission033_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_03_coefficients]
def admission033_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(70520076389754379881691966603264/422121211125:ℝ),(14102363274579779836644773855232/28141414075:ℝ),(211510669991889668818355642957824/422121211125:ℝ),(70495297262947351150376001732608/422121211125:ℝ)],
![(4936898408029844010358409927852032/14774242389375:ℝ),(4936320177968782545099564555173888/4924747463125:ℝ),(14807225908389552103027095998824448/14774242389375:ℝ),(1645054594171016159362270753718272/4924747463125:ℝ)],
![(2468695734388440714499191096737792/14774242389375:ℝ),(2468406604917321073686729130508288/4924747463125:ℝ),(2468117486224471231461549498433536/4924747463125:ℝ),(2467828378309891187823652200513536/14774242389375:ℝ)]]
theorem admission033_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (93918602578942713/1180336456204288000:ℝ) admission033_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission033_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_04_coefficients]
def admission033_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4369254449791938155364035338436608/44322727168125:ℝ),(13107857103387287759142398977900544/44322727168125:ℝ),(13107950810765849505104217593872384/44322727168125:ℝ),(485483128574499989036205994934272/4924747463125:ℝ)],
![(249593459398589582926315861835776/1266363633375:ℝ),(26207501022273963499239393244217344/44322727168125:ℝ),(5241537742885107812903297128333312/8864545433625:ℝ),(2911986257034070322566049187233792/14774242389375:ℝ)],
![(4366516629158697247057019825815552/44322727168125:ℝ),(523985756755467029603879770652672/1772909086725:ℝ),(13099737903659689559412268047794176/44322727168125:ℝ),(1455536871310570355457431202430976/14774242389375:ℝ)]]
theorem admission033_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (260264672586840227070869197/5544772709955886372618240000:ℝ) admission033_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission033_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_05_coefficients]
def admission033_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(551644576128089481469701789388228188438528/2297257191156675992797:ℝ),(44674481645316457813953799480944868110368768/62025944161230251805519:ℝ),(44665753307228736142812596352572726519529472/62025944161230251805519:ℝ),(14885675217355915423685204221372419497000960/62025944161230251805519:ℝ)],
![(2068857938971123137079179899785909635087597568/4307357233418767486494375:ℝ),(55848252732543950546268149546063418866664472576/38766215100768907378449375:ℝ),(55837341966609868809124695430100629019168866304/38766215100768907378449375:ℝ),(3721762136957510388548188820160959373658554368/7753243020153781475689875:ℝ)],
![(147789194104422194189069863526140254537908224/615336747631252498070625:ℝ),(27926701704221164412547024870472876297683992576/38766215100768907378449375:ℝ),(27921246149591908719866822709742674944462946304/38766215100768907378449375:ℝ),(1861052734788020960587538292489406936533434368/7753243020153781475689875:ℝ)]]
theorem admission033_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6610567745360247570689617645/57812370155383264459754569728:ℝ) admission033_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission033_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_06_coefficients]
def admission033_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106922153247092483719559911856078363172012032/209547108652804904748375:ℝ),(45819873482739592659768317298854441651273728/29935301236114986392625:ℝ),(106903923289628837504190077527450042637484032/69849036217601634916125:ℝ),(15270686962400263944821703335206771360792576/29935301236114986392625:ℝ)],
![(1069091083801075214527579739551534089286713344/1047735543264024523741875:ℝ),(3206999814467528306499918156172081697508032512/1047735543264024523741875:ℝ),(152701256478543232642427979887858674992939008/49892168726858310654375:ℝ),(1710108248612727669629838657639175306608640/1676376869222439237987:ℝ)],
![(534480317565612795929780180271142273426653184/1047735543264024523741875:ℝ),(1603304242571642563408027050712176239713452032/1047735543264024523741875:ℝ),(534389178901658440976045471577760511763152896/349245181088008174580625:ℝ),(106868722339789111089977908858449513800531968/209547108652804904748375:ℝ)]]
theorem admission033_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (94918492923125362539218760157/390624122671508543646990336000:ℝ) admission033_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission033_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_07_coefficients]
def admission033_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141474866072492095973358408416489255658940761005056/28421645596354831915740966796875:ℝ),(546018319684793753863377280024542601657220555592704/36542115766741926748809814453125:ℝ),(84987445706573215168148989309036073668224141294592/5684329119270966383148193359375:ℝ),(182225801949071162946909811225973279623798474021888/36542115766741926748809814453125:ℝ)],
![(283662755850246349898251855613400362081732365878272/28421645596354831915740966796875:ℝ),(38317531199483481231879118886666172371028661702178816/1278974051835967436208343505859375:ℝ),(4260065556826439463972177579483864248504069164447744/142108227981774159578704833984375:ℝ),(2557576565020772564751453030823535354409001448474624/255794810367193487241668701171875:ℝ)],
![(142187889777754253924893447196911106422791604873216/28421645596354831915740966796875:ℝ),(19206890010515699846660914085807181313025942256434176/1278974051835967436208343505859375:ℝ),(711793138054036361589484282252654135599488544027648/47369409327258053192901611328125:ℝ),(1281995951377274424123084352241722397042412130321408/255794810367193487241668701171875:ℝ)]]
theorem admission033_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (414477146696754187421948462157683366188303010757/174762274156543890202959589786255360000000000000000:ℝ) admission033_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission033_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_08_coefficients]
def admission033_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7376195021007645599628108422378760609355248652288/409271696587509579586669921875:ℝ),(819314592698674137772327008812758388187709046784/15158210984722577021728515625:ℝ),(22114403187431409603720878479832030066003721322496/409271696587509579586669921875:ℝ),(272929785392212487820855390244551814854326878208/15158210984722577021728515625:ℝ)],
![(14741116948051449153047307304229040952407107495936/409271696587509579586669921875:ℝ),(24560651007563126125196799339595702678876647325696/227373164770838655325927734375:ℝ),(220974966361687579433854029472933869507268768169984/2046358482937547897933349609375:ℝ),(327265297929002375037325220915443889966944354304/9094926590833546213037109375:ℝ)],
![(1052131703863400507631314125978611477578836977664/58467385226787082798095703125:ℝ),(12270932117083014058611894207404326856061011623936/227373164770838655325927734375:ℝ),(110402950424530531415249637073773719177250161557504/2046358482937547897933349609375:ℝ),(817537133468374411724059933843564005271741136896/45474632954167731065185546875:ℝ)]]
theorem admission033_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (139414817136021340227908911034017593/16276005111312855985291264000000000000:ℝ) admission033_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission033_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_09_coefficients]
def admission033_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(411721550184381677973477260208279977984/86567826500244140625:ℝ),(1234676429699408651332045399622131812352/86567826500244140625:ℝ),(1234188221180519933250665657619423690752/86567826500244140625:ℝ),(45692593518471280565810314522841317376/9618647388916015625:ℝ)],
![(117533918266497703643043422720429195264/12366832357177734375:ℝ),(2467235999596976718756586165086707759104/86567826500244140625:ℝ),(2466259740257874336625671285724402417664/86567826500244140625:ℝ),(91306796503097647037139585242299891712/9618647388916015625:ℝ)],
![(137005266326092013619397613552748249088/28855942166748046875:ℝ),(410853111269905650296355458890015528448/28855942166748046875:ℝ),(410690427670043245292267808707786309632/28855942166748046875:ℝ),(45614194242159726735230274248506343424/9618647388916015625:ℝ)]]
theorem admission033_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (382333759385568593272075493109/169213034361446727680000000000000:ℝ) admission033_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission033_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_10_coefficients]
def admission033_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(146182864534769338849830630547832035359064064/349245181088008174580625:ℝ),(187933422604563274572964014042622419772899328/149676506180574931963125:ℝ),(1315422139731810500661036514887302053674090496/1047735543264024523741875:ℝ),(20877941671627409295227633725354343873380352/49892168726858310654375:ℝ)],
![(292329174646525224776312933859926153082437632/349245181088008174580625:ℝ),(2630738940950952872997831369599189577239625728/1047735543264024523741875:ℝ),(375787902606334083593343646863417540331175936/149676506180574931963125:ℝ),(58450926748864092432300864001634110955061248/69849036217601634916125:ℝ)],
![(146146310111755885926482303312094117723373568/349245181088008174580625:ℝ),(1315204982719009950987083271300832638829330432/1047735543264024523741875:ℝ),(1315093178512528084492369013156620728644141056/1047735543264024523741875:ℝ),(146109042042928597094910883930690147661643776/349245181088008174580625:ℝ)]]
theorem admission033_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (129770898065587478504766213599/651040204452514239411650560000:ℝ) admission033_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission033_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_11_coefficients]
def admission033_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(189696976223085150696309260288/10986328125:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/10986328125:ℝ)],
![(379393952446170301392618520576/10986328125:ℝ),(379393952446170301392618520576/3662109375:ℝ),(379393952446170301392618520576/3662109375:ℝ),(379393952446170301392618520576/10986328125:ℝ)],
![(189696976223085150696309260288/10986328125:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/3662109375:ℝ),(189696976223085150696309260288/10986328125:ℝ)]]
theorem admission033_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission033_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission033_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_12_coefficients]
def admission033_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6675672401954239904317433708544/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(6675672401954239904317433708544/762939453125:ℝ)],
![(13351344803908479808634867417088/762939453125:ℝ),(40054034411725439425904602251264/762939453125:ℝ),(40054034411725439425904602251264/762939453125:ℝ),(13351344803908479808634867417088/762939453125:ℝ)],
![(6675672401954239904317433708544/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(20027017205862719712952301125632/762939453125:ℝ),(6675672401954239904317433708544/762939453125:ℝ)]]
theorem admission033_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission033_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission033_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_13_coefficients]
def admission033_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)],
![(18889465931478580854784/9:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/9:ℝ)],
![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)]]
theorem admission033_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission033_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission033_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_14_coefficients]
theorem admission033_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission033_00_pos hd hp
 · exact admission033_01_pos hd hp
 · exact admission033_02_pos hd hp
 · exact admission033_03_pos hd hp
 · exact admission033_04_pos hd hp
 · exact admission033_05_pos hd hp
 · exact admission033_06_pos hd hp
 · exact admission033_07_pos hd hp
 · exact admission033_08_pos hd hp
 · exact admission033_09_pos hd hp
 · exact admission033_10_pos hd hp
 · exact admission033_11_pos hd hp
 · exact admission033_12_pos hd hp
 · exact admission033_13_pos hd hp
 · exact admission033_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission033_all
