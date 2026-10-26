/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission47_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(75497623030295749/157406588190789:ℝ), (75140216442104960/157406588190789:ℝ)]]
theorem admission47_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission47_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission47_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_00_coefficients]
def admission47_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(55192173153683968/157406588190789:ℝ), (54992173153683968/157406588190789:ℝ)]]
theorem admission47_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission47_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission47_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_01_coefficients]
def admission47_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9358455101362090/52468862730263:ℝ), (9326379717444096/52468862730263:ℝ)]]
theorem admission47_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission47_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission47_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_02_coefficients]
def admission47_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129353844737543296453120/1416659293717101:ℝ), (85943691798921934417408/472219764572367:ℝ), (128477794059222506799104/1416659293717101:ℝ)],
![(128914561966263416022016/1416659293717101:ℝ), (85650900841549219744768/472219764572367:ℝ), (128038705758384243212288/1416659293717101:ℝ)]]
theorem admission47_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (976857801501344629/1934212155688415232:ℝ) admission47_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission47_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_03_coefficients]
def admission47_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(107960377665746840534/7495551818609:ℝ), (1503016758064422075904/52468862730263:ℝ), (747304153999360524288/52468862730263:ℝ)],
![(760524646208661073540/52468862730263:ℝ), (216084833564686103552/7495551818609:ℝ), (107439894344955985920/7495551818609:ℝ)]]
theorem admission47_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (17104434677109387/214912461743157248:ℝ) admission47_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission47_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_04_coefficients]
def admission47_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(832642557828956367710776/98379117619243125:ℝ), (713946729083764515713564/42162478979675625:ℝ), (71419208268262053962182/8432495795935125:ℝ)],
![(816015416624057878517242/98379117619243125:ℝ), (4898025758434559586661988/295137352857729375:ℝ), (2449952281140540794207762/295137352857729375:ℝ)]]
theorem admission47_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (408007708312028939258621/8802814432999720878080000:ℝ) admission47_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission47_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_05_coefficients]
def admission47_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12575491928642594732195702772394460014592/1178669389136131925580579908499:ℝ), (12497864578266877366414542511703288281088/392889796378710641860193302833:ℝ), (37261293687799854771751739967259392868352/1178669389136131925580579908499:ℝ), (12343191478916073831322770004543988039680/1178669389136131925580579908499:ℝ)],
![(88541683188821554640850834558333821284352/8250685723952923479064059359493:ℝ), (87997197474280701281695535434152421019648/2750228574650974493021353119831:ℝ), (262362218003788792976790520077499896430592/8250685723952923479064059359493:ℝ), (86912305941681392736479549133376454656000/8250685723952923479064059359493:ℝ)]]
theorem admission47_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (367855771747710520962559282915115/3218553211934397578118703536807936:ℝ) admission47_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission47_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_06_coefficients]
def admission47_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1088972042475150885581445114961641914/24776834005864635072264442521:ℝ), (6507325071228663378661401540114665984/74330502017593905216793327563:ℝ), (120016123899562692847916412614737920/2752981556207181674696049169:ℝ)],
![(1080528113031139936676973166561684292/24776834005864635072264442521:ℝ), (6456765083210972056668979499018826752/74330502017593905216793327563:ℝ), (119081742312109350083529520128983040/2752981556207181674696049169:ℝ)]]
theorem admission47_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1362782390351593209268907777355/5638106227112308069777508698112:ℝ) admission47_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission47_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_07_coefficients]
def admission47_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2414712852113433270962562410856459947812322329998150611/10753834203934303416781442066406250000000000000:ℝ), (199208929181298463002189105113631320803880901365788514879/290353523506226192253098935792968750000000000000:ℝ), (17384953255869964640205021329340066945272970400226558557/24887444871962245050265623067968750000000000000:ℝ), (206438262955714406564315621692387380981257538171664204349/871060570518678576759296807378906250000000000000:ℝ)],
![(111781094955078572277309364766492596576118445325155601/430153368157372136671257682656250000000000000:ℝ), (229878372918822956795293284569057777971826840819275056209/290353523506226192253098935792968750000000000000:ℝ), (700195677750184731887990855588028761152484787586477096631/871060570518678576759296807378906250000000000000:ℝ), (33845317375239271256763394419493255378458573174941717147/124437224359811225251328115339843750000000000000:ℝ)]]
theorem admission47_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7244138556340299812887687232569379843436966989994451833/2955991437600257773287510480315744256000000000000000000000:ℝ) admission47_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission47_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_08_coefficients]
def admission47_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1789231634752972002052257792740804118539059132/2177651426296696441898242018447265625:ℝ), (354335005263444643877616485287102042359535582/145176761753113096126549467896484375:ℝ), (5262413115602385450812802815783032059875427328/2177651426296696441898242018447265625:ℝ), (347323956928217324273184846683110356584759296/435530285259339288379648403689453125:ℝ)],
![(34791338409827658169462428290412834303490264/44441865842789723304045755478515625:ℝ), (337492974777311678676716859520813361586502828/145176761753113096126549467896484375:ℝ), (5010518931697782211126165295600982388494444544/2177651426296696441898242018447265625:ℝ), (330580001143768386973287008741980647918272512/435530285259339288379648403689453125:ℝ)]]
theorem admission47_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2522125252866885276590629644332738097521/304457736264064635767985469698048000000000:ℝ) admission47_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission47_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_09_coefficients]
def admission47_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(296584342885702194804640392434944/1976366202172294921875:ℝ), (2051306697658576895611586739509504/4611521138402021484375:ℝ), (34740735064437127364118520776704/79054648086891796875:ℝ), (667266353534750759339487888146432/4611521138402021484375:ℝ)],
![(161751752543890947630802640559104/553382536608242578125:ℝ), (3994484111150414599053167686317056/4611521138402021484375:ℝ), (62622439512699488090471629185024/73198748228603515625:ℝ), (3895982783001639392709700870995968/13834563415206064453125:ℝ)],
![(1967316607189177829021161521703936/13834563415206064453125:ℝ), (129519445572647242203991217929216/307434742560134765625:ℝ), (5754858465561869001344381608517632/13834563415206064453125:ℝ), (1893800139834952181185938323406848/13834563415206064453125:ℝ)]]
theorem admission47_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1806068553767158681093157123/825263853093723832320000000000:ℝ) admission47_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission47_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_10_coefficients]
def admission47_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(893087172021180252336868260900556870/24776834005864635072264442521:ℝ), (1778947108835327596287633189380709376/24776834005864635072264442521:ℝ), (2657605096341756870024949894162677760/74330502017593905216793327563:ℝ)],
![(885988282634746453199740195461650620/24776834005864635072264442521:ℝ), (1764778931323038829074579882030635008/24776834005864635072264442521:ℝ), (2636397125224438725904814069648588800/74330502017593905216793327563:ℝ)]]
theorem admission47_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (20114113809390554244268906171025/101485912088021545255995156566016:ℝ) admission47_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission47_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_11_coefficients]
def admission47_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission47_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission47_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission47_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_12_coefficients]
def admission47_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission47_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission47_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission47_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_13_coefficients]
def admission47_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission47_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission47_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission47_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission47_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission47_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission47_14_coefficients]
theorem admission47_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (939/2048:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission47_00_pos hδ hp
 · exact admission47_01_pos hδ hp
 · exact admission47_02_pos hδ hp
 · exact admission47_03_pos hδ hp
 · exact admission47_04_pos hδ hp
 · exact admission47_05_pos hδ hp
 · exact admission47_06_pos hδ hp
 · exact admission47_07_pos hδ hp
 · exact admission47_08_pos hδ hp
 · exact admission47_09_pos hδ hp
 · exact admission47_10_pos hδ hp
 · exact admission47_11_pos hδ hp
 · exact admission47_12_pos hδ hp
 · exact admission47_13_pos hδ hp
 · exact admission47_14_pos hδ hp
#print axioms admission47_all
end
end Record1252270103Finite
