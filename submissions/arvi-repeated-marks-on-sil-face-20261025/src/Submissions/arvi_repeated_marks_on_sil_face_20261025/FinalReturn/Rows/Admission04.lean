/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission04_00_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 0 := by
 rw [admission04_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]
def admission04_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission04_01_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 1 := by
 rw [admission04_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]
def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1270613545954726835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2558591076383360746323227/3829204622338087582216250:ℝ) admission04_02_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 2 := by
 rw [admission04_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]
def admission04_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(135154719904615541564266688/9190091093611410197319:ℝ), (178221176298659405816594624/9190091093611410197319:ℝ), (14511220978834248084109312/3063363697870470065773:ℝ)],
![(91413708955538807564567168/9190091093611410197319:ℝ), (90933875209229687564567168/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (780949968430480320498417/784221106654840336837888:ℝ) admission04_03_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 3 := by
 rw [admission04_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]
def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4580790974048620590272081851/1914602311169043791108125:ℝ), (2368:ℝ), (0:ℝ)],
![(7324593397725955523973879322/1914602311169043791108125:ℝ), (9896307345196237308444928896/1914602311169043791108125:ℝ), (2619997262216561404234984448/1914602311169043791108125:ℝ)]]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (284003609478553042841878197/1960552766637100842094720000:ℝ) admission04_04_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 4 := by
 rw [admission04_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]
def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5075698893201987446652537041/1914602311169043791108125:ℝ), (9984856242633782426452386508/1914602311169043791108125:ℝ), (4886468588848235526871807616/1914602311169043791108125:ℝ)],
![(10926017397669009818276662/382920462233808758221625:ℝ), (77932057317406108855318184/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (784876440276957820602152571/7842211066548403368378880000:ℝ) admission04_05_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 5 := by
 rw [admission04_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]
def admission04_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(241137363846725677846948863213000463974302490302196928/651028676964250692137413394579714034384822324375:ℝ), (477200906999724529446948338588450670629870042287250624/651028676964250692137413394579714034384822324375:ℝ), (236093273269897041996985988866869250905167551985053696/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(316558546801389917452269067582900807917868134881299072/651028676964250692137413394579714034384822324375:ℝ), (699296216510627531250423014492263349675651054589454976/651028676964250692137413394579714034384822324375:ℝ), (454113673034349344939449649400915736339815874700713984/651028676964250692137413394579714034384822324375:ℝ), (4756364646102707778635051314438818951442196999503872/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9252626556250598431082402026190223407027787715887/44443557680759513916580754403308478080670537344000:ℝ) admission04_06_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 6 := by
 rw [admission04_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]
def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(195402268362997011322994773309978024848489618799139/17595369647682451138849010664316595523914116875:ℝ), (281763490303057243024073728298887288645730315891648/17595369647682451138849010664316595523914116875:ℝ), (5820455200455618277721565104444296338030192098304/1173024643178830075923267377621106368260941125:ℝ)],
![(104926518651910409357775395535854875484869536556106/17595369647682451138849010664316595523914116875:ℝ), (104008633935628114066264426707936165323901357579392/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (282307234657515339642094140808007862749511270393/600588617307560998872712897342006460549601856000:ℝ) admission04_07_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 7 := by
 rw [admission04_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]
def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (16762516379185475753831871621631292169974836666247647842788094901199105933/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (66976103752659027888209873635859592856401678616126096623539292534741027911/1322501900961975472103302977990912709392244563089817600000000000000000:ℝ), (6687797953449744549265784939649255578026252677753909337340590594468563209/264500380192395094420660595598182541878448912617963520000000000000000:ℝ)],
![(883454829523504281009884350807000852854177218827153289565579681984197247/12595256199637861639079075980865835327545186315141120000000000000000:ℝ), (1804871362961284259716129548644068841659468375653140512705700317774058761/7825455035277961373392325313555696505279553627750400000000000000000:ℝ), (331799421696867927655236910996259524966402281336420112589260706399881672199/1322501900961975472103302977990912709392244563089817600000000000000000:ℝ), (4781060428387590854985896784529849196106506983380777738668425322576258101/52900076038479018884132119119636508375689782523592704000000000000000:ℝ)]]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (309864905346170702654381581323790295700866818705807460616583215994370449/845253335346654105987774795245591945242625362277466562887680000000000000000:ℝ) admission04_08_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 8 := by
 rw [admission04_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]
def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(23217228515254373999688177862085970940104200688778951/175953696476824511388490106643165955239141168750:ℝ), (1483946617020805547904880782810244566690027754688531969/4398842411920612784712252666079148880978529218750:ℝ), (614485005586127351026471871497039444479074749637537312/2199421205960306392356126333039574440489264609375:ℝ), (10849523185630136502550718057539141250893999060179456/146628080397353759490408422202638296032617640625:ℝ)],
![(23175099131327631851051478181155302909601339015047269/439884241192061278471225266607914888097852921875:ℝ), (230737786856364251536426824979785739297928978914110103/2199421205960306392356126333039574440489264609375:ℝ), (8834313081505299764271186062213553268984102935655616/169186246612331260950471256387659572345328046875:ℝ), (0:ℝ)]]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (238545079840074110573923655079182365745890601689659/9609417876920975981963406357472103368793629696000000:ℝ) admission04_09_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 9 := by
 rw [admission04_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]
def admission04_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54412483089004756738208851055648/17231420800521394119973125:ℝ), (137128338864415746065647432720928/17231420800521394119973125:ℝ), (4450378013450098396879976300032/689256832020855764798925:ℝ), (5709159721541104072192165167104/3446284160104278823994625:ℝ)],
![(6118699375477460429935693650304/1325493907732414932305625:ℝ), (20895652069088881561602416793472/1914602311169043791108125:ℝ), (45982168611068507486644889212928/5743806933507131373324375:ℝ), (29433256324009000541876933951488/17231420800521394119973125:ℝ)],
![(24180377211412906974243601889408/17231420800521394119973125:ℝ), (48145496242472403126199765790848/17231420800521394119973125:ℝ), (4792558847311725693111232780288/3446284160104278823994625:ℝ), (0:ℝ)]]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2487567169645437021660409993/501901508259097815576248320000:ℝ) admission04_10_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 10 := by
 rw [admission04_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]
def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(55249419385023191008065309918703327152646698894751/5865123215894150379616336888105531841304705625:ℝ), (79725830153563643972923881801473706442051474227392/5865123215894150379616336888105531841304705625:ℝ), (24781475219861924075974640284441874086334303458304/5865123215894150379616336888105531841304705625:ℝ)],
![(29537620337539214593820125276758146380804051296658/5865123215894150379616336888105531841304705625:ℝ), (29242070324785349559650343074336112196806521369216/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1172740653528050771034509978664345794274697926163/3002943086537804994363564486710032302748009280000:ℝ) admission04_11_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 11 := by
 rw [admission04_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]
def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission04_12_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 12 := by
 rw [admission04_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]
def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (30094022595683136330185461/1503238553600000000000000000:ℝ) admission04_13_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 13 := by
 rw [admission04_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]
def admission04_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_14_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 14 := by
 rw [admission04_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]
theorem admission04_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC7 δ p j := by
 fin_cases j
 · exact admission04_00_pos hδ hp
 · exact admission04_01_pos hδ hp
 · exact admission04_02_pos hδ hp
 · exact admission04_03_pos hδ hp
 · exact admission04_04_pos hδ hp
 · exact admission04_05_pos hδ hp
 · exact admission04_06_pos hδ hp
 · exact admission04_07_pos hδ hp
 · exact admission04_08_pos hδ hp
 · exact admission04_09_pos hδ hp
 · exact admission04_10_pos hδ hp
 · exact admission04_11_pos hδ hp
 · exact admission04_12_pos hδ hp
 · exact admission04_13_pos hδ hp
 · exact admission04_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
