/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission11_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3249977881151303/52468862730263:ℝ), (9392527055263120/157406588190789:ℝ)]]
theorem admission11_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission11_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission11_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_00_coefficients]
def admission11_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2358007214736832/52468862730263:ℝ), (6874021644210496/157406588190789:ℝ)]]
theorem admission11_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission11_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission11_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_01_coefficients]
def admission11_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1197872848598506/52468862730263:ℝ), (1165797464680512/52468862730263:ℝ)]]
theorem admission11_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission11_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission11_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_02_coefficients]
def admission11_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(90523145159043844736/472219764572367:ℝ), (75613568814235480192/202379899102443:ℝ), (257793946222516827136/1416659293717101:ℝ)],
![(88228648990443853376/472219764572367:ℝ), (515548938493250518720/1416659293717101:ℝ), (250933191521918958592/1416659293717101:ℝ)]]
theorem admission11_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (245051944845623983/483553038922103808:ℝ) admission11_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission11_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_03_coefficients]
def admission11_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(220918979400055140/7495551818609:ℝ), (2962823708263004800/52468862730263:ℝ), (1417609717051502592/52468862730263:ℝ)],
![(1624433976138593574/52468862730263:ℝ), (3115403790956847168/52468862730263:ℝ), (1492220754791055360/52468862730263:ℝ)]]
theorem admission11_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1038288366981081/13432028858947328:ℝ) admission11_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission11_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_04_coefficients]
def admission11_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1132718146808182193069/59027470571545875:ℝ), (11337920252538384018754/295137352857729375:ℝ), (1890344826728333945303/98379117619243125:ℝ)],
![(973292562361056419711/59027470571545875:ℝ), (9764003912952433017142/295137352857729375:ℝ), (1631386450433380328279/98379117619243125:ℝ)]]
theorem admission11_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (973292562361056419711/20631596327343095808000:ℝ) admission11_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission11_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_05_coefficients]
def admission11_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(23707340874219099558915961436681744896/8250685723952923479064059359493:ℝ), (67885748162858608091821536390339154432/8250685723952923479064059359493:ℝ), (64712805986672387178879873897688047616/8250685723952923479064059359493:ℝ), (20534056445484027146427898944030638080/8250685723952923479064059359493:ℝ)],
![(3536497459229154335436575013005542144/1178669389136131925580579908499:ℝ), (70976955788791329007030405941112857856/8250685723952923479064059359493:ℝ), (67751907820406922988652103039355752448/8250685723952923479064059359493:ℝ), (3075726141003542917464074598468812800/1178669389136131925580579908499:ℝ)]]
theorem admission11_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (156662417949554650470183555176015/1408117030221298940426932797353472:ℝ) admission11_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission11_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_06_coefficients]
def admission11_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7154471607080994000108380017781236/74330502017593905216793327563:ℝ), (13874222864901624458031435313824128/74330502017593905216793327563:ℝ), (249006204295291865162131938478080/2752981556207181674696049169:ℝ)],
![(6747253412390984072501527672803538/74330502017593905216793327563:ℝ), (13072915613586514911138763920833984/74330502017593905216793327563:ℝ), (234406491991333384468586743388160/2752981556207181674696049169:ℝ)]]
theorem admission11_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (343368884752929762405156362385/1409526556778077017444377174528:ℝ) admission11_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission11_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_07_coefficients]
def admission11_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(386718364426090782294901826668176511015431557116201/139369691282988572281487489180625000000000000000:ℝ), (19284145080287740292418356567393748459112724150200009/497748897439244901005312461359375000000000000000:ℝ), (240405505702901663666076745070651674506280167392039293/3484242282074714307037187229515625000000000000000:ℝ), (23011598790810575661773522853997394152439127453708851/696848456414942861407437445903125000000000000000:ℝ)],
![(13295759963849280030140068695202461360962281863782411/174212114103735715351859361475781250000000000000:ℝ), (442654575067985937429115456866095825959948519105698317/1742121141037357153518593614757812500000000000000:ℝ), (19848897161621306106853917686970857597775589117199821/71106985348463557286473208765625000000000000000:ℝ), (70634971714186344775879990422849592071114868161408563/696848456414942861407437445903125000000000000000:ℝ)]]
theorem admission11_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (386718364426090782294901826668176511015431557116201/3117647219344021870264171209708011520000000000000000000:ℝ) admission11_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission11_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_08_coefficients]
def admission11_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(281660861282357245551600383417979571002503/871060570518678576759296807378906250:ℝ), (569918990610432539288270752559200081939837/622186121799056126256640576699218750:ℝ), (1878045199076347169764157874550958265919712/2177651426296696441898242018447265625:ℝ), (117498926563429888347745983938512701639808/435530285259339288379648403689453125:ℝ)],
![(84636212879695012884946520154501919158863/348424228207471430703718722951562500:ℝ), (5924114533061269117339311145376408824429919/8710605705186785767592968073789062500:ℝ), (196573947560659109909436845461024740815888/311093060899528063128320288349609375:ℝ), (84795887921928057683883019209743739400576/435530285259339288379648403689453125:ℝ)]]
theorem admission11_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (662467874390062950655336087576122964067/76114434066016158941996367424512000000000:ℝ) admission11_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission11_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_09_coefficients]
def admission11_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106306987192126357839168944896/13834563415206064453125:ℝ), (11955623637254235491501339264/553382536608242578125:ℝ), (278997025983795690663790128512/13834563415206064453125:ℝ), (86415148275816161215425591808/13834563415206064453125:ℝ)],
![(186613845571295037696010223872/13834563415206064453125:ℝ), (74459255960406814275387638144/1976366202172294921875:ℝ), (19313603577003997431113050496/553382536608242578125:ℝ), (148242686179797273546123019264/13834563415206064453125:ℝ)],
![(26502242212424591461053330112/4611521138402021484375:ℝ), (73325137919444323771941008992/4611521138402021484375:ℝ), (67181740754157359920274527648/4611521138402021484375:ℝ), (20359451070575127609386848768/4611521138402021484375:ℝ)]]
theorem admission11_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39764552872217046112083689/17192996939452579840000000000:ℝ) admission11_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission11_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_10_coefficients]
def admission11_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5875734799364514061053387191866508/74330502017593905216793327563:ℝ), (11394463482228354299210989993500416/74330502017593905216793327563:ℝ), (5522009502500589888644602520069120/74330502017593905216793327563:ℝ)],
![(5533179723124426491955132025493614/74330502017593905216793327563:ℝ), (10720640597033410620595711349679488/74330502017593905216793327563:ℝ), (5190634953792493886767480262036480/74330502017593905216793327563:ℝ)]]
theorem admission11_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5068979447062982311296367443395/25371478022005386313998789141504:ℝ) admission11_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission11_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_11_coefficients]
def admission11_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission11_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission11_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission11_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_12_coefficients]
def admission11_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission11_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission11_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission11_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_13_coefficients]
def admission11_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission11_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission11_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission11_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_14_coefficients]
theorem admission11_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission11_00_pos hδ hp
 · exact admission11_01_pos hδ hp
 · exact admission11_02_pos hδ hp
 · exact admission11_03_pos hδ hp
 · exact admission11_04_pos hδ hp
 · exact admission11_05_pos hδ hp
 · exact admission11_06_pos hδ hp
 · exact admission11_07_pos hδ hp
 · exact admission11_08_pos hδ hp
 · exact admission11_09_pos hδ hp
 · exact admission11_10_pos hδ hp
 · exact admission11_11_pos hδ hp
 · exact admission11_12_pos hδ hp
 · exact admission11_13_pos hδ hp
 · exact admission11_14_pos hδ hp
#print axioms admission11_all
end
end Record1252270103Finite
