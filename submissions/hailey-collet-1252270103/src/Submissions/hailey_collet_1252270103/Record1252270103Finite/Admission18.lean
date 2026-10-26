/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission18_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1806072133773489/7495551818609:ℝ), (37570108221052480/157406588190789:ℝ)]]
theorem admission18_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission18_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission18_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_00_coefficients]
def admission18_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1318861265563904/7495551818609:ℝ), (27496086576841984/157406588190789:ℝ)]]
theorem admission18_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission18_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission18_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_01_coefficients]
def admission18_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(670752177520006/7495551818609:ℝ), (4663189858722048/52468862730263:ℝ)]]
theorem admission18_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission18_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission18_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_02_coefficients]
def admission18_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(606992383519399603456/52468862730263:ℝ), (4651144526805166934272/202379899102443:ℝ), (16169496332612379246592/1416659293717101:ℝ)],
![(1808769549399268330496/157406588190789:ℝ), (32338369401996228324352/1416659293717101:ℝ), (16059724257402813349888/1416659293717101:ℝ)]]
theorem admission18_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (245051944845623983/483553038922103808:ℝ) admission18_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission18_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_03_coefficients]
def admission18_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(94604622954689557230/52468862730263:ℝ), (187117338067227700480/52468862730263:ℝ), (92517686797045432320/52468862730263:ℝ)],
![(95811863662765266840/52468862730263:ℝ), (189518323303752336384/52468862730263:ℝ), (93711463400878276608/52468862730263:ℝ)]]
theorem admission18_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8470247204319345/107456230871578624:ℝ) admission18_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission18_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_04_coefficients]
def admission18_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(46378482929064850958866/42162478979675625:ℝ), (649634013889715581504264/295137352857729375:ℝ), (108323731032802707924484/98379117619243125:ℝ)],
![(312138627402496727180788/295137352857729375:ℝ), (624693345438135117072088/295137352857729375:ℝ), (4167215880483338002084/3935164704769725:ℝ)]]
theorem admission18_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (78034656850624181795197/1650527706187447664640000:ℝ) admission18_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission18_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_05_coefficients]
def admission18_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5554878097125930863922251683769172198400/8250685723952923479064059359493:ℝ), (16461080508810933693114114189883111736320/8250685723952923479064059359493:ℝ), (16258540805746961486378018467329883832320/8250685723952923479064059359493:ℝ), (5352336998031825183964321961215944294400/8250685723952923479064059359493:ℝ)],
![(5619444494469325708192125245972638093312/8250685723952923479064059359493:ℝ), (16653954649810696949998110477973345030144/8250685723952923479064059359493:ℝ), (16450594257068585411052543880912718528512/8250685723952923479064059359493:ℝ), (5416082696690434673616841848912011591680/8250685723952923479064059359493:ℝ)]]
theorem admission18_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1276096581943470283499794473937975/11264936241770391523415462378827776:ℝ) admission18_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission18_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_06_coefficients]
def admission18_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(418065981266675414303953941245312170/74330502017593905216793327563:ℝ), (829414119637145904797785033585683200/74330502017593905216793327563:ℝ), (15235610884308672297086274698280960/2752981556207181674696049169:ℝ)],
![(411707111228178164927137592314513480/74330502017593905216793327563:ℝ), (116678325294131481588685294513636352/10618643145370557888113332509:ℝ), (15002015487445336605989551576842240/2752981556207181674696049169:ℝ)]]
theorem admission18_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (343368884752929762405156362385/1409526556778077017444377174528:ℝ) admission18_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission18_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_07_coefficients]
def admission18_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(717926303643343797988512575816022180216467549375601857/69684845641494286140743744590312500000000000000:ℝ), (11355127176144828981552146395580274454954629189440770363/348424228207471430703718722951562500000000000000:ℝ), (11940703129788523109614058678874478850445910876753025713/348424228207471430703718722951562500000000000000:ℝ), (835039336176761326077481220381799903534523574338052927/69684845641494286140743744590312500000000000000:ℝ)],
![(3673028019118571868531230356316649279462092822450289593/248874448719622450502656230679687500000000000000:ℝ), (11417267471683146568718466530871911530234928038401684347/248874448719622450502656230679687500000000000000:ℝ), (82705453543090231113706743491886548285230610633343040373/1742121141037357153518593614757812500000000000000:ℝ), (5699144614431831242038813064112269851070241574336655419/348424228207471430703718722951562500000000000000:ℝ)]]
theorem admission18_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (717926303643343797988512575816022180216467549375601857/399058844076034799393813914842625474560000000000000000000:ℝ) admission18_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission18_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_08_coefficients]
def admission18_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(25172812164118633274338271293029622042631629/435530285259339288379648403689453125:ℝ), (74143264518781995905284601104023842417631511/435530285259339288379648403689453125:ℝ), (72771182920527427970672347199299053490951936/435530285259339288379648403689453125:ℝ), (23800741781069699929561282660335610869858304/435530285259339288379648403689453125:ℝ)],
![(115214663184303429520616511869431628414176148/2177651426296696441898242018447265625:ℝ), (338953268804372602925686126224360738231240572/2177651426296696441898242018447265625:ℝ), (332277285722328087369010802090601053359176704/2177651426296696441898242018447265625:ℝ), (21707747308013582767074052917694397286547456/435530285259339288379648403689453125:ℝ)]]
theorem admission18_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (662467874390062950655336087576122964067/76114434066016158941996367424512000000000:ℝ) admission18_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission18_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_09_coefficients]
def admission18_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73964375199468144107012481656704/13834563415206064453125:ℝ), (217095063488451378245106545558912/13834563415206064453125:ℝ), (212304956257727552985757396147712/13834563415206064453125:ℝ), (9882042383732447335380476035072/1976366202172294921875:ℝ)],
![(141252418329467617601820659657728/13834563415206064453125:ℝ), (414255704950823654684585411369984/13834563415206064453125:ℝ), (57824243858754546733518120538112/1976366202172294921875:ℝ), (131766478195238290051862092054528/13834563415206064453125:ℝ)],
![(22413096026619235960204672362496/4611521138402021484375:ℝ), (65671728726394683439810117863424/4611521138402021484375:ℝ), (12821340179933875630323515727872/922304227680404296875:ℝ), (20848077896268930672012133138432/4611521138402021484375:ℝ)]]
theorem admission18_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (39764552872217046112083689/17192996939452579840000000000:ℝ) admission18_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission18_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_10_coefficients]
def admission18_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(342989659063626195960436545151571030/74330502017593905216793327563:ℝ), (680479485826388061818721535518440960/74330502017593905216793327563:ℝ), (337502629822049144783152692898856960/74330502017593905216793327563:ℝ)],
![(337643264393428413338598353731441592/74330502017593905216793327563:ℝ), (95690172159516283294172783821481984/10618643145370557888113332509:ℝ), (332200637042719608753118736770334720/74330502017593905216793327563:ℝ)]]
theorem admission18_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5068979447062982311296367443395/25371478022005386313998789141504:ℝ) admission18_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission18_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_11_coefficients]
def admission18_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission18_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission18_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission18_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_12_coefficients]
def admission18_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission18_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission18_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission18_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_13_coefficients]
def admission18_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission18_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission18_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission18_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_14_coefficients]
theorem admission18_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission18_00_pos hδ hp
 · exact admission18_01_pos hδ hp
 · exact admission18_02_pos hδ hp
 · exact admission18_03_pos hδ hp
 · exact admission18_04_pos hδ hp
 · exact admission18_05_pos hδ hp
 · exact admission18_06_pos hδ hp
 · exact admission18_07_pos hδ hp
 · exact admission18_08_pos hδ hp
 · exact admission18_09_pos hδ hp
 · exact admission18_10_pos hδ hp
 · exact admission18_11_pos hδ hp
 · exact admission18_12_pos hδ hp
 · exact admission18_13_pos hδ hp
 · exact admission18_14_pos hδ hp
#print axioms admission18_all
end
end Record1252270103Finite
