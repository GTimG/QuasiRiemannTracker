/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission38_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(50212613157466903/52468862730263:ℝ), (150280432884209920/157406588190789:ℝ)]]
theorem admission38_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission38_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission38_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_00_coefficients]
def admission38_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(36728115435789312/52468862730263:ℝ), (109984346307367936/157406588190789:ℝ)]]
theorem admission38_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission38_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission38_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_01_coefficients]
def admission38_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(18684834818806186/52468862730263:ℝ), (18652759434888192/52468862730263:ℝ)]]
theorem admission38_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission38_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission38_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_02_coefficients]
def admission38_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(343775273042648815565824/472219764572367:ℝ), (2059147046601726501090304/1416659293717101:ℝ), (1027822352473780054392832/1416659293717101:ℝ)],
![(343189691727903386220544/472219764572367:ℝ), (2055633947654137158707200/1416659293717101:ℝ), (1026065999270427000045568/1416659293717101:ℝ)]]
theorem admission38_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1957065580883840561/3868424311376830464:ℝ) admission38_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission38_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_03_coefficients]
def admission38_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6002483138426538506250/52468862730263:ℝ), (11971346110475811200000/52468862730263:ℝ), (5968883019164221440000/52468862730263:ℝ)],
![(6021637324278683722164/52468862730263:ℝ), (12009600689913898006528/52468862730263:ℝ), (5987983444825546948608/52468862730263:ℝ)]]
theorem admission38_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (34154222598061875/429824923486314496:ℝ) admission38_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission38_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_04_coefficients]
def admission38_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(571046138370463020839792/8432495795935125:ℝ), (7995977063761898770947524/59027470571545875:ℝ), (88858739027263117456394/1311721568256575:ℝ)],
![(113070926091149069394346/1686499159187025:ℝ), (39581802595511385430197268/295137352857729375:ℝ), (2199370694237741894423802/32793039206414375:ℝ)]]
theorem admission38_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (56535463045574534697173/1207243122239961720422400:ℝ) admission38_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission38_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_05_coefficients]
def admission38_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1393377050233283923594463772200068539166720/8250685723952923479064059359493:ℝ), (4167135427540538426732476855800595438120960/8250685723952923479064059359493:ℝ), (4154155966217933032582209437703179405885440/8250685723952923479064059359493:ℝ), (1380397583281524765439269604102652506931200/8250685723952923479064059359493:ℝ)],
![(1397469853979303679752074400316582034235392/8250685723952923479064059359493:ℝ), (4179400742391386278834673598750119672111104/8250685723952923479064059359493:ℝ), (4166408202045918781886964708148738451832832/8250685723952923479064059359493:ℝ), (1384477307995675772777030876915200813957120/8250685723952923479064059359493:ℝ)]]
theorem admission38_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5142381725018936266896387949968325/45059744967081566093661849515311104:ℝ) admission38_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission38_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_06_coefficients]
def admission38_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(531215509298992263048764482574379550/1516949020767222555444761787:ℝ), (7421855687401516685032372996996029440/10618643145370557888113332509:ℝ), (960128991196501542783331300917903360/2752981556207181674696049169:ℝ)],
![(529151834213054213592758686994561308/1516949020767222555444761787:ℝ), (1056141971925107614952815969557530624/1516949020767222555444761787:ℝ), (19518193160136493300526198591324160/56183297065452687238694881:ℝ)]]
theorem admission38_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (55841998558434944058970065855/230126784780094206929694232576:ℝ) admission38_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission38_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_07_coefficients]
def admission38_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6225258762602435579604891497045755641154807663924180927/1777674633711588932161830219140625000000000000:ℝ), (131986381937847699935123721402837739934396016631777947271/12443722435981122525132811533984375000000000000:ℝ), (932694165134171432756463493841188082053620159829831693651/87106057051867857675929680737890625000000000000:ℝ), (313827160058756265232590888404322667055541480267795928177/87106057051867857675929680737890625000000000000:ℝ)],
![(6725206884931243655128850058360542270815140029323211293/1777674633711588932161830219140625000000000000:ℝ), (712344743234228056395622489045721332192488209969795188541/62218612179905612625664057669921875000000000000:ℝ), (5029789205286092056142116522792585686411677290623820456607/435530285259339288379648403689453125000000000000:ℝ), (338210326995524659019013399799574992389903459510138180721/87106057051867857675929680737890625000000000000:ℝ)]]
theorem admission38_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6225258762602435579604891497045755641154807663924180927/2606098573557778281755519443870207180800000000000000000000:ℝ) admission38_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission38_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_08_coefficients]
def admission38_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5641904293861705825748554125547850502156021238/435530285259339288379648403689453125:ℝ), (673637794287366394026665887067937485955137716/17421211410373571535185936147578125:ℝ), (16756223828951327848007456786499583086941851648/435530285259339288379648403689453125:ℝ), (5557183310851477188370957546929765705356148736/435530285259339288379648403689453125:ℝ)],
![(5507364199303653994558910144969329769360632396/435530285259339288379648403689453125:ℝ), (82189567962184929219562761891541435375682697224/2177651426296696441898242018447265625:ℝ), (81768905062071290043296863575301934229196120064/2177651426296696441898242018447265625:ℝ), (5423231664575885689971774843400728036024254464/435530285259339288379648403689453125:ℝ)]]
theorem admission38_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5171996750427137079211973994637229953789/608915472528129271535970939396096000000000:ℝ) admission38_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission38_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_09_coefficients]
def admission38_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7249189027522533725228165235295744/1537173712800673828125:ℝ), (194533281548476303171939263301785088/13834563415206064453125:ℝ), (193338943791692188824849440250585088/13834563415206064453125:ℝ), (21349454652612544830821221355487232/4611521138402021484375:ℝ)],
![(128763552820158424048359746558400512/13834563415206064453125:ℝ), (18281293403300785103337583088285696/658788734057431640625:ℝ), (127174875846396805726501995077599232/4611521138402021484375:ℝ), (126381019825364385307776486937198592/13834563415206064453125:ℝ)],
![(63517770027916780919505385607223296/13834563415206064453125:ℝ), (27052092597400778876955978785712128/1976366202172294921875:ℝ), (188176464892501661316456897698299904/13834563415206064453125:ℝ), (62329587207027271347270431805538304/13834563415206064453125:ℝ)]]
theorem admission38_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (7430265808943184774788669563/3301055412374895329280000000000:ℝ) admission38_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission38_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_10_coefficients]
def admission38_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3049656166452396299783863590691089710/10618643145370557888113332509:ℝ), (869558841986988696784672938202327040/1516949020767222555444761787:ℝ), (21260840770734054960199599153301422080/74330502017593905216793327563:ℝ)],
![(433930285578638535822782963101155044/1516949020767222555444761787:ℝ), (6062648901117062994670015832822460416/10618643145370557888113332509:ℝ), (3025144126609254626245579407892152320/10618643145370557888113332509:ℝ)]]
theorem admission38_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (5770004513948926212779196563515/28995974882291870073141473304576:ℝ) admission38_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission38_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_11_coefficients]
def admission38_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission38_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission38_12_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission38_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_12_coefficients]
def admission38_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission38_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission38_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission38_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_13_coefficients]
def admission38_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission38_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission38_14_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission38_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission38_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission38_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission38_14_coefficients]
theorem admission38_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission38_00_pos hδ hp
 · exact admission38_01_pos hδ hp
 · exact admission38_02_pos hδ hp
 · exact admission38_03_pos hδ hp
 · exact admission38_04_pos hδ hp
 · exact admission38_05_pos hδ hp
 · exact admission38_06_pos hδ hp
 · exact admission38_07_pos hδ hp
 · exact admission38_08_pos hδ hp
 · exact admission38_09_pos hδ hp
 · exact admission38_10_pos hδ hp
 · exact admission38_11_pos hδ hp
 · exact admission38_12_pos hδ hp
 · exact admission38_13_pos hδ hp
 · exact admission38_14_pos hδ hp
#print axioms admission38_all
end
end Record1252270103Finite
