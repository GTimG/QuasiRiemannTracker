/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission15_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1806072133773489/7495551818609:ℝ), (37570108221052480/157406588190789:ℝ)]]
theorem admission15_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission15_00_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission15_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_00_coefficients]
def admission15_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1318861265563904/7495551818609:ℝ), (27496086576841984/157406588190789:ℝ)]]
theorem admission15_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission15_01_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission15_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_01_coefficients]
def admission15_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(670752177520006/7495551818609:ℝ), (4663189858722048/52468862730263:ℝ)]]
theorem admission15_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission15_02_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission15_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_02_coefficients]
def admission15_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1833195455630552448256/157406588190789:ℝ), (4682536015499559596800/202379899102443:ℝ), (2325609772545992163328/202379899102443:ℝ)],
![(86713707355791522304/7495551818609:ℝ), (32558109822856976962048/1416659293717101:ℝ), (16169496332612379246592/1416659293717101:ℝ)]]
theorem admission15_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (493453867572399269/967106077844207616:ℝ) admission15_03_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission15_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_03_coefficients]
def admission15_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93383918142370982298/52468862730263:ℝ), (184702920801844117248/52468862730263:ℝ), (91323910193212588032/52468862730263:ℝ)],
![(94591158850446691908/52468862730263:ℝ), (187103906038368753152/52468862730263:ℝ), (92517686797045432320/52468862730263:ℝ)]]
theorem admission15_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8360953692005547/107456230871578624:ℝ) admission15_04_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission15_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_04_coefficients]
def admission15_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(337160133604411186243336/295137352857729375:ℝ), (674493844590962051306068/295137352857729375:ℝ), (112440148040588813825494/98379117619243125:ℝ)],
![(46378482929064850958866/42162478979675625:ℝ), (92793310877054512410556/42162478979675625:ℝ), (3094194686281987312946/2810831931978375:ℝ)]]
theorem admission15_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (23189241464532425479433/471579344624985047040000:ℝ) admission15_05_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission15_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_05_coefficients]
def admission15_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(112030428593831646225204580552210361344/168381341305161703654368558357:ℝ), (2323795617541033664043383039541549577216/1178669389136131925580579908499:ℝ), (2295095857011363157998075329036059475968/1178669389136131925580579908499:ℝ), (755513042767602242044543153359982428160/1178669389136131925580579908499:ℝ)],
![(5554057398441145509304898009261773600768/8250685723952923479064059359493:ℝ), (16459443463786998905187677564881080334336/8250685723952923479064059359493:ℝ), (16257724450401166030661052716835251027968/8250685723952923479064059359493:ℝ), (5352336998031825183964321961215944294400/8250685723952923479064059359493:ℝ)]]
theorem admission15_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (180128346149349747191558636035915/1609276605967198789059351768403968:ℝ) admission15_06_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission15_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_06_coefficients]
def admission15_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(424476645628359849397975114828064110/74330502017593905216793327563:ℝ), (842131653362976844832537929008449792/74330502017593905216793327563:ℝ), (15469206281172007988182997819719680/2752981556207181674696049169:ℝ)],
![(418117775589862600021158765897265420/74330502017593905216793327563:ℝ), (118495115826393044450792851002603008/10618643145370557888113332509:ℝ), (15235610884308672297086274698280960/2752981556207181674696049169:ℝ)]]
theorem admission15_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (697430918165985365162030396955/2819053113556154034888754349056:ℝ) admission15_07_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission15_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_07_coefficients]
def admission15_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10185119048337186819707016296584564054588727711628065699/1742121141037357153518593614757812500000000000000:ℝ), (6754855733369521430248211759589065350699865674454783353/348424228207471430703718722951562500000000000000:ℝ), (36988755488886608806814787495792057538696324952895247127/1742121141037357153518593614757812500000000000000:ℝ), (13399542611685195165428758986328284705209813354749396061/1742121141037357153518593614757812500000000000000:ℝ)],
![(717926303643343797988512575816022180216467549375601857/69684845641494286140743744590312500000000000000:ℝ), (56919515087905488224509592536147335190370678693881855379/1742121141037357153518593614757812500000000000000:ℝ), (11998138676606844874490247518661242314339476240494631787/348424228207471430703718722951562500000000000000:ℝ), (21019282279425318223685793797344636372197931867981349981/1742121141037357153518593614757812500000000000000:ℝ)]]
theorem admission15_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (10185119048337186819707016296584564054588727711628065699/9976471101900869984845347871065636864000000000000000000000:ℝ) admission15_08_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission15_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_08_coefficients]
def admission15_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(136697883727892054261404896943375005894567899/2177651426296696441898242018447265625:ℝ), (402847513077142975290588317972017956052328801/2177651426296696441898242018447265625:ℝ), (395618255267413487384755157668665491896262912/2177651426296696441898242018447265625:ℝ), (3699105179160831013149787486139546350452736/62218612179905612625664057669921875:ℝ)],
![(126048486091602317410330052347658524095585902/2177651426296696441898242018447265625:ℝ), (371084459287605598689851438676259482195411818/2177651426296696441898242018447265625:ℝ), (364039626387104434900404223762771277800679936/2177651426296696441898242018447265625:ℝ), (23800741781069699929561282660335610869858304/435530285259339288379648403689453125:ℝ)]]
theorem admission15_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1452681993473492427341386881123999686881/152228868132032317883992734849024000000000:ℝ) admission15_09_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission15_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_09_coefficients]
def admission15_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2301140113166355720890853510784/395273240434458984375:ℝ), (78878580292269586481924712953984/4611521138402021484375:ℝ), (77220143172280544651024243030528/4611521138402021484375:ℝ), (75564620581925637238478463107072/13834563415206064453125:ℝ)],
![(51532832017581097435644028584448/4611521138402021484375:ℝ), (64845554408613045938016378122752/1976366202172294921875:ℝ), (63437035106813506835046336636928/1976366202172294921875:ℝ), (16082101918672529842904643928064/1537173712800673828125:ℝ)],
![(10572833863111296637365435994624/1976366202172294921875:ℝ), (31019669242899190857184570825216/1976366202172294921875:ℝ), (6064404805037336405663854733312/395273240434458984375:ℝ), (9875192695117537808500138835968/1976366202172294921875:ℝ)]]
theorem admission15_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (75341741143169691532136069/29473709039061565440000000000:ℝ) admission15_10_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission15_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_10_coefficients]
def admission15_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(348380455624692225174078971863307666/74330502017593905216793327563:ℝ), (691172061687277147277677720797530624/74330502017593905216793327563:ℝ), (342804622601378680813186649027379200/74330502017593905216793327563:ℝ)],
![(343034060954494442552240780443178228/74330502017593905216793327563:ℝ), (97217682996786152645452238861351936/10618643145370557888113332509:ℝ), (337502629822049144783152692898856960/74330502017593905216793327563:ℝ)]]
theorem admission15_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (10299762872987339623509298489345/50742956044010772627997578283008:ℝ) admission15_11_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission15_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_11_coefficients]
def admission15_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission15_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission15_12_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission15_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_12_coefficients]
def admission15_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission15_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission15_13_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission15_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_13_coefficients]
def admission15_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission15_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission15_14_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission15_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission15_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission15_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission15_14_coefficients]
theorem admission15_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission15_00_pos hδ hp
 · exact admission15_01_pos hδ hp
 · exact admission15_02_pos hδ hp
 · exact admission15_03_pos hδ hp
 · exact admission15_04_pos hδ hp
 · exact admission15_05_pos hδ hp
 · exact admission15_06_pos hδ hp
 · exact admission15_07_pos hδ hp
 · exact admission15_08_pos hδ hp
 · exact admission15_09_pos hδ hp
 · exact admission15_10_pos hδ hp
 · exact admission15_11_pos hδ hp
 · exact admission15_12_pos hδ hp
 · exact admission15_13_pos hδ hp
 · exact admission15_14_pos hδ hp
#print axioms admission15_all
end
end Record1252270103Finite
