/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission19_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3249977881151303/52468862730263:ℝ), (9392527055263120/157406588190789:ℝ)]]
theorem admission19_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission19_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission19_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_00_coefficients]
def admission19_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2358007214736832/52468862730263:ℝ), (6874021644210496/157406588190789:ℝ)]]
theorem admission19_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission19_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission19_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_01_coefficients]
def admission19_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1197872848598506/52468862730263:ℝ), (1165797464680512/52468862730263:ℝ)]]
theorem admission19_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission19_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission19_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_02_coefficients]
def admission19_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(89372108107210164800/472219764572367:ℝ), (522409693193848387264/1416659293717101:ℝ), (36337652696031127552/202379899102443:ℝ)],
![(12439658848372881920/67459966367481:ℝ), (508663649987450544640/1416659293717101:ℝ), (247502814171620024320/1416659293717101:ℝ)]]
theorem admission19_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (30212745870559085/60444129865262976:ℝ) admission19_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission19_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_03_coefficients]
def admission19_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(226732636752688170/7495551818609:ℝ), (3040792753217294400/52468862730263:ℝ), (1454915235921278976/52468862730263:ℝ)],
![(1665129577607024784/52468862730263:ℝ), (3193372835911136768/52468862730263:ℝ), (1529526273660831744/52468862730263:ℝ)]]
theorem admission19_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131223490119061/26864057717894656:ℝ) admission19_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission19_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_04_coefficients]
def admission19_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(210601070916923861278/11805494114309175:ℝ), (10561131835188061883932/295137352857729375:ℝ), (1764241104139318472744/98379117619243125:ℝ)],
![(893579770137493533032/59027470571545875:ℝ), (1797443099120422176464/59027470571545875:ℝ), (301056545568872971144/19675823523848625:ℝ)]]
theorem admission19_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (111697471267186691629/2578949540917886976000:ℝ) admission19_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission19_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_05_coefficients]
def admission19_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(24257468943833693710145713468413269248/8250685723952923479064059359493:ℝ), (69482915976480169093299471073236280576/8250685723952923479064059359493:ℝ), (66257868008095763074921168171479175168/8250685723952923479064059359493:ℝ), (21032069716254413784338210566656163840/8250685723952923479064059359493:ℝ)],
![(25305610284218674499285777122770319360/8250685723952923479064059359493:ℝ), (72574123602412890008508340624009984000/8250685723952923479064059359493:ℝ), (69296969841830298884693397313146880000/8250685723952923479064059359493:ℝ), (22028096257795187060158833811907215360/8250685723952923479064059359493:ℝ)]]
theorem admission19_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320923915348120327519809121195315/2816234060442597880853865594706944:ℝ) admission19_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission19_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_06_coefficients]
def admission19_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6944349528494423561864387806517458/74330502017593905216793327563:ℝ), (13467107845793393889864484188261824/74330502017593905216793327563:ℝ), (241706348143312624815359340933120/2752981556207181674696049169:ℝ)],
![(933875904829201947751076494505680/10618643145370557888113332509:ℝ), (1809400084925469191853116113610240/10618643145370557888113332509:ℝ), (32443805119907734874544877977600/393283079458168810670864167:ℝ)]]
theorem admission19_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (5940638144514355750954262325/25170117085322803882935306688:ℝ) admission19_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission19_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_07_coefficients]
def admission19_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7873804525361082004576397702021532571275183605815807/199099558975697960402124984543750000000000000000:ℝ), (1001876579772943756580175342752348860508214531379563683/6968484564149428614074374459031250000000000000000:ℝ), (1176450201339888005335397448611109601250428188442352873/6968484564149428614074374459031250000000000000000:ℝ), (90020495395106023342674215198230221253457766653268487/1393696912829885722814874891806250000000000000000:ℝ)],
![(157615527744060906450206315209088653776470224579807927/1393696912829885722814874891806250000000000000000:ℝ), (100100673956834365688111207130928787436817218787982273/278739382565977144562974978361250000000000000000:ℝ), (528166222354594535294985578358590059363975117428771349/1393696912829885722814874891806250000000000000000:ℝ), (185267241241857561570887150335934617090809248068667911/1393696912829885722814874891806250000000000000000:ℝ)]]
theorem admission19_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7873804525361082004576397702021532571275183605815807/4453781741920031243234530299582873600000000000000000000:ℝ) admission19_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission19_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_08_coefficients]
def admission19_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(488587141681478725752458530230047520272779/1742121141037357153518593614757812500:ℝ), (6905205692306324037255200087239477691606879/8710605705186785767592968073789062500:ℝ), (1621290422735877499345030153692940402505456/2177651426296696441898242018447265625:ℝ), (14449629606096996145116357367732602931456/62218612179905612625664057669921875:ℝ)],
![(87111620878809824768497591041649493515522/435530285259339288379648403689453125:ℝ), (242522717841076880227936034839354268443954/435530285259339288379648403689453125:ℝ), (223852571316828819789386039473831064459392/435530285259339288379648403689453125:ℝ), (13688873720235428470390307369071851656192/87106057051867857675929680737890625:ℝ)]]
theorem admission19_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (13368040742417410615615534540109230133/1902860851650403973549909185612800000000:ℝ) admission19_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission19_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_09_coefficients]
def admission19_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18584861772314978615865878848/2766912683041212890625:ℝ), (4130605721130735355624305376/219596244685810546875:ℝ), (26866440992819492872147977184/1537173712800673828125:ℝ), (74495935436026501524329950208/13834563415206064453125:ℝ)],
![(10549881695093486481931236352/922304227680404296875:ℝ), (87838471331258179502519012864/2766912683041212890625:ℝ), (16153851718823803817699379712/553382536608242578125:ℝ), (8193726074380433010590531584/922304227680404296875:ℝ)],
![(2580951392917299947038314496/553382536608242578125:ℝ), (1009230909667975593050896384/79054648086891796875:ℝ), (6390019314255499769597605888/553382536608242578125:ℝ), (1906430839496970565279645696/553382536608242578125:ℝ)]]
theorem admission19_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (58179652084258134926747/32236869261473587200000000:ℝ) admission19_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission19_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_10_coefficients]
def admission19_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5698866997478474492893693154509934/74330502017593905216793327563:ℝ), (11052015145741506622472833607712128/74330502017593905216793327563:ℝ), (5356322228146541887706041391052800/74330502017593905216793327563:ℝ)],
![(765187417319769560542205426876720/10618643145370557888113332509:ℝ), (1482598894363794706265364994841600/10618643145370557888113332509:ℝ), (102549952641600936445488145571840/1516949020767222555444761787:ℝ)]]
theorem admission19_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (12518304765820426812193377145/64723158219401495698976502912:ℝ) admission19_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission19_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_11_coefficients]
def admission19_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission19_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission19_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission19_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_12_coefficients]
def admission19_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission19_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission19_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission19_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_13_coefficients]
def admission19_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission19_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission19_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission19_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission19_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission19_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission19_14_coefficients]
theorem admission19_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission19_00_pos hδ hp
 · exact admission19_01_pos hδ hp
 · exact admission19_02_pos hδ hp
 · exact admission19_03_pos hδ hp
 · exact admission19_04_pos hδ hp
 · exact admission19_05_pos hδ hp
 · exact admission19_06_pos hδ hp
 · exact admission19_07_pos hδ hp
 · exact admission19_08_pos hδ hp
 · exact admission19_09_pos hδ hp
 · exact admission19_10_pos hδ hp
 · exact admission19_11_pos hδ hp
 · exact admission19_12_pos hδ hp
 · exact admission19_13_pos hδ hp
 · exact admission19_14_pos hδ hp
#print axioms admission19_all
end
end Record1252270103Finite
