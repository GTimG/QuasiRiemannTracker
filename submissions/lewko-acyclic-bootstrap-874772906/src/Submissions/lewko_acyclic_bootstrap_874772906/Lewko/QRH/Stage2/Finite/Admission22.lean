/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission22_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission22_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission22_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission22_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_00_coefficients]
def admission22_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission22_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission22_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission22_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_01_coefficients]
def admission22_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission22_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission22_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission22_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_02_coefficients]
def admission22_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1199625117502700745728/52465400575843:ℝ),(64341190687402981784576/1416565815547761:ℝ),(31951881314830061649920/1416565815547761:ℝ)],
![(3586668769721121473792/157396201727529:ℝ),(64121566756388547816704/1416565815547761:ℝ),(31842118428898454552576/1416565815547761:ℝ)]]
theorem admission22_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1943488673638821689/3868169053655752704:ℝ) admission22_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission22_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_03_coefficients]
def admission22_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(192853155507477418456/52465400575843:ℝ),(381441798327335269376/52465400575843:ℝ),(188598778641175937024/52465400575843:ℝ)],
![(194060281881365561986/52465400575843:ℝ),(383842555781796304640/52465400575843:ℝ),(189792441797132746752/52465400575843:ℝ)]]
theorem admission22_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4316683471096251/53724570189663232:ℝ) admission22_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission22_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_04_coefficients]
def admission22_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(121092082627817380138213/59023575647823375:ℝ),(1212075885589796298910562/295117878239116875:ℝ),(202196023868598387961499/98372626079705625:ℝ)],
![(592950780338841419387951/295117878239116875:ℝ),(1187137454000014007098226/295117878239116875:ℝ),(7922122481396317528787/3934905043188225:ℝ)]]
theorem admission22_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (592950780338841419387951/13203350369811635896320000:ℝ) admission22_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission22_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_05_coefficients]
def admission22_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(11303990836579107850364524440428784791552/8249596917978249986997496465053:ℝ),(33499975826312536432866240690946031366144/8249596917978249986997496465053:ℝ),(33090033268807830074524669979211531026432/8249596917978249986997496465053:ℝ),(10894045433056967895364020928694284451840/8249596917978249986997496465053:ℝ)],
![(11368544115326935494298652196266841334784/8249596917978249986997496465053:ℝ),(33692810726653406447994663014879782888448/8249596917978249986997496465053:ℝ),(33282047594239402915429329225037055197184/8249596917978249986997496465053:ℝ),(10957778127889114081540654806424113643520/8249596917978249986997496465053:ℝ)]]
theorem admission22_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (649335708204327100239039714854615/5631724829339818657790290920142848:ℝ) admission22_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission22_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_06_coefficients]
def admission22_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(813598093097739894484318242659831720/74320692954759008891869337523:ℝ),(1614073313619014894206822264346860544/74320692954759008891869337523:ℝ),(800501311721262709525941684239564800/74320692954759008891869337523:ℝ)],
![(807240385989872057711191794700565150/74320692954759008891869337523:ℝ),(1601409791254416384128432429934810368/74320692954759008891869337523:ℝ),(794195393291948605030770152372469760/74320692954759008891869337523:ℝ)]]
theorem admission22_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (24236919961302142487511296153945/101472519447564300140365602164736:ℝ) admission22_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission22_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_07_coefficients]
def admission22_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(14764310584229482998433457950051099546286534327791071217/435472810281791067725796899548828125000000000000:ℝ),(9108598322971526089467002814217379325395156216115481859/87094562056358213545159379909765625000000000000:ℝ),(46792279533944289441248436477904306749768948408203792941/435472810281791067725796899548828125000000000000:ℝ),(16013571006344260123213818757919847379318687592917454863/435472810281791067725796899548828125000000000000:ℝ)],
![(33409729226471937956441936093629391171479854396373003937/870945620563582135451593799097656250000000000000:ℝ),(102657377406860497008754714542808854408914026060234379357/870945620563582135451593799097656250000000000000:ℝ),(52542156778096710002302006368244537923518272232394625453/435472810281791067725796899548828125000000000000:ℝ),(17918305103914814803629223071291749514123207103588937743/435472810281791067725796899548828125000000000000:ℝ)]]
theorem admission22_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (14764310584229482998433457950051099546286534327791071217/4987577275886680480499250077601103872000000000000000000000:ℝ) admission22_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission22_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_08_coefficients]
def admission22_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(213995048406788981599350371880951107921457268/2177364051408955338628984497744140625:ℝ),(629346105408658972714286432492019728047029052/2177364051408955338628984497744140625:ℝ),(616733679833452219246231783527160067662633984/2177364051408955338628984497744140625:ℝ),(8055309486040049753306634513645985804607488/87094562056358213545159379909765625:ℝ)],
![(203347211194382581294163454046120699266825031/2177364051408955338628984497744140625:ℝ),(597587706433841085014326318737937410358155709/2177364051408955338628984497744140625:ℝ),(585159679384352420707341112804151801910009088/2177364051408955338628984497744140625:ℝ),(38183859765216649205875101746671732487954432/435472810281791067725796899548828125:ℝ)]]
theorem admission22_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (4661115693996172998764050506185514219721/608835116685385800842193612988416000000000:ℝ) admission22_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission22_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_09_coefficients]
def admission22_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5509785725627898515454398298112/307414456499080078125:ℝ),(725794433729592090366337386149888/13833650542458603515625:ℝ),(707795231545462178581454682054656/13833650542458603515625:ℝ),(25549030536472280156729468813312/1537072282495400390625:ℝ)],
![(481944351745687328294886269805568/13833650542458603515625:ℝ),(52221430713415740791384541109248/512357427498466796875:ℝ),(50895493719058455524934456684544/512357427498466796875:ℝ),(89228858474345625220146798067712/2766730108491720703125:ℝ)],
![(233955244029165564697132417359232/13833650542458603515625:ℝ),(684038755149201607140354050651008/13833650542458603515625:ℝ),(133247693130694682213919343844864/2766730108491720703125:ℝ),(216155074649195181126375085932544/13833650542458603515625:ℝ)]]
theorem admission22_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (6596529377722020908397677183/3300837592452908974080000000000:ℝ) admission22_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission22_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_10_coefficients]
def admission22_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(222345994871692470549153872706307784/24773564318253002963956445841:ℝ),(1323344309313405572084481167921543168/74320692954759008891869337523:ℝ),(72925698854939081421067234911109120/8257854772751000987985481947:ℝ)],
![(220564174701829167453097818537591158/24773564318253002963956445841:ℝ),(1312697893020288029482984230271801856/74320692954759008891869337523:ℝ),(72336691908267154374487164941189120/8257854772751000987985481947:ℝ)]]
theorem admission22_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (4415081293229196433989695125805/22549448766125400031192356036608:ℝ) admission22_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission22_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_11_coefficients]
def admission22_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission22_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission22_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission22_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_12_coefficients]
def admission22_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission22_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission22_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission22_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_13_coefficients]
def admission22_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission22_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission22_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission22_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission22_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission22_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission22_14_coefficients]
theorem admission22_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission22_00_pos hδ hp
 · exact admission22_01_pos hδ hp
 · exact admission22_02_pos hδ hp
 · exact admission22_03_pos hδ hp
 · exact admission22_04_pos hδ hp
 · exact admission22_05_pos hδ hp
 · exact admission22_06_pos hδ hp
 · exact admission22_07_pos hδ hp
 · exact admission22_08_pos hδ hp
 · exact admission22_09_pos hδ hp
 · exact admission22_10_pos hδ hp
 · exact admission22_11_pos hδ hp
 · exact admission22_12_pos hδ hp
 · exact admission22_13_pos hδ hp
 · exact admission22_14_pos hδ hp
#print axioms admission22_all
end
end LewkoStage2Finite
