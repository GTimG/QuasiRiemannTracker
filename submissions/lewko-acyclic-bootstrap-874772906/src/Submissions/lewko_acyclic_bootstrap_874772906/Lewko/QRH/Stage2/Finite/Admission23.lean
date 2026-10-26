/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission23_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission23_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission23_00_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission23_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_00_coefficients]
def admission23_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission23_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission23_01_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission23_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_01_coefficients]
def admission23_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission23_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission23_02_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission23_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_02_coefficients]
def admission23_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3592766707828432979200/157396201727529:ℝ),(64231329642320154914048/1416565815547761:ℝ),(31896999871864258101248/1416565815547761:ℝ)],
![(1193520041680484071936/52465400575843:ℝ),(64011705711305720946176/1416565815547761:ℝ),(31787236985932651003904/1416565815547761:ℝ)]]
theorem admission23_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (970069488096089203/1934084526827876352:ℝ) admission23_03_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission23_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_03_coefficients]
def admission23_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(193463450303387157122/52465400575843:ℝ),(382648892625839494912/52465400575843:ℝ),(189195610219154341888/52465400575843:ℝ)],
![(194670576677275300652/52465400575843:ℝ),(385049650080300530176/52465400575843:ℝ),(190389273375111151616/52465400575843:ℝ)]]
theorem admission23_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (17321375447310273/214898280758652928:ℝ) admission23_04_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission23_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_04_coefficients]
def admission23_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(599205596738964160039508/295117878239116875:ℝ),(239929417360051897680268/59023575647823375:ℝ),(200138000834948851770194/98372626079705625:ℝ)],
![(586695963938718678736394/295117878239116875:ℝ),(1174708655210477196589004/295117878239116875:ℝ),(39199007800251680405674/19674525215941125:ℝ)]]
theorem admission23_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (293347981969359339368197/6601675184905817948160000:ℝ) admission23_05_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission23_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_05_coefficients]
def admission23_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(11336677767910862401210335257401926738944/8249596917978249986997496465053:ℝ),(33597211684405187168729712198285039100928/8249596917978249986997496465053:ℝ),(33186448551991183636164378408442311409664/8249596917978249986997496465053:ℝ),(10925911780473040988452337867559199047680/8249596917978249986997496465053:ℝ)],
![(11401231046658690045144463013239983282176/8249596917978249986997496465053:ℝ),(33790046584746057183858134522218790623232/8249596917978249986997496465053:ℝ),(33378462877422756477069037654267835580416/8249596917978249986997496465053:ℝ),(10989644475305187174628971745289028239360/8249596917978249986997496465053:ℝ)]]
theorem admission23_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2604940362089405295479855029001045/22526899317359274631161163680571392:ℝ) admission23_06_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission23_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_06_coefficients]
def admission23_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(810393345204529109958777560634112670/74320692954759008891869337523:ℝ),(1607715709683730488623603961801905408/74320692954759008891869337523:ℝ),(797348352506605657278355918306017280/74320692954759008891869337523:ℝ)],
![(804035638096661273185651112674846100/74320692954759008891869337523:ℝ),(1595052187319131978545214127389855232/74320692954759008891869337523:ℝ),(791042434077291552783184386438922240/74320692954759008891869337523:ℝ)]]
theorem admission23_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12070349641071953625231695349715/50736259723782150070182801082368:ℝ) admission23_07_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission23_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_07_coefficients]
def admission23_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(62938350394930903953308851993731590264052923051955146371/1741891241127164270903187598195312500000000000000:ℝ),(38734286127936415627756873701007226516221538979619234841/348378248225432854180637519639062500000000000000:ℝ),(198525302938347924130482964892396575457352731707205917303/1741891241127164270903187598195312500000000000000:ℝ),(67792112357646287254941872091639805977586042673564889469/1741891241127164270903187598195312500000000000000:ℝ)],
![(70700566510956847872458892380785974421866494533536869377/1741891241127164270903187598195312500000000000000:ℝ),(216814218993972550366953741306306254891032622696255295739/1741891241127164270903187598195312500000000000000:ℝ),(221524811914957606374697244453757500152350027003969247351/1741891241127164270903187598195312500000000000000:ℝ),(202174393426081785460062974115623095219313996558313193/4669949708115721905906669164062500000000000000:ℝ)]]
theorem admission23_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (62938350394930903953308851993731590264052923051955146371/19950309103546721921997000310404415488000000000000000000000:ℝ) admission23_08_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission23_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_08_coefficients]
def admission23_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(208578930356841580195808631100016190604532551/2177364051408955338628984497744140625:ℝ),(613282863921218081719261849899623884371278269/2177364051408955338628984497744140625:ℝ),(600854836871729417412276643965838275923131648/2177364051408955338628984497744140625:ℝ),(39230203597708448986204137157450830755495936/435472810281791067725796899548828125:ℝ)],
![(197931093144435179890621713265185781949900314/2177364051408955338628984497744140625:ℝ),(581524464946400194019301736145541566682404926/2177364051408955338628984497744140625:ℝ),(569280836422629618873385973242830010170506752/2177364051408955338628984497744140625:ℝ),(37137515932724849425546066335892634220412928/435472810281791067725796899548828125:ℝ)]]
theorem admission23_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2266694087690725672945926900384071912867/304417558342692900421096806494208000000000:ℝ) admission23_09_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission23_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_09_coefficients]
def admission23_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(240896287012975658403021169139072/13833650542458603515625:ℝ),(704861884100631888258020305990528/13833650542458603515625:ℝ),(137412318920980738437452594912768/2766730108491720703125:ℝ),(223096117633005274832263837712384/13833650542458603515625:ℝ)],
![(93551742067719023581084180638208/2766730108491720703125:ℝ),(1367822649237441989429366103333376/13833650542458603515625:ℝ),(1332421790102175907340489057093632/13833650542458603515625:ℝ),(432358092192672785816543856951296/13833650542458603515625:ℝ)],
![(75604557754117709700031268340224/4611216847486201171875:ℝ),(220938441584459599103551541398016/4611216847486201171875:ℝ),(43014370818775300375403143555072/922243369497240234375:ℝ),(69738010555128362473495444717568/4611216847486201171875:ℝ)]]
theorem admission23_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (532058796349551105297053869/275069799371075747840000000000:ℝ) admission23_10_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission23_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_10_coefficients]
def admission23_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(221447685121837058022967923492471158/24773564318253002963956445841:ℝ),(1317998955540335372902204860001081856/74320692954759008891869337523:ℝ),(24210398460534372632592399975383040/2752618257583666995995160649:ℝ)],
![(219665864951973754926911869323754532/24773564318253002963956445841:ℝ),(1307352539247217830300707922351340544/74320692954759008891869337523:ℝ),(72042188434931190851197129956229120/8257854772751000987985481947:ℝ)]]
theorem admission23_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2198553113858984095800693663215/11274724383062700015596178018304:ℝ) admission23_11_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission23_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_11_coefficients]
def admission23_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission23_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission23_12_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission23_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_12_coefficients]
def admission23_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission23_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission23_13_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission23_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_13_coefficients]
def admission23_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission23_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission23_14_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission23_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_14_coefficients]
theorem admission23_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission23_00_pos hδ hp
 · exact admission23_01_pos hδ hp
 · exact admission23_02_pos hδ hp
 · exact admission23_03_pos hδ hp
 · exact admission23_04_pos hδ hp
 · exact admission23_05_pos hδ hp
 · exact admission23_06_pos hδ hp
 · exact admission23_07_pos hδ hp
 · exact admission23_08_pos hδ hp
 · exact admission23_09_pos hδ hp
 · exact admission23_10_pos hδ hp
 · exact admission23_11_pos hδ hp
 · exact admission23_12_pos hδ hp
 · exact admission23_13_pos hδ hp
 · exact admission23_14_pos hδ hp
#print axioms admission23_all
end
end LewkoStage2Finite
