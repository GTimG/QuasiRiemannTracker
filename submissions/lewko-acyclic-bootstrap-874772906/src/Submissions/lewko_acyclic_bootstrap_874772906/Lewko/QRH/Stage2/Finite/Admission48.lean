/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission48_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission48_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission48_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission48_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_00_coefficients]
def admission48_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission48_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission48_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission48_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_01_coefficients]
def admission48_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission48_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission48_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission48_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_02_coefficients]
def admission48_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(602865096662458709760/52465400575843:ℝ),(32335337831750121311488/1416565815547761:ℝ),(16058262821863736147968/1416565815547761:ℝ)],
![(1796388707200395365888/157396201727529:ℝ),(32115713900735687343616/1416565815547761:ℝ),(15948499935932129050624/1416565815547761:ℝ)]]
theorem admission48_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (486709592771366243/967042263413938176:ℝ) admission48_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission48_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_03_coefficients]
def admission48_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(95816282957828970562/52465400575843:ℝ),(189513804865163409152/52465400575843:ℝ),(93702557742609563648/52465400575843:ℝ)],
![(97023409331717114092/52465400575843:ℝ),(191914562319624444416/52465400575843:ℝ),(94896220898566373376/52465400575843:ℝ)]]
theorem admission48_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8578725379267233/107449140379326464:ℝ) admission48_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission48_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_04_coefficients]
def admission48_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(312112431169727561322868/295117878239116875:ℝ),(124944311596911540123212/59023575647823375:ℝ),(104198504367969186947314/98372626079705625:ℝ)],
![(299602798369482080019754/295117878239116875:ℝ),(599783126394775408803724/295117878239116875:ℝ),(20011108506855747441098/19674525215941125:ℝ)]]
theorem admission48_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (149801399184741040009877/3300837592452908974080000:ℝ) admission48_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission48_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_05_coefficients]
def admission48_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5619308486957799374336451403241250448384/8249596917978249986997496465053:ℝ),(16652752055063617480569648838134007948288/8249596917978249986997496465053:ℝ),(16448601351220561475622626560374985129984/8249596917978249986997496465053:ℝ),(5415156369112410854593693525482227630080/8249596917978249986997496465053:ℝ)],
![(5683861765705627018270579159079306991616/8249596917978249986997496465053:ℝ),(16845586955404487495698071162067759470592/8249596917978249986997496465053:ℝ),(16640615676652134316527285806200509300736/8249596917978249986997496465053:ℝ),(5478889063944557040770327403212056821760/8249596917978249986997496465053:ℝ)]]
theorem admission48_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1291073887136557305954383260126645/11263449658679637315580581840285696:ℝ) admission48_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission48_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_06_coefficients]
def admission48_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(411580274049409257891492686322408670/74320692954759008891869337523:ℝ),(816547219959448904934215200651932928/74320692954759008891869337523:ℝ),(404980094682616933134349491020103680/74320692954759008891869337523:ℝ)],
![(405222566941541421118366238363142100/74320692954759008891869337523:ℝ),(803883697594850394855825366239882752/74320692954759008891869337523:ℝ),(398674176253302828639177959153008640/74320692954759008891869337523:ℝ)]]
theorem admission48_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (6083285160115094431139800402115/25368129861891075035091400541184:ℝ) admission48_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission48_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_07_coefficients]
def admission48_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(25647513110445994037291895706575007013666282914791280931/1741891241127164270903187598195312500000000000000:ℝ),(15917303809892740909045143184297049436149398317073656313/348378248225432854180637519639062500000000000000:ℝ),(82228374265317812517007653975029265041260958742016840343/1741891241127164270903187598195312500000000000000:ℝ),(28289313680419273484341040455879278298326082883939839709/1741891241127164270903187598195312500000000000000:ℝ)],
![(33409729226471937956441936093629391171479854396373003937/1741891241127164270903187598195312500000000000000:ℝ),(102729307403754176773395088722755369490671919383527403099/1741891241127164270903187598195312500000000000000:ℝ),(105227883241927494761221933536390189736258254038780170391/1741891241127164270903187598195312500000000000000:ℝ),(35908250070701492206002657709366886837544160926625771229/1741891241127164270903187598195312500000000000000:ℝ)]]
theorem admission48_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (25647513110445994037291895706575007013666282914791280931/9975154551773360960998500155202207744000000000000000000000:ℝ) admission48_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission48_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_08_coefficients]
def admission48_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(115029501834571391654039515248358216946507111/2177364051408955338628984497744140625:ℝ),(338583872935458875704635564419248944705826589/2177364051408955338628984497744140625:ℝ),(332093261622137409809538796905745062577380608/2177364051408955338628984497744140625:ℝ),(21707789463837824053760139400283611912830976/435472810281791067725796899548828125:ℝ)],
![(104381664622164991348852597413527808291874874/2177364051408955338628984497744140625:ℝ),(306825473960640988004675450665166627016953246/2177364051408955338628984497744140625:ℝ),(300519261173037611270648126182736796824755712/2177364051408955338628984497744140625:ℝ),(19615101798854224493102068578725415377747968/435472810281791067725796899548828125:ℝ)]]
theorem admission48_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1197210803152723662909061802900721153427/152208779171346450210548403247104000000000:ℝ) admission48_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission48_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_09_coefficients]
def admission48_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22393748702692459803012357887104/4611216847486201171875:ℝ),(196938462080300555806967954543488/13833650542458603515625:ℝ),(38468083188350022302290591620608/2766730108491720703125:ℝ),(20861076477594915871174025740288/4611216847486201171875:ℝ)],
![(25498362112455130114936243374592/2766730108491720703125:ℝ),(124454228609661376550890724736512/4611216847486201171875:ℝ),(121421343992204204357474752600064/4611216847486201171875:ℝ),(118393216011747883994433300463616/13833650542458603515625:ℝ)],
![(60261814390931940763338214180352/13833650542458603515625:ℝ),(176278783365252269985013046517248/13833650542458603515625:ℝ),(34355796563843958407758474098688/2766730108491720703125:ℝ),(55762043684680712817117538156544/13833650542458603515625:ℝ)]]
theorem admission48_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (425430631139226629769268327/206302349528306810880000000000:ℝ) admission48_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission48_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_10_coefficients]
def admission48_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(112513062395705593085697938044430518/24773564318253002963956445841:ℝ),(669668039689796656934127206745872896/74320692954759008891869337523:ℝ),(36904604637473485995468669932994560/8257854772751000987985481947:ℝ)],
![(110731242225842289989641883875713892/24773564318253002963956445841:ℝ),(659021623396679114332630269096131584/74320692954759008891869337523:ℝ),(12105199230267186316296199987691520/2752618257583666995995160649:ℝ)]]
theorem admission48_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1108264089685106169094500731295/5637362191531350007798089009152:ℝ) admission48_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission48_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_11_coefficients]
def admission48_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission48_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission48_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission48_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_12_coefficients]
def admission48_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission48_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission48_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission48_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_13_coefficients]
def admission48_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission48_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission48_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission48_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_14_coefficients]
theorem admission48_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission48_00_pos hδ hp
 · exact admission48_01_pos hδ hp
 · exact admission48_02_pos hδ hp
 · exact admission48_03_pos hδ hp
 · exact admission48_04_pos hδ hp
 · exact admission48_05_pos hδ hp
 · exact admission48_06_pos hδ hp
 · exact admission48_07_pos hδ hp
 · exact admission48_08_pos hδ hp
 · exact admission48_09_pos hδ hp
 · exact admission48_10_pos hδ hp
 · exact admission48_11_pos hδ hp
 · exact admission48_12_pos hδ hp
 · exact admission48_13_pos hδ hp
 · exact admission48_14_pos hδ hp
#print axioms admission48_all
end
end LewkoStage2Finite
