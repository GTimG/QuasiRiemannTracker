/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission42_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1202494501891624489/157396201727529:ℝ),(1202137105689896960/157396201727529:ℝ)]]
theorem admission42_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission42_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission42_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_00_coefficients]
def admission42_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(879989684551917568/157396201727529:ℝ),(879789684551917568/157396201727529:ℝ)]]
theorem admission42_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission42_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission42_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_01_coefficients]
def admission42_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(149239969878519210/52465400575843:ℝ),(149207894494601216/52465400575843:ℝ)]]
theorem admission42_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission42_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission42_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_02_coefficients]
def admission42_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(525803107082856068171137024/1416565815547761:ℝ),(116820229960991129232834560/157396201727529:ℝ),(525578971573264094924374016/1416565815547761:ℝ)],
![(525690706748369263470714880/1416565815547761:ℝ),(116795252457493265858600960/157396201727529:ℝ),(525466574378070129256693760/1416565815547761:ℝ)]]
theorem admission42_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (31320248507146246985/61890704858492043264:ℝ) admission42_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission42_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_03_coefficients]
def admission42_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3060373163891886174148344/52465400575843:ℝ),(6118595304779497498509312/52465400575843:ℝ),(3058222301392832450002944/52465400575843:ℝ)],
![(3061595904792222848533666/52465400575843:ℝ),(6121040356719458562138112/52465400575843:ℝ),(3059444612464532223164416/52465400575843:ℝ)]]
theorem admission42_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68356595219511519/859593123034611712:ℝ) admission42_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission42_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_04_coefficients]
def admission42_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1129297669933974497548256073/32790875359901875:ℝ),(4065557607861020975752600042/59023575647823375:ℝ),(10164108575994815569092580553/295117878239116875:ℝ)],
![(225576650431714609217803123/6558175071980375:ℝ),(4060466220132021257712333802/59023575647823375:ℝ),(406055255889668740299427889/11804715129564675:ℝ)]]
theorem admission42_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (676729951295143827653409369/14421579497266256168353792000:ℝ) admission42_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission42_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_05_coefficients]
def admission42_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5663959636383358276907625569166298924009521152/8249596917978249986997496465053:ℝ),(209694287753125222538187238387416781260980224/101846875530595678851820944013:ℝ),(16978596747120670357620420922259202248038940672/8249596917978249986997496465053:ℝ),(5657319075455817661980077393121541889909063680/8249596917978249986997496465053:ℝ)],
![(5666048865297031800238235961772784378540687360/8249596917978249986997496465053:ℝ),(629314968838372024166737659180099486075944960/305540626591787036555462832039:ℝ),(16984862761784167233811480490770894678371860480/8249596917978249986997496465053:ℝ),(5659407468400077428208713332026992932862033920/8249596917978249986997496465053:ℝ)]]
theorem admission42_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10290603450731973975016585233100235/90107597269437098524644654722285568:ℝ) admission42_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission42_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_06_coefficients]
def admission42_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13241651430842565962498126821525900334216/74320692954759008891869337523:ℝ),(26476523817984486449148954649634793684992/74320692954759008891869337523:ℝ),(13234872809966094628429558054271278120960/74320692954759008891869337523:ℝ)],
![(13235192516331584686429063768086889178750/74320692954759008891869337523:ℝ),(26463607643105060113508025855709291520000/74320692954759008891869337523:ℝ),(13228415549494476985426502405639372800000/74320692954759008891869337523:ℝ)]]
theorem admission42_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (394237504884436040682390403915625/1623560311161028802245849634635776:ℝ) admission42_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission42_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_07_coefficients]
def admission42_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7447091638836829059846429131988242531175129244530336514051/504019456344665587645598263366699218750000000:ℝ),(201304342059760809056988247376691228364451302014853297949933/4536175107101990288810384370300292968750000000:ℝ),(24184464337928962199802846812928308556200908732924019344661/544341012852238834657246124436035156250000000:ℝ),(201770056503928927066455946141286401213316411442334285021103/13608525321305970866431153110900878906250000000:ℝ)],
![(15038745459840624851843728381369045029248119397673561141863/1008038912689331175291196526733398437500000000:ℝ),(406511101779202906004963144294617527207563516735250100259311/9072350214203980577620768740600585937500000000:ℝ),(610464093194406903181941127796293382055760946749232923307789/13608525321305970866431153110900878906250000000:ℝ),(203720504219841175059201320158179228999356239421261883490223/13608525321305970866431153110900878906250000000:ℝ)]]
theorem admission42_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7447091638836829059846429131988242531175129244530336514051/3026535781041754555277767158200610586624000000000000000000000:ℝ) admission42_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission42_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_08_coefficients]
def admission42_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(112141568700370164258375244124533217122411126591576/2177364051408955338628984497744140625:ℝ),(22413912995417050389257691063731550318133190735488/145157603427263689241932299849609375:ℝ),(335992698744571322671410381799713848081724986097664/2177364051408955338628984497744140625:ℝ),(22385114503099205947775551776047284232769853456384/435472810281791067725796899548828125:ℝ)],
![(22359702927319103103700508660059798726376510980802/435472810281791067725796899548828125:ℝ),(22345314725299594190721163548870020722725034624096/145157603427263689241932299849609375:ℝ),(66992782561910570742180722150100067351089834622976/435472810281791067725796899548828125:ℝ),(4463308262738604671474381622273293049741650690048/87094562056358213545159379909765625:ℝ)]]
theorem admission42_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (16627118970225023744532397472386408782533/1948272373393234562695019561562931200000000:ℝ) admission42_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission42_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_09_coefficients]
def admission42_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2064610366932437621332882246066549489664/13833650542458603515625:ℝ),(2062984530774796349145656812716140331008/4611216847486201171875:ℝ),(2061358777019392936774996592247651172352/4611216847486201171875:ℝ),(2059733105696158028345901584661082013696/13833650542458603515625:ℝ)],
![(824435633084773671459842042754806349824/2766730108491720703125:ℝ),(91531723170007479086107616840384217088/102471485499693359375:ℝ),(493881250146851565338932429163809734656/553346021698344140625:ℝ),(91387262026756023668566503764831240192/307414456499080078125:ℝ)],
![(82302649066989799440213523694072705024/553346021698344140625:ℝ),(82237657613340981399757879199720722432/184448673899448046875:ℝ),(49303601670487913610023544327285243904/110669204339668828125:ℝ),(82107684580604127611370107731336757248/553346021698344140625:ℝ)]]
theorem admission42_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (76468740199323862429121609527/33800576946717787894579200000000:ℝ) admission42_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission42_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_10_coefficients]
def admission42_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10859298330090286176362176915657974475640/74320692954759008891869337523:ℝ),(21713053103833723238037634970833147592704/74320692954759008891869337523:ℝ),(1205972797637074895973178422293776302080/8257854772751000987985481947:ℝ)],
![(10853868624642924445606371317258488265090/74320692954759008891869337523:ℝ),(21702195110472569547330653339445464350720/74320692954759008891869337523:ℝ),(401789884841227614225826810214859407360/2752618257583666995995160649:ℝ)]]
theorem admission42_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (71845630080919435183851744571005/360791180258006400499077696585728:ℝ) admission42_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission42_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_11_coefficients]
def admission42_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission42_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission42_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission42_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_12_coefficients]
def admission42_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission42_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission42_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission42_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_13_coefficients]
def admission42_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission42_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission42_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission42_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_14_coefficients]
theorem admission42_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission42_00_pos hδ hp
 · exact admission42_01_pos hδ hp
 · exact admission42_02_pos hδ hp
 · exact admission42_03_pos hδ hp
 · exact admission42_04_pos hδ hp
 · exact admission42_05_pos hδ hp
 · exact admission42_06_pos hδ hp
 · exact admission42_07_pos hδ hp
 · exact admission42_08_pos hδ hp
 · exact admission42_09_pos hδ hp
 · exact admission42_10_pos hδ hp
 · exact admission42_11_pos hδ hp
 · exact admission42_12_pos hδ hp
 · exact admission42_13_pos hδ hp
 · exact admission42_14_pos hδ hp
#print axioms admission42_all
end
end LewkoStage2Finite
