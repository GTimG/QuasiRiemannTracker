/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission41_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(200475316348892003/52465400575843:ℝ),(601068552844948480/157396201727529:ℝ)]]
theorem admission41_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission41_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission41_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_00_coefficients]
def admission41_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(146698280758652928/52465400575843:ℝ),(439894842275958784/157396201727529:ℝ)]]
theorem admission41_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission41_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission41_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_01_coefficients]
def admission41_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74636022631218602/52465400575843:ℝ),(74603947247300608/52465400575843:ℝ)]]
theorem admission41_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission41_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission41_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_02_coefficients]
def admission41_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21920144133518542677155840/472188605182587:ℝ),(131464824168313262751244288/1416565815547761:ℝ),(65704396271357634719776768/1416565815547761:ℝ)],
![(21910777177670239032725504/472188605182587:ℝ),(131408624000169860401033216/1416565815547761:ℝ),(65676296972559143302856704/1416565815547761:ℝ)]]
theorem admission41_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15658449404849801851/30945352429246021632:ℝ) admission41_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission41_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_03_coefficients]
def admission41_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(382815543425172768697212/52465400575843:ℝ),(765093250846666262126592/52465400575843:ℝ),(382277787674104056250368/52465400575843:ℝ)],
![(383121336123453854558502/52465400575843:ℝ),(765704621280796907360256/52465400575843:ℝ),(382583365442028999540736/52465400575843:ℝ)]]
theorem admission41_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68356595219511519/859593123034611712:ℝ) admission41_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission41_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_04_coefficients]
def admission41_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1271228910449371837848668383/295117878239116875:ℝ),(508513106594878814457798398/59023575647823375:ℝ),(423778801857587606190755369/98372626079705625:ℝ)],
![(1268045825104983804414449029/295117878239116875:ℝ),(2536200653028443307991768054/295117878239116875:ℝ),(16908728145126514042273937/3934905043188225:ℝ)]]
theorem admission41_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1268045825104983804414449029/27040461557374230315663360000:ℝ) admission41_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission41_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_05_coefficients]
def admission41_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(354412642364988572884318985450263554355462144/8249596917978249986997496465053:ℝ),(1062407466868583978614450857990678362883063808/8249596917978249986997496465053:ℝ),(1061577266742117983081288104072111176646918144/8249596917978249986997496465053:ℝ),(353582442215988603873754837070096368119316480/8249596917978249986997496465053:ℝ)],
![(354673900510053031029739533580527315145179136/8249596917978249986997496465053:ℝ),(1063191032207383766309034795065339709779525632/8249596917978249986997496465053:ℝ),(1062360623053894789793314519110490143122784256/8249596917978249986997496465053:ℝ),(353843491334021074652334329433277748488437760/8249596917978249986997496465053:ℝ)]]
theorem admission41_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10290603450731973975016585233100235/90107597269437098524644654722285568:ℝ) admission41_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission41_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_06_coefficients]
def admission41_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1656457440950399300203210483177655593540/74320692954759008891869337523:ℝ),(3311219909563550160555231104919867056128/74320692954759008891869337523:ℝ),(1654762680025237931241385734823403847680/74320692954759008891869337523:ℝ)],
![(1654842298761226781203847914543419190330/74320692954759008891869337523:ℝ),(3307990452359645814236294532273068634112/74320692954759008891869337523:ℝ),(1653148364907333520490621822665427517440/74320692954759008891869337523:ℝ)]]
theorem admission41_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (197070642102638902722671249230555/811780155580514401122924817317888:ℝ) admission41_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission41_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_07_coefficients]
def admission41_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(50180540489092366972813713132247152662358725930812359965893/54434101285223883465724612443603515625000000000:ℝ),(30178188865634751003836916387770245073507737142502471702191/10886820257044776693144922488720703125000000000:ℝ),(151240246065334019741142676081659509311744239989101762554289/54434101285223883465724612443603515625000000000:ℝ),(50529842199038460947763670043995084726402499330350982759227/54434101285223883465724612443603515625000000000:ℝ)],
![(12789226558822857756624505328094858424144697828986611371839/13608525321305970866431153110900878906250000000:ℝ),(76909449694360147153761338320862171090552354472634694955221/27217050642611941732862306221801757812500000000:ℝ),(154167059237648495938894572529405935783422726446842804541873/54434101285223883465724612443603515625000000000:ℝ),(51505066056994584944136357052441498619422413319814781993787/54434101285223883465724612443603515625000000000:ℝ)]]
theorem admission41_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (50180540489092366972813713132247152662358725930812359965893/20429116522031843248124928317854121459712000000000000000000000:ℝ) admission41_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission41_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_08_coefficients]
def admission41_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7033064239068772674468287690829127521940767095756/2177364051408955338628984497744140625:ℝ),(21072187575860761957155033796928314539568831351904/2177364051408955338628984497744140625:ℝ),(21045186178950057847138425902739035940772760649728/2177364051408955338628984497744140625:ℝ),(1401212568612643577686085850524230857800040841216/435472810281791067725796899548828125:ℝ)],
![(6990158960799292302495127756178510030442913001774/2177364051408955338628984497744140625:ℝ),(20943518787352482591377631088797062642030066996336/2177364051408955338628984497744140625:ℝ),(20916564425332032964018565011712193704319307415552/2177364051408955338628984497744140625:ℝ),(1392640919936870753885630392439128484792340840448/435472810281791067725796899548828125:ℝ)]]
theorem admission41_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503933666255198534894895328257336759339/4870680933483086406737548903907328000000000:ℝ) admission41_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission41_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_09_coefficients]
def admission41_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64781568411419738709544281935164792832/13833650542458603515625:ℝ),(64679943353158091978584540740524220416/4611216847486201171875:ℝ),(516626628731478777672563609248989184/36889734779889609375:ℝ),(64476724133732665432252013181963075584/13833650542458603515625:ℝ)],
![(8608185298860867691765025239816904704/922243369497240234375:ℝ),(386758981770468258177138081097425903616/13833650542458603515625:ℝ),(386149686778280833283522322620051095552/13833650542458603515625:ℝ),(14279276056188543765456624457764306944/1537072282495400390625:ℝ)],
![(64341014491395739141872490042325727232/13833650542458603515625:ℝ),(192718562176746088665463070132134033408/13833650542458603515625:ℝ),(38482822335146190720643677618722177024/2766730108491720703125:ℝ),(64036563997869247649940308003802578944/13833650542458603515625:ℝ)]]
theorem admission41_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477109581216195580735357910423/211253605916986174341120000000000:ℝ) admission41_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission41_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_10_coefficients]
def admission41_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(150938283825522729624481728944874733276/8257854772751000987985481947:ℝ),(2715503017277578353527417533152638058496/74320692954759008891869337523:ℝ),(50261432049740455109209475754932305920/2752618257583666995995160649:ℝ)],
![(150787419295309729033633366287503592214/8257854772751000987985481947:ℝ),(2712788164607265748004567679880187797504/74320692954759008891869337523:ℝ),(150633510370873352003703929352497397760/8257854772751000987985481947:ℝ)]]
theorem admission41_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (35913827507704103470731718385815/180395590129003200249538848292864:ℝ) admission41_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission41_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_11_coefficients]
def admission41_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission41_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission41_12_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission41_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_12_coefficients]
def admission41_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission41_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission41_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission41_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_13_coefficients]
def admission41_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission41_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission41_14_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission41_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_14_coefficients]
theorem admission41_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission41_00_pos hδ hp
 · exact admission41_01_pos hδ hp
 · exact admission41_02_pos hδ hp
 · exact admission41_03_pos hδ hp
 · exact admission41_04_pos hδ hp
 · exact admission41_05_pos hδ hp
 · exact admission41_06_pos hδ hp
 · exact admission41_07_pos hδ hp
 · exact admission41_08_pos hδ hp
 · exact admission41_09_pos hδ hp
 · exact admission41_10_pos hδ hp
 · exact admission41_11_pos hδ hp
 · exact admission41_12_pos hδ hp
 · exact admission41_13_pos hδ hp
 · exact admission41_14_pos hδ hp
#print axioms admission41_all
end
end LewkoStage2Finite
