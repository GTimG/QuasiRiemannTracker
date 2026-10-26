/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission35_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12641393584845603/52465400575843:ℝ),(37566784552809280/157396201727529:ℝ)]]
theorem admission35_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission35_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission35_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_00_coefficients]
def admission35_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9231142547415808/52465400575843:ℝ),(27493427642247424/157396201727529:ℝ)]]
theorem admission35_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission35_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission35_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_01_coefficients]
def admission35_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4694822086874282/52465400575843:ℝ),(4662746702956288/52465400575843:ℝ)]]
theorem admission35_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission35_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission35_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_02_coefficients]
def admission35_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1814703934667045387264/157396201727529:ℝ),(32445198876832948182016/1416565815547761:ℝ),(16113144264829539696640/1416565815547761:ℝ)],
![(1802497351880064623872/157396201727529:ℝ),(32225574945818514214144/1416565815547761:ℝ),(16003381378897932599296/1416565815547761:ℝ)]]
theorem admission35_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (976768882989375769/1934084526827876352:ℝ) admission35_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission35_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_03_coefficients]
def admission35_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(95205988161919231896/52465400575843:ℝ),(188306710566659183616/52465400575843:ℝ),(93105726164631158784/52465400575843:ℝ)],
![(96413114535807375426/52465400575843:ℝ),(190707468021120218880/52465400575843:ℝ),(94299389320587968512/52465400575843:ℝ)]]
theorem admission35_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (2131020954085491/26862285094831616:ℝ) admission35_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission35_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_04_coefficients]
def admission35_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12734689902794012078977/11804715129564675:ℝ),(637150356774094511125282/295117878239116875:ℝ),(106256527401618723138619/98372626079705625:ℝ)],
![(305857614769604820671311/295117878239116875:ℝ),(612211925184312219312946/295117878239116875:ℝ),(20422713113585654679359/19674525215941125:ℝ)]]
theorem admission35_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (305857614769604820671311/6601675184905817948160000:ℝ) admission35_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission35_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_05_coefficients]
def admission35_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5586621555626044823490640586268108500992/8249596917978249986997496465053:ℝ),(16555516196970966744706177330795000213504/8249596917978249986997496465053:ℝ),(16352186068037207913982918131144204746752/8249596917978249986997496465053:ℝ),(5383290021696337761505376586617313034240/8249596917978249986997496465053:ℝ)],
![(5651174834373872467424768342106165044224/8249596917978249986997496465053:ℝ),(16748351097311836759834599654728751735808/8249596917978249986997496465053:ℝ),(16544200393468780754887577376969728917504/8249596917978249986997496465053:ℝ),(5447022716528483947682010464347142225920/8249596917978249986997496465053:ℝ)]]
theorem admission35_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (320869089466115102857671772636015/2815862414669909328895145460071424:ℝ) admission35_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission35_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_06_coefficients]
def admission35_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(414785021942620042417033368348127720/74320692954759008891869337523:ℝ),(822904823894733310517433503196888064/74320692954759008891869337523:ℝ),(408133053897273985381935256953651200/74320692954759008891869337523:ℝ)],
![(408427314834752205643906920388861150/74320692954759008891869337523:ℝ),(810241301530134800439043668784837888/74320692954759008891869337523:ℝ),(401827135467959880886763725086556160/74320692954759008891869337523:ℝ)]]
theorem admission35_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (12262790999388424099327506258745/50736259723782150070182801082368:ℝ) admission35_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission35_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_07_coefficients]
def admission35_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5441601263108255519429218878261953733689874293500104857/435472810281791067725796899548828125000000000000:ℝ),(3404352743460607409789070185039835055377121050479087227/87094562056358213545159379909765625000000000000:ℝ),(17718047365686761537879608748562479145746005166906523701/435472810281791067725796899548828125000000000000:ℝ),(6137871337037506680563610848979715459503697645511192423/435472810281791067725796899548828125000000000000:ℝ)],
![(14764310584229482998433457950051099546286534327791071217/870945620563582135451593799097656250000000000000:ℝ),(45614921611751310211975388251033411708733674403870433037/870945620563582135451593799097656250000000000000:ℝ),(23467924609839182098933178638902710319495328991097356213/435472810281791067725796899548828125000000000000:ℝ),(8042605434608061360979015162351617594308217156182675303/435472810281791067725796899548828125000000000000:ℝ)]]
theorem admission35_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5441601263108255519429218878261953733689874293500104857/2493788637943340240249625038800551936000000000000000000000:ℝ) admission35_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission35_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_08_coefficients]
def admission35_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(120445619884518793057581256029293134263431828/2177364051408955338628984497744140625:ℝ),(354647114422899766699660147011644788381577372/2177364051408955338628984497744140625:ℝ),(347972104583860211643493936467066854316882944/2177364051408955338628984497744140625:ℝ),(4550826659265924766817834962212542036074496/87094562056358213545159379909765625:ℝ)],
![(109797782672112392752394338194462725608799591/2177364051408955338628984497744140625:ℝ),(322888715448081878999700033257562470692704029/2177364051408955338628984497744140625:ℝ),(316398104134760413104603265744058588564258048/2177364051408955338628984497744140625:ℝ),(20661445631346024273431103989504513645289472/435472810281791067725796899548828125:ℝ)]]
theorem admission35_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2522149124920168978690320311218812700841/304417558342692900421096806494208000000000:ℝ) admission35_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission35_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_09_coefficients]
def admission35_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14118516964927627970384361109504/2766730108491720703125:ℝ),(23008386822925575745881523075072/1537072282495400390625:ℝ),(22486756001204328860572097634304/1537072282495400390625:ℝ),(65897936518271917884136976580608/13833650542458603515625:ℝ)],
![(44803996040643277421687512902656/4611216847486201171875:ℝ),(393927605247905989185986026771456/13833650542458603515625:ℝ),(384634074546075728584173957419008/13833650542458603515625:ℝ),(8341234398085804777550031290368/922243369497240234375:ℝ)],
![(63770653234025362010834804129152/13833650542458603515625:ℝ),(186706683458144503612361145947008/13833650542458603515625:ℝ),(36421727463918811863369229901312/2766730108491720703125:ℝ),(158639776296870590389597339648/37087534966376953125:ℝ)]]
theorem admission35_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4841301766872271435229411/2212357635692298240000000000:ℝ) admission35_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission35_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_10_coefficients]
def admission35_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(113411372145561005611883887258267144/24773564318253002963956445841:ℝ),(675013393462866856116403514666334208/74320692954759008891869337523:ℝ),(12399702703603149839586234972651520/2752618257583666995995160649:ℝ)],
![(111629551975697702515827833089550518/24773564318253002963956445841:ℝ),(664366977169749313514906577016592896/74320692954759008891869337523:ℝ),(36610101164137522472178634948034560/8257854772751000987985481947:ℝ)]]
theorem admission35_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2234503244881440580577309261965/11274724383062700015596178018304:ℝ) admission35_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission35_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_11_coefficients]
def admission35_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission35_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission35_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission35_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_12_coefficients]
def admission35_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission35_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission35_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission35_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_13_coefficients]
def admission35_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission35_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission35_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission35_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_14_coefficients]
theorem admission35_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission35_00_pos hδ hp
 · exact admission35_01_pos hδ hp
 · exact admission35_02_pos hδ hp
 · exact admission35_03_pos hδ hp
 · exact admission35_04_pos hδ hp
 · exact admission35_05_pos hδ hp
 · exact admission35_06_pos hδ hp
 · exact admission35_07_pos hδ hp
 · exact admission35_08_pos hδ hp
 · exact admission35_09_pos hδ hp
 · exact admission35_10_pos hδ hp
 · exact admission35_11_pos hδ hp
 · exact admission35_12_pos hδ hp
 · exact admission35_13_pos hδ hp
 · exact admission35_14_pos hδ hp
#print axioms admission35_all
end
end LewkoStage2Finite
