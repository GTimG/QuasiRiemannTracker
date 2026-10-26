/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19140788478132169/157396201727529:ℝ),(18783392276404640/157396201727529:ℝ)]]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission12_00_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission12_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]
def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(13946713821123712/157396201727529:ℝ),(13746713821123712/157396201727529:ℝ)]]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission12_01_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission12_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]
def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2363448735396138/52465400575843:ℝ),(2331373351478144/52465400575843:ℝ)]]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission12_02_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission12_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]
def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2103406480902006650368/1416565815547761:ℝ),(461301512873258481152/157396201727529:ℝ),(2048443934957319680000/1416565815547761:ℝ)],
![(2075918479843494989440/1416565815547761:ℝ),(455198121479768099456/157396201727529:ℝ),(2021003213474417905664/1416565815547761:ℝ)]]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (493408987664652809/967042263413938176:ℝ) admission12_03_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission12_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]
def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11852621127569260664/52465400575843:ℝ),(23189983379981185536/52465400575843:ℝ),(11339799981589692416/52465400575843:ℝ)],
![(12157784563216088994/52465400575843:ℝ),(23793530529233298304/52465400575843:ℝ),(11638215770578894848/52465400575843:ℝ)]]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1038189695580111/13431142547415808:ℝ) admission12_04_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission12_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]
def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(971303881723062945297/6558175071980375:ℝ),(87447070829590413511946/295117878239116875:ℝ),(43731806075427638538581/295117878239116875:ℝ)],
![(4506781810768406648339/32790875359901875:ℝ),(81192297785234942218514/295117878239116875:ℝ),(40624584700159801232213/295117878239116875:ℝ)]]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (13520345432305219945017/275069799371075747840000:ℝ) admission12_05_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission12_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]
def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(353620301410393731346629583658310023168/8249596917978249986997496465053:ℝ),(115053230647794560435896903071836862464/916621879775361109666388496117:ℝ),(1010348498406965697961990145935575154688/8249596917978249986997496465053:ℝ),(328489039502002836822006801947353415680/8249596917978249986997496465053:ℝ)],
![(361793124491661304670631754269643198976/8249596917978249986997496465053:ℝ),(117754347094094938983465707872147931648/916621879775361109666388496117:ℝ),(1034452319202804088371917253243270250496/8249596917978249986997496465053:ℝ),(336455626356021110094086036663582064640/8249596917978249986997496465053:ℝ)]]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (156635780097009104166987801526715/1407931207334954664447572730035712:ℝ) admission12_06_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission12_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]
def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(54705428095083762874504380708998408/74320692954759008891869337523:ℝ),(107685827023656447681403539655603712/74320692954759008891869337523:ℝ),(52987231246319905827483010827673600/74320692954759008891869337523:ℝ)],
![(53103002562186655016779966988983166/74320692954759008891869337523:ℝ),(104507025056014244889794388383126144/74320692954759008891869337523:ℝ),(51410751638991379703690127860899840/74320692954759008891869337523:ℝ)]]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (6275726518431564905235611311145/25368129861891075035091400541184:ℝ) admission12_07_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission12_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]
def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1758428101169259002305091891294213313325144374508509/10752415068686199203106096285156250000000000000:ℝ),(212707179027480543456463938812342722736261306721001649/290315206854527378483864599699218750000000000000:ℝ),(848336437317502721053904448254587332575762893533297209/870945620563582135451593799097656250000000000000:ℝ),(352634350038232955604689116024426303367600042705481491/870945620563582135451593799097656250000000000000:ℝ)],
![(15718487489349024497341316129176119332800556049723849/21504830137372398406212192570312500000000000000:ℝ),(1401661303120370091113145574295502782029387785677043319/580630413709054756967729199398437500000000000000:ℝ),(458944897243159398253827231679155263669407034525020261/174189124112716427090318759819531250000000000000:ℝ),(828817874430871625708540194367401837068729920373352211/870945620563582135451593799097656250000000000000:ℝ)]]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5275284303507777006915275673882639939975433123525527/11545317768256204815970486290743296000000000000000000000:ℝ) admission12_08_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission12_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]
def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9674346504768224296137464244191112096595198/2177364051408955338628984497744140625:ℝ),(9363295888530770579953983513538949791874018/725788017136318446209661499248046875:ℝ),(27161092559651718145780298360856747987801856/2177364051408955338628984497744140625:ℝ),(2798585245878862273573435186495820151808/696756496450865708361275039278125:ℝ)],
![(16640276916221135863238459738247337365340577/4354728102817910677257968995488281250:ℝ),(16049266020592678655395564156438803269478127/1451576034272636892419322998496093750:ℝ),(23191381819221017687291513470526300052926272/2177364051408955338628984497744140625:ℝ),(1487529820551338975901138138865113027994624/435472810281791067725796899548828125:ℝ)]]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1452665840382166968653455213735461941401/152208779171346450210548403247104000000000:ℝ) admission12_09_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission12_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]
def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2876382201593778490306051646464/13833650542458603515625:ℝ),(307811004528803058983262589952/512357427498466796875:ℝ),(7993762929506363054482264918016/13833650542458603515625:ℝ),(853084970982486317413408878592/4611216847486201171875:ℝ)],
![(5348187417535412342613863470592/13833650542458603515625:ℝ),(5139787483177500034893298339328/4611216847486201171875:ℝ),(4932102499505723230626453208064/4611216847486201171875:ℝ),(189005858258303277192533123072/553346021698344140625:ℝ)],
![(493121980453116189055389540416/2766730108491720703125:ℝ),(2363361052668203835484350403136/4611216847486201171875:ℝ),(6784364850456038093274994312576/13833650542458603515625:ℝ),(2159898681724820032098890805248/13833650542458603515625:ℝ)]]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (527319014092973640649143263/206302349528306810880000000000:ℝ) admission12_10_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission12_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]
def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(44913793240862495890674329406474488/74320692954759008891869337523:ℝ),(88412810444447898011962364373167104/74320692954759008891869337523:ℝ),(4833953184686158391901109980344320/8257854772751000987985481947:ℝ)],
![(43566275247819522048449478292875266/74320692954759008891869337523:ℝ),(85740133557912798420824210412936448/74320692954759008891869337523:ℝ),(4686701448018176630256092487864320/8257854772751000987985481947:ℝ)]]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1144214220707562653871116330045/5637362191531350007798089009152:ℝ) admission12_11_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission12_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]
def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission12_12_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission12_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]
def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission12_13_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission12_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]
def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission12_14_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission12_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]
theorem admission12_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission12_00_pos hδ hp
 · exact admission12_01_pos hδ hp
 · exact admission12_02_pos hδ hp
 · exact admission12_03_pos hδ hp
 · exact admission12_04_pos hδ hp
 · exact admission12_05_pos hδ hp
 · exact admission12_06_pos hδ hp
 · exact admission12_07_pos hδ hp
 · exact admission12_08_pos hδ hp
 · exact admission12_09_pos hδ hp
 · exact admission12_10_pos hδ hp
 · exact admission12_11_pos hδ hp
 · exact admission12_12_pos hδ hp
 · exact admission12_13_pos hδ hp
 · exact admission12_14_pos hδ hp
#print axioms admission12_all
end
end LewkoStage2Finite
