/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission005_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)],
![(87375252593976541184/23638787823:ℝ),(776778238366752702464/70916363469:ℝ),(767179203387716534272/70916363469:ℝ),(252526722802893455360/70916363469:ℝ)],
![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)]]
theorem admission005_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission005_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission005_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_00_coefficients]
def admission005_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)],
![(190210218178314764288/70916363469:ℝ),(565261945414944292864/70916363469:ℝ),(559893236294944292864/70916363469:ℝ),(61613836352771588096/23638787823:ℝ)],
![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)]]
theorem admission005_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission005_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission005_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_01_coefficients]
def admission005_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)],
![(12076411408011342381056/8864545433625:ℝ),(179531207110792358920192/44322727168125:ℝ),(177916243101414582124544/44322727168125:ℝ),(58767093030678935109632/44322727168125:ℝ)],
![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)]]
theorem admission005_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission005_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission005_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_02_coefficients]
def admission005_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74273801763926573056/70916363469:ℝ),(657113760035390881792/212749090407:ℝ),(645819337475442606080/212749090407:ℝ),(211526982731831443456/212749090407:ℝ)],
![(146665183017725591552/70916363469:ℝ),(1297302797002892902400/212749090407:ℝ),(1274732487966255480832/212749090407:ℝ),(59632177145219907584/30392727201:ℝ)],
![(72391381253799018496/70916363469:ℝ),(640189036967502020608/212749090407:ℝ),(628913150490812874752/212749090407:ℝ),(205898257284707909632/212749090407:ℝ)]]
theorem admission005_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (12272492485327/24206118730752:ℝ) admission005_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission005_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_03_coefficients]
def admission005_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(339844835830239067136/2110606055625:ℝ),(462450998168422571008/984949492625:ℝ),(6738661214650016202752/14774242389375:ℝ),(2180810092935351107584/14774242389375:ℝ)],
![(4877820436985110744576/14774242389375:ℝ),(4742748536520474761728/4924747463125:ℝ),(13826824837022560550912/14774242389375:ℝ),(1492133221482082336768/4924747463125:ℝ)],
![(2498906586173437274624/14774242389375:ℝ),(2430493545678361906688/4924747463125:ℝ),(472544241491502956544/984949492625:ℝ),(459117914302179180544/2954848477875:ℝ)]]
theorem admission005_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478695447551829/161374124871680000:ℝ) admission005_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission005_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_04_coefficients]
def admission005_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4647517180579076141824/44322727168125:ℝ),(13951548174295966855424/44322727168125:ℝ),(13957843573397626838272/44322727168125:ℝ),(1551270859893578708224/14774242389375:ℝ)],
![(8641045601647313441792/44322727168125:ℝ),(25957805960343728410624/44322727168125:ℝ),(25987001563740383853056/44322727168125:ℝ),(2890080401681322961408/14774242389375:ℝ)],
![(3993528421068237299968/44322727168125:ℝ),(68607187348844351744/253272726675:ℝ),(12029157990342757014784/44322727168125:ℝ),(446269847262581417728/4924747463125:ℝ)]]
theorem admission005_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (15599720394797801953/330494207737200640000:ℝ) admission005_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission005_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_05_coefficients]
def admission005_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3171328152011374976254331338673152/12922071700256302459483125:ℝ),(27244116214045649585184345310389248/38766215100768907378449375:ℝ),(25971652709843546724700588833636352/38766215100768907378449375:ℝ),(1648276795964687451095847507853312/7753243020153781475689875:ℝ)],
![(6482853499255667166991761755068928/12922071700256302459483125:ℝ),(55728665989545076614490806306115072/38766215100768907378449375:ℝ),(53162842772768987101495904629096448/38766215100768907378449375:ℝ),(3376491946489440131356076717637632/7753243020153781475689875:ℝ)],
![(473075049606327455819632916627968/1846010242893757494211875:ℝ),(28484549775499427029306460995725824/38766215100768907378449375:ℝ),(27191190062925440376795315795460096/38766215100768907378449375:ℝ),(49377575729278648007435120279552/221521229147250899305425:ℝ)]]
theorem admission005_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3143838493279814626876540199/28228696364933234599489536000:ℝ) admission005_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission005_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_06_coefficients]
def admission005_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(551142976848916274300320812854272/1047735543264024523741875:ℝ),(231425153204877627318772150842368/149676506180574931963125:ℝ),(75561229027541884053743030370304/49892168726858310654375:ℝ),(103590542798630489639503878946816/209547108652804904748375:ℝ)],
![(1070915000173470950283374127385088/1047735543264024523741875:ℝ),(3146849605513367923366799618312704/1047735543264024523741875:ℝ),(1027157156763590911902641894653952/349245181088008174580625:ℝ),(201107372990175152524900038606848/209547108652804904748375:ℝ)],
![(519772023324554675983053314530816/1047735543264024523741875:ℝ),(1526873533079224532135394562416128/1047735543264024523741875:ℝ),(498228553570797723526440682061824/349245181088008174580625:ℝ),(97516830191544662885396159660032/209547108652804904748375:ℝ)]]
theorem admission005_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (371997185484102870503983153/1525875479185580248621056000:ℝ) admission005_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission005_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_07_coefficients]
def admission005_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1151561840926477967771152125464988853/68211949431251596597778320312500:ℝ),(1945268048224986401788385825754392236831/730842315334838534976196289062500:ℝ),(2989227750377730328107400491033158937043/568432911927096638314819335937500:ℝ),(2673845606269454266130976638888699287909/1023179241468773948966674804687500:ℝ)],
![(307796360075252732847005218855089529171/48722821022322568998413085937500:ℝ),(121362801462780894369653036761775643633023/5115896207343869744833374023437500:ℝ),(8092394233919745785743093159177192017011/284216455963548319157409667968750:ℝ),(808745719127661868737996304287503492659/73084231533483853497619628906250:ℝ)],
![(537204177830534185022545192839575439983/85264936789064495747222900390625:ℝ),(53872962562602994778567167990747448987603/2557948103671934872416687011718750:ℝ),(628360034164845773494227896539105956999/27068233901290316110229492187500:ℝ),(8648594461517811896200971621136349609317/1023179241468773948966674804687500:ℝ)]]
theorem admission005_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1151561840926477967771152125464988853/130208040890502847882330112000000000000000:ℝ) admission005_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission005_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_08_coefficients]
def admission005_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11325552088476694472279872624942918624/409271696587509579586669921875:ℝ),(7640023115405035685758082292344426032/97445642044645137996826171875:ℝ),(151083065036500566747400686626658184192/2046358482937547897933349609375:ℝ),(350158841485386454603179656176267264/15158210984722577021728515625:ℝ)],
![(2834299389866031832788300307642988912/58467385226787082798095703125:ℝ),(93221740106595534261794485229500803416/682119494312515965977783203125:ℝ),(261885380882240738764159317736119362048/2046358482937547897933349609375:ℝ),(258485318535634368662923135237439488/6496376136309675866455078125:ℝ)],
![(1702908728117105671447645905711600752/81854339317501915917333984375:ℝ),(39741578298760284461487909183089821192/682119494312515965977783203125:ℝ),(2261271751953881061566502675703289344/41762418019133630570068359375:ℝ),(758920705293281216830922978133274624/45474632954167731065185546875:ℝ)]]
theorem admission005_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (555850125947227453733586165624957/63578144966065843692544000000000000:ℝ) admission005_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission005_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_09_coefficients]
def admission005_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(665149117232536719465771224/86567826500244140625:ℝ),(74802675398241077122699816/3462713060009765625:ℝ),(1745541097644322931690802128/86567826500244140625:ℝ),(60070457512905024787675328/9618647388916015625:ℝ)],
![(1167525645495921417164550968/86567826500244140625:ℝ),(465827100360236900205524536/12366832357177734375:ℝ),(120823078111165543700972624/3462713060009765625:ℝ),(103037226546384912027799424/9618647388916015625:ℝ)],
![(165789286292135865767133778/28855942166748046875:ℝ),(458673262656689008970415998/28855942166748046875:ℝ),(420217220962941910604274412/28855942166748046875:ℝ),(6063668202136816304809152/1374092484130859375:ℝ)]]
theorem admission005_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (852703340925489792863787/368855142563840000000000000:ℝ) admission005_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission005_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_10_coefficients]
def admission005_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(150918895633073695520574011726848/349245181088008174580625:ℝ),(27159045528612493577481590330368/21382358025796418851875:ℝ),(186224096295084465191048754429952/149676506180574931963125:ℝ),(141844043354266719200821796667392/349245181088008174580625:ℝ)],
![(58608239599362622496853813144064/69849036217601634916125:ℝ),(516657092608133528485358831369728/209547108652804904748375:ℝ),(2529696487659833264146372890165248/1047735543264024523741875:ℝ),(275178206203201653057461976825856/349245181088008174580625:ℝ)],
![(142122302363739416963695053993472/349245181088008174580625:ℝ),(1252492232138655457130196230660608/1047735543264024523741875:ℝ),(1226127813594242007809031609155584/1047735543264024523741875:ℝ),(133334162848934933856640180158464/349245181088008174580625:ℝ)]]
theorem admission005_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (508629466434230552126465531/2543125798642633747701760000:ℝ) admission005_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission005_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_11_coefficients]
def admission005_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission005_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission005_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission005_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_12_coefficients]
def admission005_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)],
![(12142977360698277888/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(12142977360698277888/762939453125:ℝ)],
![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)]]
theorem admission005_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission005_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission005_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_13_coefficients]
def admission005_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission005_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission005_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission005_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission005_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission005_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission005_14_coefficients]
theorem admission005_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission005_00_pos hd hp
 · exact admission005_01_pos hd hp
 · exact admission005_02_pos hd hp
 · exact admission005_03_pos hd hp
 · exact admission005_04_pos hd hp
 · exact admission005_05_pos hd hp
 · exact admission005_06_pos hd hp
 · exact admission005_07_pos hd hp
 · exact admission005_08_pos hd hp
 · exact admission005_09_pos hd hp
 · exact admission005_10_pos hd hp
 · exact admission005_11_pos hd hp
 · exact admission005_12_pos hd hp
 · exact admission005_13_pos hd hp
 · exact admission005_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission005_all
