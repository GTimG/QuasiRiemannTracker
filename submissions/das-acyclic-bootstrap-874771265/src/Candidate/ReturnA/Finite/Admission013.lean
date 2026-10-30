/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission013_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)],
![(87375252593976541184/23638787823:ℝ),(776778238366752702464/70916363469:ℝ),(767179203387716534272/70916363469:ℝ),(252526722802893455360/70916363469:ℝ)],
![(43687626296988270592/23638787823:ℝ),(388389119183376351232/70916363469:ℝ),(383589601693858267136/70916363469:ℝ),(126263361401446727680/70916363469:ℝ)]]
theorem admission013_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission013_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission013_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_00_coefficients]
def admission013_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)],
![(190210218178314764288/70916363469:ℝ),(565261945414944292864/70916363469:ℝ),(559893236294944292864/70916363469:ℝ),(61613836352771588096/23638787823:ℝ)],
![(95105109089157382144/70916363469:ℝ),(282630972707472146432/70916363469:ℝ),(279946618147472146432/70916363469:ℝ),(30806918176385794048/23638787823:ℝ)]]
theorem admission013_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission013_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission013_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_01_coefficients]
def admission013_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)],
![(12076411408011342381056/8864545433625:ℝ),(179531207110792358920192/44322727168125:ℝ),(177916243101414582124544/44322727168125:ℝ),(58767093030678935109632/44322727168125:ℝ)],
![(6038205704005671190528/8864545433625:ℝ),(89765603555396179460096/44322727168125:ℝ),(88958121550707291062272/44322727168125:ℝ),(29383546515339467554816/44322727168125:ℝ)]]
theorem admission013_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission013_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission013_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_02_coefficients]
def admission013_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73329502161652940800/70916363469:ℝ),(648632125138187321344/212749090407:ℝ),(637356238661498175488/212749090407:ℝ),(29816088572609953792/30392727201:ℝ)],
![(144776583813178327040/70916363469:ℝ),(1280339527208485781504/212749090407:ℝ),(179686612905480945664/30392727201:ℝ),(411796514569415819264/212749090407:ℝ)],
![(10206725950217912320/10130909067:ℝ),(631707402070298460160/212749090407:ℝ),(620450051676868444160/212749090407:ℝ),(203083894561146142720/212749090407:ℝ)]]
theorem admission013_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1513092924365/3025764841344:ℝ) admission013_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission013_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_03_coefficients]
def admission013_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(116262706994555470336/703535351875:ℝ),(474620761278117901824/984949492625:ℝ),(2305331468169742385152/4924747463125:ℝ),(746066610741041168384/4924747463125:ℝ)],
![(1667675476377697852928/4924747463125:ℝ),(694920881088204009984/703535351875:ℝ),(2836298243348196491264/2954848477875:ℝ),(918235828604358361088/2954848477875:ℝ)],
![(853836527415809560576/4924747463125:ℝ),(2491342361226838560768/4924747463125:ℝ),(7265496812231755300864/14774242389375:ℝ),(2352979310798668300288/14774242389375:ℝ)]]
theorem admission013_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25614164339711649/322748249743360000:ℝ) admission013_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission013_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_04_coefficients]
def admission013_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4320522800823656720896/44322727168125:ℝ),(12987240925314019817984/44322727168125:ℝ),(13010141129609015277568/44322727168125:ℝ),(96520511224858937344/984949492625:ℝ)],
![(7987056842136474599936/44322727168125:ℝ),(24029191462379834335744/44322727168125:ℝ),(24091596676163160731648/44322727168125:ℝ),(536630803727986733056/2954848477875:ℝ)],
![(733306808262563575808/8864545433625:ℝ),(315484301059023271936/1266363633375:ℝ),(2216291109310829090816/8864545433625:ℝ),(247069270053409921024/2954848477875:ℝ)]]
theorem admission013_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (358059964971954871/8262355193430016000:ℝ) admission013_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission013_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_05_coefficients]
def admission013_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3244910051777571166433778998119936/12922071700256302459483125:ℝ),(27885012116298937810573598231243264/38766215100768907378449375:ℝ),(26591652403724951158062453030977536/38766215100768907378449375:ℝ),(1688245973244720065678038358818816/7753243020153781475689875:ℝ)],
![(947145328398294221050093867708928/1846010242893757494211875:ℝ),(57010457794051653065269312147823104/38766215100768907378449375:ℝ),(54402842160531795968219633023778816/38766215100768907378449375:ℝ),(98755151458557296014870240559104/221521229147250899305425:ℝ)],
![(677021449402097676183375615168512/2584414340051260491896625:ℝ),(5825089135550543050939142783315968/7753243020153781475689875:ℝ),(5562237951361368962031435998560256/7753243020153781475689875:ℝ),(1768184327804785294842420060749824/7753243020153781475689875:ℝ)]]
theorem admission013_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6440147297839050543510583339/56457392729866469198979072000:ℝ) admission013_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission013_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_06_coefficients]
def admission013_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(534956304842269242868322612747776/1047735543264024523741875:ℝ),(1572426377632368232791202457067008/1047735543264024523741875:ℝ),(513412835088512290411709980278784/349245181088008174580625:ℝ),(100553686495087576262450019303424/209547108652804904748375:ℝ)],
![(1038541656160176887419377727172096/1047735543264024523741875:ℝ),(3051750215909817606486394420653568/1047735543264024523741875:ℝ),(996125620555029115973659430027264/349245181088008174580625:ℝ),(195033660383089325770792319320064/209547108652804904748375:ℝ)],
![(14388152894797361272887288983552/29935301236114986392625:ℝ),(42266395379355696391291198959616/29935301236114986392625:ℝ),(13791793870471909301769984278528/9978433745371662130875:ℝ),(2699427825371478557381208571904/5987060247222997278525:ℝ)]]
theorem admission013_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1287187493024577406588177/5449555282805643745075200:ℝ) admission013_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission013_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_07_coefficients]
def admission013_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(307796360075252732847005218855089529171/97445642044645137996826171875000:ℝ),(119054199655124283352959046480095839245397/10231792414687739489666748046875000:ℝ),(5225275641445333578500315533662522038541/378955274618064425543212890625000:ℝ),(10868012216683110741647968210079768771633/2046358482937547897933349609375000:ℝ)],
![(1074408355661068370045090385679150879966/85264936789064495747222900390625:ℝ),(106591624221377684048787340840654995781393/2557948103671934872416687011718750:ℝ),(528207344722857788791272080352563923991/11600671671981564047241210937500:ℝ),(16842761071931468371717963192327419093041/1023179241468773948966674804687500:ℝ)],
![(6440692324761777830431686553447580335531/682119494312515965977783203125000:ℝ),(12292491889215458113687612675300965755207/409271696587509579586669921875000:ℝ),(7217698571700812513208743454712739687099/227373164770838655325927734375000:ℝ),(22817509927179826001787958174575069414449/2046358482937547897933349609375000:ℝ)]]
theorem admission013_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (307796360075252732847005218855089529171/186011486986432639831900160000000000000000:ℝ) admission013_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission013_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_08_coefficients]
def admission013_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9826544826818480018642001485337876016/409271696587509579586669921875:ℝ),(46301584229925042768506768966989182472/682119494312515965977783203125:ℝ),(130482333639234446937815210461159261696/2046358482937547897933349609375:ℝ),(129242659267817184331461567618719744/6496376136309675866455078125:ℝ)],
![(16842081205745793922242359874290837168/409271696587509579586669921875:ℝ),(78864584950775120198194871070657203912/682119494312515965977783203125:ℝ),(220683918087708499144988365405121517056/2046358482937547897933349609375:ℝ),(1517841410586562433661845956266549248/45474632954167731065185546875:ℝ)],
![(7015536378927313903600358388952961152/409271696587509579586669921875:ℝ),(6512600144170015485937620420733604288/136423898862503193195556640625:ℝ),(18040316889694810441434630988792451072/409271696587509579586669921875:ℝ),(40876186380789476222774332195700736/3031642196944515404345703125:ℝ)]]
theorem admission013_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (11226979901950234558257110283243/1589453624151646092313600000000000:ℝ) admission013_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission013_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_09_coefficients]
def admission013_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5536849465560667173358022/824455490478515625:ℝ),(542674597664151464871606974/28855942166748046875:ℝ),(504218555970404366505465388/28855942166748046875:ℝ),(51779159082453542567129728/9618647388916015625:ℝ)],
![(197989692004926776768687264/17313565300048828125:ℝ),(78494213125810986903241888/2473366471435546875:ℝ),(101041508352837562805364928/3462713060009765625:ℝ),(17082489289687520274757632/1923729477783203125:ℝ)],
![(16142823870151469209738624/3462713060009765625:ℝ),(44182825472614632021548672/3462713060009765625:ℝ),(39959913946549441663881472/3462713060009765625:ℝ),(1324487829898475428007936/384745895556640625:ℝ)]]
theorem admission013_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2910251579366767297869/1613741248716800000000000:ℝ) admission013_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission013_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_10_coefficients]
def admission013_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(146377242616405309635785862247936/349245181088008174580625:ℝ),(1290786694412648491179013504950784/1047735543264024523741875:ℝ),(252884455173647008371569776689152/209547108652804904748375:ℝ),(137589103101600826528730988412928/349245181088008174580625:ℝ)],
![(283957891963476340714692766762496/349245181088008174580625:ℝ),(2503272390061940254191625314374144/1047735543264024523741875:ℝ),(490280738253024167037477619007488/209547108652804904748375:ℝ),(266668325697869867713280360316928/349245181088008174580625:ℝ)],
![(3930875695630600887968768700416/9978433745371662130875:ℝ),(34642448447122621800360337412096/29935301236114986392625:ℝ),(33913754725625308380843977474048/29935301236114986392625:ℝ),(147519111538593189925199282176/399137349814866485235:ℝ)]]
theorem admission013_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (70342593926712603533363/363303685520376249671680:ℝ) admission013_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission013_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_11_coefficients]
def admission013_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission013_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission013_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission013_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_12_coefficients]
def admission013_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)],
![(12142977360698277888/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(12142977360698277888/762939453125:ℝ)],
![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)]]
theorem admission013_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission013_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission013_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_13_coefficients]
def admission013_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission013_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission013_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission013_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission013_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission013_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission013_14_coefficients]
theorem admission013_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission013_00_pos hd hp
 · exact admission013_01_pos hd hp
 · exact admission013_02_pos hd hp
 · exact admission013_03_pos hd hp
 · exact admission013_04_pos hd hp
 · exact admission013_05_pos hd hp
 · exact admission013_06_pos hd hp
 · exact admission013_07_pos hd hp
 · exact admission013_08_pos hd hp
 · exact admission013_09_pos hd hp
 · exact admission013_10_pos hd hp
 · exact admission013_11_pos hd hp
 · exact admission013_12_pos hd hp
 · exact admission013_13_pos hd hp
 · exact admission013_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission013_all
