/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission05_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission05_00_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission05_00_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 0 := by
 rw [admission05_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_00_coefficients]
def admission05_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission05_01_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission05_01_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 1 := by
 rw [admission05_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_01_coefficients]
def admission05_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1270613545954726835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission05_02_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2558591076383360746323227/3829204622338087582216250:ℝ) admission05_02_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 2 := by
 rw [admission05_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_02_coefficients]
def admission05_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(539684466533544406257066752/9190091093611410197319:ℝ), (712884705194637623266378496/9190091093611410197319:ℝ), (58044883915336992336437248/3063363697870470065773:ℝ)],
![(365122491558535209753011840/9190091093611410197319:ℝ), (364175451269767209753011840/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission05_03_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (241927426544433500968125/241298802047643180565504:ℝ) admission05_03_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 3 := by
 rw [admission05_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_03_coefficients]
def admission05_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(18229138493793832575232243702/1914602311169043791108125:ℝ), (9472:ℝ), (0:ℝ)],
![(28955467252035670524269914517/1914602311169043791108125:ℝ), (39340160284955311628517875584/1914602311169043791108125:ℝ), (10479989048866245616939937792/1914602311169043791108125:ℝ)]]
theorem admission05_04_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (284003609478553042841878197/1960552766637100842094720000:ℝ) admission05_04_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 4 := by
 rw [admission05_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_04_coefficients]
def admission05_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20348173093975068692466231866/1914602311169043791108125:ℝ), (39939424970535129705809546032/1914602311169043791108125:ℝ), (19545874355392942107487230464/1914602311169043791108125:ℝ)],
![(106742302719362890087240439/382920462233808758221625:ℝ), (115940448901886992625635784/382920462233808758221625:ℝ), (0:ℝ)]]
theorem admission05_05_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (130161294746358472102786731/1254753770647744538940620800:ℝ) admission05_05_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 5 := by
 rw [admission05_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_05_coefficients]
def admission05_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1908863088232694498581766381336640771018680169149002496/651028676964250692137413394579714034384822324375:ℝ), (3797549814158074453763681265288756689760820585029432064/651028676964250692137413394579714034384822324375:ℝ), (1888746186159176335975887910934954007241340415880429568/651028676964250692137413394579714034384822324375:ℝ), (0:ℝ)],
![(499149090030850931922510138372196512742861620747705472/130205735392850138427482678915942806876964464875:ℝ), (221675794015477334768705595101282467808830945218073216/26041147078570027685496535783188561375392892975:ℝ), (55645744946391891506154642918001959388300448717750272/10015825799450010648267898378149446682843420375:ℝ), (38050917168821662229080410515510551611537575996030976/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission05_06_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9252626556250598431082402026190223407027787715887/44443557680759513916580754403308478080670537344000:ℝ) admission05_06_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 6 := by
 rw [admission05_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_06_coefficients]
def admission05_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(779717861318439960362490050084401736847534106432454/17595369647682451138849010664316595523914116875:ℝ), (1127053961212228972096294913195549154582921263566592/17595369647682451138849010664316595523914116875:ℝ), (23281820801822473110886260417777185352120768393216/1173024643178830075923267377621106368260941125:ℝ)],
![(84836085446617991054727578830532603818326436880521/3519073929536490227769802132863319104782823375:ℝ), (84463387290006723503476480749397825531490364208768/3519073929536490227769802132863319104782823375:ℝ), (0:ℝ)]]
theorem admission05_07_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (229256210695029235548277792199791620085173581997/480470893846048799098170317873605168439681484800:ℝ) admission05_07_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 7 := by
 rw [admission05_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_07_coefficients]
def admission05_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (6688402014801712230976645224366792109342289772496972049903598082468563209/33062547524049386802582574449772817734806114077245440000000000000000:ℝ), (133675956691392339041089483095144170423867014558783064873568649939315868359/330625475240493868025825744497728177348061140772454400000000000000000:ℝ), (66785895929855539914214428004300884017283745886382717248902594234630236269/330625475240493868025825744497728177348061140772454400000000000000000:ℝ)],
![(119195303928117331047624256597953337262120184007630076518633687411160451741/220416983493662578683883829665152118232040760514969600000000000000000:ℝ), (1193175466593861278422904614430720612344941716630662614231224993557261180939/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (93823119637560626384724572171506279795923121552332395882759014868663917441/47232210748641981146546534928246882478294448681779200000000000000000:ℝ), (238960937814737637170851417834300788042346568277882510808917954418757509229/330625475240493868025825744497728177348061140772454400000000000000000:ℝ)]]
theorem admission05_08_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (110351149887603249442714692174014868941362662287508513984230867893952890771/118335466948531574838288471334382872333967550718845318804275200000000000000000:ℝ) admission05_08_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 8 := by
 rw [admission05_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_08_coefficients]
def admission05_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2316890254367707314720464347177950016570322355766929328/2199421205960306392356126333039574440489264609375:ℝ), (5930859105317205333562407287239759264051733675645060354/2199421205960306392356126333039574440489264609375:ℝ), (4915880044689018808211774971976315555832597997100298496/2199421205960306392356126333039574440489264609375:ℝ), (86796185485041092020405744460313130007151992481435648/146628080397353759490408422202638296032617640625:ℝ)],
![(193786617723723354986879744966192995914850049285113352/439884241192061278471225266607914888097852921875:ℝ), (386675046639236437427405943691502091089595663494508067/439884241192061278471225266607914888097852921875:ℝ), (38576405166774416855554396434648684909702100814877568/87976848238412255694245053321582977619570584375:ℝ), (0:ℝ)]]
theorem admission05_09_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (125261753141673602875732644176630506923140853231/4730790339407249714197369283678573966175325388800:ℝ) admission05_09_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 9 := by
 rw [admission05_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_09_coefficients]
def admission05_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172310368827159553024912798031104/3446284160104278823994625:ℝ), (2170779764519149314272123566944512/17231420800521394119973125:ℝ), (1758852220188755834410003925229568/17231420800521394119973125:ℝ), (449633115992860484328044348440576/17231420800521394119973125:ℝ)],
![(50707474000100979327706266089216/689256832020855764798925:ℝ), (597659408639790547000740977029888/3446284160104278823994625:ℝ), (435465020053893505085284289257472/3446284160104278823994625:ℝ), (91346555544657665155074642673664/3446284160104278823994625:ℝ)],
![(1063429391451540525534696908224/45950455468057050986595:ℝ), (2121923787494883289683784478144/45950455468057050986595:ℝ), (211694049303195836029817513984/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission05_10_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (346718683130492169682121229/64243393057164520393759784960:ℝ) admission05_10_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 10 := by
 rw [admission05_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_10_coefficients]
def admission05_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(220387548637449821810029102871470319016727739327678/5865123215894150379616336888105531841304705625:ℝ), (318903320614254575891695527205894825768205896909568/5865123215894150379616336888105531841304705625:ℝ), (99125900879447696303898561137767496345337213833216/5865123215894150379616336888105531841304705625:ℝ)],
![(23882102908265125381307147843589133982661167082621/1173024643178830075923267377621106368260941125:ℝ), (190095840123600465217999821782163425491806043776/9384197145430640607386139020968850946087529:ℝ), (0:ℝ)]]
theorem admission05_11_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (952712918459078462965874373723141796017219846863/2402354469230243995490851589368025842198407424000:ℝ) admission05_11_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 11 := by
 rw [admission05_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_11_coefficients]
def admission05_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_12_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission05_12_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 12 := by
 rw [admission05_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_12_coefficients]
def admission05_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_13_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (30094022595683136330185461/1503238553600000000000000000:ℝ) admission05_13_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 13 := by
 rw [admission05_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_13_coefficients]
def admission05_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_14_identity (δ p : ℝ) : admissionGuard .weakC7 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission05_14_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC7 δ p 14 := by
 rw [admission05_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_14_coefficients]
theorem admission05_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC7 δ p j := by
 fin_cases j
 · exact admission05_00_pos hδ hp
 · exact admission05_01_pos hδ hp
 · exact admission05_02_pos hδ hp
 · exact admission05_03_pos hδ hp
 · exact admission05_04_pos hδ hp
 · exact admission05_05_pos hδ hp
 · exact admission05_06_pos hδ hp
 · exact admission05_07_pos hδ hp
 · exact admission05_08_pos hδ hp
 · exact admission05_09_pos hδ hp
 · exact admission05_10_pos hδ hp
 · exact admission05_11_pos hδ hp
 · exact admission05_12_pos hδ hp
 · exact admission05_13_pos hδ hp
 · exact admission05_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
