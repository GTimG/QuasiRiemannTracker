/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission014_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)],
![(8234439689357169262592/70916363469:ℝ),(24549734508406929096704/70916363469:ℝ),(24396149948742350405632/70916363469:ℝ),(8080855129692590571520/70916363469:ℝ)],
![(4117219844678584631296/70916363469:ℝ),(12274867254203464548352/70916363469:ℝ),(12198074974371175202816/70916363469:ℝ),(4040427564846295285760/70916363469:ℝ)]]
theorem admission014_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission014_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission014_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_00_coefficients]
def admission014_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)],
![(6000827635786072457216/70916363469:ℝ),(17916583561438217371648/70916363469:ℝ),(17830684215518217371648/70916363469:ℝ),(1971642763288690819072/23638787823:ℝ)],
![(3000413817893036228608/70916363469:ℝ),(8958291780719108685824/70916363469:ℝ),(8915342107759108685824/70916363469:ℝ),(985821381644345409536/23638787823:ℝ)]]
theorem admission014_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission014_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission014_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_01_coefficients]
def admission014_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)],
![(635462133710590117412864/14774242389375:ℝ),(5693319779245266627985408/44322727168125:ℝ),(1133496071019044439851008/8864545433625:ℝ),(1880546976981725923508224/44322727168125:ℝ)],
![(317731066855295058706432/14774242389375:ℝ),(2846659889622633313992704/44322727168125:ℝ),(566748035509522219925504/8864545433625:ℝ),(940273488490862961754112/44322727168125:ℝ)]]
theorem admission014_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission014_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission014_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_02_coefficients]
def admission014_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6813728157594667712512/212749090407:ℝ),(2894395755593853829120/30392727201:ℝ),(20080816168249950470144/212749090407:ℝ),(6633774036687641378816/212749090407:ℝ)],
![(13537242521129285844992/212749090407:ℝ),(5750149640685696843776/30392727201:ℝ),(39891293429891898277888/212749090407:ℝ),(13177488466221306216448/212749090407:ℝ)],
![(6723514363534618132480/212749090407:ℝ),(2855753885091843014656/30392727201:ℝ),(19810477261641947807744/212749090407:ℝ),(6543714429533664837632/212749090407:ℝ)]]
theorem admission014_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (24377235880247/48412237461504:ℝ) admission014_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission014_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_03_coefficients]
def admission014_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24953363337053045420032/4924747463125:ℝ),(73775732599625582276608/4924747463125:ℝ),(72696500806285854244864/4924747463125:ℝ),(23874131543713317388288/4924747463125:ℝ)],
![(151598160594655440320512/14774242389375:ℝ),(89649326252095048996864/2954848477875:ℝ),(441729731585308425715712/14774242389375:ℝ),(145081260919488621051904/14774242389375:ℝ)],
![(76738070583496304060416/14774242389375:ℝ),(226919433461598498154496/14774242389375:ℝ),(44728045833290172596224/2954848477875:ℝ),(14691773257669733777408/2954848477875:ℝ)]]
theorem admission014_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25614164339711649/322748249743360000:ℝ) admission014_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission014_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_04_coefficients]
def admission014_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6340597574660342447104/2110606055625:ℝ),(399824050472321501520896/44322727168125:ℝ),(400168275192656995308544/44322727168125:ℝ),(133496773788202685176832/44322727168125:ℝ)],
![(12189257179308168957952/2110606055625:ℝ),(768788847275401182871552/44322727168125:ℝ),(769609850817254951266304/44322727168125:ℝ),(256795404307325316511744/44322727168125:ℝ)],
![(1949553201549275503616/703535351875:ℝ),(368964796803079681350656/44322727168125:ℝ),(73888315124919591191552/8864545433625:ℝ),(123298630519122631334912/44322727168125:ℝ)]]
theorem admission014_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (17134744935491679231/377707665985372160000:ℝ) admission014_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission014_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_05_coefficients]
def admission014_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(290610498166320811185310320202698752/38766215100768907378449375:ℝ),(851136052179357128894952637403844608/38766215100768907378449375:ℝ),(830645472038332034291728454612156416/38766215100768907378449375:ℝ),(54023871143831042101697227482202112/7753243020153781475689875:ℝ)],
![(587781504878711120141596737185363968/38766215100768907378449375:ℝ),(1721786438702788430533014455359485952/38766215100768907378449375:ℝ),(1680639845448527045299940529150623744/38766215100768907378449375:ℝ),(109326755960623127870024562195300352/7753243020153781475689875:ℝ)],
![(297171006712390308956286416982665216/38766215100768907378449375:ℝ),(870650386523431301638061817955641344/38766215100768907378449375:ℝ),(849994373410195011008212074538467328/38766215100768907378449375:ℝ),(1580082423336916736237923848945664/221521229147250899305425:ℝ)]]
theorem admission014_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6440147297839050543510583339/56457392729866469198979072000:ℝ) admission014_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission014_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_06_coefficients]
def admission014_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16358609976579015842663311657201664/1047735543264024523741875:ℝ),(48560823971867745743092774711914496/1047735543264024523741875:ℝ),(1779550197415529964157672495251456/38805020120889797175625:ℝ),(3169128266986115826365538863415296/209547108652804904748375:ℝ)],
![(32223335543596639713860426954745856/1047735543264024523741875:ℝ),(95648013838962775288160791559972864/1047735543264024523741875:ℝ),(71526881297551343686792997502976/791939186140608105625:ℝ),(6241077132258858424665354218242048/209547108652804904748375:ℝ)],
![(15864725567017623871197115297544192/1047735543264024523741875:ℝ),(47087189867095029545068016848058368/1047735543264024523741875:ℝ),(1725266986164485876495184382394368/38805020120889797175625:ℝ),(3071948865272742598299815354826752/209547108652804904748375:ℝ)]]
theorem admission014_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (732409683530984544348672713/3051750958371160497242112000:ℝ) admission014_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission014_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_07_coefficients]
def admission014_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1029497046477342986770624725777963236753/8700503753986173035430908203125:ℝ),(71150640534532734848296668591199940035499/182710578833709633744049072265625:ℝ),(180673489112283840569945718936500090859197/426324683945322478736114501953125:ℝ),(195298649733098943573419721431372381881789/1278974051835967436208343505859375:ℝ)],
![(2902550804857378886419405755297455900713/8700503753986173035430908203125:ℝ),(194796177501046756220957693752130465502049/182710578833709633744049072265625:ℝ),(96466492915911088586443939942641016378418/85264936789064495747222900390625:ℝ),(510092276571165039748239342507697770191738/1278974051835967436208343505859375:ℝ)],
![(374610751676007179929756205903898532792/1740100750797234607086181640625:ℝ),(4945821478660560854906441006437221018662/7308423153348385349761962890625:ℝ),(301658975467271602362273980776704991032893/426324683945322478736114501953125:ℝ),(314793626838066096174819621076325388309949/1278974051835967436208343505859375:ℝ)]]
theorem admission014_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1029497046477342986770624725777963236753/531461391389807542376857600000000000000000:ℝ) admission014_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission014_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_08_coefficients]
def admission014_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(443988299210407140230507305937487284576/682119494312515965977783203125:ℝ),(3861149579114741692258150004156640489664/2046358482937547897933349609375:ℝ),(532426580237319797051405285735203053568/292336926133935413990478515625:ℝ),(8872636374229341371472821074476335104/15158210984722577021728515625:ℝ)],
![(815528895874300521836785284437052044944/682119494312515965977783203125:ℝ),(7077750020246546443236886927002266325536/2046358482937547897933349609375:ℝ),(973835120728640800305376040932585336832/292336926133935413990478515625:ℝ),(48570925138769997877179070600529575936/45474632954167731065185546875:ℝ)],
![(371540596663893381606277978499564760368/682119494312515965977783203125:ℝ),(3216600441131804750978736922845625835872/2046358482937547897933349609375:ℝ),(441408540491321003253970755197382283264/292336926133935413990478515625:ℝ),(21953016016081973762760607377100570624/45474632954167731065185546875:ℝ)]]
theorem admission014_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1004929322025236836063870576954677/127156289932131687385088000000000000:ℝ) admission014_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission014_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_09_coefficients]
def admission014_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5129821229244093398500097008/28855942166748046875:ℝ),(14774212472390139121642025648/28855942166748046875:ℝ),(14160915145013582467502510272/28855942166748046875:ℝ),(1505513017484491414786860544/9618647388916015625:ℝ)],
![(28090674321915874485158912336/86567826500244140625:ℝ),(16131266233324827292413439568/17313565300048828125:ℝ),(77051793563312189281563908672/86567826500244140625:ℝ),(2720692087505471089406180352/9618647388916015625:ℝ)],
![(2532484983677672671164496804/17313565300048828125:ℝ),(36218611973878433340389661508/86567826500244140625:ℝ),(4922176209212441066782276208/12366832357177734375:ℝ),(1211010337072802289767639552/9618647388916015625:ℝ)]]
theorem admission014_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (21287291081357852749821789/10327943991787520000000000000:ℝ) admission014_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission014_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_10_coefficients]
def admission014_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13424194897611644917861292965302272/1047735543264024523741875:ℝ),(4427861555124924396049471661314048/116415060362669391526875:ℝ),(39430875864138391145081768077950976/1047735543264024523741875:ℝ),(4334772255208572166165938697142272/349245181088008174580625:ℝ)],
![(26433067234105881498926799750387712/1047735543264024523741875:ℝ),(1743609364782943865680174834497536/23283012072533878305375:ℝ),(11089930492588871393879426056060928/149676506180574931963125:ℝ),(8533386422331835766824971530141696/349245181088008174580625:ℝ)],
![(2601774467298847316213101357017088/209547108652804904748375:ℝ),(1430061756263264977450467503724544/38805020120889797175625:ℝ),(7639727516796741722414842862895104/209547108652804904748375:ℝ),(4198614167123263600659032832999424/349245181088008174580625:ℝ)]]
theorem admission014_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1001027623921218776860006531/5086251597285267495403520000:ℝ) admission014_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission014_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_11_coefficients]
def admission014_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)],
![(11041817268303429632/10986328125:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/3662109375:ℝ),(11041817268303429632/10986328125:ℝ)],
![(5520908634151714816/10986328125:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/3662109375:ℝ),(5520908634151714816/10986328125:ℝ)]]
theorem admission014_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission014_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission014_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_12_coefficients]
def admission014_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)],
![(388575275542344892416/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(1165725826627034677248/762939453125:ℝ),(388575275542344892416/762939453125:ℝ)],
![(194287637771172446208/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(582862913313517338624/762939453125:ℝ),(194287637771172446208/762939453125:ℝ)]]
theorem admission014_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission014_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission014_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_13_coefficients]
def admission014_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission014_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission014_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission014_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission014_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission014_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission014_14_coefficients]
theorem admission014_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission014_00_pos hd hp
 · exact admission014_01_pos hd hp
 · exact admission014_02_pos hd hp
 · exact admission014_03_pos hd hp
 · exact admission014_04_pos hd hp
 · exact admission014_05_pos hd hp
 · exact admission014_06_pos hd hp
 · exact admission014_07_pos hd hp
 · exact admission014_08_pos hd hp
 · exact admission014_09_pos hd hp
 · exact admission014_10_pos hd hp
 · exact admission014_11_pos hd hp
 · exact admission014_12_pos hd hp
 · exact admission014_13_pos hd hp
 · exact admission014_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission014_all
