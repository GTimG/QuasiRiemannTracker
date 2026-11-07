/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission028_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(84833816866648844184584192/1418317983:ℝ),(254400797713356264732360704/1418317983:ℝ),(254300144826765996910968832/1418317983:ℝ),(84733163980058576363192320/1418317983:ℝ)],
![(169667633733297688369168384/1418317983:ℝ),(508801595426712529464721408/1418317983:ℝ),(508600289653531993821937664/1418317983:ℝ),(169466327960117152726384640/1418317983:ℝ)],
![(84833816866648844184584192/1418317983:ℝ),(254400797713356264732360704/1418317983:ℝ),(254300144826765996910968832/1418317983:ℝ),(84733163980058576363192320/1418317983:ℝ)]]
theorem admission028_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission028_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission028_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_00_coefficients]
def admission028_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(62078218656354757410553856/1418317983:ℝ),(186178360973722141031661568/1418317983:ℝ),(186122065978380009831661568/1418317983:ℝ),(6891324851223625134505984/157590887:ℝ)],
![(124156437312709514821107712/1418317983:ℝ),(372356721947444282063323136/1418317983:ℝ),(372244131956760019663323136/1418317983:ℝ),(13782649702447250269011968/157590887:ℝ)],
![(62078218656354757410553856/1418317983:ℝ),(186178360973722141031661568/1418317983:ℝ),(186122065978380009831661568/1418317983:ℝ),(6891324851223625134505984/157590887:ℝ)]]
theorem admission028_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission028_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission028_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_01_coefficients]
def admission028_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(493392974467301171934292606976/22161218484375:ℝ),(493251856864233406265450037248/7387072828125:ℝ),(98622147852233128119321493504/1477414565625:ℝ),(492969621658097874927764897792/22161218484375:ℝ)],
![(986785948934602343868585213952/22161218484375:ℝ),(986503713728466812530900074496/7387072828125:ℝ),(197244295704466256238642987008/1477414565625:ℝ),(985939243316195749855529795584/22161218484375:ℝ)],
![(493392974467301171934292606976/22161218484375:ℝ),(493251856864233406265450037248/7387072828125:ℝ),(98622147852233128119321493504/1477414565625:ℝ),(492969621658097874927764897792/22161218484375:ℝ)]]
theorem admission028_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission028_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission028_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_02_coefficients]
def admission028_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138350990220024317701259264/4254953949:ℝ),(414817656063930146710618112/4254953949:ℝ),(414582379216523340317458432/4254953949:ℝ),(138115713372617511308099584/4254953949:ℝ)],
![(276583925407670868014792704/4254953949:ℝ),(829281160084823257548587008/4254953949:ℝ),(828810619474304899852795904/4254953949:ℝ),(276113384797152510319001600/4254953949:ℝ)],
![(138232935187646550313533440/4254953949:ℝ),(414463504020893110837968896/4254953949:ℝ),(414228240257781559535337472/4254953949:ℝ),(137997671424534999010902016/4254953949:ℝ)]]
theorem admission028_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (7844259438601/15491814555648:ℝ) admission028_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission028_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_03_coefficients]
def admission028_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20115406054283849362833408/3939772175:ℝ),(180869341626926257472536576/11819316525:ℝ),(180700079232885485132054528/11819316525:ℝ),(60176955768810775748018176/11819316525:ℝ)],
![(3019721371621210650901741568/295482913125:ℝ),(226267377138124501133029015552/7387072828125:ℝ),(226055714514376515321256214528/7387072828125:ℝ),(25093790555594093486923579392/2462357609375:ℝ)],
![(1511065917549921948689235968/295482913125:ℝ),(37741346207098530070897885184/2462357609375:ℝ),(37706054997941029037907378176/2462357609375:ℝ),(37670774311275545618259378176/7387072828125:ℝ)]]
theorem admission028_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656767469286687/8262301096345600:ℝ) admission028_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission028_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_04_coefficients]
def admission028_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28825493454592808562589696/9531706875:ℝ),(8042760072291837740590956544/886448739375:ℝ),(8043205650976778808283234304/886448739375:ℝ),(2681216469962072264013119488/886448739375:ℝ)],
![(3833809427953544902213632/635447125:ℝ),(401134952282676457149477945344/22161218484375:ℝ),(401157502140542614646368239616/22161218484375:ℝ),(133726653657746035961590710272/22161218484375:ℝ)],
![(28681647964710364970614784/9531706875:ℝ),(200065950475380513634704031744/22161218484375:ℝ),(6454108415036230465783463936/714878015625:ℝ),(66696241908694229361262723072/22161218484375:ℝ)]]
theorem admission028_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (656470824387596854491/13973630055486586880000:ℝ) admission028_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission028_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_05_coefficients]
def admission028_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(189990989919769934258403601636648288256/25843804976855543990625:ℝ),(1707253822392456909884962309878699261952/77531414930566631971875:ℝ),(1704590402546374848136769014974983962624/77531414930566631971875:ℝ),(37820636641657763316681167333748637696/5168760995371108798125:ℝ)],
![(1901309132671646165102375281362216943616/129219024884277719953125:ℝ),(17085124611390004087365353808317711122432/387657074652833159859375:ℝ),(17058483703578457290788893521224572862464/387657074652833159859375:ℝ),(378485765821241689386503890466234171392/25843804976855543990625:ℝ)],
![(951354183072796493810357273178975502336/129219024884277719953125:ℝ),(231050148633181609133528169160113913856/10477218233860355671875:ℝ),(8535531690846583050105048446349653049344/387657074652833159859375:ℝ),(189382582612952872803098053797490982912/25843804976855543990625:ℝ)]]
theorem admission028_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (137590674573067238513180809/1204408606551612395356160000:ℝ) admission028_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission028_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_06_coefficients]
def admission028_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6551128971633306020155036136568782848/419088729354414226875:ℝ),(98200063547242162986818999096656265216/2095443646772071134375:ℝ),(19626641835426890029762839254738665472/419088729354414226875:ℝ),(32688790488058817262770377859880976384/2095443646772071134375:ℝ)],
![(327237690867187534391304664219731623936/10477218233860355671875:ℝ),(981044688352414828851914413024820854784/10477218233860355671875:ℝ),(980376470593553826915821987842540699648/10477218233860355671875:ℝ),(13062778924333061298208489561498058752/419088729354414226875:ℝ)],
![(163459466576354883887428760805512052736/10477218233860355671875:ℝ),(490044370616204013917819417541539528704/10477218233860355671875:ℝ),(489710424707881576171751006474074062848/10477218233860355671875:ℝ),(32625104133606489228272069947609317376/2095443646772071134375:ℝ)]]
theorem admission028_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (237378874834441297776881183/976547518825631671910400000:ℝ) admission028_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission028_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_07_coefficients]
def admission028_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(208821452179136431322356244204205951104/1419584936733160400390625:ℝ),(58554291817129989895364295146362532418688/132021399116183917236328125:ℝ),(1824268234329034342451047931615455851451264/4092663372601701434326171875:ℝ),(203705810613662876358263793793485201168256/1364221124200567144775390625:ℝ)],
![(2131777117386401906589710387059949479808/7097924683665802001953125:ℝ),(597687419783334926894801587814276161284352/660106995580919586181640625:ℝ),(18618868702603474746589445911405928080261888/20463316863008507171630859375:ℝ),(415764806055951150859538529457424832048896/1364221124200567144775390625:ℝ)],
![(1087669856490719749977929166038919724288/7097924683665802001953125:ℝ),(304915960697684977417980112082463499190912/660106995580919586181640625:ℝ),(9497527530958303034334206253328648823005568/20463316863008507171630859375:ℝ),(42411799088457654900254947132787926176128/272844224840113428955078125:ℝ)]]
theorem admission028_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1631417595149503369705908157845358993/710360243565803368716697600000000000000:ℝ) admission028_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission028_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_08_coefficients]
def admission028_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3672882335637663380470233602736698804992/6548261396162722294921875:ℝ),(10990813380023354104414160387870726488064/6548261396162722294921875:ℝ),(3654329149908237049958223221814613508096/2182753798720907431640625:ℝ),(3645056409056168702310608106699112841216/6548261396162722294921875:ℝ)],
![(36508225906114079119850962037576575148416/32741306980813611474609375:ℝ),(109246824630541073774544611093958356860928/32741306980813611474609375:ℝ),(36323016091505830993934161569072759701504/10913768993604537158203125:ℝ),(289843596698214797472104059005080436736/261930455846508891796875:ℝ)],
![(18143814227925762217499794023893081123456/32741306980813611474609375:ℝ),(54292757730424303252473809154604724420608/32741306980813611474609375:ℝ),(18051370341964645744143045459999692161024/10913768993604537158203125:ℝ),(3601033508399201234491993368427898077184/6548261396162722294921875:ℝ)]]
theorem admission028_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (209607737394934591982280449501/24413687970640791797760000000000:ℝ) admission028_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission028_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_09_coefficients]
def admission028_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10282393555965857721133093567616/69253807763671875:ℝ),(30751483044968505229109590302848/69253807763671875:ℝ),(30655804816620079069361149902848/69253807763671875:ℝ),(10186715336955810467634653167616/69253807763671875:ℝ)],
![(20427054602842724961683114605952/69253807763671875:ℝ),(61090014537638950944548208945536/69253807763671875:ℝ),(60898903939602862748181832073216/69253807763671875:ℝ),(20235944023498335984066737733632/69253807763671875:ℝ)],
![(225434174415778724447279659168/1538973505859375:ℝ),(3370906906244047288701916673056/7694867529296875:ℝ),(3360303338269973146221173358592/7694867529296875:ℝ),(1116567305144077956318154981376/7694867529296875:ℝ)]]
theorem admission028_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1197946756636703205926823/528787270166118400000000000:ℝ) admission028_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission028_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_10_coefficients]
def admission028_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(134355687307970105056978103871709118464/10477218233860355671875:ℝ),(134264523897290521557660166313729327104/3492406077953451890625:ℝ),(134173387089517630977355957163549261824/3492406077953451890625:ℝ),(134082276884651433316065476421168922624/10477218233860355671875:ℝ)],
![(268443402344884748866952858875325579264/10477218233860355671875:ℝ),(268261168632797512891058772068061151232/3492406077953451890625:ℝ),(268078988098526331025187268459940020224/3492406077953451890625:ℝ),(53579372148414240653867669610192437248/2095443646772071134375:ℝ)],
![(5363508601476585752398990200144658432/419088729354414226875:ℝ),(133996644735506991333398605754331824128/3492406077953451890625:ℝ),(5356224040360348001913252451855630336/139696243118138075625:ℝ),(133814583857419769953272871629793263616/10477218233860355671875:ℝ)]]
theorem admission028_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (973629240306179926507123103/4882737594128158359552000000:ℝ) admission028_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission028_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_11_coefficients]
def admission028_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(231558754342892757581824/439453125:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/439453125:ℝ)],
![(463117508685785515163648/439453125:ℝ),(463117508685785515163648/146484375:ℝ),(463117508685785515163648/146484375:ℝ),(463117508685785515163648/439453125:ℝ)],
![(231558754342892757581824/439453125:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/439453125:ℝ)]]
theorem admission028_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission028_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission028_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_12_coefficients]
def admission028_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73334806060409864415346688/274658203125:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/274658203125:ℝ)],
![(146669612120819728830693376/274658203125:ℝ),(146669612120819728830693376/91552734375:ℝ),(146669612120819728830693376/91552734375:ℝ),(146669612120819728830693376/274658203125:ℝ)],
![(73334806060409864415346688/274658203125:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/274658203125:ℝ)]]
theorem admission028_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission028_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission028_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_13_coefficients]
def admission028_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)],
![(576460752303423488/9:ℝ),(576460752303423488/3:ℝ),(576460752303423488/3:ℝ),(576460752303423488/9:ℝ)],
![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)]]
theorem admission028_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission028_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission028_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_14_coefficients]
theorem admission028_all {δ p : ℝ}
 (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission028_00_pos hd hp
 · exact admission028_01_pos hd hp
 · exact admission028_02_pos hd hp
 · exact admission028_03_pos hd hp
 · exact admission028_04_pos hd hp
 · exact admission028_05_pos hd hp
 · exact admission028_06_pos hd hp
 · exact admission028_07_pos hd hp
 · exact admission028_08_pos hd hp
 · exact admission028_09_pos hd hp
 · exact admission028_10_pos hd hp
 · exact admission028_11_pos hd hp
 · exact admission028_12_pos hd hp
 · exact admission028_13_pos hd hp
 · exact admission028_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission028_all
