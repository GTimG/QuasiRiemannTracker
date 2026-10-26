/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission41_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(200493046041676823/52468862730263:ℝ), (601121731536839680/157406588190789:ℝ)]]
theorem admission41_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission41_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission41_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_00_coefficients]
def admission41_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(146712461743157248/52468862730263:ℝ), (439937385229471744/157406588190789:ℝ)]]
theorem admission41_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission41_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission41_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_01_coefficients]
def admission41_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(74643113123470762/52468862730263:ℝ), (74611037739552768/52468862730263:ℝ)]]
theorem admission41_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission41_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission41_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_02_coefficients]
def admission41_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21922138419975799238205440/472219764572367:ℝ), (18782398169502171288838144/202379899102443:ℝ), (65710376430187801307250688/1416659293717101:ℝ)],
![(21912770680103405303435264/472219764572367:ℝ), (131420582313844368348000256/1416659293717101:ℝ), (65682274778934152437694464/1416659293717101:ℝ)]]
theorem admission41_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15659874624951875791/30947394491014643712:ℝ) admission41_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission41_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_03_coefficients]
def admission41_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(54693130181283331793316/7495551818609:ℝ), (765165951053464140029952/52468862730263:ℝ), (382314120037091380297728/52468862730263:ℝ)],
![(383157733024101657766182/52468862730263:ℝ), (765777379587088299462656/52468862730263:ℝ), (382619726847672588435456/52468862730263:ℝ)]]
theorem admission41_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (68363091952280649/859649846972628992:ℝ) admission41_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission41_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_04_coefficients]
def admission41_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1271335935147709707264007903/295137352857729375:ℝ), (508555928270750653524939518/59027470571545875:ℝ), (423814496417928048164210729/98379117619243125:ℝ)],
![(1268152563903849544004134789/295137352857729375:ℝ), (2536414189668692248857549814/295137352857729375:ℝ), (16910152116344956725955217/3935164704769725:ℝ)]]
theorem admission41_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1268152563903849544004134789/27042245938175142537461760000:ℝ) admission41_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission41_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_05_coefficients]
def admission41_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(354473207604029220694604618212633100925435904/8250685723952923479064059359493:ℝ), (1062589038806878607584928302157144820415234048/8250685723952923479064059359493:ℝ), (1061758714927160019660457946820393852913844224/8250685723952923479064059359493:ℝ), (353642883701776004422069740110282133424046080/8250685723952923479064059359493:ℝ)],
![(50676359863151676135561595838506717546528768/1178669389136131925580579908499:ℝ), (1063372763995281965769129433083391551612731392/8250685723952923479064059359493:ℝ), (1062542231059245536705971654432529753860734976/8250685723952923479064059359493:ℝ), (50557712297640238413098065938612175010529280/1178669389136131925580579908499:ℝ)]]
theorem admission41_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10292362529486883560372217910779935/90119489934163132187323699030622208:ℝ) admission41_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission41_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_06_coefficients]
def admission41_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1656761314226456407381356461933705806900/74330502017593905216793327563:ℝ), (3311827471137981613130269279015997431808/74330502017593905216793327563:ℝ), (61298754382583563895831300461025034240/2752981556207181674696049169:ℝ)],
![(1655145875681799762803412233042181353170/74330502017593905216793327563:ℝ), (3308597421313381174034823939810307960832/74330502017593905216793327563:ℝ), (61238953960986549958910539341936721920/2752981556207181674696049169:ℝ)]]
theorem admission41_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (21900756583566623911467983487345/90209699633796929116440139169792:ℝ) admission41_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission41_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_07_coefficients]
def admission41_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(50309898702648924577462713985150058682431788669898527926553/54441285657417411047456050461181640625000000000:ℝ), (4322255642771325631026593616771505927455163534467454981373/1555465304497640315641601441748046875000000000:ℝ), (151628177782060874344905413899761679719564911764921206924469/54441285657417411047456050461181640625000000000:ℝ), (50659128960496644306767978408000478299857498597501779252967/54441285657417411047456050461181640625000000000:ℝ)],
![(12821591855268986952554074805375739027252588033522755073019/13610321414354352761864012615295410156250000000:ℝ), (77103605660740715896056853427026269731626332611740590721241/27220642828708705523728025230590820312500000000:ℝ), (22079328509371499938629005433215382793134948982811619090019/7777326522488201578208007208740234375000000000:ℝ), (51634455637967380058224878863810571313231977767195469354727/54441285657417411047456050461181640625000000000:ℝ)]]
theorem admission41_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (50309898702648924577462713985150058682431788669898527926553/20431812816692981728963272439942424297472000000000000000000000:ℝ) admission41_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission41_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_08_coefficients]
def admission41_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7033038654104484033549133797320358106465518596636/2177651426296696441898242018447265625:ℝ), (3010300983308836346108821478062522416034226236832/311093060899528063128320288349609375:ℝ), (21045101549021612362648619664631568095553443463168/2177651426296696441898242018447265625:ℝ), (1401206664173883520479095899449373993478070992896/435530285259339288379648403689453125:ℝ)],
![(6990127085669113169237320707250429335485989130294/2177651426296696441898242018447265625:ℝ), (20943419230893643152769339701991470020393207365616/2177651426296696441898242018447265625:ℝ), (426866549762861650952109416170929087231556517888/44441865842789723304045755478515625:ℝ), (1392633758812245664581548206423515582640829759488/435530285259339288379648403689453125:ℝ)]]
theorem admission41_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503720248110463159726506663069593389059/4871323780225034172287767515168768000000000:ℝ) admission41_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission41_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_09_coefficients]
def admission41_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64790869346253211499711902099279142912/13834563415206064453125:ℝ), (64689235452627495261221223579511955456/4611521138402021484375:ℝ), (516700894832356360733193798844678144/36892169107216171875:ℝ), (64485998557987022022245905927497580544/13834563415206064453125:ℝ)],
![(2869807516394863344146925382996287488/307434742560134765625:ℝ), (55259229293032267204466603209500663808/1976366202172294921875:ℝ), (386205257066252307617726924627870482432/13834563415206064453125:ℝ), (14281332251974065675480260488466530304/1537173712800673828125:ℝ)],
![(64350272291225540902738623487248013312/13834563415206064453125:ℝ), (192746309098533384328699349437904508928/13834563415206064453125:ℝ), (38488366423065360445353990278236995584/2766912683041212890625:ℝ), (64045795315507602371121725440528482304/13834563415206064453125:ℝ)]]
theorem admission41_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477178359892275947117222290043/211267546391993301073920000000000:ℝ) admission41_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission41_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_10_coefficients]
def admission41_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1358686546458356338917132773233001880524/74330502017593905216793327563:ℝ), (2715986877905890928125519426054699728896/74330502017593905216793327563:ℝ), (1357300533948208614393552613889036779520/74330502017593905216793327563:ℝ)],
![(1357328527477690384346360614181143241006/74330502017593905216793327563:ℝ), (2713271548880456365570950934332719980544/74330502017593905216793327563:ℝ), (1355943223796700253169863921120135086080/74330502017593905216793327563:ℝ)]]
theorem admission41_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (323282056760001242916551571159395/1623774593408344724095922505056256:ℝ) admission41_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
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
def admission41_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission41_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission41_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Finite
