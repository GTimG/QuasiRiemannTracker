/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission07_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission07_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]
def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission07_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission07_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]
def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission07_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission07_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]
def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(15024228448548393226537049344/64169064140007830059431:ℝ), (19867772376349049595899354368/64169064140007830059431:ℝ), (539696578751066167262478336/7129896015556425562159:ℝ)],
![(10160806219276191469669958656/64169064140007830059431:ℝ), (10146992388117517242469958656/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (10737712547960772081955373/10951520279894669663476224:ℝ) admission07_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission07_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]
def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(28364363910483115458805454763339/712989601555642556215900000:ℝ), (39680:ℝ), (0:ℝ)],
![(55251221934411544352797508423667/891237001944553195269875000:ℝ), (9340810657722664164039716204544/111404625243069149408734375:ℝ), (2445877772007727306626250102272/111404625243069149408734375:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (444270767181091092805158709983/2920405407971911910260326400000:ℝ) admission07_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission07_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]
def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(146703580134959667841667535596373/3564948007778212781079500000:ℝ), (110344434623648722656642134443801/1336855502916829792904812500:ℝ), (110530586681230577580039081827801/2673711005833659585809625000:ℝ)],
![(0:ℝ), (692322272986143555586708563673/1336855502916829792904812500:ℝ), (1253204516835834021424078310873/2673711005833659585809625000:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (5496073059822480969539939580408359/59809902755264755922131484672000000:ℝ) admission07_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission07_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]
def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1271070806855342671848126458277669412562607265699243209736/52900606016098693363386369178953088764133895540625:ℝ), (101414130578266229203115566004838575466829820607896372552/2116024240643947734535454767158123550565355821625:ℝ), (1264292647048279514262515235649133280734903049498166104064/52900606016098693363386369178953088764133895540625:ℝ), (0:ℝ)],
![(8252644419744254509702734049303444061993175079848183709472/264503030080493466816931845894765443820669477703125:ℝ), (3668506782740589085293149832309745871032384964235792796832/52900606016098693363386369178953088764133895540625:ℝ), (11961275432057157020938655269808167621604697770249445982208/264503030080493466816931845894765443820669477703125:ℝ), (41585214714928804364398170645690735733146293975970349056/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (98881801244380840329817756609694346228057018562361791/462252548782805862435051878734915950032837197086720000:ℝ) admission07_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission07_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]
def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7874265965626180758488868587304150868853324327822763283/45751875473382653719685508479094563255467152900000:ℝ), (359413208972338363481906981443819897592331084762248752/1429746108543207928740172139971705101733348528125:ℝ), (12625899398089164408805560459694759395892890923125248/158860678727023103193352459996856122414816503125:ℝ)],
![(5256583714009480288109779457294357884376195851618961147/57189844341728317149606885598868204069333941125000:ℝ), (655630707710660150929864242505267159257491243162100416/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (2375576123729015959729692039617047829044951482280727/5205546720527093045439773409176981419288707174400000:ℝ) admission07_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission07_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]
def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (4320642533688239408854770851824002706653466657251237571518230997908500803127/8791965519581280889769238227491525535150828220910770585600000000000000:ℝ), (17323919310825693961581338165210576593486223700376911486382818029029778171429/17583931039162561779538476454983051070301656441821541171200000000000000:ℝ), (115759461884124359610882706908148356500108593131851354197804054206933020869/234452413855500823727179686066440680937355419224287215616000000000000:ℝ)],
![(39441026713445121049196650438967300640717748232656981335194790546344290594207/9768850577312534321965820252768361705723142467678633984000000000000000:ℝ), (1101122674229052651868408420125139340047265477908623830274753433688533037318077/87919655195812808897692382274915255351508282209107705856000000000000000:ℝ), (1137575089028685485947629791364438481398537715756986020877723951405201487173049/87919655195812808897692382274915255351508282209107705856000000000000000:ℝ), (26094550696572008761688291190777903070092456708939299947878943020831617680189/5861310346387520593179492151661017023433885480607180390400000000000000:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (356242571476252682828474769955888238996873662231646543773867245920990694794357/20139308999552666152185951559418192154998243005933665599632409886720000000000000:ℝ) admission07_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission07_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]
def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(222508512692501557020732880499864658644999457570272667397571/28594922170864158574803442799434102034666970562500000:ℝ), (18084266144626913790935552072536025684239142041922674972723/893591317839504955462607587482315688583342830078125:ℝ), (1701673641360637386641224590168432790877747248259460387072/99287924204389439495845287498035076509260314453125:ℝ), (464912504354966518456241296421239011792756538752320520192/99287924204389439495845287498035076509260314453125:ℝ)],
![(107771325422695810600549919624307072859273258983155412364459/35743652713580198218504303499292627543333713203125000:ℝ), (26910710764166515720345077029142320782613471889521722732652/4467956589197524777313037937411578442916714150390625:ℝ), (1493241092639154692743403809682803967454218291321191801856/496439621021947197479226437490175382546301572265625:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1419329810340479424234507451141895002256486191136138087/78083200807906395681596601137654721289330607616000000000:ℝ) admission07_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission07_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]
def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(499342770158416068598564519943404553048/626651016992263965424130859375:ℝ), (428782335976780203305671740034421000648/208883672330754655141376953125:ℝ), (119456472600962195620886545372534524416/69627890776918218380458984375:ℝ), (288105428375615172575128208192952270848/626651016992263965424130859375:ℝ)],
![(708423191993460926931834387114461806016/626651016992263965424130859375:ℝ), (568719676632868865714242742066825719616/208883672330754655141376953125:ℝ), (143101839917834176325370929823111811072/69627890776918218380458984375:ℝ), (290183565062010596919684529321990946816/626651016992263965424130859375:ℝ)],
![(22996241089495786213746964868368313728/69627890776918218380458984375:ℝ), (45945056599395085003037255543199747456/69627890776918218380458984375:ℝ), (22948656506946899466154290674831433728/69627890776918218380458984375:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5059145212598222474719852850012427/1168162163188764764104130560000000000:ℝ) admission07_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission07_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]
def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11006214545060810420936025740487547895841920938046813323/76253125788971089532809180798490938759111921500000:ℝ), (1511934582660838711675160569496477714327741184679191784/7148730542716039643700860699858525508666742640625:ℝ), (53498775366471215545986014618759530501823746859125248/794303393635115515966762299984280612074082515625:ℝ)],
![(1455599600828126988256123680733323613536713073849025111/19063281447242772383202295199622734689777980375000:ℝ), (544474498591642520097124116931359894266273642837130784/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (29221617358954914148386533249015437210038999686029061/78083200807906395681596601137654721289330607616000000:ℝ) admission07_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission07_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]
def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission07_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission07_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]
def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission07_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission07_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]
def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission07_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]
theorem admission07_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission07_00_pos hδ hp
 · exact admission07_01_pos hδ hp
 · exact admission07_02_pos hδ hp
 · exact admission07_03_pos hδ hp
 · exact admission07_04_pos hδ hp
 · exact admission07_05_pos hδ hp
 · exact admission07_06_pos hδ hp
 · exact admission07_07_pos hδ hp
 · exact admission07_08_pos hδ hp
 · exact admission07_09_pos hδ hp
 · exact admission07_10_pos hδ hp
 · exact admission07_11_pos hδ hp
 · exact admission07_12_pos hδ hp
 · exact admission07_13_pos hδ hp
 · exact admission07_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
