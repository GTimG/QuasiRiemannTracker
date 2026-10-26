/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission02_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission02_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission02_00_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission02_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_00_coefficients]
def admission02_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission02_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission02_01_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission02_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_01_coefficients]
def admission02_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission02_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission02_02_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission02_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_02_coefficients]
def admission02_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(237205785555000530042026432/64169064140007830059431:ℝ), (311506713346637568213312448/64169064140007830059431:ℝ), (8432759042985408863476224/7129896015556425562159:ℝ)],
![(160619308028824273632642208/64169064140007830059431:ℝ), (158936854233857540832642208/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission02_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (5442972320256624986066833/5475760139947334831738112:ℝ) admission02_03_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission02_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_03_coefficients]
def admission02_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1047880145169059779448537447421/1782474003889106390539750000:ℝ), (576:ℝ), (0:ℝ)],
![(3435130303582989854371148551247/3564948007778212781079500000:ℝ), (144167692523027521172580815696/111404625243069149408734375:ℝ), (38216840187620739166035157848/111404625243069149408734375:ℝ)]]
theorem admission02_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (128981835633219994685368657737/912626689991222471956352000000:ℝ) admission02_04_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission02_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_04_coefficients]
def admission02_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3630578377681502179749275680841/5347422011667319171619250000:ℝ), (442239305295933904695557430188/334213875729207448226203125:ℝ), (71144129013277827837639976248/111404625243069149408734375:ℝ)],
![(53219926663152393625477462867/10694844023334638343238500000:ℝ), (146568515815883078738174954/13368555029168297929048125:ℝ), (0:ℝ)]]
theorem admission02_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (181104607940579094781366689233/1825253379982444943912704000000:ℝ) admission02_05_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission02_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_05_coefficients]
def admission02_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2460300289689669238027122171710810765218413083439435542/52900606016098693363386369178953088764133895540625:ℝ), (24087719608529873565729060534875243896835700673958952686/264503030080493466816931845894765443820669477703125:ℝ), (11792134613158824426869120273259561660478035256761774976/264503030080493466816931845894765443820669477703125:ℝ), (0:ℝ)],
![(3275686395245123239335486205274525608061060055511061993/52900606016098693363386369178953088764133895540625:ℝ), (35877475754521389544745581758809141284153895584821534413/264503030080493466816931845894765443820669477703125:ℝ), (23160239435264987459393263773888984464419856301247993408/264503030080493466816931845894765443820669477703125:ℝ), (81221122490095321024215177042364718228801355421817088/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission02_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (28937454703683603232609723128226234391421301165298633/144453921494626832010953712104661234385261624089600000:ℝ) admission02_06_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission02_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_06_coefficients]
def admission02_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(173021983780006966700044714123043359229016980711543/61002500631176871626247344638792751007289537200:ℝ), (28956474209605740374506365062085051590210928079028516/7148730542716039643700860699858525508666742640625:ℝ), (197279678095143193887586882182730615560826420673832/158860678727023103193352459996856122414816503125:ℝ)],
![(22931521394508425722839385052794850672777350697382809/15250625157794217906561836159698187751822384300000:ℝ), (10563254265666994213727267747976298305511050522399758/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission02_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1224778001507347328718768560217785904940130695016707/2602773360263546522719886704588490709644353587200000:ℝ) admission02_07_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission02_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_07_coefficients]
def admission02_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (158187228430373063971396080797011634428228538766317578072505762421009698251/58613103463875205931794921516610170234338854806071803904000000000000000:ℝ), (1894164037755685977618711641374282914077283271261633875848621258070482200883/351678620783251235590769529099661021406033128836430823424000000000000000:ℝ), (943473849300158933790247158898535692271702204116563760549207919870824011377/351678620783251235590769529099661021406033128836430823424000000000000000:ℝ)],
![(234619266708161638978907311010332628040824378238943415800105127228286191061/26050268206166758191908854007382297881928379913809690624000000000000000:ℝ), (6658106838343547913358871510146208641714028112136206097711733096847149711689/234452413855500823727179686066440680937355419224287215616000000000000000:ℝ), (10483743980831878955131792861012670631327940190310552925007361612742816111907/351678620783251235590769529099661021406033128836430823424000000000000000:ℝ), (3662289960566045625753085852422855320114250080754417208939892490065155123697/351678620783251235590769529099661021406033128836430823424000000000000000:ℝ)]]
theorem admission02_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (450874975994697536358621993575674807261377149619590810116578220873592150487/54631372069099029275678036999289800767681865793005820311502848000000000000000:ℝ) admission02_08_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission02_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_08_coefficients]
def admission02_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1226037258333613332306998431206107219934875411294670321017/71487305427160396437008606998585255086667426406250000:ℝ), (154683372349859432468212454736082750997180778404285037553/3574365271358019821850430349929262754333371320312500:ℝ), (17508209461011847720734803894708372782936728118948491352/496439621021947197479226437490175382546301572265625:ℝ), (908032235068293981359846282072732444907727614750626016/99287924204389439495845287498035076509260314453125:ℝ)],
![(951924467810828775690111215100958602031787374310830164067/142974610854320792874017213997170510173334852812500000:ℝ), (94279986559986276814840487958787736218256360694360816107/7148730542716039643700860699858525508666742640625000:ℝ), (3240232984369712006288676931730279702396284699387502196/496439621021947197479226437490175382546301572265625:ℝ), (0:ℝ)]]
theorem admission02_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (837356938226718553245982108987425501193392291392375827/39041600403953197840798300568827360644665303808000000000:ℝ) admission02_09_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission02_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_09_coefficients]
def admission02_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25128661396616285578248042099964924/125330203398452793084826171875:ℝ), (104281908357561123139553310116732036/208883672330754655141376953125:ℝ), (83303747156141830951363815410521952/208883672330754655141376953125:ℝ), (62727875507735304542671726381194368/626651016992263965424130859375:ℝ)],
![(185702311943021032546939252303349924/626651016992263965424130859375:ℝ), (9690647531241718751499699250220564/13925578155383643676091796875:ℝ), (35235926891685750614464500560324832/69627890776918218380458984375:ℝ), (66786736223351367715633291086348032/626651016992263965424130859375:ℝ)],
![(6157975354433153238502543199378987/69627890776918218380458984375:ℝ), (36638741321286200379545123066578297/208883672330754655141376953125:ℝ), (18157739312989680056037493468441336/208883672330754655141376953125:ℝ), (0:ℝ)]]
theorem admission02_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1533599453857209522203846311873907/292040540797191191026032640000000000:ℝ) admission02_10_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission02_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_10_coefficients]
def admission02_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(272967735509178514112507742680961802634192419313934923/114379688683456634299213771197736408138667882250000:ℝ), (4878868702689675440401033291244958423883694583859574/1429746108543207928740172139971705101733348528125:ℝ), (835918365101112742906031478418117664090996044673832/794303393635115515966762299984280612074082515625:ℝ)],
![(11475577256161598431421075243439430650085355992652881/9150375094676530743937101695818912651093430580000:ℝ), (8787547007539058860910576166267890287200531817943077/7148730542716039643700860699858525508666742640625:ℝ), (0:ℝ)]]
theorem admission02_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (15081012759846832992077909331117909791070685118143561/39041600403953197840798300568827360644665303808000000:ℝ) admission02_11_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission02_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_11_coefficients]
def admission02_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission02_12_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission02_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_12_coefficients]
def admission02_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission02_13_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission02_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_13_coefficients]
def admission02_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission02_14_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission02_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_14_coefficients]
theorem admission02_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission02_00_pos hδ hp
 · exact admission02_01_pos hδ hp
 · exact admission02_02_pos hδ hp
 · exact admission02_03_pos hδ hp
 · exact admission02_04_pos hδ hp
 · exact admission02_05_pos hδ hp
 · exact admission02_06_pos hδ hp
 · exact admission02_07_pos hδ hp
 · exact admission02_08_pos hδ hp
 · exact admission02_09_pos hδ hp
 · exact admission02_10_pos hδ hp
 · exact admission02_11_pos hδ hp
 · exact admission02_12_pos hδ hp
 · exact admission02_13_pos hδ hp
 · exact admission02_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
