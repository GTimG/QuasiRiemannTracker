/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission06_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(16968807097233225562159/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission06_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (25810568996105327810795/14259792031112851124318:ℝ) admission06_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission06_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_00_coefficients]
def admission06_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9838911081676800000000/7129896015556425562159:ℝ), (0:ℝ)]]
theorem admission06_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (9340336490274451124318/7129896015556425562159:ℝ) admission06_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission06_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_01_coefficients]
def admission06_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2352790992103833166404605269/3564948007778212781079500000:ℝ), (0:ℝ)]]
theorem admission06_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (4777105023452592395754394731/7129896015556425562159000000:ℝ) admission06_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission06_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_02_coefficients]
def admission06_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(15030381469060999478041835008/64169064140007830059431:ℝ), (19874013947061390938604140032/64169064140007830059431:ℝ), (539696578751066167262478336/7129896015556425562159:ℝ)],
![(10166959239788797721174744320/64169064140007830059431:ℝ), (10153233958829858585174744320/64169064140007830059431:ℝ), (0:ℝ)]]
theorem admission06_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (43099082284395566217999785/43806081119578678653904896:ℝ) admission06_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission06_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_03_coefficients]
def admission06_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(70453420035716125494452258605713/1782474003889106390539750000:ℝ), (39424:ℝ), (0:ℝ)],
![(220089908256662851106067277089399/3564948007778212781079500000:ℝ), (9312291073660438461791080204544/111404625243069149408734375:ℝ), (2445877772007727306626250102272/111404625243069149408734375:ℝ)]]
theorem admission06_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1103511260417548843419265182861/7301013519929779775650816000000:ℝ) admission06_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission06_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_04_coefficients]
def admission06_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(146703580134959667841667535596373/3564948007778212781079500000:ℝ), (439875447492366203505787634506597/5347422011667319171619250000:ℝ), (439121134977622281029613734589797/10694844023334638343238500000:ℝ)],
![(0:ℝ), (253399617943177420313186197217/1069484402333463834323850000:ℝ), (402321264008661359030744104417/2138968804666927668647700000:ℝ)]]
theorem admission06_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4484880595938960576336952185684511/47847922204211804737705187737600000:ℝ) admission06_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission06_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_05_coefficients]
def admission06_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6329398310980968405176448212529333171624480806062914095408/264503030080493466816931845894765443820669477703125:ℝ), (505000108695160018540275815073166553420811200702045051056/10580121203219738672677273835790617752826779108125:ℝ), (6295655024941026710880250123851414509719082411488212180992/264503030080493466816931845894765443820669477703125:ℝ), (0:ℝ)],
![(329067547857940382225541998817777206832184782296595270248/10580121203219738672677273835790617752826779108125:ℝ), (3658154061759733447916639757554614251465695452548608738312/52900606016098693363386369178953088764133895540625:ℝ), (2387093444351357232101265843082783145529852986849365528576/52900606016098693363386369178953088764133895540625:ℝ), (41585214714928804364398170645690735733146293975970349056/5877845112899854818154041019883676529348210615625:ℝ)]]
theorem admission06_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (245776788067180894009665609115288048257526897580130349/1155631371957014656087629696837289875082092992716800000:ℝ) admission06_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission06_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_06_coefficients]
def admission06_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19767514833487744841884780490951811810471348471225715561/114379688683456634299213771197736408138667882250000:ℝ), (1802170436184698687096705130560403471035459421379114784/7148730542716039643700860699858525508666742640625:ℝ), (12625899398089164408805560459694759395892890923125248/158860678727023103193352459996856122414816503125:ℝ)],
![(4238006938976501408752867174912060162836171741962691859/45751875473382653719685508479094563255467152900000:ℝ), (132147019806733404123406893169314228466259048145994288/1429746108543207928740172139971705101733348528125:ℝ), (0:ℝ)]]
theorem admission06_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1915256874840348507325322647857343059403023167375119/4164437376421674436351818727341585135430965739520000:ℝ) admission06_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission06_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_07_coefficients]
def admission06_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (12549474426932601159249139690864457846295764379534854301467632755233206197013/21979913798953202224423095568728813837877070552276926464000000000000000:ℝ), (10057182534258972199649315213978440183570372352852159003636357363639214058483/8791965519581280889769238227491525535150828220910770585600000000000000:ℝ), (8395096064253204620934586045024737848359054718118641407820335043304019299463/14653275865968801482948730379152542558584713701517950976000000000000000:ℝ)],
![(39441026713445121049196650438967300640717748232656981335194790546344290594207/9768850577312534321965820252768361705723142467678633984000000000000000:ℝ), (1108114146599900662416857270370357144365913868854250871765441654730380854074859/87919655195812808897692382274915255351508282209107705856000000000000000:ℝ), (575763658908573369068108126339085000133405160391811526741086717448222368450367/43959827597906404448846191137457627675754141104553852928000000000000000:ℝ), (66396506437925454049475144840210223242333409419726181640154939207449749695623/14653275865968801482948730379152542558584713701517950976000000000000000:ℝ)]]
theorem admission06_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (4275547523242655490634549697473250134577690910848625381164964016553834377255531/251741362494408326902324394492727401937478037574170819995405123584000000000000000:ℝ) admission06_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission06_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_08_coefficients]
def admission06_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(562262909481540270614070829827417059015666061983381737720697/71487305427160396437008606998585255086667426406250000:ℝ), (91168762594182142197417868679350669467755815798141756768658/4467956589197524777313037937411578442916714150390625:ℝ), (8549807755642721396825222645682938764431906109988604265984/496439621021947197479226437490175382546301572265625:ℝ), (464912504354966518456241296421239011792756538752320520192/99287924204389439495845287498035076509260314453125:ℝ)],
![(3544548457530847988213415485221912929947422976384174303291/1143796886834566342992137711977364081386678822500000:ℝ), (5531628527042817792617037069162572365834715495610020927539/893591317839504955462607587482315688583342830078125:ℝ), (306936128295737831272500700904715755499477632002498826496/99287924204389439495845287498035076509260314453125:ℝ), (0:ℝ)]]
theorem admission06_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1186540661494975075839097314280107201831248631238633183/62466560646325116545277280910123777031464486092800000000:ℝ) admission06_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission06_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_09_coefficients]
def admission06_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(499385438076589323879183781167057152864/626651016992263965424130859375:ℝ), (85483946412790632845637006888135906976/41776734466150931028275390625:ℝ), (355607172849766815321747629363285456896/208883672330754655141376953125:ℝ), (283949155002824323886015565934874918912/626651016992263965424130859375:ℝ)],
![(142547406377794600462433455254650372896/125330203398452793084826171875:ℝ), (114039762104604320471637560336990748256/41776734466150931028275390625:ℝ), (85592258941362694664853867723034863616/41776734466150931028275390625:ℝ), (57205458337843949646114377412782718976/125330203398452793084826171875:ℝ)],
![(2816497890437345280312484156672697096/8355346893230186205655078125:ℝ), (1875692101348867076407247091219583064/2785115631076728735218359375:ℝ), (2810559577090856571501257116986052096/8355346893230186205655078125:ℝ), (0:ℝ)]]
theorem admission06_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3413698534436650941300642474516347/747623784440809449026643558400000000:ℝ) admission06_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission06_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_10_coefficients]
def admission06_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5527074125813938098216449677320443204680954941110751197/38126562894485544766404590399245469379555960750000:ℝ), (303283342026710604685089751784784797071276256611399664/1429746108543207928740172139971705101733348528125:ℝ), (53498775366471215545986014618759530501823746859125248/794303393635115515966762299984280612074082515625:ℝ)],
![(1174066421975914745704273667417326593533368247914157903/15250625157794217906561836159698187751822384300000:ℝ), (109791325212871366369482461271761233058982748242987464/1429746108543207928740172139971705101733348528125:ℝ), (0:ℝ)]]
theorem admission06_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (23565375519311681685863083681856426242451673858874861/62466560646325116545277280910123777031464486092800000:ℝ) admission06_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission06_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_11_coefficients]
def admission06_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission06_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission06_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_12_coefficients]
def admission06_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (267590012974094731788830531/24597277704192000000000000000:ℝ) admission06_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission06_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_13_coefficients]
def admission06_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission06_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission06_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_14_coefficients]
theorem admission06_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission06_00_pos hδ hp
 · exact admission06_01_pos hδ hp
 · exact admission06_02_pos hδ hp
 · exact admission06_03_pos hδ hp
 · exact admission06_04_pos hδ hp
 · exact admission06_05_pos hδ hp
 · exact admission06_06_pos hδ hp
 · exact admission06_07_pos hδ hp
 · exact admission06_08_pos hδ hp
 · exact admission06_09_pos hδ hp
 · exact admission06_10_pos hδ hp
 · exact admission06_11_pos hδ hp
 · exact admission06_12_pos hδ hp
 · exact admission06_13_pos hδ hp
 · exact admission06_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
