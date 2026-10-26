/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission14_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission14_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]
def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission14_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission14_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]
def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission14_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission14_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]
def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(33759441005225793080537984/9190091093611410197319:ℝ), (44390312662346679143619968/9190091093611410197319:ℝ), (3627805244708562021027328/3063363697870470065773:ℝ)],
![(1752204989749094780290016/706930084123954630563:ℝ), (22513493585883192143770208/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (738436625719051859314503/784221106654840336837888:ℝ) admission14_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission14_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]
def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(250160757349597312605412092/382920462233808758221625:ℝ), (640:ℝ), (0:ℝ)],
![(393550804425303008447431919/382920462233808758221625:ℝ), (2595432845187855729742152224/1914602311169043791108125:ℝ), (654410046041129151058746112/1914602311169043791108125:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (7668867727044482238969681/49013819165927521052368000:ℝ) admission14_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission14_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]
def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1288636893088537120480571473/1914602311169043791108125:ℝ), (2649404738839147619109760866/1914602311169043791108125:ℝ), (1348457614159874361911328933/1914602311169043791108125:ℝ)],
![(0:ℝ), (140355479631099623747130512/1914602311169043791108125:ℝ), (127429736460826680193377029/1914602311169043791108125:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (17441177975527522528381039761/250950754129548907788124160000:ℝ) admission14_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission14_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]
def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1293391032479831271904837947572578308875725964623232/26041147078570027685496535783188561375392892975:ℝ), (4221103765773131406418622698382104614519809317697152/43401911797616712809160892971980935625654821625:ℝ), (6199570201611934118865355491490886542380798129975296/130205735392850138427482678915942806876964464875:ℝ), (0:ℝ)],
![(8454506391946297364562791508835804088149649769685216/130205735392850138427482678915942806876964464875:ℝ), (30679959000712632783683483110244292068231547560312864/217009558988083564045804464859904678128274108125:ℝ), (58679153134497101581996531473235075295724513206582272/651028676964250692137413394579714034384822324375:ℝ), (592995616130618979553882315472802150331874624937984/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (248086823551465661389479734349422206237573573587/1111088942018987847914518860082711952016763433600:ℝ) admission14_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission14_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]
def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9335444582001730806006595481787500846473409232988/3519073929536490227769802132863319104782823375:ℝ), (13610458266209939704405834138708982043948036490112/3519073929536490227769802132863319104782823375:ℝ), (1453804708363719187018652172367788426907548024576/1173024643178830075923267377621106368260941125:ℝ)],
![(4654271356109179250632383602668726850809644541879/3519073929536490227769802132863319104782823375:ℝ), (22867126146414957867160845167492676578852144031712/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (247979709369332309244066972109609744693865613567/600588617307560998872712897342006460549601856000:ℝ) admission14_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission14_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]
def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (4443773406622090933772025457955004038860807495321901714561477157063013/3148814049909465409769768995216458831886296578785280000000000000000:ℝ), (380554151322976651153527514177766167405643690152300974772997785991458667/132250190096197547210330297799091270939224456308981760000000000000000:ℝ), (193262628945424311166604839843616504458855078329253845936542785394812121/132250190096197547210330297799091270939224456308981760000000000000000:ℝ)],
![(8375757423374601486045758374421218362519326620946839342907518741606038717/881667933974650314735535318660608472928163042059878400000000000000000:ℝ), (5040009983702915267733842226405158720223957526096874081016743394483848849/176333586794930062947107063732121694585632608411975680000000000000000:ℝ), (19019991056024213494517468907810632683298401874606012767571925645837942031/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (1279668645669450724203053382566398782889244791620069274521838786545607577/132250190096197547210330297799091270939224456308981760000000000000000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (99447180558074825211304720712432834597509793171556540618028634685176323/14223012854390814283448133573844095232448022922938139279360000000000000000:ℝ) admission14_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission14_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]
def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6408904351765550225057898425084256744115059521022857/439884241192061278471225266607914888097852921875:ℝ), (1124351686536493145297574894702230284322145485641139/29325616079470751898081684440527659206523528125:ℝ), (14531064093060632050240405956324248120673009708493024/439884241192061278471225266607914888097852921875:ℝ), (1358808581704137827642317964678963971561749882522432/146628080397353759490408422202638296032617640625:ℝ)],
![(34878457575755694166243179179047324122711314620098349/8797684823841225569424505332158297761957058437500:ℝ), (4636893024326453271074425896563326663328112861734719/586512321589415037961633688810553184130470562500:ℝ), (8659638306033727192733869418250977054473440387470984/2199421205960306392356126333039574440489264609375:ℝ), (0:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (117552233959862692889806758969706299811976550203181/9609417876920975981963406357472103368793629696000000:ℝ) admission14_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission14_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]
def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3458166312083730680502976000256/17231420800521394119973125:ℝ), (9068771741422282909515298855168/17231420800521394119973125:ℝ), (7781412631210156029123171770368/17231420800521394119973125:ℝ), (2171451189267966040110848915456/17231420800521394119973125:ℝ)],
![(4601652250271070232128518467712/17231420800521394119973125:ℝ), (881189425749123051942012706432/1325493907732414932305625:ℝ), (702667046547794044326385318912/1325493907732414932305625:ℝ), (2282213694186153837125362429952/17231420800521394119973125:ℝ)],
![(112978562331642410968999303184/1914602311169043791108125:ℝ), (51872217650637842102297374064/441831302577471644101875:ℝ), (67033295419040318244573590656/1148761386701426274664875:ℝ), (0:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (449109907720501906136644953/501901508259097815576248320000:ℝ) admission14_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission14_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]
def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(39620138568666050764473329522418851211891400004788/17595369647682451138849010664316595523914116875:ℝ), (19263953768850266749081201314456509588880609100672/5865123215894150379616336888105531841304705625:ℝ), (6196043933552235389759585684167182863983575864576/5865123215894150379616336888105531841304705625:ℝ)],
![(3924228154031189718618903817339789387256031780809/3519073929536490227769802132863319104782823375:ℝ), (6411094311583312055069102747891488703025284400736/5865123215894150379616336888105531841304705625:ℝ), (0:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1029156144842523647962100805635887417100082866837/3002943086537804994363564486710032302748009280000:ℝ) admission14_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission14_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_11_coefficients]
def admission14_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission14_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission14_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_12_coefficients]
def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission14_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission14_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_13_coefficients]
def admission14_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission14_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission14_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission14_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission14_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission14_14_coefficients]
theorem admission14_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission14_00_pos hδ hp
 · exact admission14_01_pos hδ hp
 · exact admission14_02_pos hδ hp
 · exact admission14_03_pos hδ hp
 · exact admission14_04_pos hδ hp
 · exact admission14_05_pos hδ hp
 · exact admission14_06_pos hδ hp
 · exact admission14_07_pos hδ hp
 · exact admission14_08_pos hδ hp
 · exact admission14_09_pos hδ hp
 · exact admission14_10_pos hδ hp
 · exact admission14_11_pos hδ hp
 · exact admission14_12_pos hδ hp
 · exact admission14_13_pos hδ hp
 · exact admission14_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
