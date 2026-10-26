/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(7272431647950470065773/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11107750539272350328865/6126727395740940131546:ℝ) admission13_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission13_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]
def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(4209067950080000000000/3063363697870470065773:ℝ), (0:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (4022193420700940131546/3063363697870470065773:ℝ) admission13_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission13_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]
def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1272915379989926835893023/1914602311169043791108125:ℝ), (0:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2556289242348160746323227/3829204622338087582216250:ℝ) admission13_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission13_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]
def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(134740023879467562069523520/9190091093611410197319:ℝ), (177781225865810946321851456/9190091093611410197319:ℝ), (14511220978834248084109312/3063363697870470065773:ℝ)],
![(90999012930390828069824000/9190091093611410197319:ℝ), (90493924776381228069824000/9190091093611410197319:ℝ), (0:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (189923324268691522476615/196055276663710084209472:ℝ) admission13_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission13_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]
def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(371422389884426188400439069/147277100859157214700625:ℝ), (2496:ℝ), (0:ℝ)],
![(7569938715956865782907505368/1914602311169043791108125:ℝ), (10136662284921785313706768896/1914602311169043791108125:ℝ), (2617640184164516604234984448/1914602311169043791108125:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (23006603181133446716909043/150811751279776987853440000:ℝ) admission13_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission13_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]
def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5018714029995632797561153731/1914602311169043791108125:ℝ), (10141492913497635683320098164/1914602311169043791108125:ℝ), (5098773931900067419159116536/1914602311169043791108125:ℝ)],
![(0:ℝ), (47856576857069793144605968/382920462233808758221625:ℝ), (42932484220775338457461784/382920462233808758221625:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4281210482018638370901457143/50190150825909781557624832000:ℝ) admission13_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission13_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]
def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(83073509172435258853992634881332877599487423158428352/217009558988083564045804464859904678128274108125:ℝ), (493186000829300795159058572967093134846949536936310848/651028676964250692137413394579714034384822324375:ℝ), (6594508390871325868206324875178845362694250471919616/17595369647682451138849010664316595523914116875:ℝ), (0:ℝ)],
![(4326104540653054993638933481356495697906846854058496/8680382359523342561832178594396187125130964325:ℝ), (28589098232715523271165168605310820507435813969540608/26041147078570027685496535783188561375392892975:ℝ), (92292245974300039478802370645968847162941358035337216/130205735392850138427482678915942806876964464875:ℝ), (4743964929044951836431058523782417202654996999503872/43401911797616712809160892971980935625654821625:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9706311461542042356621468799462922618277891200949/44443557680759513916580754403308478080670537344000:ℝ) admission13_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission13_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]
def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(63004902222978421503154922733008933501785072420731/5865123215894150379616336888105531841304705625:ℝ), (275351213191645124176734203484216802546283925165376/17595369647682451138849010664316595523914116875:ℝ), (5815218833454876748074608689471153707630192098304/1173024643178830075923267377621106368260941125:ℝ)],
![(6574440315292131884829706712790924698835675667944/1173024643178830075923267377621106368260941125:ℝ), (19550520064110498329175684418009005930010993370624/3519073929536490227769802132863319104782823375:ℝ), (0:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (13250824164773482173347090112727238266084422099/30029430865378049943635644867100323027480092800:ℝ) admission13_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission13_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]
def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (11136024226629637721565349512278054757122077026134754048520858977594691871/661250950480987736051651488995456354696122281544908800000000000000000:ℝ), (44681043694124667863838496484453923968913508657572962788865320614978050877/1322501900961975472103302977990912709392244563089817600000000000000000:ℝ), (1493084064968440951048139610696469622335598534228178212249238662652577809/88166793397465031473553531866060847292816304205987840000000000000000:ℝ)],
![(891388828077251553835736682556198502152203773425797961667979681984197247/12595256199637861639079075980865835327545186315141120000000000000000:ℝ), (59252310389191334953391078858938527680189057767171442147366896371321420497/264500380192395094420660595598182541878448912617963520000000000000000:ℝ), (62397505619256495867642194461312442430144348328645375473751266896023739033/264500380192395094420660595598182541878448912617963520000000000000000:ℝ), (7287249487496581820575865171884641773964343671779193831370817335456820241/88166793397465031473553531866060847292816304205987840000000000000000:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3670383253703279969072360453673408859050629350080866067565261307899553931/845253335346654105987774795245591945242625362277466562887680000000000000000:ℝ) admission13_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission13_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]
def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(35645784155946661990713753678880817255617447112815931/293256160794707518980816844405276592065235281250:ℝ), (1393885983703229015310592607985391739579407991800210523/4398842411920612784712252666079148880978529218750:ℝ), (592639747652758205267871646064237464141371842105659744/2199421205960306392356126333039574440489264609375:ℝ), (10870468653633102621138543717431711772493999060179456/146628080397353759490408422202638296032617640625:ℝ)],
![(6180175684724456716182167029122477151215669320774596/146628080397353759490408422202638296032617640625:ℝ), (36958287112627759734407401147399693096043819493989876/439884241192061278471225266607914888097852921875:ℝ), (18414294861787132811676354193708579012938086126329088/439884241192061278471225266607914888097852921875:ℝ), (0:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (9062319311362207678027020678201636798946678797321/480470893846048799098170317873605168439681484800000:ℝ) admission13_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission13_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]
def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54455101536976131001873524072224/17231420800521394119973125:ℝ), (46935715285522022826352631567456/5743806933507131373324375:ℝ), (13159390496418468841445514325504/1914602311169043791108125:ℝ), (32084918910250949513425258299392/17231420800521394119973125:ℝ)],
![(15167349241205101740489421090304/3446284160104278823994625:ℝ), (4095519957109056201256543657472/382920462233808758221625:ℝ), (28285529542357369354327745110016/3446284160104278823994625:ℝ), (507246445378406952146790252544/265098781546482986461125:ℝ)],
![(817310777574465174138480674816/689256832020855764798925:ℝ), (542777205379296064721493563392/229752277340285254932975:ℝ), (12475658470461616332707692544/10603951261859319458445:ℝ), (0:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3773472021825627372898801/1254753770647744538940620800:ℝ) admission13_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission13_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]
def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(160440916917461137430455187804483983930490031845519/17595369647682451138849010664316595523914116875:ℝ), (77977358255726034825310659654287348671298782344256/5865123215894150379616336888105531841304705625:ℝ), (24784175734208941559038342736668731455934303458304/5865123215894150379616336888105531841304705625:ℝ)],
![(16659041789298693001552264923313493681072417810248/3519073929536490227769802132863319104782823375:ℝ), (5497492721396636775649623956897715088730765897216/1173024643178830075923267377621106368260941125:ℝ), (0:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (2203532069377677812871691900744443182574780793/6005886173075609988727128973420064605496018560:ℝ) admission13_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission13_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]
def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission13_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission13_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]
def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission13_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission13_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]
def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission13_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission13_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission13_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]
theorem admission13_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission13_00_pos hδ hp
 · exact admission13_01_pos hδ hp
 · exact admission13_02_pos hδ hp
 · exact admission13_03_pos hδ hp
 · exact admission13_04_pos hδ hp
 · exact admission13_05_pos hδ hp
 · exact admission13_06_pos hδ hp
 · exact admission13_07_pos hδ hp
 · exact admission13_08_pos hδ hp
 · exact admission13_09_pos hδ hp
 · exact admission13_10_pos hδ hp
 · exact admission13_11_pos hδ hp
 · exact admission13_12_pos hδ hp
 · exact admission13_13_pos hδ hp
 · exact admission13_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
