/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(391013200118207/3198839752287:ℝ), (383814360365920/3198839752287:ℝ)]]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (11994198761435/12795359009148:ℝ) admission09_00_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 0 := by
 rw [admission09_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]
def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(285451488292736/3198839752287:ℝ), (281451488292736/3198839752287:ℝ)]]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2198839752287/3198839752287:ℝ) admission09_01_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 1 := by
 rw [admission09_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]
def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(145045152528932/3198839752287:ℝ), (143119972154176/3198839752287:ℝ)]]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2236249564909/6397679504574:ℝ) admission09_02_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 2 := by
 rw [admission09_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]
def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21917613607427737984/28789557770583:ℝ), (4808553657416293760/3198839752287:ℝ), (21360701309318905856/28789557770583:ℝ)],
![(21356650499052524800/28789557770583:ℝ), (4683989737400175872/3198839752287:ℝ), (20800625137549058048/28789557770583:ℝ)]]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2539138810735969/4913417859512832:ℝ) admission09_03_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 3 := by
 rw [admission09_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]
def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(354129030801785972/3198839752287:ℝ), (692965893189008768/3198839752287:ℝ), (338908094061088768/3198839752287:ℝ)],
![(372859763906187992/3198839752287:ℝ), (243338019182923520/1066279917429:ℝ), (119075816832274432/1066279917429:ℝ)]]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (82741233901633/1091870635447296:ℝ) admission09_04_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 4 := by
 rw [admission09_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]
def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(54938831219055701656/666424948393125:ℝ), (988508183950017512144/5997824535538125:ℝ), (98798898168003499948/1199564907107625:ℝ)],
![(47791579396773665668/666424948393125:ℝ), (860676894002911914248/5997824535538125:ℝ), (430486731830247558236/5997824535538125:ℝ)]]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (11947894849193416417/232932402228756480000:ℝ) admission09_05_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 5 := by
 rw [admission09_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]
def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(71939674045125756944797591359367424/3407447728350247988736212877:ℝ), (70214369057858778134019207804920576/1135815909450082662912070959:ℝ), (205517752738256797298658170460422144/3407447728350247988736212877:ℝ), (66814185365842519193422138405027840/3407447728350247988736212877:ℝ)],
![(75371592001371319521602718210285056/3407447728350247988736212877:ℝ), (73617541526783939350822850516109824/1135815909450082662912070959:ℝ), (215641929164360977987321325128810496/3407447728350247988736212877:ℝ), (70160758713201543655831491790766080/3407447728350247988736212877:ℝ)]]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (63718972555010337060377252965/581537745638442323410980331008:ℝ) admission09_06_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 6 := by
 rw [admission09_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]
def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(35807257797974544272501696377492/92093181847303999695573321:ℝ), (70519711423956017337609363590528/92093181847303999695573321:ℝ), (34716708358940192762106163773440/92093181847303999695573321:ℝ)],
![(33797753272801192512936245137048/92093181847303999695573321:ℝ), (66532797609921814277327146003712/92093181847303999695573321:ℝ), (32739174338494232414897584824320/92093181847303999695573321:ℝ)]]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (3996481242491971730334177835/15717236368606549281377846784:ℝ) admission09_07_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 7 := by
 rw [admission09_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]
def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10843169821913823550658585353339747515016550749/355297769472623455615637812500000000000000:ℝ), (724447627470128559488868386245780773533483587003/3197679925253611100540740312500000000000000:ℝ), (10391616223901784763315448748963200852700675258809/28779119327282499904866662812500000000000000:ℝ), (4749673454711912127978018064813589244428163586451/28779119327282499904866662812500000000000000:ℝ)],
![(211490709136242844193906514589697348952182967823/355297769472623455615637812500000000000000:ℝ), (6075339113937088129648978719466308635658100662781/3197679925253611100540740312500000000000000:ℝ), (57955089741298901368814241944789884409684823163577/28779119327282499904866662812500000000000000:ℝ), (20407568578974239617178334026515133591263737592211/28779119327282499904866662812500000000000000:ℝ)]]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (10843169821913823550658585353339747515016550749/63583012509444371216319664619520000000000000000000:ℝ) admission09_08_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 8 := by
 rw [admission09_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]
def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5307603607910528477558386594472793588223/1998549953283506937837962695312500:ℝ), (5150130565032700539670181319292338635813/666183317761168979279320898437500:ℝ), (3745074104327237319647528251618536224224/499637488320876734459490673828125:ℝ), (241876017456015702254553874288300816384/99927497664175346891898134765625:ℝ)],
![(2029980552306483900723576186456110863721/999274976641753468918981347656250:ℝ), (1958395060487687694817651445959471545811/333091658880584489639660449218750:ℝ), (2830713840121677217416335122384767601216/499637488320876734459490673828125:ℝ), (181622922300514877140354385040738767872/99927497664175346891898134765625:ℝ)]]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (177366135059096559707377329141346453/17463595965118388090419829760000000000:ℝ) admission09_09_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 9 := by
 rw [admission09_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]
def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5928717742703063690058151808/93716008367783203125:ℝ), (258119681042529254210277715648/1405740125516748046875:ℝ), (249478362398431218320963599936/1405740125516748046875:ℝ), (8921067903858796606839795712/156193347279638671875:ℝ)],
![(52806773598702599671795759616/468580041838916015625:ℝ), (152816365044374625760267292416/468580041838916015625:ℝ), (147231924844791064224047305984/468580041838916015625:ℝ), (47222445439744038135575773184/468580041838916015625:ℝ)],
![(918063610158004906245113344/18743201673556640625:ℝ), (198445812749117437513800305408/1405740125516748046875:ℝ), (190354428790194209803350108416/1405740125516748046875:ℝ), (20254519802017380085977767936/468580041838916015625:ℝ)]]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2472475561769699717526583/873496508357836800000000000:ℝ) admission09_10_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 10 := by
 rw [admission09_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]
def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29397172958989159018849313555692/92093181847303999695573321:ℝ), (57899174380776642777426596896256/92093181847303999695573321:ℝ), (28506096756975876627969912504320/92093181847303999695573321:ℝ)],
![(27710388400457144656924960976488/92093181847303999695573321:ℝ), (54553015600571435245450305987584/92093181847303999695573321:ℝ), (26846593495669727740409786777600/92093181847303999695573321:ℝ)]]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1638586028788435531030870775/7858618184303274640688923392:ℝ) admission09_11_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 11 := by
 rw [admission09_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]
def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission09_12_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 12 := by
 rw [admission09_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]
def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(67552311962667713/20000000000000000000:ℝ)]]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (67552311962667713/20000000000000000000:ℝ) admission09_13_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 13 := by
 rw [admission09_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]
def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .weakC6 δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission09_14_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .weakC6 δ p 14 := by
 rw [admission09_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]
theorem admission09_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .weakC6 δ p j := by
 fin_cases j
 · exact admission09_00_pos hδ hp
 · exact admission09_01_pos hδ hp
 · exact admission09_02_pos hδ hp
 · exact admission09_03_pos hδ hp
 · exact admission09_04_pos hδ hp
 · exact admission09_05_pos hδ hp
 · exact admission09_06_pos hδ hp
 · exact admission09_07_pos hδ hp
 · exact admission09_08_pos hδ hp
 · exact admission09_09_pos hδ hp
 · exact admission09_10_pos hδ hp
 · exact admission09_11_pos hδ hp
 · exact admission09_12_pos hδ hp
 · exact admission09_13_pos hδ hp
 · exact admission09_14_pos hδ hp
#print axioms admission09_all
end
end Record1252270103Return.C30
