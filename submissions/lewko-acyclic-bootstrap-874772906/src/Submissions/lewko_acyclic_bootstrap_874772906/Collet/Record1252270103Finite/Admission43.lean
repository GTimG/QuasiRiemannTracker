/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def admission43_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1202600869661870149/157406588190789:ℝ), (1202243463073679360/157406588190789:ℝ)]]
theorem admission43_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (587032940953945/629626352763156:ℝ) admission43_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission43_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_00_coefficients]
def admission43_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(880074770458943488/157406588190789:ℝ), (879874770458943488/157406588190789:ℝ)]]
theorem admission43_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107406588190789/157406588190789:ℝ) admission43_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission43_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_01_coefficients]
def admission43_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(149254150863023530/52468862730263:ℝ), (149222075479105536/52468862730263:ℝ)]]
theorem admission43_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18215585385633/52468862730263:ℝ) admission43_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission43_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_02_coefficients]
def admission43_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(525794748009719134739734528/1416659293717101:ℝ), (116818371537467438857723904/157406588190789:ℝ), (75081514976641116425682944/202379899102443:ℝ)],
![(525682338266177473392001024/1416659293717101:ℝ), (116793391942983410321506304/157406588190789:ℝ), (525458198231473219501555712/1416659293717101:ℝ)]]
theorem admission43_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15659874624951875791/30947394491014643712:ℝ) admission43_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission43_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_03_coefficients]
def admission43_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(437325086885319853181390/7495551818609:ℝ), (874342803082547988766720/7495551818609:ℝ), (437017739131127636951040/7495551818609:ℝ)],
![(437499780756651810721876/7495551818609:ℝ), (6122844905887409072783360/52468862730263:ℝ), (3060346601160218291208192/52468862730263:ℝ)]]
theorem admission43_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (39072430652182785/491228483984359424:ℝ) admission43_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission43_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_04_coefficients]
def admission43_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(161240782878899131672982172/4684719886630625:ℝ), (2902395920085354840876859316/42162478979675625:ℝ), (1451228812176515460637901018/42162478979675625:ℝ)],
![(161038705046250979735315318/4684719886630625:ℝ), (20291312215115712288419756012/295137352857729375:ℝ), (10145873363123958664281343478/295137352857729375:ℝ)]]
theorem admission43_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (241558057569376469602972977/5150903988223836673802240000:ℝ) admission43_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission43_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_05_coefficients]
def admission43_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5665972935693092098799312441416195094452797440/8250685723952923479064059359493:ℝ), (5663758459893673812806990142685378074114949120/2750228574650974493021353119831:ℝ), (16984632992788246331595392167658465629275422720/8250685723952923479064059359493:ℝ), (5659330548755238728631582727604526501383372800/8250685723952923479064059359493:ℝ)],
![(5668062590833319150752970554071494740147109888/8250685723952923479064059359493:ℝ), (5665847836292134736596375949705729946141786112/2750228574650974493021353119831:ℝ), (16990900285897056373412847655627046332858892288/8250685723952923479064059359493:ℝ), (5661419367808884044388516499284551234580643840/8250685723952923479064059359493:ℝ)]]
theorem admission43_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41177049197396545268068313653963025/360477959736652528749294796122488832:ℝ) admission43_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission43_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_06_coefficients]
def admission43_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(490401859542074519682514503277117035890/2752981556207181674696049169:ℝ), (26474922286008297870642305136372480450560/74330502017593905216793327563:ℝ), (490150833374280455418967359211847024640/2752981556207181674696049169:ℝ)],
![(490162596588282798942875610006280059692/2752981556207181674696049169:ℝ), (26462003740826619487263972257099563778048/74330502017593905216793327563:ℝ), (489911631687892399671284314735493775360/2752981556207181674696049169:ℝ)]]
theorem admission43_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (21900756583566623911467983487345/90209699633796929116440139169792:ℝ) admission43_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission43_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_07_coefficients]
def admission43_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(40829374304124739047251908027568395301565461815608664399/2743325052024056994076898486328125000000000:ℝ), (4635363948856128266947329228777090725887557983979324516049/103697686966509354376106762783203125000000000:ℝ), (487271052620659165716243204371345686984227604383528930198163/10888257131483482209491210092236328125000000000:ℝ), (162609624592947908353326433425958906212811567981040098137649/10888257131483482209491210092236328125000000000:ℝ)],
![(206113911330127958001664186167562012354301160240997861241/13716625260120284970384492431640625000000000:ℝ), (23399838552356384047337577189599208119098834515243700309979/518488434832546771880533813916015625000000000:ℝ), (2459767670367103158500689323857433550411150696413009439034591/54441285657417411047456050461181640625000000000:ℝ), (32834029455380217111131494831051011006842146930510000460093/2177651426296696441898242018447265625000000000:ℝ)]]
theorem admission43_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (122488122912374217141755724082705185904696385446825993197/49419350728206758528104665009686891724800000000000000000000:ℝ) admission43_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission43_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_08_coefficients]
def admission43_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22393891291232314792584549227874291125015703070394/435530285259339288379648403689453125:ℝ), (2486611221239275583259921685193135663914307081312/16130751305901455125172163099609375:ℝ), (67095335065755016828169314116080349609346579300352/435530285259339288379648403689453125:ℝ), (3192960483412719068640736120997588086993029431296/62218612179905612625664057669921875:ℝ)],
![(111626352098008411083135525667470005086859229339724/2177651426296696441898242018447265625:ℝ), (2478988073772970960438497350610229757294761259584/16130751305901455125172163099609375:ℝ), (334447738564511246923012675909826072111669726150656/2177651426296696441898242018447265625:ℝ), (22282140140995930633304771302776249322253276151808/435530285259339288379648403689453125:ℝ)]]
theorem admission43_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (41503720248110463159726506663069593389059/4871323780225034172287767515168768000000000:ℝ) admission43_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission43_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_09_coefficients]
def admission43_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2061384809267863304024825936814339715072/13834563415206064453125:ℝ), (2059759881612567251467058847404826038272/4611521138402021484375:ℝ), (6174405108669985566150057911513937084416/13834563415206064453125:ℝ), (76167047152966286065982215041251803136/512391237600224609375:ℝ)],
![(4115723216528400558547172866478277607424/13834563415206064453125:ℝ), (587496344483514257275408754665630810112/658788734057431640625:ℝ), (4109225770648670132095904568645353734144/4611521138402021484375:ℝ), (586568184911501247592150389205155971072/1976366202172294921875:ℝ)],
![(2054336835282373319317318599027463929856/13834563415206064453125:ℝ), (410542591613711891144322361888991952896/922304227680404296875:ℝ), (6153267488989593749442162043404326797312/13834563415206064453125:ℝ), (2049465450096243275875895214096911433728/13834563415206064453125:ℝ)]]
theorem admission43_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (477178359892275947117222290043/211267546391993301073920000000000:ℝ) admission43_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission43_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_10_coefficients]
def admission43_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3619505752822434294841126760936912232190/24776834005864635072264442521:ℝ), (7237163961517443352548868953603842293760/24776834005864635072264442521:ℝ), (10852975030979635470253666140036687462400/74330502017593905216793327563:ℝ)],
![(3617695533436564668724783646422665538420/24776834005864635072264442521:ℝ), (7233543995298475829214238368763986870272/24776834005864635072264442521:ℝ), (10847545790373602025358911368961080688640/74330502017593905216793327563:ℝ)]]
theorem admission43_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (323282056760001242916551571159395/1623774593408344724095922505056256:ℝ) admission43_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission43_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_11_coefficients]
def admission43_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission43_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission43_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission43_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_12_coefficients]
def admission43_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4066544978453549211/1000000000000000000000:ℝ)]]
theorem admission43_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4066544978453549211/1000000000000000000000:ℝ) admission43_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission43_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_13_coefficients]
def admission43_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission43_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission43_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission43_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_14_coefficients]
theorem admission43_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission43_00_pos hδ hp
 · exact admission43_01_pos hδ hp
 · exact admission43_02_pos hδ hp
 · exact admission43_03_pos hδ hp
 · exact admission43_04_pos hδ hp
 · exact admission43_05_pos hδ hp
 · exact admission43_06_pos hδ hp
 · exact admission43_07_pos hδ hp
 · exact admission43_08_pos hδ hp
 · exact admission43_09_pos hδ hp
 · exact admission43_10_pos hδ hp
 · exact admission43_11_pos hδ hp
 · exact admission43_12_pos hδ hp
 · exact admission43_13_pos hδ hp
 · exact admission43_14_pos hδ hp
#print axioms admission43_all
end
end Record1252270103Finite
