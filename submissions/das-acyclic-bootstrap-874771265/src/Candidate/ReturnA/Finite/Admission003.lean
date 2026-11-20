/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission003_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2415919104/1:ℝ),(64961380352/9:ℝ),(64692944896/9:ℝ),(21474836480/9:ℝ)],
![(4831838208/1:ℝ),(129922760704/9:ℝ),(129385889792/9:ℝ),(42949672960/9:ℝ)],
![(2415919104/1:ℝ),(64961380352/9:ℝ),(64692944896/9:ℝ),(21474836480/9:ℝ)]]
theorem admission003_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (5/4:ℝ) admission003_00_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission003_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_00_coefficients]
def admission003_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(34359738368/9:ℝ),(34359738368/3:ℝ),(34359738368/3:ℝ),(34359738368/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)]]
theorem admission003_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (1/1:ℝ) admission003_01_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission003_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_01_coefficients]
def admission003_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(128807088422912/140625:ℝ),(643434259939328/234375:ℝ),(214277692588032/78125:ℝ),(642231895588864/703125:ℝ)],
![(257614176845824/140625:ℝ),(1286868519878656/234375:ℝ),(428555385176064/78125:ℝ),(1284463791177728/703125:ℝ)],
![(128807088422912/140625:ℝ),(643434259939328/234375:ℝ),(214277692588032/78125:ℝ),(642231895588864/703125:ℝ)]]
theorem admission003_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (9570001/20000000:ℝ) admission003_02_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission003_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_02_coefficients]
def admission003_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4266655744/3:ℝ),(114179440640/27:ℝ),(113159176192/27:ℝ),(37379637248/27:ℝ)],
![(2811232256/1:ℝ),(225659846656/27:ℝ),(223609880576/27:ℝ),(73853304832/27:ℝ)],
![(4167041024/3:ℝ),(111480406016/27:ℝ),(110450704384/27:ℝ),(36473667584/27:ℝ)]]
theorem admission003_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1087/1536:ℝ) admission003_03_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission003_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_03_coefficients]
def admission003_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(49446402280192/234375:ℝ),(29060004187904/46875:ℝ),(142264907988992/234375:ℝ),(46411289329664/234375:ℝ)],
![(101483552982272/234375:ℝ),(99430048995072/78125:ℝ),(97379297001472/78125:ℝ),(95331297001472/234375:ℝ)],
![(10407430140416/46875:ℝ),(152990126045696/234375:ℝ),(149872983015424/234375:ℝ),(16306669223936/78125:ℝ)]]
theorem admission003_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (1062270111/10240000000:ℝ) admission003_04_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission003_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_04_coefficients]
def admission003_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106648392898048/703125:ℝ),(322423046669312/703125:ℝ),(324888695792896/703125:ℝ),(12123782446848/78125:ℝ)],
![(199690075250432/703125:ℝ),(604210966756096/703125:ℝ),(609326939818496/703125:ℝ),(68268682770944/234375:ℝ)],
![(93041682352384/703125:ℝ),(281787920086784/703125:ℝ),(11377529761024/28125:ℝ),(1275893417216/9375:ℝ)]]
theorem admission003_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (363444071689/5242880000000:ℝ) admission003_05_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission003_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_05_coefficients]
def admission003_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32707518939205376/78046875:ℝ),(95128838193188608/78046875:ℝ),(30717101777649664/26015625:ℝ),(5945997215793152/15609375:ℝ)],
![(13431456874728704/15609375:ℝ),(39088345335991552/15609375:ℝ),(12629611313594368/5203125:ℝ),(12231945479520256/15609375:ℝ)],
![(34449765434438144/78046875:ℝ),(100312888486769152/78046875:ℝ),(32430954790322176/26015625:ℝ),(6285948263727104/15609375:ℝ)]]
theorem admission003_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (45364358641/227328000000:ℝ) admission003_06_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission003_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_06_coefficients]
def admission003_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(670465472798464/703125:ℝ),(6004646532603136/2109375:ℝ),(5975137604501504/2109375:ℝ),(396377498058752/421875:ℝ)],
![(260602361920768/140625:ℝ),(2333777382913792/421875:ℝ),(2322146828189696/421875:ℝ),(770176531038208/421875:ℝ)],
![(632546336805376/703125:ℝ),(5664240381965824/2109375:ℝ),(5635596536446976/2109375:ℝ),(373799032979456/421875:ℝ)]]
theorem admission003_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1425930149/3072000000:ℝ) admission003_07_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission003_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_07_coefficients]
def admission003_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27435200147138/703125:ℝ),(251850747758894/2109375:ℝ),(85613304071098/703125:ℝ),(87294192137146/2109375:ℝ)],
![(59996444670904/703125:ℝ),(548782067738716/2109375:ℝ),(185905004664692/703125:ℝ),(188921119270772/2109375:ℝ)],
![(32561244523766/703125:ℝ),(296931319979822/2109375:ℝ),(100291700593594/703125:ℝ),(101626927133626/2109375:ℝ)]]
theorem admission003_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (13717600073569/671088640000000:ℝ) admission003_08_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission003_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_08_coefficients]
def admission003_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(227481139836023563973/16479492187500:ℝ),(1022209604344133174339/27465820312500:ℝ),(679883932105401189008/20599365234375:ℝ),(13172249799246530048/1373291015625:ℝ)],
![(12654717858586575331/659179687500:ℝ),(273007308193366777001/5493164062500:ℝ),(172068330850105124528/4119873046875:ℝ),(15469034631365900032/1373291015625:ℝ)],
![(44443403314320409651/8239746093750:ℝ),(171413468311350355333/13732910156250:ℝ),(180457722145124433632/20599365234375:ℝ),(2296784832119369984/1373291015625:ℝ)]]
theorem admission003_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (8971815750466289/10240000000000000000:ℝ) admission003_09_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission003_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_09_coefficients]
def admission003_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(130257051657600941/10986328125:ℝ),(369454242290738561/10986328125:ℝ),(38669154711104436/1220703125:ℝ),(12091689085200256/1220703125:ℝ)],
![(25838533068261708/1220703125:ℝ),(43742106552880228/732421875:ℝ),(68265090723753136/1220703125:ℝ),(63600338611643392/3662109375:ℝ)],
![(101379476580279796/10986328125:ℝ),(283992525267350596/10986328125:ℝ),(29302718054658256/1220703125:ℝ),(27037137934951168/3662109375:ℝ)]]
theorem admission003_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (316841460175209/81920000000000000:ℝ) admission003_10_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission003_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_10_coefficients]
def admission003_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(345339059947264/421875:ℝ),(114763675799296/46875:ℝ),(572083558924288/234375:ℝ),(1711081919086592/2109375:ℝ)],
![(3359844027313408/2109375:ℝ),(1116475482424576/234375:ℝ),(1113026867511296/234375:ℝ),(3328806493093888/2109375:ℝ)],
![(1633148727577088/2109375:ℝ),(542657103428096/234375:ℝ),(540943308587008/234375:ℝ),(1617724574007296/2109375:ℝ)]]
theorem admission003_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (6171129509/15360000000:ℝ) admission003_11_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission003_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_11_coefficients]
def admission003_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission003_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission003_12_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission003_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_12_coefficients]
def admission003_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60341401606437994496/6866455078125:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/6866455078125:ℝ)],
![(120682803212875988992/6866455078125:ℝ),(120682803212875988992/2288818359375:ℝ),(120682803212875988992/2288818359375:ℝ),(120682803212875988992/6866455078125:ℝ)],
![(60341401606437994496/6866455078125:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/2288818359375:ℝ),(60341401606437994496/6866455078125:ℝ)]]
theorem admission003_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (230184179712059/50000000000000000:ℝ) admission003_13_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission003_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_13_coefficients]
def admission003_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13664178904832/421875:ℝ),(202335513795328/2109375:ℝ),(199719552729088/2109375:ℝ),(13140986691584/421875:ℝ)],
![(1080448309504/16875:ℝ),(79981386756352/421875:ℝ),(78933654519808/421875:ℝ),(25963475501056/421875:ℝ)],
![(13347028832768/421875:ℝ),(197571419986432/2109375:ℝ),(194948719869952/2109375:ℝ),(12822488809472/421875:ℝ)]]
theorem admission003_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (48913913/3072000000:ℝ) admission003_14_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission003_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission003_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission003_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission003_14_coefficients]
theorem admission003_all {δ p : ℝ}
 (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .capP δ p j := by
 intro j
 fin_cases j
 · exact admission003_00_pos hd hp
 · exact admission003_01_pos hd hp
 · exact admission003_02_pos hd hp
 · exact admission003_03_pos hd hp
 · exact admission003_04_pos hd hp
 · exact admission003_05_pos hd hp
 · exact admission003_06_pos hd hp
 · exact admission003_07_pos hd hp
 · exact admission003_08_pos hd hp
 · exact admission003_09_pos hd hp
 · exact admission003_10_pos hd hp
 · exact admission003_11_pos hd hp
 · exact admission003_12_pos hd hp
 · exact admission003_13_pos hd hp
 · exact admission003_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission003_all
