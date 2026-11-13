/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission004_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172872433664/9:ℝ),(517543559168/9:ℝ),(516469817344/9:ℝ),(171798691840/9:ℝ)],
![(345744867328/9:ℝ),(1035087118336/9:ℝ),(1032939634688/9:ℝ),(343597383680/9:ℝ)],
![(172872433664/9:ℝ),(517543559168/9:ℝ),(516469817344/9:ℝ),(171798691840/9:ℝ)]]
theorem admission004_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (5/4:ℝ) admission004_00_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission004_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_00_coefficients]
def admission004_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(137438953472/9:ℝ),(137438953472/3:ℝ),(137438953472/3:ℝ),(137438953472/9:ℝ)]]
theorem admission004_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (1/1:ℝ) admission004_01_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission004_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_01_coefficients]
def admission004_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5145069350813696/703125:ℝ),(1714221540704256/78125:ℝ),(1028051978682368/46875:ℝ),(5137855164710912/703125:ℝ)],
![(10290138701627392/703125:ℝ),(3428443081408512/78125:ℝ),(2056103957364736/46875:ℝ),(10275710329421824/703125:ℝ)],
![(5145069350813696/703125:ℝ),(1714221540704256/78125:ℝ),(1028051978682368/46875:ℝ),(5137855164710912/703125:ℝ)]]
theorem admission004_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (9570001/20000000:ℝ) admission004_02_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission004_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_02_coefficients]
def admission004_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(303118155776/27:ℝ),(905273409536/27:ℝ),(901192351744/27:ℝ),(299037097984/27:ℝ)],
![(599026302976/27:ℝ),(1788879044608/27:ℝ),(1780679180288/27:ℝ),(590826438656/27:ℝ)],
![(295908147200/27:ℝ),(883605635072/27:ℝ),(879486828544/27:ℝ),(291789340672/27:ℝ)]]
theorem admission004_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1087/1536:ℝ) admission004_03_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission004_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_03_coefficients]
def admission004_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(127807540179456/78125:ℝ),(1138127409812992/234375:ℝ),(1125995103911936/234375:ℝ),(371290314637312/234375:ℝ)],
![(787242887973376/234375:ℝ),(779039879998976/78125:ℝ),(770842376011776/78125:ℝ),(762650376011776/234375:ℝ)],
![(403820267435008/234375:ℝ),(1198992230183936/234375:ℝ),(1186532024123392/234375:ℝ),(130453353791488/78125:ℝ)]]
theorem admission004_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (1062270111/10240000000:ℝ) admission004_04_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission004_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_04_coefficients]
def admission004_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57184065360896/46875:ℝ),(2583145537734656/703125:ℝ),(2592983696525824/703125:ℝ),(867599139204608/703125:ℝ)],
![(107160509080064/46875:ℝ),(968537360170496/140625:ℝ),(972620231443456/140625:ℝ),(325564398513152/140625:ℝ)],
![(16658814573056/15625:ℝ),(2259541263117824/703125:ℝ),(2270117460691456/703125:ℝ),(760222853361152/703125:ℝ)]]
theorem admission004_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (292830724917/4194304000000:ℝ) admission004_05_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission004_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_05_coefficients]
def admission004_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(249717648544308736/78046875:ℝ),(737242814191967744/78046875:ℝ),(241788351426461696/26015625:ℝ),(47567977726345216/15609375:ℝ)],
![(102640581631023616/15609375:ℝ),(303123699312237056/15609375:ℝ),(99446227172458496/5203125:ℝ),(97855563836162048/15609375:ℝ)],
![(263485259610809344/78046875:ℝ),(778375682369217536/78046875:ℝ),(255442784435830784/26015625:ℝ),(50287586109816832/15609375:ℝ)]]
theorem admission004_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (45364358641/227328000000:ℝ) admission004_06_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission004_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_06_coefficients]
def admission004_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15973068045793792/2109375:ℝ),(47801168424974848/2109375:ℝ),(47683200301531136/2109375:ℝ),(3171019984470016/421875:ℝ)],
![(49663262623232/3375:ℝ),(18577201264815616/421875:ℝ),(3706141137043456/84375:ℝ),(6161412248305664/421875:ℝ)],
![(15066471093726208/2109375:ℝ),(45084837899103232/2109375:ℝ),(44970328124555264/2109375:ℝ),(2990392263835648/421875:ℝ)]]
theorem admission004_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1425930149/3072000000:ℝ) admission004_07_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission004_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_07_coefficients]
def admission004_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44557841869402/140625:ℝ),(2025057823664686/2109375:ℝ),(681707160323258/703125:ℝ),(27537228503498/84375:ℝ)],
![(97037459066456/140625:ℝ),(880482792004012/421875:ℝ),(295891769344484/140625:ℝ),(298304661029348/421875:ℝ)],
![(52479617197054/140625:ℝ),(2377356136355374/2109375:ℝ),(797751686399162/703125:ℝ),(160618518511858/421875:ℝ)]]
theorem admission004_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (22278920934701/1073741824000000:ℝ) admission004_08_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission004_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_08_coefficients]
def admission004_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(77141775604502042839/823974609375:ℝ),(217542221473769462627/823974609375:ℝ),(67876563815807234176/274658203125:ℝ),(12645893862401794048/164794921875:ℝ)],
![(20093992510952586469/164794921875:ℝ),(55052284304277400073/164794921875:ℝ),(16603176500962275712/54931640625:ℝ),(14851328412476076032/164794921875:ℝ)],
![(23328186950260889506/823974609375:ℝ),(57719200047617537738/823974609375:ℝ),(15139318689004144384/274658203125:ℝ),(2205434550074281984/164794921875:ℝ)]]
theorem admission004_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (538436169451729/614400000000000000:ℝ) admission004_09_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission004_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_09_coefficients]
def admission004_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7652763478431194/87890625:ℝ),(111362335986215938/439453125:ℝ),(35974674939755072/146484375:ℝ),(3869500691689472/48828125:ℝ)],
![(22585858926296296/146484375:ℝ),(65531121367813096/146484375:ℝ),(21099448765760768/48828125:ℝ),(6784361285255168/48828125:ℝ)],
![(1168392797678792/17578125:ℝ),(84386548835994248/439453125:ℝ),(27044621727308032/146484375:ℝ),(2884126254211072/48828125:ℝ)]]
theorem admission004_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3168595738269/819200000000000:ℝ) admission004_10_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission004_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_10_coefficients]
def admission004_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13750894660109824/2109375:ℝ),(2746015363848704/140625:ℝ),(13709330383437824/703125:ℝ),(13688655352692736/2109375:ℝ)],
![(26754171669830144/2109375:ℝ),(26712788290870784/703125:ℝ),(26671548382511104/703125:ℝ),(26630451944751104/2109375:ℝ)],
![(2600655401944064/421875:ℝ),(12982711471627264/703125:ℝ),(2592443599814656/140625:ℝ),(12941796592058368/2109375:ℝ)]]
theorem admission004_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (6171129509/15360000000:ℝ) admission004_11_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission004_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_11_coefficients]
def admission004_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)],
![(110415818377920512/439453125:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/146484375:ℝ),(110415818377920512/439453125:ℝ)],
![(55207909188960256/439453125:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/146484375:ℝ),(55207909188960256/439453125:ℝ)]]
theorem admission004_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission004_12_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission004_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_12_coefficients]
def admission004_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19307878491852111872/274658203125:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/274658203125:ℝ)],
![(38615756983704223744/274658203125:ℝ),(38615756983704223744/91552734375:ℝ),(38615756983704223744/91552734375:ℝ),(38615756983704223744/274658203125:ℝ)],
![(19307878491852111872/274658203125:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/91552734375:ℝ),(19307878491852111872/274658203125:ℝ)]]
theorem admission004_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (4603356955493/1000000000000000:ℝ) admission004_13_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission004_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_13_coefficients]
def admission004_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(536080894506496/2109375:ℝ),(59176994046464/78125:ℝ),(1587337412411392/2109375:ℝ),(105127893532672/421875:ℝ)],
![(211889724514816/421875:ℝ),(70164249399808/46875:ℝ),(627296324091904/421875:ℝ),(207707804008448/421875:ℝ)],
![(523367728067584/2109375:ℝ),(173290264859648/234375:ℝ),(1549144208048128/2109375:ℝ),(102579910475776/421875:ℝ)]]
theorem admission004_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (48913913/3072000000:ℝ) admission004_14_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission004_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission004_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission004_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission004_14_coefficients]
theorem admission004_all {δ p : ℝ}
 (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .capP δ p j := by
 intro j
 fin_cases j
 · exact admission004_00_pos hd hp
 · exact admission004_01_pos hd hp
 · exact admission004_02_pos hd hp
 · exact admission004_03_pos hd hp
 · exact admission004_04_pos hd hp
 · exact admission004_05_pos hd hp
 · exact admission004_06_pos hd hp
 · exact admission004_07_pos hd hp
 · exact admission004_08_pos hd hp
 · exact admission004_09_pos hd hp
 · exact admission004_10_pos hd hp
 · exact admission004_11_pos hd hp
 · exact admission004_12_pos hd hp
 · exact admission004_13_pos hd hp
 · exact admission004_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission004_all
