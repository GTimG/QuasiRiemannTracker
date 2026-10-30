/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission001_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(687865856/9:ℝ),(2046820352/9:ℝ),(2030043136/9:ℝ),(671088640/9:ℝ)],
![(1375731712/9:ℝ),(4093640704/9:ℝ),(4060086272/9:ℝ),(1342177280/9:ℝ)],
![(687865856/9:ℝ),(2046820352/9:ℝ),(2030043136/9:ℝ),(671088640/9:ℝ)]]
theorem admission001_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (5/4:ℝ) admission001_00_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission001_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_00_coefficients]
def admission001_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(536870912/9:ℝ),(536870912/3:ℝ),(536870912/3:ℝ),(536870912/9:ℝ)],
![(1073741824/9:ℝ),(1073741824/3:ℝ),(1073741824/3:ℝ),(1073741824/9:ℝ)],
![(536870912/9:ℝ),(536870912/3:ℝ),(536870912/3:ℝ),(536870912/9:ℝ)]]
theorem admission001_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (1/1:ℝ) admission001_01_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission001_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_01_coefficients]
def admission001_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20182468395008/703125:ℝ),(6714964836352/78125:ℝ),(20107320623104/234375:ℝ),(20069746737152/703125:ℝ)],
![(40364936790016/703125:ℝ),(13429929672704/78125:ℝ),(40214641246208/234375:ℝ),(40139493474304/703125:ℝ)],
![(20182468395008/703125:ℝ),(6714964836352/78125:ℝ),(20107320623104/234375:ℝ),(20069746737152/703125:ℝ)]]
theorem admission001_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (9570001/20000000:ℝ) admission001_02_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission001_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_02_coefficients]
def admission001_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1259601920/27:ℝ),(3715629056/27:ℝ),(3652452352/27:ℝ),(1196425216/27:ℝ)],
![(2463760384/27:ℝ),(7263748096/27:ℝ),(7136215040/27:ℝ),(2336227328/27:ℝ)],
![(1204158464/27:ℝ),(3548119040/27:ℝ),(3483762688/27:ℝ),(1139802112/27:ℝ)]]
theorem admission001_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1087/1536:ℝ) admission001_03_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission001_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_03_coefficients]
def admission001_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(531989808768/78125:ℝ),(1534199187072/78125:ℝ),(1472594067456/78125:ℝ),(470384689152/78125:ℝ)],
![(3359001268928/234375:ℝ),(1939217466304/46875:ℝ),(9316189093888/234375:ℝ),(2979103031296/234375:ℝ)],
![(1763031842624/234375:ℝ),(5093489770304/234375:ℝ),(979681378304/46875:ℝ),(313589792768/46875:ℝ)]]
theorem admission001_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (258390027/2560000000:ℝ) admission001_04_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission001_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_04_coefficients]
def admission001_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(248516797856/46875:ℝ),(11328045912608/703125:ℝ),(11471349845152/703125:ℝ),(3871055900384/703125:ℝ)],
![(146522246016/15625:ℝ),(20093291421952/703125:ℝ),(20403024918848/703125:ℝ),(6903234567616/703125:ℝ)],
![(191049940192/46875:ℝ),(8765245509344/703125:ℝ),(8931675073696/703125:ℝ),(3032178667232/703125:ℝ)]]
theorem admission001_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (17910931893/262144000000:ℝ) admission001_05_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission001_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_05_coefficients]
def admission001_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43477709154688/3121875:ℝ),(3074390368628096/78046875:ℝ),(963317009702912/26015625:ℝ),(180500677869568/15609375:ℝ)],
![(457091261845696/15609375:ℝ),(6478107658585024/78046875:ℝ),(2034630943510528/26015625:ℝ),(382248296235008/15609375:ℝ)],
![(239702716072256/15609375:ℝ),(3403717289956928/78046875:ℝ),(1071313933807616/26015625:ℝ),(40349523673088/3121875:ℝ)]]
theorem admission001_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (11016887077/56832000000:ℝ) admission001_06_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission001_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_06_coefficients]
def admission001_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13472483796608/421875:ℝ),(200182359056512/2109375:ℝ),(198281809313792/2109375:ℝ),(13092373848064/421875:ℝ)],
![(25512161693248/421875:ℝ),(378981136455488/2109375:ℝ),(375288296132608/2109375:ℝ),(24773593628672/421875:ℝ)],
![(2407935579328/84375:ℝ),(178798777398976/2109375:ℝ),(177006486818816/2109375:ℝ),(11681219780608/421875:ℝ)]]
theorem admission001_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1425930149/3072000000:ℝ) admission001_07_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission001_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_07_coefficients]
def admission001_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(82923972762/78125:ℝ),(7085126466118/2109375:ℝ),(2486488935362/703125:ℝ),(2613148284866/2109375:ℝ)],
![(203904473982/78125:ℝ),(17118986407436/2109375:ℝ),(5911981498756/703125:ℝ),(6122092507012/2109375:ℝ)],
![(24196100244/15625:ℝ),(10033859941318/2109375:ℝ),(3425492563394/703125:ℝ),(3508944222146/2109375:ℝ)]]
theorem admission001_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (373157877429/20971520000000:ℝ) admission001_08_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission001_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_08_coefficients]
def admission001_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46156873072759725791/54931640625000:ℝ),(73484170621040059577/32958984375000:ℝ),(39889784988891869804/20599365234375:ℝ),(751491086449177816/1373291015625:ℝ)],
![(123455567516646848003/109863281250000:ℝ),(187968865115377723829/65917968750000:ℝ),(47938538952794282866/20599365234375:ℝ),(823265612452908128/1373291015625:ℝ)],
![(31141821371127396421/109863281250000:ℝ),(1640020954931904187/2636718750000:ℝ),(8048753963902413062/20599365234375:ℝ),(71774526003730312/1373291015625:ℝ)]]
theorem admission001_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (8971815750466289/10240000000000000000:ℝ) admission001_09_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission001_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_09_coefficients]
def admission001_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1870855431315034/3662109375:ℝ),(1716826953908642/1220703125:ℝ),(12490395292268/9765625:ℝ),(1404272804189608/3662109375:ℝ)],
![(1905192277285306/2197265625:ℝ),(25936230131639102/10986328125:ℝ),(2585096541343596/1220703125:ℝ),(761733347431088/1220703125:ℝ)],
![(7587701421989443/21972656250:ℝ),(4055081156453321/4394531250:ℝ),(986509317948917/1220703125:ℝ),(844910560467224/3662109375:ℝ)]]
theorem admission001_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (316841460175209/81920000000000000:ℝ) admission001_10_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission001_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_10_coefficients]
def admission001_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57383022292864/2109375:ℝ),(11409433798784/140625:ℝ),(11343147446272/140625:ℝ),(56388727005184/2109375:ℝ)],
![(108907680972992/2109375:ℝ),(108243734997056/703125:ℝ),(107588714653696/703125:ℝ),(106942619942912/2109375:ℝ)],
![(51524658680128/2109375:ℝ),(51196566003136/703125:ℝ),(50872977422336/703125:ℝ),(50553892937728/2109375:ℝ)]]
theorem admission001_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (6171129509/15360000000:ℝ) admission001_11_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission001_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_11_coefficients]
def admission001_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5391512338038784/10986328125:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/10986328125:ℝ)],
![(10783024676077568/10986328125:ℝ),(10783024676077568/3662109375:ℝ),(10783024676077568/3662109375:ℝ),(10783024676077568/10986328125:ℝ)],
![(5391512338038784/10986328125:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/3662109375:ℝ),(5391512338038784/10986328125:ℝ)]]
theorem admission001_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission001_12_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission001_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_12_coefficients]
def admission001_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1885668800201187328/6866455078125:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/6866455078125:ℝ)],
![(3771337600402374656/6866455078125:ℝ),(3771337600402374656/2288818359375:ℝ),(3771337600402374656/2288818359375:ℝ),(3771337600402374656/6866455078125:ℝ)],
![(1885668800201187328/6866455078125:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/2288818359375:ℝ),(1885668800201187328/6866455078125:ℝ)]]
theorem admission001_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (230184179712059/50000000000000000:ℝ) admission001_13_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission001_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_13_coefficients]
def admission001_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2266814905216/2109375:ℝ),(442352409728/140625:ℝ),(6471515705344/2109375:ℝ),(420608892928/421875:ℝ)],
![(4434954563264/2109375:ℝ),(864911019328/140625:ℝ),(12645269067776/2109375:ℝ),(821311668224/421875:ℝ)],
![(2168139658048/2109375:ℝ),(16902344384/5625:ℝ),(6173753362432/2109375:ℝ),(400702775296/421875:ℝ)]]
theorem admission001_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (48913913/3072000000:ℝ) admission001_14_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission001_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission001_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission001_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission001_14_coefficients]
theorem admission001_all {δ p : ℝ}
 (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .capP δ p j := by
 intro j
 fin_cases j
 · exact admission001_00_pos hd hp
 · exact admission001_01_pos hd hp
 · exact admission001_02_pos hd hp
 · exact admission001_03_pos hd hp
 · exact admission001_04_pos hd hp
 · exact admission001_05_pos hd hp
 · exact admission001_06_pos hd hp
 · exact admission001_07_pos hd hp
 · exact admission001_08_pos hd hp
 · exact admission001_09_pos hd hp
 · exact admission001_10_pos hd hp
 · exact admission001_11_pos hd hp
 · exact admission001_12_pos hd hp
 · exact admission001_13_pos hd hp
 · exact admission001_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission001_all
