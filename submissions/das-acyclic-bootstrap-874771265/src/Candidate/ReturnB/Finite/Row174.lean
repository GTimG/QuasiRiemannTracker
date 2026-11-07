/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row174_coefficients : Fin 3 → Fin 4 → ℝ := ![![(598600249281191344091945538768907723343369/163384883363937073359375000000000:ℝ),(1194118211467013185793945399353636006517003/163384883363937073359375000000000:ℝ),(232650516134848023458718184860162628012/63822220064037919281005859375:ℝ),(125540980972006752425493808020254528/319111100320189596405029296875:ℝ)],
![(9702166528375161297502966986633392511667/1317620027128524785156250000000:ℝ),(120063839979483222740275996108472597213579/8169244168196853667968750000000:ℝ),(2343098374239543988491034043947116562096/319111100320189596405029296875:ℝ),(567200613700090782333660369963797888/63822220064037919281005859375:ℝ)],
![(152107110980201570248123403898188629335521/40846220840984268339843750000000:ℝ),(304755230788099952279884297646832144997139/40846220840984268339843750000000:ℝ),(1202979717235100934086698711064759108912/319111100320189596405029296875:ℝ),(10410222910194169143648165055712459456/319111100320189596405029296875:ℝ)]]
theorem row174_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1961577827687605506648340750316477/311881213648392975946874880000000000000000:ℝ) row174_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row174_coefficients,Fin.sum_univ_succ]
 ring
theorem row174_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row174_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row174_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row174_pos
