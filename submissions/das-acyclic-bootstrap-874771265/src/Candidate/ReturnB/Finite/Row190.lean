/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row190_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1539311438652300881020970303675321/441443668154966793893238750000000:ℝ),(125068528033986257059244617313771/13377080853180811936158750000000:ℝ),(134688464232821863809156808580849/16349765487220992366416250000000:ℝ),(1048638547816944720913131764003801/441443668154966793893238750000000:ℝ)],
![(241024268721630856066108160823137/220721834077483396946619375000000:ℝ),(68016994179939274517324163690311/24524648230831488549624375000000:ℝ),(546682260570713790700595496982687/220721834077483396946619375000000:ℝ),(212792220209565061952468102537/267541617063616238723175000000:ℝ)],
![(708511771410828006684201017970953/441443668154966793893238750000000:ℝ),(63812224352746903382081086301257/29429577876997786259549250000000:ℝ),(327042365261989661768555210901701/441443668154966793893238750000000:ℝ),(18849040172966092912524934353799/441443668154966793893238750000000:ℝ)]]
theorem row190_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (18849040172966092912524934353799/25113239788371444274815360000000000:ℝ) row190_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row190_coefficients,Fin.sum_univ_succ]
 ring
theorem row190_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row190_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row190_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row190_pos
