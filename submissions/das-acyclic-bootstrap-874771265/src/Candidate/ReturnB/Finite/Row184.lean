/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row184_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1627002824427965695629582186094843907/408462208409842683398437500000:ℝ),(3283565703260316808132482973545985163/408462208409842683398437500000:ℝ),(53703328217820405401629520124812336/12764444012807583856201171875:ℝ),(1931805712980759148381028715499328/12764444012807583856201171875:ℝ)],
![(72494913497284891335921314000373619571/8169244168196853667968750000000:ℝ),(151660145350962671044876233387261062459/8169244168196853667968750000000:ℝ),(680954541341485930468362032872476476/63822220064037919281005859375:ℝ),(12487171787201873623988019339480736/12764444012807583856201171875:ℝ)],
![(3447244922185955300159575238265982842659/653539533455748293437500000000000:ℝ),(7627181504988086394118727935467441455147/653539533455748293437500000000000:ℝ),(9701123459747475175290173179255747583/1276444401280758385620117187500:ℝ),(384192914709679767896508468941937146/319111100320189596405029296875:ℝ)]]
theorem row184_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (30184464265324361693453573679677/3045714977035087655731200000000000000:ℝ) row184_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row184_coefficients,Fin.sum_univ_succ]
 ring
theorem row184_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row184_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row184_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row184_pos
