/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row193_coefficients : Fin 3 → Fin 4 → ℝ := ![![(358922734788319966415217378293551/183934861731236164122182812500:ℝ),(21996768341254406647557185417576549/4598371543280904103054570312500:ℝ),(52840142934924881540072970092517719/13795114629842712309163710937500:ℝ),(13739282154681335066138209711804397/13795114629842712309163710937500:ℝ)],
![(7404667395517316821747958787298111/2299185771640452051527285156250:ℝ),(3234989166036533702605694828951249/459837154328090410305457031250:ℝ),(10794551506135500962514780126237407/2299185771640452051527285156250:ℝ),(2011872710801680932732386643779273/2299185771640452051527285156250:ℝ)],
![(10713004773759437528526981074219797/4598371543280904103054570312500:ℝ),(8135188539864813091926354319059547/1532790514426968034351523437500:ℝ),(104859043821137505264658195057265471/27590229259685424618327421875000:ℝ),(22610676041113982242381617822012407/27590229259685424618327421875000:ℝ)]]
theorem row193_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2011872710801680932732386643779273/2142996461941029911450910720000000000:ℝ) row193_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row193_coefficients,Fin.sum_univ_succ]
 ring
theorem row193_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row193_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row193_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row193_pos
