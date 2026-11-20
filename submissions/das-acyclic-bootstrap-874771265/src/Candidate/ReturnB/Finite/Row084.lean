/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row084_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6956708019538544671615043965731421877/183851751581252498759765625:ℝ),(20662491625929830550964456836386827807/183851751581252498759765625:ℝ),(20455734587750977438850505658025460383/183851751581252498759765625:ℝ),(749994462547483155602208506096672717/20427972397916944306640625:ℝ)],
![(13759766028100568449015176399744161002/183851751581252498759765625:ℝ),(40861913000252309440328650802064897086/183851751581252498759765625:ℝ),(40446289352893449301239569486034238366/183851751581252498759765625:ℝ),(164742478186520683595672050485660522/2269774710879660478515625:ℝ)],
![(272308823033960092377496615327968101/7354070063250099950390625:ℝ),(20213389311969641464872184354496696479/183851751581252498759765625:ℝ),(20004502970737060412246042640539324033/183851751581252498759765625:ℝ),(733203711708867515516483322116279731/20427972397916944306640625:ℝ)]]
theorem row084_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (733203711708867515516483322116279731/319442391941644194506615029760000000000:ℝ) row084_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row084_coefficients,Fin.sum_univ_succ]
 ring
theorem row084_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row084_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row084_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row084_pos
