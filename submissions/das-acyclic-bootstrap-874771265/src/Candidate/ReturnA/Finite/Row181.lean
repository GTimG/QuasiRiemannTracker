/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row181_coefficients : Fin 3 → Fin 4 → ℝ := ![![(507857606159498265308051107179244831/18650523883772380925250000000000:ℝ),(1127437067015150336841882185270230037/18650523883772380925250000000000:ℝ),(755876177871269982345457658633283631/18650523883772380925250000000000:ℝ),(1813933770740777900946983704813979/248673651783631745670000000000:ℝ)],
![(3143404551457231786251905681055206207/46626309709430952313125000000000:ℝ),(7219391537887323964788132649812996817/46626309709430952313125000000000:ℝ),(1028503625514202975367717569820311/9325261941886190462625000000:ℝ),(35504895932853169099301515519896313/1554210323647698410437500000000:ℝ)],
![(22239055026043462114065092577055645873/466263097094309523131250000000000:ℝ),(54298142237940137153220357556696134449/466263097094309523131250000000000:ℝ),(85218331160869568333444025919907860247/932526194188619046262500000000000:ℝ),(1405661989491174291771801759894083873/62168412945907936417500000000000:ℝ)]]
theorem row181_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1813933770740777900946983704813979/3708490283984688943611248640000000000:ℝ) row181_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row181_coefficients,Fin.sum_univ_succ]
 ring
theorem row181_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row181_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row181_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row181_pos
