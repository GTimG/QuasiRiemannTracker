/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row201_coefficients : Fin 3 → Fin 4 → ℝ := ![![(40318953786931105909051702668334402207/4834024896900757371048105468750:ℝ),(103173478505189878177987681057798960573/4834024896900757371048105468750:ℝ),(1143224193828696966634045099118608303/64453665292010098280641406250:ℝ),(7628648953277701702519216881164521453/1611341632300252457016035156250:ℝ)],
![(38910630543782546963900581050493129487/2417012448450378685524052734375:ℝ),(3937241075876115120358661424499577573/96680497938015147420962109375:ℝ),(8943421453688377025655832202601550921/268556938716708742836005859375:ℝ),(6989672809995587310004017169274632817/805670816150126228508017578125:ℝ)],
![(13131866189545289655275835033600528589/1611341632300252457016035156250:ℝ),(11037198379602176452251296467891254853/537113877433417485672011718750:ℝ),(26950847854193639190871002064580523701/1611341632300252457016035156250:ℝ),(2323549127072660326940471259601387577/537113877433417485672011718750:ℝ)]]
theorem row201_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2323549127072660326940471259601387577/8202263245526330732358538362880000000000:ℝ) row201_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row201_coefficients,Fin.sum_univ_succ]
 ring
theorem row201_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row201_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row201_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row201_pos
