/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row150_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106353522363127216149886995203923/20735321245312500000000000:ℝ),(231271586937426819309549749076307/20735321245312500000000000:ℝ),(283047953948450193876630081493/40498674307250976562500:ℝ),(9766839769192820363853441334/10124668576812744140625:ℝ)],
![(47469928716439044915322861188629/5183830311328125000000000:ℝ),(97003832314860817025507130493973/5183830311328125000000000:ℝ),(102210076169248531751931069083/10124668576812744140625:ℝ),(5464170703581008099227418096/10124668576812744140625:ℝ)],
![(23642166089820462835724650917187/5183830311328125000000000:ℝ),(47433828443608599168787289454403/5183830311328125000000000:ℝ),(47491186800532578097625389657/10124668576812744140625:ℝ),(1023096265790124322112423764/10124668576812744140625:ℝ)]]
theorem row150_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (255774066447531080528105941/38653440373555200000000000000000:ℝ) row150_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row150_coefficients,Fin.sum_univ_succ]
 ring
theorem row150_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row150_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row150_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row150_pos
