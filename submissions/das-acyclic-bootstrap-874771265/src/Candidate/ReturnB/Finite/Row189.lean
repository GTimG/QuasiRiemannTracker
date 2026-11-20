/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row189_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7702361527506915589898149244136263/184201542477917415000000000000000:ℝ),(1040161215629003577903392849636477851/14920324940711310615000000000000000:ℝ),(46331536447277352264145615355008649/1492032494071131061500000000000000:ℝ),(14462141064650186484239185769322971/7460162470355655307500000000000000:ℝ)],
![(543091726992011455669604347447619/4186398692679941250000000000000:ℝ),(176642599632933325985948727376801183/746016247035565530750000000000000:ℝ),(481487093653106559599910384752855071/3730081235177827653750000000000000:ℝ),(14017611455327129394178841468935537/746016247035565530750000000000000:ℝ)],
![(10017240956213053058875903141997069/92100771238958707500000000000000:ℝ),(1642964166874150183762765875760394471/7460162470355655307500000000000000:ℝ),(1070022395896362169379492509824162319/7460162470355655307500000000000000:ℝ),(222347057193220630451154769765530437/7460162470355655307500000000000000:ℝ)]]
theorem row189_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14462141064650186484239185769322971/13580811323811895173120000000000000000:ℝ) row189_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row189_coefficients,Fin.sum_univ_succ]
 ring
theorem row189_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row189_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row189_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row189_pos
