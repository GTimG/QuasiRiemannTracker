/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row055_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17969511656336180329513757004127443883/16610775770661202968750000000:ℝ),(16016084071846941942215079518319887641/4983232731198360890625000000:ℝ),(634411314408064939723616749112464622029/199329309247934435625000000000:ℝ),(13960136454582454209722843995279896199/13288620616528962375000000000:ℝ)],
![(1957246229889907605908350798330620671/934356137099692666992187500:ℝ),(2325390443645278580475530561658750641/373742454839877066796875000:ℝ),(15347918983753556401606588259454698519/2491616365599180445312500000:ℝ),(337642544163559054547267498485201069/166107757706612029687500000:ℝ)],
![(757753284550299621647073734754093757/747484909679754133593750000:ℝ),(90004720055978843696046263990106679/29899396387190165343750000:ℝ),(247453303665836917419879105531152917/83053878853306014843750000:ℝ),(16326996449779298392632757439595623/16610775770661202968750000:ℝ)]]
theorem row055_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (16326996449779298392632757439595623/253663070919747779721953280000000000:ℝ) row055_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row055_coefficients,Fin.sum_univ_succ]
 ring
theorem row055_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row055_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row055_pos
