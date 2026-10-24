/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row185_coefficients : Fin 3 → Fin 4 → ℝ := ![![(119688677006430761721637527323924122106833/16986033098386205746753125000000000:ℝ),(56959670537407165934668165271120508650239/3397206619677241149350625000000000:ℝ),(211957988861457463934457914354613471292633/16986033098386205746753125000000000:ℝ),(15614341555462839768366316310531761507757/5662011032795401915584375000000000:ℝ)],
![(136586011707590218878056871587011183775977/8493016549193102873376562500000000:ℝ),(333273311946507609198413966032766441603723/8493016549193102873376562500000000:ℝ),(258249318328768797237488363868210091183639/8493016549193102873376562500000000:ℝ),(20518866862409958236917431364913642368631/2831005516397700957792187500000000:ℝ)],
![(32043556949876497331259431557115914883141/3397206619677241149350625000000000:ℝ),(401833439858770591502957019346040422233899/16986033098386205746753125000000000:ℝ),(324508450995733590170618641616270741139811/16986033098386205746753125000000000:ℝ),(27629082083171223948084496085562776940539/5662011032795401915584375000000000:ℝ)]]
theorem row185_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (15614341555462839768366316310531761507757/86464541210479767774615620812800000000000000:ℝ) row185_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row185_coefficients,Fin.sum_univ_succ]
 ring
theorem row185_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row185_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row185_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row185_pos
