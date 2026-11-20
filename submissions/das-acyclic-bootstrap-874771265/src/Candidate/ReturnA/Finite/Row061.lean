/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![![(350079273193648453456224541259/6666055013795182558593750:ℝ),(498660449812277836963951526326/3333027506897591279296875:ℝ),(1892006770991696555207462759929/13332110027590365117187500:ℝ),(597489162024677932424261987143/13332110027590365117187500:ℝ)],
![(287225904297139268270933278343/3333027506897591279296875:ℝ),(810215774090978059783921022351/3333027506897591279296875:ℝ),(253506209020958235512716852766/1111009168965863759765625:ℝ),(5277958746798075687139034762/74067277931057583984375:ℝ)],
![(235977665843201904877061137727/6666055013795182558593750:ℝ),(26304907471137689238497039633/266642200551807302343750:ℝ),(609244731889023589805226191419/6666055013795182558593750:ℝ),(187574974558036252795173838321/6666055013795182558593750:ℝ)]]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (187574974558036252795173838321/3106606800953465487360000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ]
 ring
theorem row061_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row061_pos
