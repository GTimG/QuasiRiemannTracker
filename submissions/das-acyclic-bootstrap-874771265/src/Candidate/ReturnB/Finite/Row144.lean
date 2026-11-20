/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row144_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3373728845861533407077786337387194393/1865040617588913826875000000000000:ℝ),(8157185785833728765024778962410999211/1865040617588913826875000000000000:ℝ),(582869790564334110870236093555976377/169549147053537620625000000000000:ℝ),(1624083833914917698391974399391935329/1865040617588913826875000000000000:ℝ)],
![(50651531754336622881345812266676567/16954914705353762062500000000000:ℝ),(107969099809957958159241298276080317/16954914705353762062500000000000:ℝ),(757202284380153142358127640244938301/186504061758891382687500000000000:ℝ),(125702305188177913492869792966497051/186504061758891382687500000000000:ℝ)],
![(834592111306289826976278056984341279/373008123517782765375000000000000:ℝ),(1881961235927591095936330464897553267/373008123517782765375000000000000:ℝ),(2650716294315547317361059109757077519/746016247035565530750000000000000:ℝ),(553461218622593427419935540993153543/746016247035565530750000000000000:ℝ)]]
theorem row144_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (125702305188177913492869792966497051/173834384944792258215936000000000000000:ℝ) row144_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row144_coefficients,Fin.sum_univ_succ]
 ring
theorem row144_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row144_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row144_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row144_pos
