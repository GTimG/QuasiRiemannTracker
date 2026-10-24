/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row215_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23603323501761870739267294986260159/11036091703874169847330968750000:ℝ),(17416564540414772091425790773875559/3678697234624723282443656250000:ℝ),(35619953662672664118270899247304127/11036091703874169847330968750000:ℝ),(6936382461184813567755187536937609/11036091703874169847330968750000:ℝ)],
![(157716666047714802177684742374361027/27590229259685424618327421875000:ℝ),(40001767286573647836043769706355793/3065581028853936068703046875000:ℝ),(258283237882012319570493524836202693/27590229259685424618327421875000:ℝ),(18586930619510620376916844534453861/9196743086561808206109140625000:ℝ)],
![(255937574815813887203970985300969459/55180458519370849236654843750000:ℝ),(19012504565391096558931896791793433/1672135106647601492019843750000:ℝ),(166825376895127944046295366963596267/18393486173123616412218281250000:ℝ),(128733207052852616786463924562574971/55180458519370849236654843750000:ℝ)]]
theorem row215_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6936382461184813567755187536937609/5143191508658471787482185728000000000:ℝ) row215_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row215_coefficients,Fin.sum_univ_succ]
 ring
theorem row215_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row215_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row215_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row215_pos
