/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row224_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1553779286585334995013357015324649/36786972346247232824436562500000:ℝ),(868124902755977522957722828119623/12262324115415744274812187500000:ℝ),(53425223337809206810772075153753/1672135106647601492019843750000:ℝ),(13353032223786492895068822391391/6131162057707872137406093750000:ℝ)],
![(3591282347121650888756569445675201/27590229259685424618327421875000:ℝ),(6561833795159095460521945676801719/27590229259685424618327421875000:ℝ),(716596535301754668048415992268427/5518045851937084923665484375000:ℝ),(523148631658356731263181230215617/27590229259685424618327421875000:ℝ)],
![(6003465810720873176588864755518241/55180458519370849236654843750000:ℝ),(12154558759396225388638114328115347/55180458519370849236654843750000:ℝ),(719330619003582886340191541879761/5016405319942804476059531250000:ℝ),(328500079589352697614965477616053/11036091703874169847330968750000:ℝ)]]
theorem row224_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13353032223786492895068822391391/11161439905942864122140160000000000:ℝ) row224_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row224_coefficients,Fin.sum_univ_succ]
 ring
theorem row224_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row224_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row224_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row224_pos
