/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row157_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28715452959040456095336865347688413456319/326769766727874146718750000000000:ℝ),(67468006905119721981960049909295899427617/326769766727874146718750000000000:ℝ),(1530692598007590619165652564582375391259/10211555210246067084960937500000:ℝ),(1022923613356303059752438200037436561149/32676976672787414671875000000000:ℝ)],
![(28077912787638751143254614453939847371291/163384883363937073359375000000000:ℝ),(65274049390539686727725367746979718934953/163384883363937073359375000000000:ℝ),(1500299390504105204291907541477390540157/5270480108514099140625000000000:ℝ),(1862553320246961098614484905401133911241/32676976672787414671875000000000:ℝ)],
![(28443798062188682616345170024142655398979/326769766727874146718750000000000:ℝ),(66081380049142265318331099324910865049817/326769766727874146718750000000000:ℝ),(47028729276536805497074167278801172243893/326769766727874146718750000000000:ℝ),(1878152896056024870889168205142233768611/65353953345574829343750000000000:ℝ)]]
theorem row157_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1862553320246961098614484905401133911241/31936636277595440736959987712000000000000000:ℝ) row157_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row157_coefficients,Fin.sum_univ_succ]
 ring
theorem row157_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row157_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row157_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row157_pos
