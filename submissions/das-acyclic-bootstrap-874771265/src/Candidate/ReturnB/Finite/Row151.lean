/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row151_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6083870661195864090162317577862319939/18650406175889138268750000000000:ℝ),(333046400253664136148890354837781986351/466260154397228456718750000000000:ℝ),(428296089262990094993754690696867782267/932520308794456913437500000000000:ℝ),(13270278619605237060022094284779586303/186504061758891382687500000000000:ℝ)],
![(31310708041797829158125478119738560909/46626015439722845671875000000000:ℝ),(67779995312154225449867372997444582607/46626015439722845671875000000000:ℝ),(42537865690787225030836827369534447389/46626015439722845671875000000000:ℝ),(6063796450175161170254996861247175691/46626015439722845671875000000000:ℝ)],
![(37469424828767402375986138848865429909/93252030879445691343750000000000:ℝ),(84589179472105000417345065563545737247/93252030879445691343750000000000:ℝ),(57722870853238520197762284211328481767/93252030879445691343750000000000:ℝ),(10598082557000219452361319990773174429/93252030879445691343750000000000:ℝ)]]
theorem row151_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6063796450175161170254996861247175691/44501602545866818103279616000000000000000:ℝ) row151_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row151_coefficients,Fin.sum_univ_succ]
 ring
theorem row151_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row151_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row151_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row151_pos
