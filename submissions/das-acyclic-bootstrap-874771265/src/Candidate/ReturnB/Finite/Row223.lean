/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row223_coefficients : Fin 3 → Fin 4 → ℝ := ![![(185419648598721746261347771322811197/27590229259685424618327421875000:ℝ),(371092813028539953178540884749555453/27590229259685424618327421875000:ℝ),(471672329711659546509967859404096/62705066499285055950744140625:ℝ),(2676565943880824107446821096694748/3448778657460678077290927734375:ℝ)],
![(3874088266203100345586529412695911/229918577164045205152728515625:ℝ),(123014629020828836061959760764020537/3448778657460678077290927734375:ℝ),(77543240021625693398033359089278104/3448778657460678077290927734375:ℝ),(463598941600945406248257262155416/127732542868914002862626953125:ℝ)],
![(38177213895813347048863144465121006/3448778657460678077290927734375:ℝ),(28654171435244515233905283864865682/1149592885820226025763642578125:ℝ),(6728709948383460376492812366962636/383197628606742008587880859375:ℝ),(12706127177921215707672462298187684/3448778657460678077290927734375:ℝ)]]
theorem row223_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (669141485970206026861705274173687/1607247346455772433588183040000000000:ℝ) row223_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row223_coefficients,Fin.sum_univ_succ]
 ring
theorem row223_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row223_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row223_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row223_pos
