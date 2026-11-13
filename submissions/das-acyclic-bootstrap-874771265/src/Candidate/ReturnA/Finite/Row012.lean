/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row012_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9238521148095340718868875699290684129/3737449068898884697968750000:ℝ),(27447926454990598565471384762644948931/3737449068898884697968750000:ℝ),(1087253059085748084775931972936148307/149497962755955387918750000:ℝ),(427234286964740471736776786192830613/177973765185661176093750000:ℝ)],
![(1274129108287447172104290623855848327/266960647778491764140625000:ℝ),(1059668637936709839560466562218772187/74748981377977693959375000:ℝ),(26227764293896908971941172358233919583/1868724534449442348984375000:ℝ),(412140520447496567474244347369312057/88986882592830588046875000:ℝ)],
![(8604664980781982479223741524693331449/3737449068898884697968750000:ℝ),(3650235010568133088521641212034849717/533921295556983528281250000:ℝ),(25290345168710888075033702049167061241/3737449068898884697968750000:ℝ),(397303041453565080147506578672211651/177973765185661176093750000:ℝ)]]
theorem row012_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (397303041453565080147506578672211651/2717836448065415535856189440000000000:ℝ) row012_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row012_coefficients,Fin.sum_univ_succ]
 ring
theorem row012_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row012_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row012_pos
