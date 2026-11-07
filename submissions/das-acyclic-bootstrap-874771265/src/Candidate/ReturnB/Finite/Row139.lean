/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row139_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7645957799700529197263837389729/699556730206834858359375000:ℝ),(53098164634740024329354025052963/2098670190620504575078125000:ℝ),(88772383159730999403597956416/4769704978682964943359375:ℝ),(1108158384984735172995815679908/262333773827563071884765625:ℝ)],
![(419903238994886154096931884281/17488918255170871458984375:ℝ),(14606292379376654292928859956327/262333773827563071884765625:ℝ),(10769984668288456846373803399784/262333773827563071884765625:ℝ),(2452888980717279878702359207672/262333773827563071884765625:ℝ)],
![(1228500978450364890693815894342/87444591275854357294921875:ℝ),(8702240484264306565279664025866/262333773827563071884765625:ℝ),(6592711967122841150243958910804/262333773827563071884765625:ℝ),(1570873385599911991847617567964/262333773827563071884765625:ℝ)]]
theorem row139_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (277039596246183793248953919977/122256399655560344739840000000000:ℝ) row139_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row139_coefficients,Fin.sum_univ_succ]
 ring
theorem row139_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row139_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row139_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row139_pos
