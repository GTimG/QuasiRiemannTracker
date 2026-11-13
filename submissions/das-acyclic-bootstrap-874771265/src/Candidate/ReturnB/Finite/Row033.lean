/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60202588187902665447321961536841/5925382076377978242187500:ℝ),(524138494180091162050629787718731/17776146229133934726562500:ℝ),(126678776635756908377432047590992/4444036557283483681640625:ℝ),(741741874270401151100834118208/80800664677881521484375:ℝ)],
![(5609758696546578756761484507931/296269103818898912109375:ℝ),(243756316566242992397320260059429/4444036557283483681640625:ℝ),(78401957178255839598080161580096/1481345519094494560546875:ℝ),(75595325394879476312738273549824/4444036557283483681640625:ℝ)],
![(1184884930603859571527443921691/134667774463135869140625:ℝ),(2055333962710138818772475389933/80800664677881521484375:ℝ),(9895462369025373122173620911936/404003323389407607421875:ℝ),(96164190867485831407158544768/12242524951194169921875:ℝ)]]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (751282741152233057868426131/5705430152543723520000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row033_coefficients,Fin.sum_univ_succ]
 ring
theorem row033_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row033_pos
