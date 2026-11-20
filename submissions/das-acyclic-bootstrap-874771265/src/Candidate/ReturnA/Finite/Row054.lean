/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row054_coefficients : Fin 3 → Fin 4 → ℝ := ![![(98911097910966739081035933412394384297569/747489813779776939593750000000:ℝ),(14059287487311354257591550955508585612317/35594753037132235218750000000:ℝ),(2294999839612324436348412686126418220544/5839764170154507340576171875:ℝ),(761140918019597339271174531120278270848/5839764170154507340576171875:ℝ)],
![(24522795436235176005161859203551674316421/93436226722472117449218750000:ℝ),(73197004924650990802914204648834612190853/93436226722472117449218750000:ℝ),(1517217197918981665434893811107965106176/1946588056718169113525390625:ℝ),(503171153064808459863105157299987233792/1946588056718169113525390625:ℝ)],
![(225175696936313752020063973322707267259/1730300494860594767578125000:ℝ),(725862238906583397297148948437188220577/1868724534449442348984375000:ℝ),(2256760193906421099371408152619601120256/5839764170154507340576171875:ℝ),(748408653581152489661302237780024957952/5839764170154507340576171875:ℝ)]]
theorem row054_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (730867825762844228184865466582055623/11147376056518305908785152000000000000:ℝ) row054_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row054_coefficients,Fin.sum_univ_succ]
 ring
theorem row054_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row054_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row054_pos
