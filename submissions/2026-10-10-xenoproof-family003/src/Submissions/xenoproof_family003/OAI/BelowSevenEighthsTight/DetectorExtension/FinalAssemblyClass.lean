/- UNVERIFIED until compilation/replay. Actual physical class bound conditional on retuned source moments. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.DetectorExtension.FinalAssemblySourceCount
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.DetectorExtension.CentralClassArithmetic
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.DetectorExtension.SourceAmplitudeClasses
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.RetunedSourceMoments

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_class_from_raw_moments_retuned (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss total : ℝ)
    (htotal : 1/6≤total) (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=total)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ κ₀ capacity ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hκ₀ : 13/18≤κ₀) (hκ₀u : κ₀≤3/4) (hcapacity : capacity=κ₀+2*Δ) (hcapacity1 : capacity≤1) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost) (counts : _root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters M H εm) :
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → 51/100<a → a≤1 → 0≤C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt_retuned M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z κ₀ capacity
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      rows'.Nonempty → 0≤q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent_retuned κ₀ (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss+total*(-4/25+q+mesh)) := by
  have hdmax0 : 0<dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcount⟩ :=
    adaptive_source_count_from_raw_moments_retuned M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C,hC,hphysical⟩ := actual_class_cube_arithmetic_retuned M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss total
    (by linarith) he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches_retuned M H hH S hS hmax η
    κ₀ dmin dmax τ ε e κ cost margin R mesh n hκ₀ hκ₀u hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0<ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi (by rw [hellsum];exact htotal) W (fun _=>b) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ κ₀ capacity ν C0 q i hi ha ha' hε.le hε1 hΔ hκ₀ hκ₀u hcapacity hcapacity1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=>ell j/d) Q bin
    (by linarith) (fun j _=>div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum_retuned Finset.univ ell total d hellsum];exact div_pos (by linarith) hd0) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent_retuned κ₀ (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=>hrows u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) hcard i hi
    (fun u hu=>hnext u (hsub hu)) t ht
    (fun u hu=>source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent_retuned κ₀ (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss+total*(-4/25+q+mesh)=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent_retuned κ₀ (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss+total*(-4/25+q+mesh)) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI

#print axioms OAI.SevenEighths.ProbeFinalAssembly.actual_nonfloor_class_from_raw_moments_retuned
