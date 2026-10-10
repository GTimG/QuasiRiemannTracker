import WeightedQRH.HighRows.NonfloorClass
import WeightedQRH.HighRows.CentralExponent
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyClass
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.WeightedHighRowFamily
open ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0 < dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=167/1000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀≤b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (μ : ℝ)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*167/1000+(13243/1000)*e)+μ≤1/40000) (counts : CountParameters M H εm) :
    ∃C : ℝ,0 < C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤d → d-v≤μ →
      51/100 < a → a≤7/8 → WeightedQRH.OriginalBranch d a → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ) < a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(WeightedQRH.signal WeightedQRH.theta-1/40000-WeightedQRH.centralScale a e) := by
  obtain ⟨C,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm 0 ν logCost heightCost momentCost hεm (by norm_num) (by norm_num) hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hbranch hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(WeightedQRH.signal WeightedQRH.theta-1/40000-WeightedQRH.centralScale a e)
  have hb : 0≤bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=>ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha (by linarith) hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      have hs := WeightedQRH.actual_central_class_saving N
        (hdmin.le.trans hd) hv hv' hdv ha ha' hp.1 hp.2.1 hbranch
        hε.le hεm.le hR hν.le he.le heps.le hfinal
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring

end SevenEighths.WeightedHighRowFamily

end

end OAI
