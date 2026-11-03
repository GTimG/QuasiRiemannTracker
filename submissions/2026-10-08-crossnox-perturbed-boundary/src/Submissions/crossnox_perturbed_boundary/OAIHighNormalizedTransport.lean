/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighNormalizedTransport.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighCanonicalRayCube
import Submissions.crossnox_perturbed_boundary.OAIHighCentralNormalizer
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem perturbedTransportPoolOutside (S : Finset (Ideal O))
    (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_probe_transport_on_perturbed_boundary (K : ℕ) (e δ a b B ζ lengthShift saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (AsymmetricGeometry.boundary:ℝ)<HeckeZeroSupremum.beta)
    (ht : 0≤lengthShift) (ht' : lengthShift≤1 / 1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6+lengthShift)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := perturbedTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6+lengthShift) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((AsymmetricGeometry.rowBase:ℝ)+3*lengthShift/2+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ)) (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (AsymmetricGeometry.signalOffset) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((AsymmetricGeometry.rowBase:ℝ)+3*lengthShift/2+ζ))) T hT WC Yp
          W0 W1 (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ)) (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z e alpha height/normer‖≤
        C*(Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-63/800+8*e+(51*lengthShift/100+49*AsymmetricGeometry.skew/150)+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-1/3000+nu)+
          Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset+e-PrincipalSlotEstimate.perturbedBoundary*ellMin)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := canonical_probe_exists_perturbed_ray_cube M H hH K e δ a b B ζ lengthShift saving τ
    he he' hδ hδ' hζ hζ' ht (by linarith) hτ ha (ha.trans_le hab) hB hβ.le S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := perturbed_ray_normalizer_inverse M H hH S hS a b ha hab ell lengthShift
    (fun j=>hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := ProbePrincipalNormalized.actual_ray_principal_comparison_on_perturbed_boundary M H hH η S hS hTail
    a b B ellMin lengthShift ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by simpa only [PrincipalSlotEstimate.perturbedBoundary] using hβ) ht ht'
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := perturbedTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ)≤b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  have hsmallExponent : HeckeZeroSupremum.beta + AsymmetricGeometry.signalOffset +
      49 * AsymmetricGeometry.skew / 150 - 63 / 800 + 8 * e + 51 * lengthShift / 100 =
      HeckeZeroSupremum.beta + AsymmetricGeometry.signalOffset - 63 / 800 + 8 * e +
        (51 * lengthShift / 100 + 49 * AsymmetricGeometry.skew / 150) := by ring
  rw [hsmallExponent] at herror
  refine ⟨hnorm.1,idx,grid,hlabels,hbins,hray,?_⟩
  have hh := normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-63/800+8*e+(51*lengthShift/100+49*AsymmetricGeometry.skew/150))+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-63/800+8*e+(51*lengthShift/100+49*AsymmetricGeometry.skew/150)+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ (HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-63/800+8*e+(51*lengthShift/100+49*AsymmetricGeometry.skew/150)) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D≤D+Cp := by linarith
  have h2 : Cp≤D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-63/800+8*e+(51*lengthShift/100+49*AsymmetricGeometry.skew/150)+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset-1/3000+nu)+Z^(HeckeZeroSupremum.beta+ AsymmetricGeometry.signalOffset+e-PrincipalSlotEstimate.perturbedBoundary*ellMin)) := by
      gcongr
    _ = _ := by ring


end SevenEighths.ProbeHighRowFamily
end

end OAI
