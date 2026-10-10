/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Cycle25.Assembly.Transport.GeometryFacts
import OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransport
import Cycle25.Assembly.Transport.CanonicalRayCube
import Cycle25.Assembly.Low.Normalizer
import Cycle25.Assembly.Transport.PrincipalRemainderNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Cycle25HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Cycle25.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Cycle25.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := transportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Cycle25.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Cycle25.h:ℝ)+ζ)),
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
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(Cycle25.lx:ℝ)) (Z^(Cycle25.ly:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+Cycle25.b)/6) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Cycle25.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(Cycle25.lx:ℝ)) (Z^(Cycle25.ly:ℝ)) Z e alpha height/normer‖≤
        C*(Z^((7/8:ℝ)-(4+Cycle25.b)/6-(Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta-(4+Cycle25.b)/6-1/4000+nu)+
          Z^(HeckeZeroSupremum.beta-(4+Cycle25.b)/6+e-Cycle25.theta*ellMin)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Cycle25WeightedLowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=>hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := Cycle25.Transport.PrincipalNormalized.actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  dsimp only [Cycle25.Transport.PrincipalSignal.signalShift] at hprincipal
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0 ≤ D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := transportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ) ≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  have hbinsHi (u : FreeRow) : (51/100:ℝ)+e*grid u ≤ 7/8 := by
    by_cases hgt : (51/100:ℝ) < 51/100+e*grid u
    · obtain ⟨j,s,hzero,hpole,has,_⟩ := (hbins u).2.2.2.2.2 hgt
      have hs : 0 < s.re := by linarith
      have hpole' : s ≠ 1 ∨ (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue ≠ 1 := by tauto
      exact has.trans ((HeckeZeroSupremum.zero_re_le_beta _ hs hpole' hzero).trans hβ)
    · linarith
  refine ⟨hnorm.1,idx,grid,hlabels,(fun u=>⟨(hbins u).1,hbinsHi u,(hbins u).2.2⟩),hray,?_⟩
  have hh := normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  simp only [neg_div] at hh ⊢
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^((7/8:ℝ)-(4+Cycle25.b)/6-(Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^((7/8:ℝ)-(4+Cycle25.b)/6-(Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ ((7/8:ℝ)-(4+Cycle25.b)/6-(Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50)+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D ≤ D+Cp := by linarith
  have h2 : Cp ≤ D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^((7/8:ℝ)-(4+Cycle25.b)/6-(Cycle25.ly/2-Cycle25.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta-(4+Cycle25.b)/6-1/4000+nu)+Z^(HeckeZeroSupremum.beta-(4+Cycle25.b)/6+e-Cycle25.theta*ellMin)) := by
      gcongr
    _ = _ := by ring

end SevenEighths.Cycle25HighRowFamily

end

end OAI
